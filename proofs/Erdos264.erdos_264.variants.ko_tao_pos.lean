import FormalConjectures.ErdosProblems.«264»
import Mathlib.Analysis.SpecificLimits.Basic

/-! Kovač and Tao's reciprocal-tail separation estimate (https://arxiv.org/abs/2406.17593,
Section 6) gives uniqueness in sufficiently narrow bands. Assigning one index to each
rational tail and perturbation bound gives a deterministic construction. -/

open Filter Asymptotics Set
open scoped Topology Asymptotics

namespace TaoAssemble

lemma abs_bound {b : ℕ → ℤ} (hA : BddAbove (Set.range b)) (hB : BddBelow (Set.range b)) :
    ∃ C : ℕ, ∀ n, |b n| ≤ (C : ℤ) := by
  obtain ⟨u, hu⟩ := hA
  obtain ⟨l, hl⟩ := hB
  refine ⟨l.natAbs + u.natAbs, fun n => abs_le.mpr ⟨?_, ?_⟩⟩
  · have h : l ≤ b n := hl ⟨n, rfl⟩
    push_cast
    have hl' : -|l| ≤ l := (abs_le.mp (le_rfl : |l| ≤ |l|)).1
    linarith only [h, hl', abs_nonneg u]
  · have h : b n ≤ u := hu ⟨n, rfl⟩
    push_cast
    linarith only [h, le_abs_self u, abs_nonneg l]

lemma interval_of_abs {a F w : ℕ → ℕ} {b : ℕ → ℤ} {C : ℕ}
    (ha : ∀ n, a n = F n ∨ a n = F n + w n) (hb : ∀ n, |b n| ≤ (C : ℤ)) (n : ℕ) :
    (F n : ℤ) - (C : ℤ) ≤ (a n : ℤ) + b n ∧
      (a n : ℤ) + b n ≤ (F n : ℤ) + (w n : ℤ) + (C : ℤ) := by
  obtain ⟨hl, hu⟩ := abs_le.mp (hb n)
  rcases ha n with he | he <;> rw [he] <;> push_cast <;> omega

lemma rational_tail {d : ℕ → ℤ} (n : ℕ) (hs : Summable (fun k => (1 : ℝ) / (d k : ℝ)))
    (hrat : ¬ Irrational (∑' k, (1 : ℝ) / (d k : ℝ))) :
    ∃ q : ℚ, (∑' k, (1 : ℝ) / (d (n + k) : ℝ)) = (q : ℝ) := by
  obtain ⟨q, hq⟩ := exists_rat_of_not_irrational hrat
  refine ⟨q - ∑ k ∈ Finset.range n, (1 : ℚ) / (d k : ℚ), ?_⟩
  have h : (∑ k ∈ Finset.range n, (1 : ℝ) / (d k : ℝ)) +
      (∑' k, (1 : ℝ) / (d (n + k) : ℝ)) = (q : ℝ) := by
    rw [← hq]
    simpa only [Nat.add_comm n] using hs.sum_add_tsum_nat_add n
  push_cast
  linarith only [h]

end TaoAssemble

namespace TaoGrowth

noncomputable def width (F : ℕ → ℕ) (n : ℕ) : ℕ :=
  min (F (n - 1)) ⌊(F n : ℝ) / F (n - 1)⌋₊

private lemma shifted_ratio {F : ℕ → ℕ}
    (hF : Tendsto (fun n => (F (n + 1) : ℝ) / F n) atTop atTop) :
    Tendsto (fun n => (F n : ℝ) / F (n - 1)) atTop atTop := by
  refine (hF.comp (tendsto_sub_atTop_nat 1)).congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  change (F (n - 1 + 1) : ℝ) / F (n - 1) = _
  rw [Nat.sub_add_cancel hn]

private lemma ratio_le_numerator (x y : ℕ) : (x : ℝ) / (y : ℝ) ≤ x := by
  by_cases hy : y = 0
  · simp [hy]
  have hy₁ : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hy
  have hy₀ : 0 < (y : ℝ) := zero_lt_one.trans_le hy₁
  exact (div_le_iff₀ hy₀).2 (le_mul_of_one_le_right (by positivity) hy₁)

theorem tendsto_nat {F : ℕ → ℕ}
    (hF : Tendsto (fun n => (F (n + 1) : ℝ) / F n) atTop atTop) :
    Tendsto F atTop atTop := by
  have h : Tendsto (fun n => (F n : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun n => ratio_le_numerator (F n) (F (n - 1))) (shifted_ratio hF)
  apply tendsto_atTop.2
  intro k
  filter_upwards [tendsto_atTop.1 h (k : ℝ)] with n hn
  exact_mod_cast hn

theorem width_tendsto {F : ℕ → ℕ}
    (hF : Tendsto (fun n => (F (n + 1) : ℝ) / F n) atTop atTop) :
    Tendsto (width F) atTop atTop := by
  have hp : Tendsto (fun n => F (n - 1)) atTop atTop :=
    (tendsto_nat hF).comp (tendsto_sub_atTop_nat 1)
  have hf : Tendsto (fun n => ⌊(F n : ℝ) / F (n - 1)⌋₊) atTop atTop :=
    (tendsto_nat_floor_atTop (α := ℝ)).comp (shifted_ratio hF)
  apply tendsto_atTop.2
  intro k
  filter_upwards [tendsto_atTop.1 hp k,tendsto_atTop.1 hf k] with n hn hf
  exact le_min hn hf

private lemma width_le_prev (F : ℕ → ℕ) (n : ℕ) :
    ((width F n : ℕ) : ℝ) ≤ (F (n - 1) : ℝ) := by
  exact_mod_cast (min_le_left (F (n - 1)) ⌊(F n : ℝ) / F (n - 1)⌋₊)

private lemma width_succ_le_ratio (F : ℕ → ℕ) (n : ℕ) :
    (width F (n + 1) : ℝ) ≤ (F (n + 1) : ℝ) / F n := by
  unfold width
  rw [Nat.add_sub_cancel]
  exact (Nat.cast_le.2 (min_le_right _ _)).trans (Nat.floor_le (by positivity))

theorem conditions {F : ℕ → ℕ}
    (hF : Tendsto (fun n => (F (n + 1) : ℝ) / F n) atTop atTop) (C : ℕ) :
    ∀ᶠ n in atTop, 1 ≤ F n ∧
      (256 : ℝ) * (F n : ℝ) ≤ (F (n + 1) : ℝ) ∧
      2 * C < width F n ∧ (width F n : ℝ) ≤ (F n : ℝ) / 4 ∧
      (width F (n + 1) : ℝ) ≤ (F (n + 1) : ℝ) / F n := by
  have hPrev : Tendsto (fun n => F (n - 1)) atTop atTop :=
    (tendsto_nat hF).comp (tendsto_sub_atTop_nat 1)
  filter_upwards [tendsto_atTop.1 (tendsto_nat hF) 1, tendsto_atTop.1 hF (256 : ℝ),
    tendsto_atTop.1 (width_tendsto hF) (2 * C + 1), tendsto_atTop.1 (shifted_ratio hF) (4 : ℝ),
    tendsto_atTop.1 hPrev 1] with n hn h256 hnWidth h4 hp
  have hFn : 0 < (F n : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hn)
  have hFp : 0 < (F (n - 1) : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hp)
  have hh : 4 * (F (n - 1) : ℝ) ≤ (F n : ℝ) := (le_div_iff₀ hFp).1 h4
  refine ⟨hn,(le_div_iff₀ hFn).1 h256,by omega,?_,width_succ_le_ratio F n⟩
  apply (width_le_prev F n).trans
  linarith only [hh]

theorem width_div_tendsto {F : ℕ → ℕ}
    (hF : Tendsto (fun n => (F (n + 1) : ℝ) / F n) atTop atTop) :
    Tendsto (fun n => (width F n : ℝ) / F n) atTop (𝓝 0) := by
  have hb : Tendsto (fun n => (F (n - 1) : ℝ) / F n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, inv_div] using
      (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp (shifted_ratio hF)
  exact squeeze_zero (fun n => by positivity)
    (fun n => div_le_div_of_nonneg_right (width_le_prev F n) (by positivity)) hb

theorem equiv_eventually {F a : ℕ → ℕ}
    (hF : Tendsto (fun n => (F (n + 1) : ℝ) / F n) atTop atTop)
    (ha : ∀ᶠ n in atTop, a n = F n ∨ a n = F n + width F n) :
    (fun n => (a n : ℝ)) ~[atTop] (fun n => (F n : ℝ)) := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  change Tendsto (fun n => (a n : ℝ) / F n) atTop (𝓝 1)
  have hOne : Tendsto (fun n => 1 + (width F n : ℝ) / F n) atTop (𝓝 1) := by
    simpa only [add_zero,Pi.add_def] using tendsto_const_nhds.add (width_div_tendsto hF)
  have hBounds : ∀ᶠ n in atTop, 1 ≤ (a n : ℝ) / F n ∧
      (a n : ℝ) / F n ≤ 1 + (width F n : ℝ) / F n := by
    filter_upwards [ha,tendsto_atTop.1 (tendsto_nat hF) 1] with n he hn
    have hn₀ : (F n : ℝ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hn).ne'
    have hw : 0 ≤ (width F n : ℝ) / F n := by positivity
    rcases he with he | he
    · rw [he, div_self hn₀]
      exact ⟨le_rfl, le_add_of_nonneg_right hw⟩
    · rw [he,Nat.cast_add,add_div,div_self hn₀]
      exact ⟨le_add_of_nonneg_right hw, le_rfl⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hOne
    (hBounds.mono (fun _ h => h.1)) (hBounds.mono (fun _ h => h.2))

theorem equiv {F a : ℕ → ℕ}
    (hF : Tendsto (fun n => (F (n + 1) : ℝ) / F n) atTop atTop)
    (ha : ∀ n, a n = F n ∨ a n = F n + width F n) :
    (fun n => (a n : ℝ)) ~[atTop] (fun n => (F n : ℝ)) :=
  equiv_eventually hF (Eventually.of_forall ha)

end TaoGrowth

namespace TaoDiagonal

private lemma exists_slots (threshold : ℕ → ℕ) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ i, threshold i ≤ s i := by
  let s : ℕ → ℕ := Nat.rec (threshold 0) (fun i v => max (threshold (i + 1)) (v + 1))
  have hs (i : ℕ) : s (i + 1) = max (threshold (i + 1)) (s i + 1) := rfl
  refine ⟨s, strictMono_nat_of_lt_succ (fun i => ?_), ?_⟩
  · rw [hs]
    exact (Nat.lt_succ_self _).trans_le (le_max_right _ _)
  · intro i
    cases i with
    | zero => exact le_rfl
    | succ i => rw [hs]; exact le_max_left _ _

private lemma separated_endpoint {F w C : ℕ} (hw : 2 * C < w) (d : ℤ) :
    ¬ |d - (F : ℤ)| ≤ (C : ℤ) ∨ ¬ |d - ((F + w : ℕ) : ℤ)| ≤ (C : ℤ) := by
  by_cases h : |d - (F : ℤ)| ≤ (C : ℤ)
  · right
    intro hh
    have h1 := (abs_le.mp h).2
    have h2 := (abs_le.mp hh).1
    omega
  · exact Or.inl h

/-- A choice between endpoints more than twice the tolerance apart excludes
every candidate denominator sequence at a code-specific index. -/
theorem exists_sequence (F w : ℕ → ℕ) (M : ℕ → ℕ)
    (Good : ℕ → ℚ → (ℕ → ℤ) → Prop)
    (hw : ∀ C n, M C ≤ n → 2 * C < w n)
    (hu : ∀ {C q d e}, Good C q d → Good C q e → ∀ n, M C ≤ n → d n = e n) :
    ∃ a : ℕ → ℕ, (∀ n, a n = F n ∨ a n = F n + w n) ∧
      ∀ C q d, Good C q d → ∃ n, M C ≤ n ∧ ¬ |d n - (a n : ℤ)| ≤ (C : ℤ) := by
  classical
  let threshold (i : ℕ) : ℕ :=
    match Encodable.decode (α := ℕ × ℚ) i with
    | some p => M p.1
    | none => 0
  obtain ⟨s, hs, hsM⟩ := exists_slots threshold
  let slot (p : ℕ × ℚ) : ℕ := s (Encodable.encode p)
  have hslot : Function.Injective slot := hs.injective.comp Encodable.encode_injective
  have hM (p : ℕ × ℚ) : M p.1 ≤ slot p := by
    simpa only [slot, threshold, Encodable.encodek] using hsM (Encodable.encode p)
  have hChoice (p : ℕ × ℚ) : ∃ z : ℕ,
      (z = F (slot p) ∨ z = F (slot p) + w (slot p)) ∧
      ∀ d, Good p.1 p.2 d → ¬ |d (slot p) - (z : ℤ)| ≤ (p.1 : ℤ) := by
    by_cases h : ∃ d, Good p.1 p.2 d
    · obtain ⟨d, hd⟩ := h
      have hEq (e : ℕ → ℤ) (he : Good p.1 p.2 e) : e (slot p) = d (slot p) :=
        hu he hd (slot p) (hM p)
      rcases separated_endpoint (hw p.1 (slot p) (hM p)) (d (slot p)) with hL | hR
      · exact ⟨F (slot p), Or.inl rfl, fun e he => by rwa [hEq e he]⟩
      · exact ⟨F (slot p) + w (slot p), Or.inr rfl, fun e he => by rwa [hEq e he]⟩
    · exact ⟨F (slot p), Or.inl rfl, fun d hd => (h ⟨d, hd⟩).elim⟩
  choose z hz hgood using hChoice
  let a := Function.extend slot z F
  have ha (p : ℕ × ℚ) : a (slot p) = z p := hslot.extend_apply z F p
  refine ⟨a, ?_, ?_⟩
  · intro n
    by_cases h : ∃ p, slot p = n
    · obtain ⟨p, rfl⟩ := h
      rw [ha]
      exact hz p
    · exact Or.inl (Function.extend_apply' z F n h)
  · intro C q d hd
    refine ⟨slot (C, q), hM (C, q), ?_⟩
    rw [ha]
    exact hgood (C, q) d hd

end TaoDiagonal

namespace TaoGap

noncomputable def tail (d : ℕ → ℤ) (m : ℕ) : ℝ :=
  ∑' k : ℕ, (1 : ℝ) / (d (m + k) : ℝ)

def Band (F w : ℕ → ℕ) (C m : ℕ) (d : ℕ → ℤ) : Prop :=
  ∀ n, m ≤ n → (F n : ℤ) - C ≤ d n ∧ d n ≤ (F n : ℤ) + w n + C

def Growth (F w : ℕ → ℕ) (C m : ℕ) : Prop :=
  ∀ n, m ≤ n → 1 ≤ F n ∧ (256 : ℝ) * (F n : ℝ) ≤ (F (n + 1) : ℝ) ∧
    C ≤ w n ∧ (w n : ℝ) ≤ (F n : ℝ) / 4 ∧
    (w (n + 1) : ℝ) ≤ (F (n + 1) : ℝ) / F n

variable {F w : ℕ → ℕ} {C m : ℕ} {d e : ℕ → ℤ}

private lemma base_pos (hG : Growth F w C m) {n : ℕ} (hn : m ≤ n) :
    0 < (F n : ℝ) := by
  exact_mod_cast (hG n hn).1

private lemma band_cast (hd : Band F w C m d) {n : ℕ} (hn : m ≤ n) :
    (F n : ℝ) - C ≤ (d n : ℝ) ∧ (d n : ℝ) ≤ (F n : ℝ) + w n + C := by
  have h := hd n hn
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

private lemma band_bounds (hG : Growth F w C m) (hd : Band F w C m d)
    {n : ℕ} (hn : m ≤ n) :
    (F n : ℝ) / 2 ≤ (d n : ℝ) ∧ (d n : ℝ) ≤ 2 * (F n : ℝ) := by
  obtain ⟨hlo,hhi⟩ := band_cast hd hn
  obtain ⟨_,_,hC,hw,_⟩ := hG n hn
  have hCR : (C : ℝ) ≤ w n := by exact_mod_cast hC
  have hF := base_pos hG hn
  exact ⟨by linarith, by linarith⟩

private lemma geometric_growth (hG : Growth F w C m) {n : ℕ} (hn : m ≤ n) (k : ℕ) :
    (F n : ℝ) * (2 : ℝ) ^ k ≤ (F (n + k) : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, Nat.add_succ]
    have h := hG (n + k) (by omega)
    have hF : (0 : ℝ) ≤ F (n + k) := Nat.cast_nonneg _
    calc
      (F n : ℝ) * 2 ^ k * 2 ≤ (F (n + k) : ℝ) * 2 :=
        mul_le_mul_of_nonneg_right ih (by norm_num)
      _ ≤ (F ((n + k) + 1) : ℝ) := by linarith [h.2.1]

private lemma div_geometric (r q : ℝ) (k : ℕ) :
    r / (q * 2 ^ k) = (r / q) * (1 / 2) ^ k := by
  rw [div_pow, one_pow, mul_div_assoc', mul_one, div_div]

private lemma summable_from (hG : Growth F w C m) (hd : Band F w C m d)
    {n : ℕ} (hn : m ≤ n) :
    Summable (fun k : ℕ => (1 : ℝ) / (d (n + k) : ℝ)) := by
  have hF := base_pos hG hn
  apply Summable.of_nonneg_of_le
    (f := fun k : ℕ => (2 / (F n : ℝ)) * (1 / 2) ^ k) _ _
    (summable_geometric_two.mul_left _)
  · intro k
    have hFn := base_pos hG (by omega : m ≤ n + k)
    have hLow := (band_bounds hG hd (by omega : m ≤ n + k)).1
    exact one_div_nonneg.mpr (by linarith)
  · intro k
    have hLow := (band_bounds hG hd (by omega : m ≤ n + k)).1
    have hGeo := geometric_growth hG hn k
    calc
      (1 : ℝ) / (d (n + k) : ℝ) ≤ 1 / (((F n : ℝ) * 2 ^ k) / 2) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      _ = (2 / (F n : ℝ)) * (1 / 2) ^ k := by
        rw [div_div_eq_mul_div, one_mul, div_geometric]

/-- Reciprocal tails of sequences in the band are summable. -/
theorem summable_tail (hG : Growth F w C m) (hd : Band F w C m d) :
    Summable (fun k : ℕ => (1 : ℝ) / (d (m + k) : ℝ)) :=
  summable_from hG hd le_rfl

private lemma abs_recip_sub {a b : ℤ} (ha : 0 < (a : ℝ)) (hb : 0 < (b : ℝ)) :
    |(1 : ℝ) / (a : ℝ) - 1 / (b : ℝ)| =
      |(b : ℝ) - (a : ℝ)| / ((a : ℝ) * (b : ℝ)) := by
  rw [div_sub_div _ _ ha.ne' hb.ne', one_mul, mul_one, abs_div, abs_of_pos (mul_pos ha hb)]

private lemma head_gap (hG : Growth F w C m) (hd : Band F w C m d) (he : Band F w C m e)
    {n : ℕ} (hn : m ≤ n) (hne : d n ≠ e n) :
    (1 / 4 : ℝ) / (F n : ℝ) ^ 2 ≤ |(1 : ℝ) / (d n : ℝ) - 1 / (e n : ℝ)| := by
  have hF := base_pos hG hn
  obtain ⟨hdLow,hdHigh⟩ := band_bounds hG hd hn
  obtain ⟨heLow,heHigh⟩ := band_bounds hG he hn
  have hdPos : (0 : ℝ) < d n := by linarith
  have hePos : (0 : ℝ) < e n := by linarith
  have hAbsInt : (1 : ℤ) ≤ |e n - d n| := by
    rw [le_abs]
    omega
  have hAbs : (1 : ℝ) ≤ |(e n : ℝ) - (d n : ℝ)| := by exact_mod_cast hAbsInt
  have hProd : (d n : ℝ) * (e n : ℝ) ≤ 4 * (F n : ℝ) ^ 2 := by
    calc
      _ ≤ (2 * (F n : ℝ)) * (2 * (F n : ℝ)) :=
        mul_le_mul hdHigh heHigh hePos.le (by positivity)
      _ = _ := by ring
  rw [abs_recip_sub hdPos hePos, div_div]
  exact (one_div_le_one_div_of_le (mul_pos hdPos hePos) hProd).trans
    (div_le_div_of_nonneg_right hAbs (mul_pos hdPos hePos).le)

private lemma gap_upper (hG : Growth F w C m) (hd : Band F w C m d) (he : Band F w C m e)
    {n : ℕ} (hn : m ≤ n) :
    |(1 : ℝ) / (d n : ℝ) - 1 / (e n : ℝ)| ≤ 12 * (w n : ℝ) / (F n : ℝ) ^ 2 := by
  have hF := base_pos hG hn
  have hdLow := (band_bounds hG hd hn).1
  have heLow := (band_bounds hG he hn).1
  have hdPos : (0 : ℝ) < d n := by linarith
  have hePos : (0 : ℝ) < e n := by linarith
  have hC : (C : ℝ) ≤ w n := by exact_mod_cast (hG n hn).2.2.1
  obtain ⟨hdlo,hdhi⟩ := band_cast hd hn
  obtain ⟨helo,hehi⟩ := band_cast he hn
  have hAbs : |(e n : ℝ) - (d n : ℝ)| ≤ 3 * (w n : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hProd : (F n : ℝ) ^ 2 / 4 ≤ (d n : ℝ) * (e n : ℝ) := by
    calc
      _ = ((F n : ℝ) / 2) * ((F n : ℝ) / 2) := by ring
      _ ≤ _ := mul_le_mul hdLow heLow (by positivity) hdPos.le
  rw [abs_recip_sub hdPos hePos]
  calc
    _ ≤ (3 * (w n : ℝ)) / ((d n : ℝ) * (e n : ℝ)) :=
      div_le_div_of_nonneg_right hAbs (mul_pos hdPos hePos).le
    _ ≤ (3 * (w n : ℝ)) / ((F n : ℝ) ^ 2 / 4) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hProd
    _ = _ := by rw [div_div_eq_mul_div]; ring

private lemma next_gap (hG : Growth F w C m) (hd : Band F w C m d) (he : Band F w C m e)
    {n : ℕ} (hn : m ≤ n) :
    |(1 : ℝ) / (d (n + 1) : ℝ) - 1 / (e (n + 1) : ℝ)| ≤
      (12 / 256 : ℝ) / (F n : ℝ) ^ 2 := by
  have hn' : m ≤ n + 1 := by omega
  have hp := base_pos hG hn
  have hp' := base_pos hG hn'
  have hProd : (256 : ℝ) * (F n : ℝ) ^ 2 ≤ (F n : ℝ) * (F (n + 1) : ℝ) := by
    calc
      _ = (F n : ℝ) * (256 * (F n : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hG n hn).2.1 hp.le
  calc
    _ ≤ 12 * (w (n + 1) : ℝ) / (F (n + 1) : ℝ) ^ 2 := gap_upper hG hd he hn'
    _ ≤ 12 * ((F (n + 1) : ℝ) / F n) / (F (n + 1) : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hG n hn).2.2.2.2 (by norm_num))
        (by positivity)
    _ = 12 / ((F n : ℝ) * (F (n + 1) : ℝ)) := by
      field_simp [hp.ne', hp'.ne']
    _ ≤ 12 / (256 * (F n : ℝ) ^ 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hProd
    _ = _ := by rw [div_div]

private lemma tail_gap (hG : Growth F w C m) (hd : Band F w C m d) (he : Band F w C m e)
    {n : ℕ} (hn : m ≤ n) :
    |tail d (n + 1) - tail e (n + 1)| ≤ (24 / 256 : ℝ) / (F n : ℝ) ^ 2 := by
  let r (k : ℕ) := (1 : ℝ) / (d ((n + 1) + k) : ℝ) - 1 / (e ((n + 1) + k) : ℝ)
  let A : ℝ := (12 / 256 : ℝ) / (F n : ℝ) ^ 2
  have hn' : m ≤ n + 1 := by omega
  have hdSum := summable_from hG hd hn'
  have heSum := summable_from hG he hn'
  have hSum : Summable r := hdSum.sub heSum
  have hTerm (k : ℕ) : |r k| ≤ A * (1 / 2) ^ k := by
    have hp := base_pos hG hn
    have hGeo := geometric_growth hG hn k
    have hBase : (F n : ℝ) ≤ F (n + k) := by
      calc
        _ = (F n : ℝ) * 1 := by rw [mul_one]
        _ ≤ (F n : ℝ) * 2 ^ k :=
          mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num)) hp.le
        _ ≤ _ := hGeo
    have hSq : (F n : ℝ) ^ 2 * 2 ^ k ≤ (F (n + k) : ℝ) ^ 2 := by
      calc
        _ = ((F n : ℝ) * 2 ^ k) * (F n : ℝ) := by ring
        _ ≤ (F (n + k) : ℝ) * (F (n + k) : ℝ) :=
          mul_le_mul hGeo hBase hp.le (Nat.cast_nonneg _)
        _ = _ := by rw [pow_two]
    dsimp only [r]
    rw [show (n + 1) + k = (n + k) + 1 by omega]
    calc
      _ ≤ (12 / 256 : ℝ) / (F (n + k) : ℝ) ^ 2 := next_gap hG hd he (by omega)
      _ ≤ (12 / 256 : ℝ) / ((F n : ℝ) ^ 2 * 2 ^ k) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hSq
      _ = A * (1 / 2) ^ k := div_geometric _ _ _
  have hSub : tail d (n + 1) - tail e (n + 1) = ∑' k, r k := (hdSum.tsum_sub heSum).symm
  rw [hSub]
  calc
    |∑' k, r k| ≤ ∑' k, |r k| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hSum.norm
    _ ≤ ∑' k : ℕ, A * (1 / 2) ^ k :=
      hSum.abs.tsum_le_tsum hTerm (summable_geometric_two.mul_left _)
    _ = _ := by
      rw [tsum_mul_left, tsum_geometric_two]
      dsimp [A]
      ring

private lemma tail_succ (hG : Growth F w C m) (hd : Band F w C m d)
    {n : ℕ} (hn : m ≤ n) :
    tail d n = 1 / (d n : ℝ) + tail d (n + 1) := by
  unfold tail
  simpa only [Nat.add_zero, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using
    (summable_from hG hd hn).tsum_eq_zero_add

private lemma head_eq (hG : Growth F w C m) (hd : Band F w C m d) (he : Band F w C m e)
    {n : ℕ} (hn : m ≤ n) (hEq : tail d n = tail e n) : d n = e n := by
  by_contra hne
  have hHead := head_gap hG hd he hn hne
  have hTail := tail_gap hG hd he hn
  rw [tail_succ hG hd hn, tail_succ hG he hn] at hEq
  have hCancel : (1 : ℝ) / (d n : ℝ) - 1 / (e n : ℝ) =
      -(tail d (n + 1) - tail e (n + 1)) := by linarith
  rw [hCancel, abs_neg] at hHead
  have hF := base_pos hG hn
  have hlt : (24 / 256 : ℝ) / (F n : ℝ) ^ 2 < (1 / 4 : ℝ) / (F n : ℝ) ^ 2 :=
    div_lt_div_of_pos_right (by norm_num) (by positivity)
  exact (not_lt_of_ge (hHead.trans hTail)) hlt

/-- Equal reciprocal tails in the same band force all denominators in the tails to agree. -/
theorem unique_after (hG : Growth F w C m) (hd : Band F w C m d) (he : Band F w C m e)
    (hEq : tail d m = tail e m) : ∀ n, m ≤ n → d n = e n := by
  have hAll (k : ℕ) : tail d (m + k) = tail e (m + k) := by
    induction k with
    | zero => simpa only [Nat.add_zero] using hEq
    | succ k ih =>
      have hm : m ≤ m + k := by omega
      have heq := head_eq hG hd he hm ih
      rw [tail_succ hG hd hm, tail_succ hG he hm, heq] at ih
      rw [Nat.add_succ]
      exact add_left_cancel ih
  intro n hn
  have h := hAll (n - m)
  rw [show m + (n - m) = n by omega] at h
  exact head_eq hG hd he hn h

end TaoGap

theorem OMA.solution : type_of% @Erdos264.erdos_264.variants.ko_tao_pos := by
  intro F hF
  classical
  let w := TaoGrowth.width F
  have hStart (C : ℕ) : ∃ m : ℕ, ∀ n ≥ m, 1 ≤ F n ∧
      (256 : ℝ) * (F n : ℝ) ≤ (F (n + 1) : ℝ) ∧
      2 * C < w n ∧ (w n : ℝ) ≤ (F n : ℝ) / 4 ∧
      (w (n + 1) : ℝ) ≤ (F (n + 1) : ℝ) / (F n : ℝ) :=
    eventually_atTop.mp (TaoGrowth.conditions hF C)
  choose M hM using hStart
  have hGrow (C : ℕ) : TaoGap.Growth F w C (M C) := by
    intro n hn
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hM C n hn
    exact ⟨h₁, h₂, by omega, h₄, h₅⟩
  have hWide (C n : ℕ) (hn : M C ≤ n) : 2 * C < w n := (hM C n hn).2.2.1
  let Good (C : ℕ) (q : ℚ) (d : ℕ → ℤ) : Prop :=
    TaoGap.Band F w C (M C) d ∧ TaoGap.tail d (M C) = (q : ℝ)
  have hUnique {C : ℕ} {q : ℚ} {d e : ℕ → ℤ} (hd : Good C q d) (he : Good C q e) :
      ∀ n, M C ≤ n → d n = e n :=
    TaoGap.unique_after (hGrow C) hd.1 he.1 (hd.2.trans he.2.symm)
  obtain ⟨a, ha, hDiag⟩ := TaoDiagonal.exists_sequence F w M Good hWide hUnique
  refine ⟨a, ?_, TaoGrowth.equiv hF ha⟩
  intro b hA hB _ _
  obtain ⟨C, hb⟩ := TaoAssemble.abs_bound hA hB
  let d (n : ℕ) : ℤ := (a n : ℤ) + b n
  have hd : TaoGap.Band F w C (M C) d := fun n _ => TaoAssemble.interval_of_abs ha hb n
  have hsum : Summable (fun n => (1 : ℝ) / (d n : ℝ)) := by
    apply (summable_nat_add_iff (M C)).mp
    simpa only [Nat.add_comm (M C)] using TaoGap.summable_tail (hGrow C) hd
  simp only [← Int.cast_add]
  change Irrational (∑' n, (1 : ℝ) / (d n : ℝ))
  by_contra hrat
  obtain ⟨q, hq⟩ := TaoAssemble.rational_tail (M C) hsum hrat
  obtain ⟨n, _, hn⟩ := hDiag C q d ⟨hd, hq⟩
  exact hn (by simpa [d] using hb n)