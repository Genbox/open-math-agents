import FormalConjectures.ErdosProblems.«878»
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling

/-! Short-interval prime bounds for the prime-power sum. -/

open Finset Filter Real Asymptotics

namespace OMA.Erdos878Upper

private theorem log_choose_le (a h : ℕ) (hh : 0 < h) :
    Real.log ((a + h).choose h : ℝ) ≤
      (h : ℝ) * (1 + Real.log (((a + h : ℕ) : ℝ) / h)) := by
  have hhr : 0 < (h : ℝ) := by exact_mod_cast hh
  have hA : 0 < ((a + h : ℕ) : ℝ) := by exact_mod_cast (show 0 < a + h by omega)
  have hc := Nat.choose_le_pow_div (α := ℝ) h (a + h)
  have hc0 : (0 : ℝ) < (a + h).choose h := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_left h a))
  have hf : (h : ℝ) * Real.log h - h ≤ Real.log (h.factorial : ℝ) := by
    have hs := Stirling.le_log_factorial_stirling hh.ne'
    have hlog : 0 ≤ Real.log (h : ℝ) := Real.log_nonneg (by exact_mod_cast hh)
    have hπ : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    linarith only [hs, hlog, hπ]
  have hl := Real.log_le_log hc0 hc
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow] at hl
  rw [Real.log_div hA.ne' hhr.ne']
  linarith only [hl, hf]

private theorem short_prime_logs (P : Finset ℕ) (a h : ℕ)
    (hh : 0 < h) (ha : h ≤ a) (hP : ∀ p ∈ P, p.Prime ∧ a < p ∧ p ≤ a + h) :
    (∑ p ∈ P, Real.log (p : ℝ)) ≤
      (h : ℝ) * (1 + Real.log (((a + h : ℕ) : ℝ) / h)) := by
  let I := (Ico (a + 1) (a + h + 1)).filter Nat.Prime
  have hsub : P ⊆ I := by
    intro p hp
    obtain ⟨hp0, hpa, hph⟩ := hP p hp
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, hp0⟩
  have hb := primorial_add_le ha
  rw [primorial_add, Nat.choose_symm_add] at hb
  have hprod : (∏ p ∈ I, p) ≤ (a + h).choose h :=
    Nat.le_of_mul_le_mul_left hb (primorial_pos _)
  have hp (p : ℕ) (hmem : p ∈ I) : 0 < (p : ℝ) := by
    exact_mod_cast (mem_filter.mp hmem).2.pos
  have hi0 : (0 : ℝ) < ((∏ p ∈ I, p : ℕ) : ℝ) := by
    rw [Nat.cast_prod]
    exact prod_pos hp
  have hle : ((∏ p ∈ I, p : ℕ) : ℝ) ≤ ((a + h).choose h : ℝ) := by exact_mod_cast hprod
  have hlog := Real.log_le_log hi0 hle
  rw [Nat.cast_prod, Real.log_prod (fun p hmem => (hp p hmem).ne')] at hlog
  calc
    (∑ p ∈ P, Real.log (p : ℝ)) ≤ ∑ p ∈ I, Real.log (p : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun p hmem _ => Real.log_nonneg (by
        have h := (mem_filter.mp hmem).2.one_lt
        exact_mod_cast h.le))
    _ ≤ _ := hlog.trans (log_choose_le a h hh)

private theorem power_close {p q k : ℕ} (hp : 0 < p) (hpq : p ≤ q) (hk : 0 < k)
    (hpow : q ^ k < 2 * p ^ k) : q ≤ p + p / k := by
  let t := ((q : ℝ) - p) / p
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp
  have hq : (p : ℝ) ≤ q := by exact_mod_cast hpq
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hq) hp0.le
  have ht := one_add_mul_le_pow (R := ℝ) (a := t) (by linarith) k
  have hqpow : (q : ℝ) ^ k < 2 * (p : ℝ) ^ k := by exact_mod_cast hpow
  have hrew : 1 + t = (q : ℝ) / p := by dsimp [t]; field_simp; ring
  rw [hrew, div_pow] at ht
  have h2 : (k : ℝ) * t ≤ 1 := by
    have hl := (div_lt_iff₀ (by positivity : 0 < (p : ℝ) ^ k)).mpr hqpow
    linarith only [ht, hl]
  have hh : ((q : ℝ) - p) * (k : ℝ) ≤ p := by
    dsimp [t] at h2
    have h3 : (k : ℝ) * ((q : ℝ) - p) / p ≤ 1 := by
      simpa only [mul_div_assoc] using h2
    have h4 := (div_le_iff₀ hp0).mp h3
    nlinarith only [h4]
  have hcast : ((q - p : ℕ) : ℝ) * (k : ℝ) ≤ p := by simpa [Nat.cast_sub hpq] using hh
  have hnat : (q - p) * k ≤ p := by exact_mod_cast hcast
  have hdiv := (Nat.le_div_iff_mul_le hk).mpr hnat
  omega

private theorem slab_weights {t k j : ℕ} (T : Finset ℕ)
    (hT : ∀ q ∈ T, q.Prime ∧ q ^ k ≤ t ∧ Nat.log 2 (t / q ^ k) = j) :
    (∀ q ∈ T, ((q : ℝ) ^ k / t) ≤ (1 / 2 : ℝ) ^ j) ∧
      ∀ p ∈ T, ∀ q ∈ T, q ^ k < 2 * p ^ k := by
  have hlo (q : ℕ) (hq : q ∈ T) : 2 ^ j * q ^ k ≤ t := by
    obtain ⟨hq', hqt, hlog⟩ := hT q hq
    have hq0 : 0 < q ^ k := Nat.pow_pos hq'.pos
    have hfloor : 0 < t / q ^ k := (Nat.le_div_iff_mul_le hq0).mpr (by simpa using hqt)
    have hh := Nat.pow_log_le_self 2 hfloor.ne'
    rw [hlog] at hh
    exact (Nat.le_div_iff_mul_le hq0).mp hh
  have hhi (q : ℕ) (hq : q ∈ T) : t < (2 ^ (j + 1)) * q ^ k := by
    obtain ⟨hq', _, hlog⟩ := hT q hq
    have hq0 : 0 < q ^ k := Nat.pow_pos hq'.pos
    have h := Nat.lt_pow_succ_log_self (b := 2) (by decide) (t / q ^ k)
    rw [hlog] at h
    exact (Nat.div_lt_iff_lt_mul hq0).mp h
  refine ⟨?_, ?_⟩
  · intro q hq
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (hT q hq).1.pos
    have ht : (0 : ℝ) < t := by
      exact_mod_cast (Nat.pow_pos (hT q hq).1.pos).trans_le (hT q hq).2.1
    rw [div_pow, one_pow, div_le_div_iff₀ ht (by positivity), one_mul]
    have hh : (2 : ℝ) ^ j * (q : ℝ) ^ k ≤ t := by exact_mod_cast hlo q hq
    simpa [mul_comm] using hh
  · intro p hp q hq
    apply Nat.lt_of_mul_lt_mul_left (a := 2 ^ j)
    calc
      2 ^ j * q ^ k ≤ t := hlo q hq
      _ < 2 ^ (j + 1) * p ^ k := hhi p hp
      _ = 2 ^ j * (2 * p ^ k) := by rw [pow_succ, mul_assoc]

private theorem reciprocal_slab {t k j m Y : ℕ} (hk : 2 ≤ k) (hkm : k ≤ m)
    (hY : m + 3 ≤ Y) (T : Finset ℕ)
    (hT : ∀ q ∈ T, q.Prime ∧ Y < q ∧ q ^ k ≤ t ∧ Nat.log 2 (t / q ^ k) = j) :
    (∑ q ∈ T, (1 / (q : ℝ))) ≤
      (2 * (2 + Real.log m) / Real.log Y) * (1 / (k : ℝ)) := by
  classical
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hYlog : 0 < Real.log (Y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  by_cases hne : T.Nonempty
  swap
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]
    positivity
  let p := T.min' hne
  have hp : p ∈ T := T.min'_mem hne
  obtain ⟨hp', hpY, _, _⟩ := hT p hp
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp'.pos
  have hpL : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp'.one_lt)
  have hkP : (k : ℝ) ≤ p := by exact_mod_cast (show k ≤ p by omega)
  let a := p - 1
  let h := p / k + 1
  have ha : h ≤ a := by
    have hkdiv : p / k ≤ p / 2 := Nat.div_le_div_left hk (by decide)
    dsimp [h, a]
    omega
  have hph : (p : ℝ) / k ≤ h := by
    have hdiv : p < (p / k + 1) * k := (Nat.div_lt_iff_lt_mul (by omega : 0 < k)).mp (by omega)
    refine (div_le_iff₀ hk0).mpr ?_
    exact_mod_cast hdiv.le
  have hhr : 0 < (h : ℝ) := by dsimp [h]; positivity
  have hh2 : (h : ℝ) ≤ 2 * ((p : ℝ) / k) := by
    have hpdiv : ((p / k : ℕ) : ℝ) ≤ (p : ℝ) / k := by
      exact (le_div_iff₀ hk0).mpr (by exact_mod_cast Nat.div_mul_le_self p k)
    have hpdiv1 : (1 : ℝ) ≤ (p : ℝ) / k :=
      (le_div_iff₀ hk0).mpr (by simpa using hkP)
    dsimp [h]
    push_cast
    linarith
  have hQ (q : ℕ) (hq : q ∈ T) : q.Prime ∧ a < q ∧ q ≤ a + h := by
    have hpq : p ≤ q := Finset.min'_le _ _ hq
    have hcl := (slab_weights T (fun q hq => ⟨(hT q hq).1, (hT q hq).2.2⟩)).2 p hp q hq
    have hbound := power_close hp'.pos hpq (by omega : 0 < k) hcl
    exact ⟨(hT q hq).1, by dsimp [a]; omega, by dsimp [a, h]; omega⟩
  have hlog := short_prime_logs T a h (Nat.succ_pos _) ha hQ
  have hratio : ((a + h : ℕ) : ℝ) / h ≤ 2 * (k : ℝ) := by
    apply (div_le_iff₀ hhr).mpr
    have hpa : (a : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
    have hha : (h : ℝ) ≤ a := by exact_mod_cast ha
    have hp' := (div_le_iff₀ hk0).mp hph
    push_cast
    linarith only [hpa, hha, hp']
  have hlogR := Real.log_le_log (div_pos (by positivity : 0 < ((a + h : ℕ) : ℝ)) hhr) hratio
  rw [Real.log_mul (by norm_num) hk0.ne'] at hlogR
  have hlog2 : Real.log 2 ≤ 1 := by linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlogKM : Real.log (k : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log hk0 (by exact_mod_cast hkm)
  have htBound : (∑ q ∈ T, Real.log (q : ℝ)) ≤ (h : ℝ) * (2 + Real.log m) :=
    hlog.trans (mul_le_mul_of_nonneg_left (by linarith only [hlogR, hlog2, hlogKM]) hhr.le)
  have hYp : Real.log (Y : ℝ) ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < Y by omega)) (by exact_mod_cast hpY.le)
  have hcon (q : ℕ) (hq : q ∈ T) : 1 / (q : ℝ) ≤ Real.log (q : ℝ) / ((p : ℝ) * Real.log p) := by
    have hle : (p : ℝ) ≤ q := by exact_mod_cast Finset.min'_le _ _ hq
    have hlogq := Real.log_le_log hp0 hle
    rw [div_le_div_iff₀ (hp0.trans_le hle) (mul_pos hp0 hpL), one_mul]
    calc
      (p : ℝ) * Real.log p = Real.log p * p := by ring
      _ ≤ Real.log q * q := mul_le_mul hlogq hle hp0.le (hpL.le.trans hlogq)
  have hlogm : 0 ≤ 2 + Real.log (m : ℝ) := by have := Real.log_nonneg hmR; linarith
  calc
    (∑ q ∈ T, 1 / (q : ℝ)) ≤ ∑ q ∈ T, Real.log (q : ℝ) / ((p : ℝ) * Real.log p) :=
      sum_le_sum hcon
    _ = (∑ q ∈ T, Real.log (q : ℝ)) / ((p : ℝ) * Real.log p) := (sum_div ..).symm
    _ ≤ ((h : ℝ) * (2 + Real.log m)) / ((p : ℝ) * Real.log p) :=
      div_le_div_of_nonneg_right htBound (by positivity)
    _ ≤ (2 * ((p : ℝ) / k) * (2 + Real.log m)) / ((p : ℝ) * Real.log Y) := by
      exact div_le_div_of_nonneg_left
        (by positivity : 0 ≤ (2 * ((p : ℝ) / k) * (2 + Real.log m))) (by positivity)
        (mul_le_mul_of_nonneg_left hYp hp0.le)
        |> fun h => (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hh2 hlogm) (by positivity)).trans h
    _ = _ := by field_simp

private theorem fixed_exponent {t k m Y : ℕ} (hk : 2 ≤ k) (hkm : k ≤ m) (hY : m + 3 ≤ Y)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ Y < q ∧ q ^ k ≤ t) :
    (∑ q ∈ T, ((q : ℝ) ^ k / t) * (1 / (q : ℝ))) ≤
      2 * ((2 * (2 + Real.log m) / Real.log Y) * (1 / (k : ℝ))) := by
  let idx (q : ℕ) := Nat.log 2 (t / q ^ k)
  let J := T.image idx
  let D : ℝ := (2 * (2 + Real.log m) / Real.log Y) * (1 / (k : ℝ))
  have hlow : 0 ≤ D := by
    have hm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
    have hy : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ Y by omega))
    dsimp [D]
    positivity
  have hs (j : ℕ) :
      (∑ q ∈ T.filter (fun q => idx q = j), ((q : ℝ) ^ k / t) * (1 / (q : ℝ))) ≤
        (1 / 2 : ℝ) ^ j * D := by
    let B := T.filter (fun q => idx q = j)
    have hB (q : ℕ) (hq : q ∈ B) : q.Prime ∧ Y < q ∧ q ^ k ≤ t ∧ Nat.log 2 (t / q ^ k) = j := by
      exact ⟨(hT q (mem_filter.mp hq).1).1, (hT q (mem_filter.mp hq).1).2.1,
        (hT q (mem_filter.mp hq).1).2.2, (mem_filter.mp hq).2⟩
    have hw := (slab_weights B (fun q hq => ⟨(hB q hq).1, (hB q hq).2.2⟩)).1
    calc
      (∑ q ∈ B, ((q : ℝ) ^ k / t) * (1 / (q : ℝ))) ≤ ∑ q ∈ B, (1 / 2 : ℝ) ^ j * (1 / (q : ℝ)) :=
        sum_le_sum fun q hq => mul_le_mul_of_nonneg_right (hw q hq) (by positivity)
      _ = (1 / 2 : ℝ) ^ j * ∑ q ∈ B, (1 / (q : ℝ)) := (mul_sum ..).symm
      _ ≤ (1 / 2 : ℝ) ^ j * D :=
        mul_le_mul_of_nonneg_left (reciprocal_slab hk hkm hY B hB) (by positivity)
  have hgeom : (∑ j ∈ J, (1 / 2 : ℝ) ^ j) ≤ 2 := by
    have h := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).sum_le_tsum
      J (fun _ _ => by positivity)
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at h
    norm_num at h ⊢
    exact h
  calc
    (∑ q ∈ T, ((q : ℝ) ^ k / t) * (1 / (q : ℝ))) =
        ∑ j ∈ J, ∑ q ∈ T.filter (fun q => idx q = j), ((q : ℝ) ^ k / t) * (1 / (q : ℝ)) :=
      (sum_fiberwise_of_maps_to (fun _ hq => mem_image_of_mem _ hq) _).symm
    _ ≤ ∑ j ∈ J, (1 / 2 : ℝ) ^ j * D := sum_le_sum fun j _ => hs j
    _ ≤ 2 * D := by rw [← sum_mul]; exact mul_le_mul_of_nonneg_right hgeom hlow

private theorem large_primes_total {t m Y : ℕ} (ht : 0 < t) (hm : Nat.log 2 t ≤ m)
    (hm1 : 1 ≤ m) (hY : m + 3 ≤ Y) :
    (∑ p ∈ t.primesLE.filter (fun p => Y < p),
      ((p : ℝ) ^ Nat.log p t / t) * (1 / (p : ℝ))) ≤
        1 + 4 * (2 + Real.log m) * (1 + Real.log m) / Real.log Y := by
  let P := t.primesLE.filter (fun p => Y < p)
  let W (p : ℕ) := ((p : ℝ) ^ Nat.log p t / t) * (1 / (p : ℝ))
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime ∧ Y < p ∧ p ≤ t := by
    have h := mem_filter.mp hp
    exact ⟨Nat.prime_of_mem_primesLE h.1, h.2, Nat.le_of_mem_primesLE h.1⟩
  have hpow (p : ℕ) (hp : p ∈ P) := Nat.pow_log_le_self p ht.ne'
  have hmap (p : ℕ) (hp : p ∈ P) : Nat.log p t ∈ Icc 1 m := by
    obtain ⟨hp', hpY, hpt⟩ := hP p hp
    refine mem_Icc.mpr ⟨Nat.le_log_of_pow_le hp'.one_lt (by simpa using hpt), ?_⟩
    exact (Nat.le_log_of_pow_le (by decide : 1 < 2) ((Nat.pow_le_pow_left hp'.two_le _).trans
      (hpow p hp))).trans hm
  let T := P.filter (fun p => Nat.log p t = 1)
  have hc (p : ℕ) (hp : p ∈ T) : W p = 1 / (t : ℝ) := by
    have hp0 : 0 < (p : ℝ) := by exact_mod_cast (hP p (mem_filter.mp hp).1).1.pos
    unfold W
    rw [(mem_filter.mp hp).2, pow_one]
    field_simp
  have hT : T.card ≤ t := by
    refine (card_le_card (show T ⊆ Icc 1 t from fun p hp => ?_)).trans_eq ?_
    · obtain ⟨hPrime, _, hpt⟩ := hP p (mem_filter.mp hp).1
      exact mem_Icc.mpr ⟨hPrime.pos, hpt⟩
    · simp [Nat.card_Icc]
  have hones : (∑ p ∈ T, W p) ≤ 1 := by
    rw [sum_congr rfl hc, sum_const, nsmul_eq_mul]
    have ht0 : 0 < (t : ℝ) := by exact_mod_cast ht
    change (T.card : ℝ) * (1 / (t : ℝ)) ≤ 1
    rw [mul_one_div]
    exact (div_le_one₀ ht0).mpr (by exact_mod_cast hT)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hYl : 0 < Real.log (Y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hconst : 0 ≤ (2 : ℝ) * (2 * (2 + Real.log m) / Real.log Y) := by
    have hMl := Real.log_nonneg hmR
    positivity
  have hharm : (∑ k ∈ Icc 2 m, 1 / (k : ℝ)) ≤ 1 + Real.log m := by
    have hh := harmonic_le_one_add_log m
    rw [harmonic_eq_sum_Icc] at hh
    push_cast at hh
    have hcomp : (∑ k ∈ Icc 2 m, 1 / (k : ℝ)) ≤ ∑ k ∈ Icc 1 m, 1 / (k : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_left (by decide : (1 : ℕ) ≤ 2))
        (fun _ _ _ => by positivity)
    exact hcomp.trans (by simpa [one_div] using hh)
  calc
    (∑ p ∈ P, W p) = ∑ k ∈ Icc 1 m, ∑ p ∈ P.filter (fun p => Nat.log p t = k), W p :=
      (sum_fiberwise_of_maps_to hmap _).symm
    _ = (∑ p ∈ T, W p) + ∑ k ∈ Icc 2 m, ∑ p ∈ P.filter (fun p => Nat.log p t = k), W p := by
      have he : Icc 1 m = insert 1 (Icc 2 m) := by
        ext k
        simp only [mem_Icc, mem_insert]
        omega
      rw [he, sum_insert (by simp)]
    _ ≤ 1 + ∑ k ∈ Icc 2 m, 2 * ((2 * (2 + Real.log m) / Real.log Y) * (1 / (k : ℝ))) := by
      refine add_le_add hones (sum_le_sum fun k hk => ?_)
      let B := P.filter (fun p => Nat.log p t = k)
      have hh (p : ℕ) (hp : p ∈ B) : W p = ((p : ℝ) ^ k / t) * (1 / (p : ℝ)) := by
        dsimp [W]
        rw [(mem_filter.mp hp).2]
      rw [sum_congr rfl hh]
      refine fixed_exponent (mem_Icc.mp hk).1 (mem_Icc.mp hk).2 hY B ?_
      intro p hp
      obtain ⟨hp', hpk⟩ := mem_filter.mp hp
      exact ⟨(hP p hp').1, (hP p hp').2.1, hpk ▸ hpow p hp'⟩
    _ ≤ 1 + (2 * (2 * (2 + Real.log m) / Real.log Y)) * (1 + Real.log m) := by
      rw [← sum_congr rfl (fun k (_ : k ∈ Icc 2 m) => mul_assoc _ _ _), ← mul_sum]
      exact add_le_add_right (mul_le_mul_of_nonneg_left hharm hconst) 1
    _ = _ := by ring

private theorem small_reciprocal_bound (Y : ℕ) :
    (∑ p ∈ Y.primesLE, (1 / (p : ℝ))) ≤ 4 * (1 + Real.log (Nat.log 2 Y : ℝ)) := by
  let J := Icc 1 (Nat.log 2 Y)
  have hJ (p : ℕ) (hp : p ∈ Y.primesLE) : Nat.log 2 p ∈ J :=
    mem_Icc.mpr ⟨Nat.le_log_of_pow_le (by decide) (by simpa using Nat.two_le_of_mem_primesLE hp),
      Nat.log_monotone (Nat.le_of_mem_primesLE hp)⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hblock (j : ℕ) (hj : j ∈ J) :
      (∑ p ∈ Y.primesLE.filter (fun p => Nat.log 2 p = j), 1 / (p : ℝ)) ≤ 4 * (1 / (j : ℝ)) := by
    let P := Y.primesLE.filter (fun p => Nat.log 2 p = j)
    have hj0 : 0 < (j : ℝ) := by exact_mod_cast (mem_Icc.mp hj).1
    let d : ℝ := 2 ^ j * ((j : ℝ) * Real.log 2)
    have hd : 0 < d := by dsimp [d]; positivity
    have hP (p : ℕ) (hp : p ∈ P) :
        (2 : ℕ) ^ j ≤ p ∧ p ≤ 2 ^ (j + 1) ∧ p.Prime := by
      have hpp := Nat.prime_of_mem_primesLE (mem_filter.mp hp).1
      have hpj := (mem_filter.mp hp).2
      have hl := Nat.pow_log_le_self 2 hpp.ne_zero
      have hu := Nat.lt_pow_succ_log_self (b := 2) (by decide) p
      rw [hpj] at hl hu
      exact ⟨hl, hu.le, hpp⟩
    have hlog := Chebyshev.theta_le_log4_mul_x (x := ((2 ^ (j + 1) : ℕ) : ℝ)) (by positivity)
    rw [Chebyshev.theta_eq_sum_primesLE_log] at hlog
    have hpSub : P ⊆ (2 ^ (j + 1)).primesLE := fun p hp =>
      Nat.mem_primesLE.mpr (hP p hp).2
    have hPlog := sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => Real.log (p : ℝ)) hpSub
      (fun p hp _ => Real.log_nonneg (by exact_mod_cast (Nat.one_lt_of_mem_primesLE hp).le))
    have hComp (p : ℕ) (hp : p ∈ P) : 1 / (p : ℝ) ≤ Real.log p / d := by
      have hl : (2 : ℝ) ^ j ≤ p := by exact_mod_cast (hP p hp).1
      have hpl : (j : ℝ) * Real.log 2 ≤ Real.log p := by
        simpa [Real.log_pow] using Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ j) hl
      have hp0 : 0 < (p : ℝ) := by exact_mod_cast (hP p hp).2.2.pos
      rw [div_le_div_iff₀ hp0 hd, one_mul, mul_comm (Real.log p)]
      exact mul_le_mul hl hpl (by positivity) hp0.le
    calc
      (∑ p ∈ P, 1 / (p : ℝ)) ≤ ∑ p ∈ P, Real.log (p : ℝ) / d := sum_le_sum hComp
      _ = (∑ p ∈ P, Real.log (p : ℝ)) / d := (sum_div ..).symm
      _ ≤ Real.log 4 * ((2 ^ (j + 1) : ℕ) : ℝ) / d :=
        div_le_div_of_nonneg_right (hPlog.trans hlog) hd.le
      _ = _ := by
        dsimp [d]
        push_cast
        rw [hlog4, pow_succ]
        field_simp
        ring
  have hs := harmonic_le_one_add_log (Nat.log 2 Y)
  rw [harmonic_eq_sum_Icc] at hs
  push_cast at hs
  calc
    (∑ p ∈ Y.primesLE, 1 / (p : ℝ)) =
        ∑ j ∈ J, ∑ p ∈ Y.primesLE.filter (fun p => Nat.log 2 p = j), 1 / (p : ℝ) :=
      (sum_fiberwise_of_maps_to hJ _).symm
    _ ≤ ∑ j ∈ J, 4 * (1 / (j : ℝ)) := sum_le_sum hblock
    _ = _ * (∑ j ∈ J, 1 / (j : ℝ)) := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa [J, one_div] using hs) (by norm_num)

private theorem all_prime_weights {t m Y : ℕ} (ht : 0 < t) (hm : Nat.log 2 t ≤ m)
    (hm1 : 1 ≤ m) (hY : m + 3 ≤ Y)
    (hYlog : (Real.log (m + 4 : ℕ)) ^ 2 ≤ Real.log Y) :
    (∑ p ∈ t.primesLE, ((p : ℝ) ^ Nat.log p t / t) * (1 / (p : ℝ))) ≤
        25 + 4 * (1 + Real.log (Nat.log 2 Y : ℝ)) := by
  let W (p : ℕ) := ((p : ℝ) ^ Nat.log p t / t) * (1 / (p : ℝ))
  have hL (p : ℕ) (hp : p ∈ t.primesLE) : W p ≤ 1 / (p : ℝ) := by
    have htR : (0 : ℝ) < t := by exact_mod_cast ht
    have hpow : (p : ℝ) ^ Nat.log p t ≤ t := by exact_mod_cast Nat.pow_log_le_self p ht.ne'
    simpa [W] using mul_le_mul_of_nonneg_right ((div_le_one₀ htR).mpr hpow)
      (by positivity : 0 ≤ 1 / (p : ℝ))
  have hsmall : (∑ p ∈ t.primesLE.filter (fun p => ¬ Y < p), W p) ≤
      4 * (1 + Real.log (Nat.log 2 Y : ℝ)) := by
    have hsub : t.primesLE.filter (fun p => ¬ Y < p) ⊆ Y.primesLE := by
      intro p hp
      exact Nat.mem_primesLE.mpr ⟨le_of_not_gt (mem_filter.mp hp).2, Nat.prime_of_mem_primesLE (mem_filter.mp hp).1⟩
    exact ((sum_le_sum fun p hp => hL p (mem_filter.mp hp).1).trans
      (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity))).trans (small_reciprocal_bound Y)
  have hlarge := large_primes_total ht hm hm1 hY
  have hYM : 0 < Real.log (Y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hM1 : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hM : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hM1
  have hm4R : (3 : ℝ) ≤ ((m + 4 : ℕ) : ℝ) := by exact_mod_cast (show 3 ≤ m + 4 by omega)
  have hL1 : 1 ≤ Real.log (m + 4 : ℕ) := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (Real.exp_one_lt_three.le.trans hm4R)
    rwa [Real.log_exp] at h
  have hLC : Real.log (m : ℝ) ≤ Real.log (m + 4 : ℕ) :=
    Real.log_le_log (by linarith) (by exact_mod_cast (Nat.le_add_right m 4))
  have hnorm : 4 * (2 + Real.log m) * (1 + Real.log m) / Real.log Y ≤ 24 := by
    rw [div_le_iff₀ hYM]
    calc
      4 * (2 + Real.log m) * (1 + Real.log m) ≤
          (4 * (3 * Real.log (m + 4 : ℕ))) * (2 * Real.log (m + 4 : ℕ)) :=
        mul_le_mul (by linarith only [hLC, hL1]) (by linarith only [hLC, hL1])
          (by linarith) (by linarith)
      _ = 24 * (Real.log (m + 4 : ℕ)) ^ 2 := by ring
      _ ≤ 24 * Real.log Y := mul_le_mul_of_nonneg_left hYlog (by norm_num)
  rw [← sum_filter_add_sum_filter_not (s := t.primesLE) (p := (Y < ·)) (f := W)]
  exact add_le_add (hlarge.trans (by linarith only [hnorm])) hsmall

private theorem weighted_band {b t : ℕ} (ht : t = 2 * b) (hb : 0 < b)
    (I : Finset ℕ) (hI : ∀ n ∈ I, b ≤ n ∧ n < t) :
    (∑ n ∈ I, (Erdos878.f n : ℝ) / n) ≤
      (2 * (t : ℝ)) * ∑ p ∈ t.primesLE, ((p : ℝ) ^ Nat.log p t / t) * (1 / (p : ℝ)) := by
  let term (p n : ℕ) : ℝ := if p ∣ n then (p : ℝ) ^ Nat.log p n / (n : ℝ) else 0
  have hterm (n : ℕ) (hn : n ∈ I) :
      (Erdos878.f n : ℝ) / n = ∑ p ∈ t.primesLE, term p n := by
    have hfac : n.primeFactors = t.primesLE.filter (· ∣ n) := by
      have hn0 : 0 < n := hb.trans_le (hI n hn).1
      ext p
      simp only [Nat.mem_primeFactors, mem_filter, Nat.mem_primesLE]
      exact ⟨fun ⟨hp, hdvd, _⟩ => ⟨⟨(Nat.le_of_dvd hn0 hdvd).trans (hI n hn).2.le, hp⟩, hdvd⟩,
        fun ⟨⟨_, hp⟩, hdvd⟩ => ⟨hp, hdvd, hn0.ne'⟩⟩
    rw [Erdos878.f, Nat.cast_sum, sum_div, hfac, sum_filter]
    simp [term, Nat.cast_pow]
  have hpr (p : ℕ) (hp : p ∈ t.primesLE) :
      (∑ n ∈ I, term p n) ≤ (2 * (t : ℝ)) * (((p : ℝ) ^ Nat.log p t / t) * (1 / (p : ℝ))) := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos
    have hto : 0 < t := by omega
    have ht0 : (0 : ℝ) < t := by exact_mod_cast hto
    have hnconst (n : ℕ) (hn : n ∈ I.filter (p ∣ ·)) :
        (p : ℝ) ^ Nat.log p n / (n : ℝ) ≤ 2 * ((p : ℝ) ^ Nat.log p t / t) := by
      have hni := (hI n (mem_filter.mp hn).1)
      have hn0 : 0 < (n : ℝ) := by exact_mod_cast hb.trans_le hni.1
      have hnp : (p : ℝ) ^ Nat.log p n ≤ (p : ℝ) ^ Nat.log p t :=
        pow_le_pow_right₀ (by exact_mod_cast (Nat.one_lt_of_mem_primesLE hp).le)
          (Nat.log_monotone hni.2.le)
      have htn : (t : ℝ) ≤ 2 * (n : ℝ) := by
        exact_mod_cast (show t ≤ 2 * n by omega)
      calc
        _ ≤ (p : ℝ) ^ Nat.log p t / n := div_le_div_of_nonneg_right hnp hn0.le
        _ ≤ (p : ℝ) ^ Nat.log p t / ((t : ℝ) / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith only [htn])
        _ = _ := by ring
    have hA : (I.filter (p ∣ ·)).card ≤ t / p := by
      rw [← Nat.card_multiples' t p]
      refine card_le_card fun n hn => ?_
      obtain ⟨hn, hdvd⟩ := mem_filter.mp hn
      have hh := hI n hn
      exact mem_filter.mpr ⟨mem_range.mpr (by omega), by omega, hdvd⟩
    have hc : ((I.filter (p ∣ ·)).card : ℝ) ≤ (t : ℝ) / p := by
      apply (le_div_iff₀ hp0).mpr
      exact_mod_cast (Nat.mul_le_mul_right p hA).trans (Nat.div_mul_le_self t p)
    unfold term
    rw [← sum_filter]
    calc
      _ ≤ ∑ _ ∈ I.filter (p ∣ ·), 2 * ((p : ℝ) ^ Nat.log p t / t) := sum_le_sum hnconst
      _ = ((I.filter (p ∣ ·)).card : ℝ) * (2 * ((p : ℝ) ^ Nat.log p t / t)) := by
        simp [nsmul_eq_mul]
      _ ≤ ((t : ℝ) / p) * (2 * ((p : ℝ) ^ Nat.log p t / t)) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by ring
  rw [mul_sum]
  calc
    _ = ∑ n ∈ I, ∑ p ∈ t.primesLE, term p n := sum_congr rfl hterm
    _ = ∑ p ∈ t.primesLE, ∑ n ∈ I, term p n := sum_comm
    _ ≤ _ := sum_le_sum hpr

private noncomputable def cutoff (m : ℕ) : ℕ :=
  (m + 4) ^ (Nat.log 2 (m + 4) + 1)

private theorem log_two_bounds : (1 / 2 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · linarith only [Real.log_two_gt_d9]
  · linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]

private theorem log_pow_bounds (t : ℕ) (ht : 0 < t) :
    (Nat.log 2 t : ℝ) * Real.log 2 ≤ Real.log (t : ℝ) ∧
      Real.log (t : ℝ) ≤ (Nat.log 2 t + 1 : ℝ) * Real.log 2 := by
  have hl : (2 : ℝ) ^ Nat.log 2 t ≤ t := by exact_mod_cast Nat.pow_log_le_self 2 ht.ne'
  have hu : (t : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 t + 1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (b := 2) (by decide) t).le
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  constructor
  · simpa [Real.log_pow] using Real.log_le_log (by positivity) hl
  · simpa [Real.log_pow] using Real.log_le_log htR hu

private theorem cutoff_bounds (m : ℕ) :
    m + 3 ≤ cutoff m ∧
    (Real.log (m + 4 : ℕ)) ^ 2 ≤ Real.log (cutoff m : ℝ) ∧
    (Nat.log 2 (cutoff m) : ℝ) ≤ 6 * (Real.log (m + 4 : ℕ)) ^ 2 := by
  let B := m + 4
  let r := Nat.log 2 B + 1
  have hB : 0 < B := by dsimp [B]; omega
  have hB3 : 3 ≤ B := by dsimp [B]; omega
  have hBpos : 0 < (B : ℝ) := by exact_mod_cast hB
  have hb3R : (3 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB3
  have hB1 : 1 ≤ Real.log (B : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (Real.exp_one_lt_three.le.trans hb3R)
    rwa [Real.log_exp] at h
  have hlo : m + 3 ≤ cutoff m := by
    calc
      m + 3 ≤ B := by dsimp [B]; omega
      _ ≤ B ^ r := Nat.le_self_pow (by dsimp [r]; omega) _
  have hp : Real.log (cutoff m : ℝ) = (r : ℝ) * Real.log (B : ℝ) := by
    change Real.log ((B ^ r : ℕ) : ℝ) = (r : ℝ) * Real.log (B : ℝ)
    simp [Real.log_pow]
  have hLoHi := log_pow_bounds B hB
  have hrlo : Real.log (B : ℝ) ≤ (r : ℝ) := by
    have hmul : (r : ℝ) * Real.log 2 ≤ (r : ℝ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left log_two_bounds.2 (by positivity : 0 ≤ (r : ℝ))
    exact hLoHi.2.trans (by simpa [r] using hmul)
  have hrhi : (r : ℝ) ≤ 3 * Real.log (B : ℝ) := by
    have h := mul_le_mul_of_nonneg_left log_two_bounds.1 (by positivity : 0 ≤ (Nat.log 2 B : ℝ))
    dsimp [r]
    push_cast
    linarith only [h, hLoHi.1, hB1]
  have hSeq := (log_pow_bounds (cutoff m) (by omega)).1
  have hhalf := mul_le_mul_of_nonneg_left log_two_bounds.1
    (by positivity : 0 ≤ (Nat.log 2 (cutoff m) : ℝ))
  have hloglo : (Real.log (B : ℝ)) ^ 2 ≤ Real.log (cutoff m : ℝ) := by
    rw [hp, pow_two]
    exact mul_le_mul_of_nonneg_right hrlo (by linarith)
  have hloghi : Real.log (cutoff m : ℝ) ≤ 3 * (Real.log (B : ℝ)) ^ 2 := by
    rw [hp, pow_two, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hrhi (by linarith)
  exact ⟨hlo, hloglo, by linarith only [hSeq, hhalf, hloghi]⟩

private theorem reciprocal_cutoff {x m : ℕ} (hx : 0 < x) (hm : m = Nat.log 2 (2 * x))
    (hlog : 6 ≤ Real.log (x : ℝ)) (hlog3 : 1 ≤ Real.log (Real.log (Real.log (x : ℝ)))) :
    25 + 4 * (1 + Real.log (Nat.log 2 (cutoff m) : ℝ)) ≤
      65 * Real.log (Real.log (Real.log (x : ℝ))) := by
  have hL := (log_pow_bounds (2 * x) (by omega)).1
  rw [← hm, Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) (by positivity)] at hL
  have hhalf := mul_le_mul_of_nonneg_left log_two_bounds.1 (by positivity : 0 ≤ (m : ℝ))
  have hM : ((m + 4 : ℕ) : ℝ) ≤ 3 * Real.log (x : ℝ) := by
    push_cast
    linarith only [hhalf, hL, log_two_bounds.2, hlog]
  have hB1 : 0 < Real.log (m + 4 : ℕ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m + 4 by omega))
  have hℓ := Real.log_le_log (by positivity : 0 < ((m + 4 : ℕ) : ℝ)) hM
  rw [Real.log_mul (by norm_num) (show (Real.log (x : ℝ)) ≠ 0 by linarith)] at hℓ
  have h3 : Real.log (3 : ℝ) ≤ Real.log (Real.log (x : ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hSlim : Real.log (m + 4 : ℕ) ≤ 2 * Real.log (Real.log (x : ℝ)) := by
    linarith only [hℓ, h3]
  have hlogL := Real.log_le_log hB1 hSlim
  rw [Real.log_mul (by norm_num) (show Real.log (Real.log (x : ℝ)) ≠ 0 by
    have h := Real.log_pos (by linarith : 1 < Real.log (x : ℝ))
    exact h.ne')] at hlogL
  have hCB := cutoff_bounds m
  have hY2 : 2 ≤ cutoff m := (show 2 ≤ m + 3 by omega).trans hCB.1
  have hYLog : 0 < Nat.log 2 (cutoff m) :=
    Nat.le_log_of_pow_le (by decide) (by simpa using hY2)
  have hLow := Real.log_le_log (by exact_mod_cast hYLog : 0 < (Nat.log 2 (cutoff m) : ℝ)) hCB.2.2
  rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hB1.ne'), Real.log_pow] at hLow
  have h6 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)
  norm_num at hLow hlogL
  linarith only [hLow, hlogL, log_two_bounds.2, h6, hlog3]

private theorem H_bound {x : ℕ} (hx : 2 ≤ x)
    (hlog : 6 ≤ Real.log (x : ℝ)) (hlog3 : 1 ≤ Real.log (Real.log (Real.log (x : ℝ)))) :
    Erdos878.H x ≤ 520 * ((x : ℝ) * Real.log (Real.log (Real.log (x : ℝ)))) := by
  let m := Nat.log 2 (2 * x)
  let Y := cutoff m
  let I := Ico 1 x
  let J := range (Nat.log 2 x + 1)
  let Z := 65 * Real.log (Real.log (Real.log (x : ℝ)))
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hm : 1 ≤ m := Nat.le_log_of_pow_le (by decide) (by simp; omega)
  have hmY := cutoff_bounds m
  have hmap (n : ℕ) (hn : n ∈ I) : Nat.log 2 n ∈ J :=
    mem_range.mpr (Nat.lt_succ_of_le (Nat.log_monotone (mem_Ico.mp hn).2.le))
  have hband (j : ℕ) (hj : j ∈ J) :
      (∑ n ∈ I.filter (fun n => Nat.log 2 n = j), (Erdos878.f n : ℝ) / n) ≤
        2 * (2 : ℝ) ^ (j + 1) * Z := by
    let B := I.filter (fun n => Nat.log 2 n = j)
    let b := (2 : ℕ) ^ j
    let t := (2 : ℕ) ^ (j + 1)
    have hb : 0 < b := by dsimp [b]; positivity
    have ht : t = 2 * b := by dsimp [t, b]; rw [pow_succ']
    have ht' : t ≤ 2 * x := by
      rw [ht]
      have h := (Nat.pow_le_pow_right (by decide : 0 < 2)
        (Nat.le_of_lt_succ (mem_range.mp hj))).trans
        (Nat.pow_log_le_self 2 (by omega : x ≠ 0))
      exact Nat.mul_le_mul_left _ h
    have hB (n : ℕ) (hn : n ∈ B) : b ≤ n ∧ n < t := by
      obtain ⟨hn, he⟩ := mem_filter.mp hn
      have hn0 : n ≠ 0 := by have := (mem_Ico.mp hn).1; omega
      have hp := Nat.pow_log_le_self 2 hn0
      have hq := Nat.lt_pow_succ_log_self (b := 2) (by decide) n
      rw [he] at hp hq
      exact ⟨hp, hq⟩
    have hW := weighted_band ht hb B hB
    have hbounds := all_prime_weights (by omega : 0 < t) (Nat.log_monotone ht') hm hmY.1 hmY.2.1
    have hC := reciprocal_cutoff (by omega : 0 < x) (show m = Nat.log 2 (2 * x) by rfl) hlog hlog3
    have h := hW.trans (mul_le_mul_of_nonneg_left (hbounds.trans hC) (by positivity))
    simpa [t, Z] using h
  have hGeom : (∑ j ∈ J, (2 : ℝ) ^ (j + 1)) ≤ 4 * (x : ℝ) := by
    have hlast : (2 : ℝ) ^ Nat.log 2 x ≤ x := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : x ≠ 0)
    calc
      (∑ j ∈ J, (2 : ℝ) ^ (j + 1)) = 2 * (∑ j ∈ J, (2 : ℝ) ^ j) := by
        simp_rw [pow_succ', mul_sum]
      _ = 2 * ((2 : ℝ) ^ (Nat.log 2 x + 1) - 1) := by
        dsimp [J]
        rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
        ring
      _ ≤ 4 * (x : ℝ) := by rw [pow_succ']; linarith
  calc
    Erdos878.H x = ∑ j ∈ J, ∑ n ∈ I.filter (fun n => Nat.log 2 n = j), (Erdos878.f n : ℝ) / n :=
      (sum_fiberwise_of_maps_to hmap _).symm
    _ ≤ ∑ j ∈ J, 2 * (2 : ℝ) ^ (j + 1) * Z := sum_le_sum hband
    _ = 2 * (∑ j ∈ J, (2 : ℝ) ^ (j + 1)) * Z := by rw [← sum_mul, ← mul_sum]
    _ ≤ 2 * (4 * (x : ℝ)) * Z :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hGeom (by norm_num)) hZ
    _ = _ := by dsimp [Z]; ring

end OMA.Erdos878Upper

open OMA.Erdos878Upper in
theorem OMA.solution : type_of% @Erdos878.erdos_878.variants.H_upper_triple_log := by
  have ht : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun x : ℕ => Real.log (Real.log (Real.log (x : ℝ)))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp ht)
  refine IsBigO.of_bound 520 ?_
  filter_upwards [eventually_ge_atTop (2 : ℕ), ht.eventually_ge_atTop 6, hu.eventually_ge_atTop 1]
    with x hx hlog hlog3
  have hH : 0 ≤ Erdos878.H x := by unfold Erdos878.H; positivity
  rw [Real.norm_of_nonneg hH, Real.norm_of_nonneg (by positivity)]
  exact H_bound hx hlog hlog3