import FormalConjectures.ErdosProblems.«263»
import Mathlib.Analysis.SpecificLimits.Basic

/-! Koizumi's tail recovery argument (https://arxiv.org/abs/2504.05933, Theorem 4).
The reciprocal tail asymptotics determine each sufficiently late denominator by rounding.
A rational tail and its index therefore encode each exceptional base. -/

open Filter Set
open scoped Topology

namespace KoizumiGrowth

noncomputable def u (α : ℝ) (n : ℕ) : ℝ := (α ^ (2 ^ n : ℕ))⁻¹

noncomputable def a (α : ℝ) (n : ℕ) : ℕ := ⌊α ^ (2 ^ n : ℕ)⌋₊

theorem a_pos {α : ℝ} (hα : 1 < α) (n : ℕ) : 0 < a α n :=
  Nat.floor_pos.2 (one_le_pow₀ hα.le)

theorem a_monotone {α : ℝ} (hα : 1 < α) : Monotone (a α) := by
  intro m n hmn
  exact Nat.floor_mono (pow_right_mono₀ hα.le (pow_right_mono₀ (by decide : (1 : ℕ) ≤ 2) hmn))

theorem u_pos {α : ℝ} (hα : 1 < α) (n : ℕ) : 0 < u α n :=
  inv_pos.2 (pow_pos (zero_lt_one.trans hα) _)

theorem u_succ (α : ℝ) (n : ℕ) : u α (n + 1) = (u α n) ^ 2 := by
  simp only [u, pow_succ (2 : ℕ) n, pow_mul, inv_pow]

theorem u_tendsto {α : ℝ} (hα : 1 < α) : Tendsto (u α) atTop (𝓝 0) := by
  have hexp : Tendsto (fun n : ℕ => (2 : ℕ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide)
  change Tendsto (fun n : ℕ => (α ^ (2 ^ n : ℕ))⁻¹) atTop (𝓝 0)
  simpa only [Function.comp_def] using
    (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp ((tendsto_pow_atTop_atTop_of_one_lt hα).comp hexp)

private lemma floor_ratio {α : ℝ} (hα : 1 < α) :
    Tendsto (fun n => (a α n : ℝ) * u α n) atTop (𝓝 1) := by
  have hsub : Tendsto (fun n => 1 - u α n) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub (u_tendsto hα)
  have hprod (n : ℕ) : α ^ (2 ^ n : ℕ) * u α n = 1 :=
    mul_inv_cancel₀ (pow_ne_zero _ (zero_lt_one.trans hα).ne')
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hsub tendsto_const_nhds
  · intro n
    have hf : α ^ (2 ^ n : ℕ) < (a α n : ℝ) + 1 := Nat.lt_floor_add_one _
    have hh := mul_le_mul_of_nonneg_right hf.le (u_pos hα n).le
    rw [hprod n, add_mul, one_mul] at hh
    linarith only [hh]
  · intro n
    have hf : (a α n : ℝ) ≤ α ^ (2 ^ n : ℕ) :=
      Nat.floor_le (pow_nonneg (zero_lt_one.trans hα).le _)
    exact (mul_le_mul_of_nonneg_right hf (u_pos hα n).le).trans_eq (hprod n)

theorem reciprocal_ratio {α : ℝ} {b : ℕ → ℕ} (hα : 1 < α) (hb : ∀ n, 0 < b n)
    (hlim : Tendsto (fun n => (a α n : ℝ) / (b n : ℝ)) atTop (𝓝 1)) :
    Tendsto (fun n => (b n : ℝ)⁻¹ / u α n) atTop (𝓝 1) := by
  have h : Tendsto (fun n => ((a α n : ℝ) / (b n : ℝ)) / ((a α n : ℝ) * u α n)) atTop (𝓝 1) := by
    simpa only [div_one, Pi.div_def] using hlim.div (floor_ratio hα) one_ne_zero
  refine h.congr ?_
  intro n
  have haN : (a α n : ℝ) ≠ 0 := by exact_mod_cast (a_pos hα n).ne'
  have hbN : (b n : ℝ) ≠ 0 := by exact_mod_cast (hb n).ne'
  field_simp [(u_pos hα n).ne', haN, hbN]

theorem base_unique {α β : ℝ} {b c : ℕ → ℕ} (hα : 1 < α) (hβ : 1 < β)
    (hbc : ∀ᶠ n in atTop, b n = c n) (hbpos : ∀ n, 0 < b n) (hcpos : ∀ n, 0 < c n)
    (hb : Tendsto (fun n => (a α n : ℝ) / (b n : ℝ)) atTop (𝓝 1))
    (hc : Tendsto (fun n => (a β n : ℝ) / (c n : ℝ)) atTop (𝓝 1)) : α = β := by
  have hRat : Tendsto (fun n => ((b n : ℝ)⁻¹ / u α n) / ((c n : ℝ)⁻¹ / u β n)) atTop (𝓝 1) := by
    simpa only [div_one, Pi.div_def] using
      (reciprocal_ratio hα hbpos hb).div (reciprocal_ratio hβ hcpos hc) one_ne_zero
  have hPow : Tendsto (fun n : ℕ => (α / β) ^ (2 ^ n : ℕ)) atTop (𝓝 1) := by
    refine hRat.congr' ?_
    filter_upwards [hbc] with n hn
    have hnz : (b n : ℝ) ≠ 0 := by exact_mod_cast (hbpos n).ne'
    rw [← hn, div_div_div_cancel_left' _ _ (inv_ne_zero hnz), div_pow]
    simp only [u, div_eq_mul_inv, inv_inv, mul_comm]
  have hα₀ : 0 < α := zero_lt_one.trans hα
  have hβ₀ : 0 < β := zero_lt_one.trans hβ
  have hn (n : ℕ) : 1 ≤ (2 : ℕ) ^ n := one_le_pow₀ (by decide)
  rcases lt_trichotomy α β with hlt | he | hgt
  · have hh : α / β < 1 := (div_lt_one₀ hβ₀).2 hlt
    have hl : 1 ≤ α / β := le_of_tendsto' hPow (fun n => by
      simpa only [pow_one] using pow_right_anti₀ (div_nonneg hα₀.le hβ₀.le) hh.le (hn n))
    exact (hh.not_ge hl).elim
  · exact he
  · have hh : 1 < α / β := (one_lt_div₀ hβ₀).2 hgt
    have hl : α / β ≤ 1 := ge_of_tendsto' hPow (fun n => by
      simpa only [pow_one] using pow_right_mono₀ hh.le (hn n))
    exact (hh.not_ge hl).elim

end KoizumiGrowth

namespace KoizumiTail

open Filter
open scoped Topology

/-- A nonnegative sequence asymptotic to a squaring sequence is summable, and its
tail after index (n) is asymptotic to the square of the comparison term at (n). -/
theorem estimate (u x : ℕ → ℝ) (hu : ∀ n, 0 < u n)
    (hSq : ∀ n, u (n + 1) = (u n) ^ 2) (h0 : Tendsto u atTop (𝓝 0))
    (hx : ∀ n, 0 ≤ x n) (hxu : Tendsto (fun n => x n / u n) atTop (𝓝 1)) :
    Summable x ∧ Tendsto (fun n => (∑' k : ℕ, x ((n + 1) + k)) / (u n) ^ 2) atTop (𝓝 1) := by
  have huSmall : ∀ᶠ n in atTop, u n < 1 / 2 :=
    h0.eventually (Iio_mem_nhds (by norm_num))
  have hxSmall : ∀ᶠ n in atTop, x n ≤ 2 * u n := by
    filter_upwards [hxu.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))] with n hn
    exact ((div_lt_iff₀ (hu n)).mp hn).le
  obtain ⟨N, hN⟩ := eventually_atTop.mp (huSmall.and hxSmall)
  have hGeo (m : ℕ) (hm : N ≤ m) (k : ℕ) : u (m + k) ≤ u m * (1 / 2) ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.add_succ, hSq, pow_two, pow_succ, ← mul_assoc]
      calc
        u (m + k) * u (m + k) ≤ u (m + k) * (1 / 2) :=
          mul_le_mul_of_nonneg_left (hN (m + k) (by omega)).1.le (hu (m + k)).le
        _ ≤ u m * (1 / 2) ^ k * (1 / 2) := by gcongr
  have hxGeo (m : ℕ) (hm : N ≤ m) (k : ℕ) :
      x (m + k) ≤ (2 * u m) * (1 / 2) ^ k := by
    calc
      x (m + k) ≤ 2 * u (m + k) := (hN (m + k) (by omega)).2
      _ ≤ 2 * (u m * (1 / 2) ^ k) := by gcongr; exact hGeo m hm k
      _ = (2 * u m) * (1 / 2) ^ k := by rw [mul_assoc]
  have hSum : Summable x := by
    have hSumN : Summable (fun k : ℕ => x (N + k)) :=
      Summable.of_nonneg_of_le (fun k => hx (N + k)) (hxGeo N le_rfl)
        (summable_geometric_two.mul_left _)
    exact (summable_nat_add_iff (f := x) N).mp (by simpa only [Nat.add_comm] using hSumN)
  have hSumShift (m : ℕ) : Summable (fun k : ℕ => x (m + k)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff (f := x) m).mpr hSum
  have hTailBound (m : ℕ) (hm : N ≤ m) : (∑' k : ℕ, x (m + k)) ≤ 4 * u m := by
    calc
      (∑' k : ℕ, x (m + k)) ≤ ∑' k : ℕ, (2 * u m) * (1 / 2) ^ k :=
        (hSumShift m).tsum_le_tsum (hxGeo m hm) (summable_geometric_two.mul_left _)
      _ = 4 * u m := by rw [tsum_mul_left, tsum_geometric_two]; ring
  have hRest : Tendsto (fun n => (∑' k : ℕ, x ((n + 2) + k)) / (u n) ^ 2) atTop (𝓝 0) := by
    have hLimit : Tendsto (fun n => 4 * (u n) ^ 2) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (4 : ℝ))).mul (h0.pow 2)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hLimit
      (Eventually.of_forall (fun n => div_nonneg (tsum_nonneg (fun k => hx _)) (sq_nonneg _))) ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    apply (div_le_iff₀ (pow_pos (hu n) 2)).mpr
    calc
      (∑' k : ℕ, x ((n + 2) + k)) ≤ 4 * u (n + 2) := hTailBound (n + 2) (by omega)
      _ = (4 * (u n) ^ 2) * (u n) ^ 2 := by
        rw [show n + 2 = (n + 1) + 1 by omega, hSq, hSq]
        ring
  have hLead : Tendsto (fun n => x (n + 1) / (u n) ^ 2) atTop (𝓝 1) := by
    simpa only [hSq] using (tendsto_add_atTop_iff_nat (f := fun n => x n / u n) 1).mpr hxu
  have hSplit (n : ℕ) : (∑' k : ℕ, x ((n + 1) + k)) =
      x (n + 1) + ∑' k : ℕ, x ((n + 2) + k) := by
    simpa only [Nat.add_zero, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (hSumShift (n + 1)).tsum_eq_zero_add
  have hEq (n : ℕ) : (∑' k : ℕ, x ((n + 1) + k)) / (u n) ^ 2 =
      x (n + 1) / (u n) ^ 2 + (∑' k : ℕ, x ((n + 2) + k)) / (u n) ^ 2 := by
    rw [hSplit n, add_div]
  refine ⟨hSum, ?_⟩
  have hCombined : Tendsto (fun n => x (n + 1) / (u n) ^ 2 +
      (∑' k : ℕ, x ((n + 2) + k)) / (u n) ^ 2) atTop (𝓝 1) := by
    simpa only [add_zero] using hLead.add hRest
  exact hCombined.congr (fun n => (hEq n).symm)

end KoizumiTail

namespace KoizumiCode

/-- The reciprocal sum starting at index `n`. -/
noncomputable def tail (b : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑' k, (b (n + k) : ℝ)⁻¹

theorem tail_step {b : ℕ → ℕ} (hs : Summable (fun k => (b k : ℝ)⁻¹)) (n : ℕ) :
    tail b n = (b n : ℝ)⁻¹ + tail b (n + 1) := by
  let f (k : ℕ) : ℝ := (b (n + k) : ℝ)⁻¹
  have hf : Summable f := by
    simpa only [f, Nat.add_comm n] using (summable_nat_add_iff n).mpr hs
  have ht : (∑' k, f (k + 1)) = tail b (n + 1) := by
    unfold f tail
    congr 1
    funext k
    rw [← Nat.add_assoc, Nat.add_right_comm n]
  have he := hf.tsum_eq_zero_add
  rw [ht] at he
  simpa only [f, tail, Nat.add_zero] using he

theorem tail_rat {b : ℕ → ℕ} (hs : Summable (fun k => (b k : ℝ)⁻¹))
    (hrat : ¬ Irrational (∑' k, (b k : ℝ)⁻¹)) (n : ℕ) :
    ∃ q : ℚ, tail b n = (q : ℝ) := by
  obtain ⟨q, hq⟩ := exists_rat_of_not_irrational hrat
  refine ⟨q - ∑ k ∈ Finset.range n, (b k : ℚ)⁻¹, ?_⟩
  have hs' : (∑ k ∈ Finset.range n, (b k : ℝ)⁻¹) + tail b n = (q : ℝ) := by
    rw [← hq]
    simpa only [tail, Nat.add_comm n] using hs.sum_add_tsum_nat_add n
  push_cast
  linarith only [hs']

private lemma equal_denominators_of_tail_eq {b c : ℕ → ℕ}
    (hsb : Summable (fun k => (b k : ℝ)⁻¹))
    (hsc : Summable (fun k => (c k : ℝ)⁻¹)) {N : ℕ}
    (hb : ∀ n ≥ N, b n = ⌊(tail b n)⁻¹ + 3 / 2⌋₊)
    (hc : ∀ n ≥ N, c n = ⌊(tail c n)⁻¹ + 3 / 2⌋₊)
    (hseed : tail b N = tail c N) : ∀ n ≥ N, b n = c n := by
  have hden {n : ℕ} (hn : N ≤ n) (ht : tail b n = tail c n) : b n = c n := by
    rw [hb n hn, hc n hn, ht]
  have htail (k : ℕ) : tail b (N + k) = tail c (N + k) := by
    induction k with
    | zero => simpa only [Nat.add_zero] using hseed
    | succ k ih =>
      have hb' := tail_step hsb (N + k)
      have hc' := tail_step hsc (N + k)
      rw [hden (by omega) ih] at hb'
      rw [Nat.add_succ]
      linarith only [hb', hc', ih]
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact hden hn (htail k)

/-- The starting index and the rational tail at that index code every parameter
admitting an asymptotic denominator sequence with a rational reciprocal sum. -/
theorem countable_bad (A : ℝ → ℕ → ℕ)
    (unique : ∀ {α β : ℝ} {b c : ℕ → ℕ}, 1 < α → 1 < β →
      (∀ᶠ n : ℕ in atTop, b n = c n) → (∀ n, 0 < b n) → (∀ n, 0 < c n) →
      Tendsto (fun n => (A α n : ℝ) / (b n : ℝ)) atTop (𝓝 1) →
      Tendsto (fun n => (A β n : ℝ) / (c n : ℝ)) atTop (𝓝 1) → α = β)
    (recovery : ∀ {α : ℝ} {b : ℕ → ℕ}, 1 < α → (∀ n, 0 < b n) →
      Tendsto (fun n => (A α n : ℝ) / (b n : ℝ)) atTop (𝓝 1) →
      Summable (fun n => (b n : ℝ)⁻¹) ∧ ∀ᶠ n : ℕ in atTop, b n = ⌊(tail b n)⁻¹ + 3 / 2⌋₊) :
    {α : ℝ | 1 < α ∧ ∃ b : ℕ → ℕ, (∀ n, 0 < b n) ∧
      Tendsto (fun n => (A α n : ℝ) / (b n : ℝ)) atTop (𝓝 1) ∧
      ¬ Irrational (∑' n, (b n : ℝ)⁻¹)}.Countable := by
  classical
  let S := {α : ℝ | 1 < α ∧ ∃ b : ℕ → ℕ, (∀ n, 0 < b n) ∧
    Tendsto (fun n => (A α n : ℝ) / (b n : ℝ)) atTop (𝓝 1) ∧
    ¬ Irrational (∑' n, (b n : ℝ)⁻¹)}
  change S.Countable
  have hB (α : S) : ∃ b : ℕ → ℕ, (∀ n, 0 < b n) ∧
      Tendsto (fun n => (A α.val n : ℝ) / (b n : ℝ)) atTop (𝓝 1) ∧
      ¬ Irrational (∑' n, (b n : ℝ)⁻¹) := α.property.2
  choose b hpos hlim hrat using hB
  have hRecover (α : S) := recovery α.property.1 (hpos α) (hlim α)
  have ht (α : S) : ∃ N : ℕ, ∀ n ≥ N, b α n = ⌊(tail (b α) n)⁻¹ + 3 / 2⌋₊ :=
    eventually_atTop.mp (hRecover α).2
  choose N hN using ht
  have hRat (α : S) : ∃ q : ℚ, tail (b α) (N α) = (q : ℝ) :=
    tail_rat (hRecover α).1 (hrat α) (N α)
  choose r hr using hRat
  let code : S → ℕ × ℚ := fun α => (N α, r α)
  apply Set.countable_coe_iff.mp
  refine Function.Injective.countable (f := code) ?_
  intro α β he
  change (N α, r α) = (N β, r β) at he
  have hindex : N α = N β := congrArg Prod.fst he
  have hvalue : r α = r β := congrArg Prod.snd he
  have hseed : tail (b α) (N α) = tail (b β) (N α) := by
    rw [hr α, hvalue, hindex, hr β]
  have hRecoverβ (n : ℕ) (hn : N α ≤ n) : b β n = ⌊(tail (b β) n)⁻¹ + 3 / 2⌋₊ :=
    hN β n (hindex ▸ hn)
  have hSame : ∀ᶠ n : ℕ in atTop, b α n = b β n :=
    eventually_atTop.mpr ⟨N α, equal_denominators_of_tail_eq
      (hRecover α).1 (hRecover β).1 (hN α) hRecoverβ hseed⟩
  apply Subtype.ext
  exact unique α.property.1 β.property.1 hSame (hpos α) (hpos β) (hlim α) (hlim β)

end KoizumiCode

namespace KoizumiRecover

lemma eventually_floor (b : ℕ → ℕ) (hb : ∀ n, 0 < b n)
    (u : ℕ → ℝ) (hu : ∀ n, 0 < u n) (hu0 : Tendsto u atTop (𝓝 0))
    (hxu : Tendsto (fun n => (b n : ℝ)⁻¹ / u n) atTop (𝓝 1))
    (hsum : Summable (fun n => (b n : ℝ)⁻¹))
    (hT : Tendsto (fun n => (∑' k, (b ((n + 1) + k) : ℝ)⁻¹) / (u n) ^ 2) atTop (𝓝 1)) :
    ∀ᶠ n in atTop, b n = ⌊(KoizumiCode.tail b n)⁻¹ + (3 / 2 : ℝ)⌋₊ := by
  let x (n : ℕ) := (b n : ℝ)⁻¹
  let T := KoizumiCode.tail b
  have hx (n : ℕ) : 0 < x n := inv_pos.mpr (Nat.cast_pos.mpr (hb n))
  have hstep (n : ℕ) : T n = x n + T (n + 1) := KoizumiCode.tail_step hsum n
  have hpos (n : ℕ) : 0 < T n := by
    rw [hstep]
    exact add_pos_of_pos_of_nonneg (hx n) (tsum_nonneg fun k => (hx (n + 1 + k)).le)
  have hx0 : Tendsto x atTop (𝓝 0) := by
    apply Tendsto.congr (f₂ := x) (fun n => div_mul_cancel₀ (x n) (hu n).ne')
    simpa only [Pi.mul_def, mul_zero] using hxu.mul hu0
  let L (n : ℕ) := T (n + 1) / (x n) ^ 2
  have hL : Tendsto L atTop (𝓝 1) := by
    have ht : Tendsto (fun n => (T (n + 1) / (u n) ^ 2) / ((x n / u n) ^ 2)) atTop (𝓝 1) := by
      simpa only [Pi.div_def, one_pow, div_one, T, KoizumiCode.tail, x] using hT.div (hxu.pow 2) (by norm_num)
    refine Tendsto.congr (fun n => ?_) ht
    change (T (n + 1) / (u n) ^ 2) / ((x n / u n) ^ 2) = T (n + 1) / (x n) ^ 2
    field_simp [(hx n).ne', (hu n).ne']
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hDen : Tendsto (fun n => T n / x n) atTop (𝓝 1) := by
    have ht : Tendsto (fun n => 1 + L n * x n) atTop (𝓝 1) := by
      simpa only [mul_zero, add_zero] using hconst.add (hL.mul hx0)
    refine Tendsto.congr (fun n => ?_) ht
    change 1 + T (n + 1) / (x n) ^ 2 * x n = T n / x n
    rw [hstep n]
    field_simp [(hx n).ne']
  have hDiff : Tendsto (fun n => (b n : ℝ) - (T n)⁻¹) atTop (𝓝 1) := by
    have ht : Tendsto (fun n => L n / (T n / x n)) atTop (𝓝 1) := by
      simpa only [Pi.div_def, div_one] using hL.div hDen one_ne_zero
    refine Tendsto.congr (fun n => ?_) ht
    have he : (b n : ℝ) = (x n)⁻¹ := by simp [x]
    rw [he]
    change (T (n + 1) / (x n) ^ 2) / (T n / x n) = (x n)⁻¹ - (T n)⁻¹
    field_simp [(hx n).ne', (hpos n).ne']
    have hs : T (n + 1) = T n - x n := by linarith only [hstep n]
    simpa only [Nat.add_comm 1 n] using hs
  have hlow : ∀ᶠ n in atTop, (1 / 2 : ℝ) < (b n : ℝ) - (T n)⁻¹ :=
    hDiff.eventually (Ioi_mem_nhds (by norm_num))
  have hhigh : ∀ᶠ n in atTop, (b n : ℝ) - (T n)⁻¹ < (3 / 2 : ℝ) :=
    hDiff.eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [hlow, hhigh] with n hl hh
  change b n = ⌊(T n)⁻¹ + (3 / 2 : ℝ)⌋₊
  have hi : 0 < (T n)⁻¹ := inv_pos.mpr (hpos n)
  apply Eq.symm
  exact (Nat.floor_eq_iff (by positivity)).mpr ⟨by linarith, by linarith⟩

lemma recovery {α : ℝ} {b : ℕ → ℕ} (hα : 1 < α) (hb : ∀ n, 0 < b n)
    (hlim : Tendsto (fun n => (KoizumiGrowth.a α n : ℝ) / (b n : ℝ)) atTop (𝓝 1)) :
    Summable (fun n => (b n : ℝ)⁻¹) ∧
      ∀ᶠ n : ℕ in atTop, b n = ⌊(KoizumiCode.tail b n)⁻¹ + (3 / 2 : ℝ)⌋₊ := by
  have hxu := KoizumiGrowth.reciprocal_ratio hα hb hlim
  have hu := KoizumiGrowth.u_pos hα
  have hu0 := KoizumiGrowth.u_tendsto hα
  obtain ⟨hs, hT⟩ := KoizumiTail.estimate (KoizumiGrowth.u α) (fun n => (b n : ℝ)⁻¹)
    hu (KoizumiGrowth.u_succ α) hu0 (fun n => inv_nonneg.mpr (Nat.cast_nonneg (b n))) hxu
  exact ⟨hs, eventually_floor b hb _ hu hu0 hxu hs hT⟩

end KoizumiRecover

theorem OMA.solution : type_of% @Erdos263.erdos_263.variants.doubly_exponential_all_but_countable := by
  classical
  have h := KoizumiCode.countable_bad KoizumiGrowth.a KoizumiGrowth.base_unique
    KoizumiRecover.recovery
  apply Filter.mem_cocountable.mpr
  refine h.mono ?_
  intro α hα
  change ¬ (1 < α → Erdos263.IsWeakIrrationalitySequence (KoizumiGrowth.a α)) at hα
  obtain ⟨ha, hbad⟩ := Classical.not_imp.mp hα
  have hn : ¬ ∀ b : ℕ → ℕ, (∀ n, 0 < b n) →
      Tendsto (fun n => (KoizumiGrowth.a α n : ℝ) / (b n : ℝ)) atTop (𝓝 1) →
        Irrational (∑' n, (b n : ℝ)⁻¹) := by
    intro hgood
    apply hbad
    refine ⟨KoizumiGrowth.a_pos ha, KoizumiGrowth.a_monotone ha, ?_⟩
    intro b hb
    simpa only [one_div] using hgood b hb.1 hb.2
  obtain ⟨b, hb⟩ := not_forall.mp hn
  obtain ⟨hpos, hn⟩ := Classical.not_imp.mp hb
  obtain ⟨hlim, hrat⟩ := Classical.not_imp.mp hn
  exact ⟨ha, b, hpos, hlim, hrat⟩