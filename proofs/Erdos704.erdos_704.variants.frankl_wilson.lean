import FormalConjectures.ErdosProblems.«704»
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Deriv

/-!
The Frankl–Wilson construction colors the scaled incidence vectors of the
sets of size 2p−1, where p is prime. Within each color the containment vectors
on the sets of size p−1 are linearly independent over ZMod p.

Chebyshev’s factorial combination supplies a prime p in (n/8, n/6].
Stirling’s estimate and concavity on this interval give the exponential
lower bound for the ratio of the two relevant binomial coefficients.

Credit: @Genbox.
-/

open Finset Filter Real
open scoped BigOperators

namespace OMA

private theorem choose_residue {p r : ℕ} (hp : p.Prime) :
    (r.choose (p-1) : ZMod p) = if r % p = p-1 then 1 else 0 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hp' := hp.two_le
  have hlt : p-1 < p := by omega
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := r) (k := p-1) (p := p)
  rw [Nat.mod_eq_of_lt hlt, Nat.div_eq_of_lt hlt, Nat.choose_zero_right, mul_one] at h
  have h' : (r.choose (p-1) : ZMod p) = ((r%p).choose (p-1) : ZMod p) := by
    exact (ZMod.natCast_eq_natCast_iff _ _ p).2 h
  rw [h']
  have hr' := Nat.mod_lt r hp.pos
  split_ifs with he
  · simp [he]
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]

private theorem residue_iff {p r : ℕ} (hp : p.Prime) (hr : r < 2*p) :
    r % p = p-1 ↔ r = p-1 ∨ r = 2*p-1 := by
  have hp' := hp.two_le
  constructor
  · intro h
    have hdiv : r / p < 2 := (Nat.div_lt_iff_lt_mul hp.pos).2 (by omega)
    have he := Nat.mod_add_div r p
    interval_cases hqr : r / p <;> simp [h] at he <;> omega
  · rintro (rfl | rfl)
    · exact Nat.mod_eq_of_lt (by omega)
    · rw [show 2*p-1 = (p-1)+p by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]

private theorem family_card {p n : ℕ} (hp : p.Prime) (𝒜 : Finset (Finset (Fin n)))
    (hc : ∀ S ∈ 𝒜, S.card = 2*p-1)
    (hd : ∀ S ∈ 𝒜, ∀ T ∈ 𝒜, S ≠ T → (S ∩ T).card ≠ p-1) :
    𝒜.card ≤ n.choose (p-1) := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let 𝒝 := (univ : Finset (Fin n)).powersetCard (p-1)
  let f (S : 𝒜) (B : 𝒝) : ZMod p := if (B : Finset (Fin n)) ⊆ S then 1 else 0
  have hdot (S T : 𝒜) :
      ∑ B : 𝒝, f S B * f T B = (((S : Finset (Fin n)) ∩ T).card.choose (p-1) : ZMod p) := by
    simp only [f, ← ite_and, mul_ite, mul_one, mul_zero]
    let g (B : Finset (Fin n)) : ZMod p := if B ⊆ (T : Finset (Fin n)) ∧ B ⊆ (S : Finset (Fin n)) then 1 else 0
    change (∑ B : 𝒝, g B) = _
    have heq : 𝒝.filter (fun B => B ⊆ (T : Finset (Fin n)) ∧ B ⊆ (S : Finset (Fin n))) =
        ((S : Finset (Fin n)) ∩ T).powersetCard (p-1) := by
      ext B
      simp [mem_powersetCard, and_assoc, and_comm, 𝒝, subset_inter_iff]
    rw [← sum_subtype 𝒝 (fun _ => Iff.rfl) g]
    rw [show g = fun B => if B ⊆ (T : Finset (Fin n)) ∧ B ⊆ (S : Finset (Fin n)) then 1 else 0 from rfl,
      ← sum_filter, sum_const, nsmul_one, heq, card_powersetCard]
  have hdot' (S T : 𝒜) : ∑ B : 𝒝, f S B * f T B = if S = T then 1 else 0 := by
    rw [hdot]
    have hN := hc S S.property
    have hle : ((S : Finset (Fin n)) ∩ T).card ≤ (S : Finset (Fin n)).card := card_le_card inter_subset_left
    have hp' := hp.two_le
    have hl : ((S : Finset (Fin n)) ∩ T).card < 2*p := by omega
    simp only [choose_residue hp, residue_iff hp hl]
    by_cases hSame : S = T
    · subst T
      simp [hN]
    · have hne := hd S S.property T T.property (fun e => hSame (Subtype.ext e))
      have hbound : ((S : Finset (Fin n)) ∩ T).card ≠ 2*p-1 := by
        intro hE
        have hST : (S : Finset (Fin n)) ⊆ T := by
          have eq : (S : Finset (Fin n)) ∩ T = S := eq_of_subset_of_card_le inter_subset_left (by omega)
          exact eq ▸ inter_subset_right
        exact hSame (Subtype.ext (eq_of_subset_of_card_le hST (by rw [hN, hc T T.property])))
      simp [hSame, hne, hbound]
  have hi : LinearIndependent (ZMod p) f := by
    rw [Fintype.linearIndependent_iff]
    intro a ha S
    have hz (B : 𝒝) : (∑ T : 𝒜, a T * f T B) = 0 := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using congrFun ha B
    have he : (∑ B : 𝒝, (∑ T : 𝒜, a T * f T B) * f S B) = 0 := by
      exact sum_eq_zero (fun B _ => by rw [hz, zero_mul])
    simp_rw [sum_mul, mul_assoc] at he
    rw [sum_comm] at he
    simp_rw [← mul_sum, hdot'] at he
    simpa using he
  simpa [Module.finrank_fintype_fun_eq_card, 𝒝, card_powersetCard] using hi.fintype_card_le_finrank

private noncomputable def point {n : ℕ} (p : ℕ) (S : Finset (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => if i ∈ S then (√(2*(p:ℝ)))⁻¹ else 0)

private theorem adjacent {n p : ℕ} (hp : 0 < p) (S T : Finset (Fin n))
    (hS : S.card = 2*p-1) (hT : T.card = 2*p-1) (hST : (S ∩ T).card = p-1) :
    (Erdos704.unitDistanceGraph n).Adj (point p S) (point p T) := by
  classical
  have hpos : 0 < 2 * (p : ℝ) := by positivity
  have hsq : (√(2*(p:ℝ)))⁻¹ ^ 2 = (2*(p:ℝ))⁻¹ := by
    rw [inv_pow, sq_sqrt hpos.le]
  have hc (U : Finset (Fin n)) :
      (∑ i : Fin n, if i ∈ U then (1:ℝ) else 0) = U.card := by
    rw [← sum_filter, filter_mem_eq_inter, univ_inter, sum_const, nsmul_one]
  have he : dist (point p S) (point p T) ^ 2 = 1 := by
    rw [PiLp.dist_sq_eq_of_L2]
    calc
      _ = ∑ i : Fin n, (((if i ∈ S then (1:ℝ) else 0) +
          (if i ∈ T then 1 else 0) - 2*(if i ∈ S ∩ T then 1 else 0)) * (2*(p:ℝ))⁻¹) := by
        apply sum_congr rfl
        intro i _
        rw [Real.dist_eq, sq_abs]
        change ((if i ∈ S then (√(2*(p:ℝ)))⁻¹ else 0) -
          (if i ∈ T then (√(2*(p:ℝ)))⁻¹ else 0))^2 = _
        by_cases hi : i ∈ S <;> by_cases hj : i ∈ T <;>
          simp only [mem_inter, hi, hj, if_true, if_false, true_and, false_and, sub_self,
            sub_zero, zero_sub, neg_sq, hsq] <;> ring
      _ = 1 := by
        rw [← sum_mul, sum_sub_distrib, sum_add_distrib, ← mul_sum, hc, hc, hc,
          hS, hT, hST]
        have hp' : (1:ℕ) ≤ p := by omega
        have hp'' : (1:ℕ) ≤ 2*p := by omega
        push_cast [Nat.cast_sub hp', Nat.cast_sub hp'']
        field_simp
        ring
  show dist (point p S) (point p T) = 1
  have hnon : 0 ≤ dist (point p S) (point p T) := dist_nonneg
  nlinarith

private theorem color_bound {n p k : ℕ} (hp : p.Prime)
    (h : (Erdos704.unitDistanceGraph n).Colorable k) :
    n.choose (2*p-1) ≤ k * n.choose (p-1) := by
  classical
  obtain ⟨c⟩ := h
  let U := (univ : Finset (Fin n)).powersetCard (2*p-1)
  let col (S : Finset (Fin n)) := c (point p S)
  have hcount : U.card = ∑ i : Fin k, (U.filter (fun S => col S = i)).card :=
    card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
  rw [show n.choose (2*p-1) = U.card by simp [U], hcount]
  calc
    _ ≤ ∑ _ : Fin k, n.choose (p-1) := by
      apply sum_le_sum
      intro i _
      apply family_card hp
      · intro S hS
        exact (mem_powersetCard.mp (mem_filter.mp hS).1).2
      · intro S hS T hT _ hST
        have hS' := (mem_powersetCard.mp (mem_filter.mp hS).1).2
        have hT' := (mem_powersetCard.mp (mem_filter.mp hT).1).2
        have hadj := c.map_rel (adjacent hp.pos S T hS' hT' hST)
        exact hadj ((mem_filter.mp hS).2.trans (mem_filter.mp hT).2.symm)
    _ = _ := by simp

end OMA

open Finset Filter Real Asymptotics
open ArithmeticFunction (vonMangoldt vonMangoldt_nonneg vonMangoldt_sum)
open scoped Topology Chebyshev

namespace OMA

private noncomputable def F (t : ℝ) : ℝ := t*log t-t

private theorem log_factorial_error (n : ℕ) :
    |log (n.factorial:ℝ) - F n| ≤ log (2*(n:ℝ)) + 1 := by
  cases n with
  | zero => simp [F]
  | succ n =>
    have hpos : 0 < ((n+1:ℕ):ℝ) := by positivity
    have hlog : 0 ≤ log (2*((n+1:ℕ):ℝ)) := log_nonneg (by norm_cast; omega)
    have ha := Stirling.log_stirlingSeq'_antitone (show 0 ≤ n by omega)
    simp only [Function.comp_apply] at ha
    rw [Stirling.stirlingSeq_one, log_div (by positivity) (by positivity), log_exp, log_sqrt (by norm_num)] at ha
    have hb := Stirling.log_stirlingSeq_bounded_by_constant n
    rw [Stirling.log_stirlingSeq_formula, log_div hpos.ne' (exp_pos 1).ne', log_exp] at ha hb
    have hh : 0 ≤ log (2:ℝ) := log_nonneg (by norm_num)
    have hh' := log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    rw [abs_le]
    constructor <;> unfold F <;> nlinarith

private theorem log_factorial_approx {n : ℕ} {t M : ℝ} (hn : 1 ≤ n)
    (ht : (n:ℝ) ≤ t) (hnear : t ≤ n+1) (hM : t ≤ M) :
    |log (n.factorial:ℝ) - F t| ≤ 2 * log (2*M) + 2 := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have ht' : (1:ℝ) ≤ t := hn'.trans ht
  have hl : 0 ≤ log t := log_nonneg ht'
  have hl' : log t ≤ log (2*M) := log_le_log (by positivity) (by linarith)
  have hs : log (t/n) ≤ t/n-1 := log_le_sub_one_of_pos (by positivity)
  have hs' : (n:ℝ)*log (t/n) ≤ t-n := by
    have he := mul_le_mul_of_nonneg_left hs (show (0:ℝ) ≤ n by positivity)
    have hm : (n:ℝ)*(t/n-1) = t-n := by field_simp
    rw [hm] at he
    linarith
  have he : F t - F n ≤ log t := by
    rw [log_div (by positivity) (by positivity)] at hs'
    dsimp [F]
    nlinarith [mul_le_mul_of_nonneg_right (show t-(n:ℝ) ≤ 1 by linarith) hl]
  have he' : -(1:ℝ) ≤ F t - F n := by
    have hlm : 0 ≤ log (n:ℝ) := log_nonneg hn'
    have hlog := log_le_log (show 0 < (n:ℝ) by positivity) ht
    have ha := mul_le_mul ht hlog hlm (show 0 ≤ t by positivity)
    dsimp [F]
    linarith
  have hfn := abs_le.mp (log_factorial_error n)
  have hlogn : log (2*(n:ℝ)) ≤ log (2*M) := log_le_log (by positivity) (by linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem log_factorial_sum (n : ℕ) :
    log (n.factorial:ℝ) = ∑ d ∈ Icc 1 n, ((n/d:ℕ):ℝ) * vonMangoldt d := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    let S := Icc 1 (n+1)
    have hS : S = insert (n+1) (Icc 1 n) := by
      ext d
      simp [S]
      omega
    have hz : (∑ d ∈ S, ((n/d:ℕ):ℝ) * vonMangoldt d) = log (n.factorial:ℝ) := by
      rw [hS, sum_insert (by simp : n+1 ∉ Icc 1 n), Nat.div_eq_of_lt (Nat.lt_succ_self n)]
      simp [← ih]
    have hd : S.filter (fun d => d ∣ n+1) = (n+1).divisors := by
      ext d
      simp only [S, mem_filter, mem_Icc, Nat.mem_divisors]
      exact ⟨fun h => ⟨h.2, by omega⟩, fun h =>
        ⟨⟨Nat.pos_of_dvd_of_pos h.1 (by omega), Nat.le_of_dvd (by omega) h.1⟩, h.1⟩⟩
    have hs : (∑ d ∈ S, if d ∣ n+1 then vonMangoldt d else 0) = log (n+1:ℕ) := by
      rw [← sum_filter, hd, vonMangoldt_sum]
    rw [Nat.factorial_succ, Nat.cast_mul, log_mul (by positivity) (by positivity), ← hz, ← hs,
      ← sum_add_distrib]
    apply sum_congr rfl
    intro d hd'
    by_cases he : d ∣ n+1
    · rw [Nat.succ_div_of_dvd he]
      simp [he]
      ring
    · rw [Nat.succ_div_of_not_dvd he]
      simp [he]

private noncomputable def combo (n : ℕ) : ℝ :=
  log (n.factorial:ℝ) + log ((n/30:ℕ).factorial:ℝ) -
    log ((n/2:ℕ).factorial:ℝ) - log ((n/3:ℕ).factorial:ℝ) - log ((n/5:ℕ).factorial:ℝ)

private def coef (q : ℕ) : ℤ :=
  (q:ℤ) + ((q/30:ℕ):ℤ) - ((q/2:ℕ):ℤ) - ((q/3:ℕ):ℤ) - ((q/5:ℕ):ℤ)

private theorem coef_bounds (q : ℕ) :
    0 ≤ coef q ∧ coef q ≤ 1 ∧ (1 ≤ q → q ≤ 5 → coef q = 1) := by
  have hmod := Nat.mod_lt q (by decide : 0 < 30)
  have hper : coef q = coef (q % 30) := by
    have h := Nat.mod_add_div q 30
    unfold coef
    omega
  constructor
  · rw [hper]
    interval_cases h : q%30 <;> norm_num [coef]
  constructor
  · rw [hper]
    interval_cases h : q%30 <;> norm_num [coef]
  · intro hq hq'
    interval_cases q <;> norm_num [coef]

private theorem combo_sum (n : ℕ) :
    combo n = ∑ d ∈ Icc 1 n, (coef (n/d):ℝ) * vonMangoldt d := by
  have h (k : ℕ) (hk : 0 < k) : log ((n/k:ℕ).factorial:ℝ) =
      ∑ d ∈ Icc 1 n, (((n/d/k:ℕ):ℝ) * vonMangoldt d) := by
    rw [log_factorial_sum]
    have hs : Icc 1 (n/k) ⊆ Icc 1 n := Icc_subset_Icc_right (Nat.div_le_self _ _)
    rw [sum_subset hs]
    · apply sum_congr rfl
      intro d _
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm k d]
    · intro d hd hd'
      have hlt : n/k < d := by simp only [mem_Icc] at hd hd'; omega
      rw [Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
        Nat.div_eq_of_lt hlt, Nat.cast_zero, zero_mul]
  have h1 := h 1 (by decide)
  simp only [Nat.div_one] at h1
  unfold combo
  rw [h1, h 30 (by decide), h 2 (by decide), h 3 (by decide), h 5 (by decide)]
  simp_rw [← sum_add_distrib, ← sum_sub_distrib, coef, Int.cast_sub, Int.cast_add,
    Int.cast_natCast]
  apply sum_congr rfl
  intro d _
  ring

private theorem combo_bounds (n : ℕ) :
    combo n ≤ ψ (n:ℝ) ∧ ψ (n:ℝ) ≤ combo n + ψ ((n/6:ℕ):ℝ) := by
  rw [combo_sum, Chebyshev.psi_eq_sum_Icc, Chebyshev.psi_eq_sum_Icc]
  simp only [Nat.floor_natCast]
  have hI (m : ℕ) :
      (∑ d ∈ Icc 0 m, vonMangoldt d) = ∑ d ∈ Icc 1 m, vonMangoldt d := by
    have he : Icc 0 m = insert 0 (Icc 1 m) := by ext d; simp; omega
    rw [he, sum_insert (by simp : 0 ∉ Icc 1 m)]
    simp
  rw [hI, hI]
  constructor
  · apply sum_le_sum
    intro d _
    have hd : (coef (n/d):ℝ) ≤ 1 := by exact_mod_cast (coef_bounds (n/d)).2.1
    simpa using mul_le_mul_of_nonneg_right hd (vonMangoldt_nonneg (n := d))
  · have hsub : Icc 1 (n/6) ⊆ Icc 1 n := Icc_subset_Icc_right (Nat.div_le_self _ _)
    have hpsi :
        (∑ d ∈ Icc 1 (n/6), vonMangoldt d) =
          ∑ d ∈ Icc 1 n, if d ≤ n/6 then vonMangoldt d else 0 := by
      rw [← sum_filter]
      congr 1
      ext d
      simp only [mem_Icc, mem_filter]
      have h := Nat.div_le_self n 6
      omega
    rw [hpsi, ← sum_add_distrib]
    apply sum_le_sum
    intro d hd
    have hd1 := (mem_Icc.mp hd).1
    have hd2 := (mem_Icc.mp hd).2
    by_cases hle : d ≤ n/6
    · have hd' : 0 ≤ (coef (n/d):ℝ) := by exact_mod_cast (coef_bounds (n/d)).1
      have hp := mul_nonneg hd' (vonMangoldt_nonneg (n := d))
      simp [hle]
      linarith
    · have hq₁ : 1 ≤ n/d := (Nat.le_div_iff_mul_le (by omega)).2 (by simpa)
      have hq₂ : n/d ≤ 5 := by
        have h₁ : n < d*6 := (Nat.div_lt_iff_lt_mul (by norm_num)).mp (by omega : n/6 < d)
        exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by omega)).2 (by simpa [mul_comm] using h₁))
      simp [hle, (coef_bounds (n/d)).2.2 hq₁ hq₂]

private noncomputable def chebC : ℝ :=
  log 2 / 2 + log 3 / 3 + log 5 / 5 - log 30 / 30

private theorem lt_chebC : log 2 < chebC := by
  have h23 : log (2:ℝ) < log 3 := log_lt_log (by norm_num) (by norm_num)
  have h45 : log (4:ℝ) < log 5 := log_lt_log (by norm_num) (by norm_num)
  have h4 : log (4:ℝ) = 2*log 2 := by rw [show (4:ℝ) = 2^2 by norm_num, log_pow]; norm_num
  have h30 : log (30:ℝ) = log 2 + log 3 + log 5 := by
    rw [show (30:ℝ) = 2*3*5 by norm_num, log_mul (by norm_num) (by norm_num),
      log_mul (by norm_num) (by norm_num)]
  unfold chebC
  linarith [log_pos (by norm_num : (1:ℝ) < 2)]

private theorem combo_approx {t : ℝ} (ht : 30 ≤ t) :
    |combo ⌊t⌋₊ - chebC*t| ≤ 10*log (2*t)+10 := by
  have h (d : ℕ) (hd : 1 ≤ d) (hd' : d ≤ 30) :
      |log ((⌊t⌋₊/d:ℕ).factorial:ℝ) - F (t/d)| ≤ 2*log (2*t)+2 := by
    have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
    have hd30 : (d:ℝ) ≤ 30 := by exact_mod_cast hd'
    have htd : 1 ≤ t/d := (le_div_iff₀ hd0).2 (by simpa using hd30.trans ht)
    rw [← Nat.floor_div_natCast]
    exact log_factorial_approx (Nat.le_floor (show ((1:ℕ):ℝ) ≤ t/d by simpa using htd)) (Nat.floor_le (by linarith))
      (Nat.lt_floor_add_one (t/d)).le (div_le_self (by linarith) hd1)
  have h1 := abs_le.mp (h 1 (by decide) (by decide))
  have h2 := abs_le.mp (h 2 (by decide) (by decide))
  have h3 := abs_le.mp (h 3 (by decide) (by decide))
  have h5 := abs_le.mp (h 5 (by decide) (by decide))
  have h30 := abs_le.mp (h 30 (by decide) (by decide))
  simp only [Nat.div_one, Nat.cast_one, div_one] at h1
  norm_num only [Nat.cast_ofNat] at h2 h3 h5 h30
  have heq : F t + F (t/30) - F (t/2) - F (t/3) - F (t/5) = chebC*t := by
    unfold F chebC
    rw [log_div (by linarith : t ≠ 0) (by norm_num : (30:ℝ) ≠ 0),
      log_div (by linarith : t ≠ 0) (by norm_num : (2:ℝ) ≠ 0),
      log_div (by linarith : t ≠ 0) (by norm_num : (3:ℝ) ≠ 0),
      log_div (by linarith : t ≠ 0) (by norm_num : (5:ℝ) ≠ 0)]
    ring
  unfold combo
  rw [← heq, abs_le]
  exact ⟨by linarith [h1.1, h30.1, h2.2, h3.2, h5.2],
    by linarith [h1.2, h30.2, h2.1, h3.1, h5.1]⟩

private theorem small_error {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, 50*(log (2*x)+1)+4*√x*log x ≤ δ*x := by
  have hl : log =o[atTop] sqrt := by
    rw [show sqrt = fun x => x ^ (1/2:ℝ) from funext sqrt_eq_rpow]
    exact isLittleO_log_rpow_atTop (by norm_num)
  have hbl := hl.bound (c := δ/200) (by positivity)
  filter_upwards [hbl, eventually_ge_atTop (1:ℝ), eventually_ge_atTop (200/δ)]
    with x hx hx1 hx2
  have hp : 0 < x := by linarith
  have hroot : 1 ≤ √x := (le_sqrt (by norm_num) hp.le).2 (by linarith)
  have hlog : 0 ≤ log x := log_nonneg hx1
  have hlog2 : log (2:ℝ) ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  simp only [Real.norm_eq_abs, abs_of_nonneg hlog, abs_of_nonneg (sqrt_nonneg _)] at hx
  have hmul := mul_le_mul_of_nonneg_left hx (sqrt_nonneg x)
  have he : √x * log x ≤ δ*x/200 := by
    nlinarith [sq_sqrt hp.le]
  have hle : log x ≤ √x*log x := by nlinarith
  have hlarge : 200 ≤ δ*x := by
    have := (div_le_iff₀ hδ).mp hx2
    simpa [mul_comm] using this
  rw [log_mul (by norm_num) hp.ne']
  linarith

private theorem prime_interval :
    ∀ᶠ N : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ N/8 < p ∧ (p:ℝ) ≤ N/6 := by
  have h4 : log (4:ℝ) = 2*log 2 := by rw [show (4:ℝ) = 2^2 by norm_num, log_pow]; norm_num
  let δ := (chebC - log 2) / 48
  have hδ : 0 < δ := by dsimp [δ]; linarith [lt_chebC]
  filter_upwards [small_error hδ, eventually_ge_atTop (240:ℝ)] with N hE hN
  have hpos : 0 < N := by linarith
  have h6 : 30 ≤ N/6 := by linarith
  have h8 : 30 ≤ N/8 := by linarith
  have h48 : 1 ≤ N/48 := by linarith
  have hx6 := abs_le.mp (combo_approx h6)
  have hx8 := abs_le.mp (combo_approx h8)
  have hb6 := (combo_bounds ⌊N/6⌋₊).1
  have hb8 := (combo_bounds ⌊N/8⌋₊).2
  rw [← Chebyshev.psi_eq_psi_coe_floor] at hb6
  nth_rw 1 [← Chebyshev.psi_eq_psi_coe_floor] at hb8
  have hdiv : ((⌊N/8⌋₊/6:ℕ):ℝ) ≤ N/48 := by
    rw [← Nat.floor_div_natCast]
    norm_num only [Nat.cast_ofNat]
    exact (Nat.floor_le (by positivity : 0 ≤ N / 8 / 6)).trans (by ring_nf; linarith)
  have hbψ := Chebyshev.psi_mono hdiv
  have H₁ := Chebyshev.psi_sub_theta_le (x := N/6) (by linarith)
  have H₂ := Chebyshev.theta_le_psi (N/8)
  have H₃ := Chebyshev.psi_le h48
  have hw (a : ℝ) (ha : 1 ≤ a) (hAN : a ≤ N) :
      √a * log a ≤ √N * log N ∧ log (2*a) ≤ log (2*N) := by
    exact ⟨mul_le_mul (sqrt_le_sqrt hAN) (log_le_log (by linarith) hAN)
      (log_nonneg ha) (sqrt_nonneg _), log_le_log (by linarith) (by linarith)⟩
  have hw6 := hw (N/6) (by linarith) (by linarith)
  have hw8 := hw (N/8) (by linarith) (by linarith)
  have hw48 := hw (N/48) h48 (by linarith)
  have hd : θ (N/8) < θ (N/6) := by
    rw [h4] at H₃
    have hδ' : 0 < δ*N := mul_pos hδ hpos
    have hf : δ*N = chebC*N/48 - log 2*N/48 := by dsimp [δ]; ring
    have hlN : 0 ≤ log (2*N) := log_nonneg (by linarith)
    linarith [hx6.1, hx8.2, hw6.1, hw6.2, hw8.2, hw48.1]
  by_contra! hnone
  have he : Nat.primesLE ⌊N/8⌋₊ = Nat.primesLE ⌊N/6⌋₊ := by
    ext p
    simp only [Nat.mem_primesLE]
    constructor
    · intro h
      exact ⟨h.1.trans (Nat.floor_mono (by linarith)), h.2⟩
    · intro h
      have hp := (Nat.le_floor_iff (by linarith : 0 ≤ N/6)).1 h.1
      exact ⟨Nat.le_floor (le_of_not_gt (fun hh => (hnone p h.2 hh).not_ge hp)), h.2⟩
  rw [Chebyshev.theta_eq_theta_coe_floor (N/8), Chebyshev.theta_eq_theta_coe_floor (N/6),
    Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log, he] at hd
  exact (lt_irrefl _) hd

private noncomputable def D (x : ℝ) : ℝ :=
  F x + F (1-x) - F (2*x) - F (1-2*x)

private theorem derivative_F {t : ℝ} (ht : 0 < t) : HasDerivAt F (log t) t := by
  have he : 1 * log t + t*t⁻¹ - 1 = log t := by field_simp; ring
  rw [← he]
  exact ((hasDerivAt_id t).mul (hasDerivAt_log ht.ne')).sub (hasDerivAt_id t)

private theorem derivative_D {x : ℝ} (hx₁ : 0 < x) (hx₂ : x < 1/2) :
    HasDerivAt D (log ((4*x*(1-x))⁻¹ - 1)) x := by
  have h₁ := derivative_F hx₁
  have h₂ := (derivative_F (t := 1-x) (by linarith)).comp x ((hasDerivAt_id x).const_sub 1)
  have h₃ := (derivative_F (t := 2*x) (by positivity)).comp x ((hasDerivAt_id x).const_mul 2)
  have h₄ := (derivative_F (t := 1-2*x) (by linarith)).comp x
    (((hasDerivAt_id x).const_mul 2).const_sub 1)
  have he : log ((4*x*(1-x))⁻¹ - 1) =
      (log x + log (1-x)*(-1)) - log (2*x)*(2*1) - log (1-2*x)*(-(2*1)) := by
    have hx12 : 0 < 1-x := by linarith
    have hx2 : 0 < 1 - 2*x := by linarith
    have hr : (4*x*(1-x))⁻¹ - 1 = (1-2*x)^2 / ((2*x)^2*(1-x)/x) := by
      field_simp
      ring
    rw [hr, log_div (by positivity) (by positivity), log_pow,
      log_div (by positivity) hx₁.ne', log_mul (by positivity) hx12.ne', log_pow]
    ring
  rw [he]
  exact ((h₁.add h₂).sub h₃).sub h₄

private theorem D_concave :
    ConcaveOn ℝ (Set.Icc (1/8:ℝ) (1/6)) D := by
  have h (x : ℝ) (hx : x ∈ Set.Icc (1/8:ℝ) (1/6)) :
      HasDerivAt D (log ((4*x*(1-x))⁻¹ - 1)) x :=
    derivative_D (by linarith [hx.1]) (by linarith [hx.2])
  have hanti : AntitoneOn (deriv D) (interior (Set.Icc (1/8:ℝ) (1/6))) := by
    intro a ha b hb hab
    have ha' := interior_subset ha
    have hb' := interior_subset hb
    rw [(h a ha').deriv, (h b hb').deriv]
    have ha₁ : 0 < a := by linarith [ha'.1]
    have hb₁ : 0 < b := by linarith [hb'.1]
    have hsum : a+b ≤ 1 := by linarith [ha'.2, hb'.2]
    have hprod : 4*a*(1-a) ≤ 4*b*(1-b) := by
      nlinarith [mul_nonneg (show 0 ≤ b-a by linarith) (show 0 ≤ 1-(a+b) by linarith)]
    have hb₂ : 0 < 4*b*(1-b) := by
      have : 0 < 1-b := by linarith [hb'.2]
      positivity
    have hb₃ : 4*b*(1-b) < 1 := by nlinarith [hb'.1, hb'.2]
    have hleft : 0 < (4*b*(1-b))⁻¹ - 1 := by
      exact sub_pos.mpr (one_lt_inv_iff₀.mpr ⟨hb₂,hb₃⟩)
    exact log_le_log hleft (sub_le_sub_right (inv_anti₀ (by
      have : 0 < 1-a := by linarith [ha'.2]
      positivity) hprod) _)
  exact hanti.concaveOn_of_deriv (convex_Icc _ _)
    (fun x hx => (h x hx).continuousAt.continuousWithinAt)
    (fun x hx => (h x (interior_subset hx)).differentiableAt.differentiableWithinAt)

private theorem D_at {d : ℝ} (hd : 2 < d) :
    D (1/d) = ((d-1)*log (d-1) - 2*log 2 - (d-2)*log (d-2))/d := by
  have hd0 : d ≠ 0 := by linarith
  have h₁ : 1-1/d = (d-1)/d := by field_simp
  have h₂ : 2*(1/d) = 2/d := by ring
  have h₃ : 1-2*(1/d) = (d-2)/d := by field_simp
  unfold D F
  rw [h₁, h₃, h₂, log_div (by norm_num) hd0, log_one,
    log_div (by linarith : d-1 ≠ 0) hd0, log_div (by norm_num) hd0,
    log_div (by linarith : d-2 ≠ 0) hd0]
  ring

private theorem entropy_gap {x : ℝ} (hx : x ∈ Set.Icc (1/8:ℝ) (1/6)) :
    log (1201/1000:ℝ) ≤ D x := by
  have h8 : log (1201/1000:ℝ) < D (1/8) := by
    rw [D_at (by norm_num : (2:ℝ) < 8)]
    have h := log_lt_log (by positivity : 0 < (1201/1000:ℝ)^8)
      (by norm_num : (1201/1000:ℝ)^8 < 7^7/(2^2*6^6))
    rw [log_pow, log_div (x := (7:ℝ)^7) (by positivity) (by positivity),
      log_mul (x := (2:ℝ)^2) (by positivity) (by positivity),
      log_pow, log_pow, log_pow] at h
    norm_num at h ⊢
    linarith
  have h6 : log (1201/1000:ℝ) < D (1/6) := by
    rw [D_at (by norm_num : (2:ℝ) < 6)]
    have h := log_lt_log (by positivity : 0 < (1201/1000:ℝ)^6)
      (by norm_num : (1201/1000:ℝ)^6 < 5^5/(2^2*4^4))
    rw [log_pow, log_div (x := (5:ℝ)^5) (by positivity) (by positivity),
      log_mul (x := (2:ℝ)^2) (by positivity) (by positivity),
      log_pow, log_pow, log_pow] at h
    norm_num at h ⊢
    linarith
  exact (le_min h8.le h6.le).trans (D_concave.min_le_of_mem_Icc
    ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩ hx)

private theorem log_choose {n k : ℕ} (hk : k ≤ n) :
    log (n.choose k:ℝ) = log (n.factorial:ℝ) -
      log (k.factorial:ℝ) - log ((n-k).factorial:ℝ) := by
  have he := congrArg (fun a : ℕ => log (a:ℝ)) (Nat.choose_mul_factorial_mul_factorial hk)
  have hk' := Nat.choose_pos hk
  push_cast at he
  rw [log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity)] at he
  linarith

private theorem log_factorial_succ (a : ℕ) :
    log ((a+1).factorial:ℝ) = log (a.factorial:ℝ) + log ((a+1:ℕ):ℝ) := by
  rw [Nat.factorial_succ, Nat.cast_mul, log_mul (by positivity) (by positivity), add_comm]

private theorem log_choose_pred {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    log (n.choose (k-1):ℝ) =
      log (n.choose k:ℝ) + log (k:ℝ) - log ((n-k+1:ℕ):ℝ) := by
  rw [log_choose (by omega : k-1 ≤ n), log_choose hkn,
    show n-(k-1) = n-k+1 by omega, log_factorial_succ]
  have h := log_factorial_succ (k-1)
  rw [show k-1+1 = k by omega] at h
  linarith

private theorem F_mul {N z : ℝ} (hN : 0 < N) (hz : 0 < z) :
    F (N*z) = N*F z + N*z*log N := by
  unfold F
  rw [log_mul hN.ne' hz.ne']
  ring

private theorem binomial_estimate :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℕ, p.Prime → (n:ℝ)/8 < p → (p:ℝ) ≤ (n:ℝ)/6 →
      (6/5:ℝ)^n * (n.choose (p-1):ℝ) ≤ (n.choose (2*p-1):ℝ) := by
  let δ := log (1201/1000:ℝ) - log (6/5)
  have hδ : 0 < δ := sub_pos.mpr (log_lt_log (by norm_num) (by norm_num))
  have hE := tendsto_natCast_atTop_atTop.eventually (small_error hδ)
  filter_upwards [hE, eventually_ge_atTop (1:ℕ)] with n hn hN
  intro p hp hp8 hp6
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hN
  have hn0 : (0:ℝ) < n := by positivity
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hn2p : 2*p ≤ n := by
    exact_mod_cast (show 2*(p:ℝ) ≤ (n:ℝ) by linarith)
  have hnp : p ≤ n := by omega
  have hp' := hp.one_lt
  have hnp' : (0:ℝ) < (n:ℝ)-(p:ℝ) := by linarith
  have hn2p' : (0:ℝ) < (n:ℝ)-2*(p:ℝ) := by linarith
  let x := (p:ℝ)/(n:ℝ)
  have hx : x ∈ Set.Icc (1/8:ℝ) (1/6) := by
    exact ⟨(le_div_iff₀ hn0).2 (by linarith), (div_le_iff₀ hn0).2 (by linarith)⟩
  have hc₁ := log_choose_pred (by omega : 1 ≤ 2*p) hn2p
  have hc₂ := log_choose_pred (by omega : 1 ≤ p) hnp
  have hlog₁ : log (p:ℝ) ≤ log ((2*p:ℕ):ℝ) := by
    apply log_le_log hp0
    push_cast
    linarith
  have hlog₂ : log ((n-2*p+1:ℕ):ℝ) ≤ log ((n-p+1:ℕ):ℝ) := by
    exact log_le_log (by positivity) (by exact_mod_cast (show n-2*p+1 ≤ n-p+1 by omega))
  have hshift :
      log (n.choose (2*p):ℝ) - log (n.choose p:ℝ) ≤
        log (n.choose (2*p-1):ℝ) - log (n.choose (p-1):ℝ) := by linarith
  have hF :
      F p + F ((n-p:ℕ):ℝ) - F ((2*p:ℕ):ℝ) - F ((n-2*p:ℕ):ℝ) =
        (n:ℝ)*D x := by
    push_cast [Nat.cast_sub hnp, Nat.cast_sub hn2p]
    have h₁ : (n:ℝ)*x = p := by dsimp [x]; field_simp
    have h₂ : (n:ℝ)*(1-x) = (n:ℝ)-p := by linarith
    have h₃ : (n:ℝ)*(2*x) = 2*(p:ℝ) := by nlinarith
    have h₄ : (n:ℝ)*(1-2*x) = (n:ℝ)-2*(p:ℝ) := by linarith
    rw [← h₄, ← h₂, ← h₃, ← h₁]
    rw [F_mul hn0 (by positivity), F_mul hn0 (by linarith [hx.2]),
      F_mul hn0 (by positivity), F_mul hn0 (by linarith [hx.2])]
    unfold D
    ring
  have hex (q : ℕ) (hq : q ≤ n) :
      |log (q.factorial:ℝ) - F q| ≤ log (2*(n:ℝ))+1 := by
    by_cases hq0 : q = 0
    · subst q
      simpa [F] using add_nonneg (log_nonneg (show 1 ≤ 2*(n:ℝ) by linarith)) zero_le_one
    · have h := log_le_log (show 0 < 2*(q:ℝ) by positivity)
        (show 2*(q:ℝ) ≤ 2*(n:ℝ) by gcongr)
      exact (log_factorial_error q).trans (by linarith)
  have h₁ := abs_le.mp (hex p hnp)
  have h₂ := abs_le.mp (hex (n-p) (by omega))
  have h₃ := abs_le.mp (hex (2*p) hn2p)
  have h₄ := abs_le.mp (hex (n-2*p) (by omega))
  have hend := mul_le_mul_of_nonneg_left (entropy_gap hx) hn0.le
  have herr : 4*(log (2*(n:ℝ))+1) ≤ δ*(n:ℝ) := by
    have hl1 := log_nonneg hn1
    have hl2 := log_nonneg (show 1 ≤ 2*(n:ℝ) by linarith)
    have hh := mul_nonneg (sqrt_nonneg (n:ℝ)) hl1
    linarith
  have hlog :
      (n:ℝ)*log (6/5) + log (n.choose (p-1):ℝ) ≤ log (n.choose (2*p-1):ℝ) := by
    have hdiff : (n:ℝ)*D x - 4*(log (2*(n:ℝ))+1) ≤
        log (n.choose (2*p):ℝ) - log (n.choose p:ℝ) := by
      rw [log_choose hn2p, log_choose hnp]
      linarith [h₁.1, h₂.1, h₃.2, h₄.2]
    have hδ' : δ*(n:ℝ) = (n:ℝ)*log (1201/1000) - (n:ℝ)*log (6/5) := by dsimp [δ]; ring
    linarith
  have hcp := Nat.choose_pos (show p-1 ≤ n by omega)
  have hcq := Nat.choose_pos (show 2*p-1 ≤ n by omega)
  have hpos : 0 < (6/5:ℝ)^n * (n.choose (p-1):ℝ) := by positivity
  apply (log_le_log_iff hpos (by positivity)).mp
  rw [log_mul (by positivity) (by positivity), log_pow]
  simpa [mul_comm] using hlog

end OMA

namespace OMA

private theorem frankl_wilson :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
      (Erdos704.unitDistanceGraph n).Colorable k →
        (1 - ε) * (1.2:ℝ)^n ≤ (k:ℝ) := by
  intro ε hε
  have hp := tendsto_natCast_atTop_atTop.eventually prime_interval
  filter_upwards [hp, binomial_estimate] with n hn he
  intro k hk
  obtain ⟨p, hp, hp₁, hp₂⟩ := hn
  have hcomp := he p hp hp₁ hp₂
  have hbound : (n.choose (2*p-1):ℝ) ≤ (k:ℝ) * (n.choose (p-1):ℝ) := by
    exact_mod_cast color_bound hp hk
  have hpn : p-1 ≤ n := by
    have h : (p:ℝ) ≤ (n:ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have h' : p ≤ n := by exact_mod_cast h
    omega
  have hcp := Nat.choose_pos hpn
  have hb : (6/5:ℝ)^n ≤ (k:ℝ) :=
    le_of_mul_le_mul_right (hcomp.trans hbound) (by positivity)
  have hbase : (1.2:ℝ) = 6/5 := by norm_num
  rw [hbase]
  exact (mul_le_of_le_one_left (by positivity) (by linarith)).trans hb

end OMA

theorem OMA.solution : type_of% @Erdos704.erdos_704.variants.frankl_wilson :=
  OMA.frankl_wilson