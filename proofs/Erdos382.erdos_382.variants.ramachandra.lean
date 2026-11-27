import FormalConjectures.ErdosProblems.«382»
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Primorial
import Mathlib.Analysis.SpecialFunctions.Stirling

/-! Bounding intervals whose largest prime factor occurs twice. -/

open Finset Filter Real Asymptotics

open ArithmeticFunction (vonMangoldt vonMangoldt_nonneg vonMangoldt_sum)
open scoped Topology Chebyshev

namespace PrimeGaps

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


private theorem choose_lower (k : ℕ) : 5^k ≤ 2*(4*k).choose k := by
  induction k using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more k ih _ =>
    have h := Finset.single_le_sum (f := fun ij : ℕ × ℕ => (4*k).choose ij.1 * (8:ℕ).choose ij.2)
      (fun i (_ : i ∈ Finset.HasAntidiagonal.antidiagonal (k+2)) => Nat.zero_le _) (a := (k,2))
      (show (k,2) ∈ Finset.HasAntidiagonal.antidiagonal (k+2) by simp)
    rw [←Nat.add_choose_eq] at h
    change (4*k).choose k * 28 ≤ _ at h
    rw [pow_add,show 4*(k+2)=4*k+8 by omega]
    norm_num
    omega

private theorem choose_upper {v k : ℕ} (hv : 0 < v) (hk : k ≤ v)
    (fac : ∀ p ∈ (v.choose k).primeFactors, p ≤ k) :
    v.choose k ≤ v^(Nat.sqrt v)*4^k := by
  classical
  let T := (v.choose k).primeFactors
  let A := T.filter (· ≤ v.sqrt)
  let B := T.filter (fun p => ¬ p ≤ v.sqrt)
  let w (p : ℕ) := p^(v.choose k).factorization p
  have split : (∏ p ∈ A, w p)*(∏ p ∈ B, w p) = v.choose k := by
    rw [Finset.prod_filter_mul_prod_filter_not]
    exact Nat.prod_factorization_pow_eq_self (Nat.choose_pos hk).ne'
  have ac : A.card ≤ v.sqrt := by
    have sub : A ⊆ Icc 1 v.sqrt := by
      intro p hp
      obtain ⟨hp,hq⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).pos,hq⟩
    simpa using Finset.card_le_card sub
  have bsub : B ⊆ k.primesLE := by
    intro p hp
    have hq := (Finset.mem_filter.mp hp).1
    exact Nat.mem_primesLE.mpr ⟨fac p hq,Nat.prime_of_mem_primeFactors hq⟩
  have ha : ∏ p ∈ A, w p ≤ v^v.sqrt := calc
    _ ≤ ∏ _p ∈ A, v := Finset.prod_le_prod' fun _ _ => Nat.pow_factorization_choose_le hv
    _ ≤ _ := by simpa using Nat.pow_le_pow_right hv ac
  have hb : ∏ p ∈ B, w p ≤ 4^k := calc
    _ ≤ ∏ p ∈ B, p := by
      apply Finset.prod_le_prod'
      intro p hp
      obtain ⟨ht,hs⟩ := Finset.mem_filter.mp hp
      have e := Nat.factorization_choose_le_one (k := k) (Nat.sqrt_lt'.mp (lt_of_not_ge hs))
      exact (Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors ht).pos e).trans_eq (pow_one p)
    _ ≤ ∏ p ∈ k.primesLE, p :=
      Finset.prod_le_prod_of_subset_of_one_le' bsub (fun _ hp _ => (Nat.prime_of_mem_primesLE hp).pos)
    _ ≤ _ := (primorial_eq_prod_primesLE k) ▸ primorial_le_four_pow k
  rw [←split]
  exact Nat.mul_le_mul ha hb

private theorem repeated_bound {u v : ℕ} (rep : Erdos382.LargestPrimeRepeated u v) :
    let p := Nat.maxPrimeFac (∏ m ∈ Icc u v, m)
    p ≤ v-u ∨ p^2 ≤ v := by
  classical
  obtain ⟨hu,huv,hv,hrep⟩ := rep
  let S := Icc u v
  let P := ∏ m ∈ S, m
  let p := Nat.maxPrimeFac P
  change p ≤ v-u ∨ p^2 ≤ v
  by_cases le : p ≤ v-u
  · exact Or.inl le
  right
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun m hm => by
    have := (Finset.mem_Icc.mp hm).1
    omega
  have vP : v ∣ P := Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨huv,le_rfl⟩)
  have h1 : 1 < P := (show 1 < v by omega).trans_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) vP)
  have hp : p.Prime := Nat.prime_maxPrimeFac_of_one_lt _ h1
  obtain ⟨m,hm,hpm⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp (Nat.maxPrimeFac_dvd (n:=P))
  have notdv : ¬ p ∣ ∏ x ∈ S.erase m, x := by
    intro hd
    obtain ⟨x,hx,hpx⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hd
    obtain ⟨neq,hx'⟩ := Finset.mem_erase.mp hx
    obtain ⟨xu,xv⟩ := Finset.mem_Icc.mp hx'
    obtain ⟨mu,mv⟩ := Finset.mem_Icc.mp hm
    rcases lt_or_gt_of_ne neq with lt|gt
    · have := Nat.le_of_dvd (show 0 < m-x by omega) (Nat.dvd_sub hpm hpx)
      omega
    · have := Nat.le_of_dvd (show 0 < x-m by omega) (Nat.dvd_sub hpx hpm)
      omega
  have hc := ((Nat.Prime.coprime_iff_not_dvd hp).mpr notdv).pow_left 2
  change p^2 ∣ ∏ m ∈ S, m at hrep
  rw [← Finset.mul_prod_erase _ _ hm] at hrep
  exact (Nat.le_of_dvd (show 0 < m by have := (Finset.mem_Icc.mp hm).1; omega)
    (hc.dvd_of_dvd_mul_right hrep)).trans (Finset.mem_Icc.mp hm).2

private theorem prime_in_product {u v k q : ℕ} (hq : q.Prime) (hk : k=v-u)
    (hd : q ∣ v.choose k) : q ∣ ∏ m ∈ Icc u v, m := by
  have hh : q ∣ v.descFactorial k := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    exact dvd_mul_of_dvd_right hd _
  rw [Nat.descFactorial_eq_prod_range] at hh
  obtain ⟨i,hi,hd'⟩ := (Prime.dvd_finsetProd_iff hq.prime _).1 hh
  have hi' := Finset.mem_range.mp hi
  exact hd'.trans (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨by omega,Nat.sub_le _ _⟩))

private theorem large_interval (short : ∀ᶠ N : ℝ in atTop,
      ∃ q : ℕ, q.Prime ∧ N/8 < q ∧ (q:ℝ) ≤ N/6) :
     type_of% @Erdos382.erdos_382.variants.ramachandra := by
  intro ε hε
  let δ := (log 5-log 4)/3
  have δpos : 0 < δ := by
    have := Real.log_lt_log (by norm_num : (0:ℝ)<4) (by norm_num : (4:ℝ)<5)
    dsimp [δ]; linarith
  have tend := tendsto_natCast_atTop_atTop (R := ℝ)
  have scale : Tendsto (fun v : ℕ => 6*(v:ℝ)) atTop atTop :=
    tend.const_mul_atTop (by norm_num)
  have small := ((isLittleO_log_rpow_atTop hε).comp_tendsto tend).bound δpos
  filter_upwards [scale.eventually short,small,eventually_ge_atTop (16:ℕ)] with v near little hv16
  intro u h
  let k := v-u
  let S := Icc u v
  let p := Nat.maxPrimeFac (∏ m ∈ S, m)
  have hu := h.1
  have huv := h.2.1
  have hu2 := Erdos382.lt_two_mul_of_largestPrimeRepeated h
  have hv : 0 < v := by omega
  have hvR : (0:ℝ) < v := by exact_mod_cast hv
  have hv1 : (1:ℝ) ≤ v := by exact_mod_cast hv
  have hs : 1 ≤ √(v:ℝ) := (Real.one_le_sqrt).mpr hv1
  have he : 1 ≤ (v:ℝ)^ε := Real.one_le_rpow hv1 hε.le
  by_contra! bad
  change (v:ℝ)^((1:ℝ)/2+ε) < (k:ℝ) at bad
  rw [Real.rpow_add hvR,← Real.sqrt_eq_rpow] at bad
  have hsk : √(v:ℝ) < k := lt_of_le_of_lt
    (le_mul_of_one_le_right (Real.sqrt_nonneg _) he) bad
  have hsq : v < k^2 := by
    exact_mod_cast (show (v:ℝ)<(k:ℝ)^2 by nlinarith [Real.sq_sqrt hvR.le])
  have H := repeated_bound h
  change p ≤ k ∨ p^2 ≤ v at H
  have pk : p ≤ k := H.elim id (fun hh => by
    by_contra! e
    have := Nat.pow_le_pow_left (Nat.le_of_lt e) 2
    omega)
  have hp0 : (∏ m ∈ S, m) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun m hm => by
    have := (Finset.mem_Icc.mp hm).1; omega
  have hk4 : 4*k ≤ v := by
    by_contra! fail
    obtain ⟨q,hq,lo,hi⟩ := near
    have lo' : 3*v < 4*q := by exact_mod_cast (show 3*(v:ℝ)<4*q by linarith)
    have hi' : q ≤ v := by exact_mod_cast (show (q:ℝ)≤v by linarith)
    have mem : q ∈ S := Finset.mem_Icc.mpr ⟨by dsimp [k] at fail; omega,hi'⟩
    have qp := Nat.le_maxPrimeFac hp0 hq (Finset.dvd_prod_of_mem _ mem)
    change q ≤ p at qp
    dsimp [k] at pk
    omega
  have hkv : k ≤ v := Nat.sub_le _ _
  have factors (q : ℕ) (hq : q ∈ (v.choose k).primeFactors) : q ≤ k :=
    (Nat.le_maxPrimeFac hp0 (Nat.prime_of_mem_primeFactors hq)
      (prime_in_product (Nat.prime_of_mem_primeFactors hq) rfl (Nat.dvd_of_mem_primeFactors hq))).trans pk
  have cc := (choose_lower k).trans (Nat.mul_le_mul_left 2 ((Nat.choose_le_choose k hk4).trans
    (choose_upper hv hkv factors)))
  have cr : (5:ℝ)^k ≤ 2*((v:ℝ)^v.sqrt*4^k) := by exact_mod_cast cc
  have l := Real.log_le_log (by positivity) cr
  rw [Real.log_pow,Real.log_mul (by norm_num) (by positivity),
    Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow] at l
  have logn := Real.log_nonneg hv1
  have lelog : Real.log 2 ≤ Real.log v := Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ v by omega))
  change ‖log (v:ℝ)‖ ≤ δ*‖(v:ℝ)^ε‖ at little
  rw [Real.norm_eq_abs,abs_of_nonneg logn,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hvR.le _)] at little
  have a := mul_le_mul_of_nonneg_left little (Real.sqrt_nonneg (v:ℝ))
  have b := mul_lt_mul_of_pos_left bad δpos
  have c := mul_le_mul_of_nonneg_right (Real.nat_sqrt_le_real_sqrt (a:=v)) logn
  have d := le_mul_of_one_le_left logn hs
  have dk : 3*(δ*(k:ℝ)) = (log 5-log 4)*(k:ℝ) := by dsimp [δ]; ring
  nlinarith

end PrimeGaps

theorem OMA.solution : type_of% @Erdos382.erdos_382.variants.ramachandra := PrimeGaps.large_interval PrimeGaps.prime_interval