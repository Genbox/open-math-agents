import FormalConjectures.OEIS.«206911»

/-! Consecutive positions of the harmonic partial sums differ by two or three. -/

open OeisA206911

theorem OMA.solution : type_of% @OeisA206911.conjecture_1 := by
  intro n hn
  by_cases hsmall : n < 5
  · interval_cases n <;> norm_num [diff, a_1, a_2, a_3, a_4, a_5]
  have hn₅ : 5 ≤ n := Nat.le_of_not_gt hsmall
  let E (k : ℕ) : ℝ := Real.exp (harmonic k : ℝ)
  have step (k : ℕ) :
      E (k + 1) = E k * Real.exp (((k : ℝ) + 1)⁻¹) := by
    simp only [E, harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast, Rat.cast_one,
      Nat.cast_add, Nat.cast_one, Real.exp_add]
  have exp_upper (k : ℕ) (hk : 0 < k) :
      Real.exp (((k : ℝ) + 1)⁻¹) ≤ 1 + (k : ℝ)⁻¹ := by
    have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
    have hc : ((k : ℝ) + 1)⁻¹ < 1 := by
      apply inv_lt_one_of_one_lt₀
      linarith
    calc
      Real.exp (((k : ℝ) + 1)⁻¹) ≤ 1 / (1 - ((k : ℝ) + 1)⁻¹) :=
        Real.exp_bound_div_one_sub_of_interval (by positivity) hc
      _ = 1 + (k : ℝ)⁻¹ := by field_simp <;> simp [ne_of_gt hk']
  have hE_upper (k : ℕ) (hk : 5 ≤ k) : E k ≤ 2 * (k : ℝ) := by
    induction k, hk using Nat.le_induction with
    | base =>
      have hsum : (harmonic 5 : ℝ) = 137 / 60 := by
        norm_num [harmonic, Finset.sum_range_succ]
      change Real.exp (harmonic 5 : ℝ) ≤ 2 * (5 : ℝ)
      rw [hsum]
      have hpow : (Real.exp (137 / 60)) ^ 60 = (Real.exp 1) ^ 137 := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        ring_nf
      have hlt : (Real.exp (137 / 60)) ^ 60 < (10 : ℝ) ^ 60 := by
        rw [hpow]
        calc
          (Real.exp 1) ^ 137 < 2.7182818286 ^ 137 := by
            gcongr
            exact Real.exp_one_lt_d9
          _ < (10 : ℝ) ^ 60 := by norm_num
      have : Real.exp (137 / 60) < (10 : ℝ) :=
        lt_of_pow_lt_pow_left₀ 60 (by norm_num) hlt
      norm_num
      exact this.le
    | succ k hk ih =>
      have hk' : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
      calc
        E (k + 1) = E k * Real.exp (((k : ℝ) + 1)⁻¹) := step k
        _ ≤ (2 * (k : ℝ)) * (1 + (k : ℝ)⁻¹) :=
          mul_le_mul ih (exp_upper k (by omega)) (Real.exp_nonneg _) (by positivity)
        _ = 2 * (↑(k + 1) : ℝ) := by push_cast; field_simp
  have hE_lower (k : ℕ) : (k : ℝ) + 1 ≤ E k := by
    have hlog : Real.log ((k : ℝ) + 1) ≤ harmonic k := by
      simpa only [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic k
    have hp : 0 < (k : ℝ) + 1 := by positivity
    rw [← Real.exp_log hp]
    exact Real.exp_le_exp.mpr hlog
  have hlower : E n + 1 ≤ E (n + 1) := by
    rw [step]
    have hmul : 1 ≤ E n * (Real.exp (((n : ℝ) + 1)⁻¹) - 1) := by
      calc
        1 = ((n : ℝ) + 1) * ((n : ℝ) + 1)⁻¹ := by field_simp
        _ ≤ E n * (Real.exp (((n : ℝ) + 1)⁻¹) - 1) :=
          mul_le_mul (hE_lower n) (by linarith [Real.add_one_le_exp (((n : ℝ) + 1)⁻¹)])
            (by positivity) (Real.exp_nonneg _)
    linarith
  have hupper : E (n + 1) ≤ E n + 2 := by
    rw [step]
    have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
    have hmul : E n * (n : ℝ)⁻¹ ≤ 2 := by
      rw [← div_eq_mul_inv]
      exact (div_le_iff₀ hn').mpr (hE_upper n hn₅)
    calc
      E n * Real.exp (((n : ℝ) + 1)⁻¹) ≤ E n * (1 + (n : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left (exp_upper n hn) (Real.exp_nonneg _)
      _ ≤ E n + 2 := by linarith
  let u : ℝ := E n - 1
  let v : ℝ := E (n + 1) - 1
  have hfloor_lower : ⌊u⌋ + 1 ≤ ⌊v⌋ := by
    apply Int.le_floor.mpr
    push_cast
    have h := Int.floor_le u
    dsimp [u, v] at *
    linarith
  have hfloor_upper : ⌊v⌋ ≤ ⌊u⌋ + 2 := by
    apply Int.floor_le_iff.mpr
    push_cast
    have h := Int.lt_floor_add_one u
    dsimp [u, v] at *
    linarith
  have floor_nonneg (k : ℕ) : 0 ≤ ⌊E k - 1⌋ := by
    apply Int.floor_nonneg.mpr
    linarith [hE_lower k, Nat.cast_nonneg (α := ℝ) k]
  unfold diff a
  push_cast
  change (n : ℤ) + 1 + (↑⌊v⌋.toNat : ℤ) -
    ((n : ℤ) + (↑⌊u⌋.toNat : ℤ)) = 2 ∨
    (n : ℤ) + 1 + (↑⌊v⌋.toNat : ℤ) -
      ((n : ℤ) + (↑⌊u⌋.toNat : ℤ)) = 3
  rw [Int.toNat_of_nonneg (floor_nonneg (n + 1)), Int.toNat_of_nonneg (floor_nonneg n)]
  dsimp only [u, v] at hfloor_lower hfloor_upper
  omega