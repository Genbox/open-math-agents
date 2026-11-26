import FormalConjectures.ErdosProblems.«367»

/-! The full part divides its argument, so at most two terms give a quadratic bound. -/

open Erdos367 Asymptotics Filter

theorem OMA.solution : type_of% @Erdos367.erdos_367.variants.k_le_two := by
  intro k hk
  have full_part_le (m : ℕ) (hm : 0 < m) : B 2 m ≤ m := by
    apply Nat.le_of_dvd hm
    have h : B 2 m ∣ m.factorization.prod (· ^ ·) :=
      Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
    simpa only [Nat.prod_factorization_pow_eq_self hm.ne'] using h
  apply isBigO_iff.mpr
  refine ⟨4, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hprod : (∏ m ∈ Finset.Ico n (n + k), B 2 m) ≤ (n + 1) ^ 2 := by
    calc
      (∏ m ∈ Finset.Ico n (n + k), B 2 m) ≤
          (n + 1) ^ (Finset.Ico n (n + k)).card := by
        apply Finset.prod_le_pow_card
        intro m hm
        obtain ⟨hm_lo, hm_hi⟩ := Finset.mem_Ico.mp hm
        exact (full_part_le m (by omega)).trans (by omega)
      _ = (n + 1) ^ k := by simp
      _ ≤ (n + 1) ^ 2 := Nat.pow_le_pow_right (by omega) hk
  simp only [Real.rpow_two, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _),
    abs_of_nonneg (sq_nonneg (n : ℝ))]
  have hcast : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  calc
    ((∏ m ∈ Finset.Ico n (n + k), B 2 m : ℕ) : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
      exact_mod_cast hprod
    _ ≤ (2 * (n : ℝ)) ^ 2 := by gcongr; linarith
    _ = 4 * (n : ℝ) ^ 2 := by ring