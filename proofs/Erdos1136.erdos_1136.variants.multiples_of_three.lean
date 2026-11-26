import FormalConjectures.ErdosProblems.«1136»

/-! Multiples of three avoid sums that are powers of two and have density one third. -/

open Filter Topology

theorem OMA.solution : type_of% @Erdos1136.erdos_1136.variants.multiples_of_three := by
  constructor
  · intro a ha b hb k hsum
    have hdiv : 3 ∣ a + b := dvd_add ha hb
    rw [hsum] at hdiv
    exact (show ¬ (3 : ℕ) ∣ 2 by decide)
      ((show Nat.Prime 3 by decide).dvd_of_dvd_pow hdiv)
  · have hcount (n : ℕ) :
        ({m : ℕ | 3 ∣ m} ∩ Set.Iio n).ncard = (n + 2) / 3 := by
      have hset :
          {m : ℕ | 3 ∣ m} ∩ Set.Iio n =
            (fun k : ℕ => 3 * k) '' Set.Iio ((n + 2) / 3) := by
        ext m
        constructor
        · rintro ⟨⟨k, rfl⟩, hk⟩
          exact ⟨k, show k < (n + 2) / 3 by
            have h : 3 * k < n := hk
            omega, rfl⟩
        · rintro ⟨k, hk, rfl⟩
          exact ⟨⟨k, rfl⟩, show 3 * k < n by
            have h : k < (n + 2) / 3 := hk
            omega⟩
      rw [hset, Set.ncard_image_of_injective _]
      · simp
      · intro a b hab
        change 3 * a = 3 * b at hab
        omega
    simp only [Set.HasDensity, Set.partialDensity, Set.inter_univ, Set.univ_inter,
      hcount, Set.ncard_Iio_nat]
    have hupper : Tendsto (fun n : ℕ => (1 / 3 : ℝ) + 1 / n) atTop (𝓝 (1 / 3)) := by
      simpa only [add_zero] using
        (tendsto_const_nhds.add
          (tendsto_one_div_atTop_nhds_zero_nat :
            Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0)))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      apply (le_div_iff₀ hn').mpr
      have h : n ≤ ((n + 2) / 3) * 3 := by omega
      have h' : (n : ℝ) ≤ (((n + 2) / 3 : ℕ) : ℝ) * 3 := by exact_mod_cast h
      linarith
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      apply (div_le_iff₀ hn').mpr
      rw [add_mul, div_mul_cancel₀ (1 : ℝ) hn'.ne']
      have h : ((n + 2) / 3) * 3 ≤ n + 2 := by omega
      have h' : (((n + 2) / 3 : ℕ) : ℝ) * 3 ≤ (n : ℝ) + 2 := by exact_mod_cast h
      linarith