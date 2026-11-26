import FormalConjectures.ErdosProblems.«292»

-- Problem: Erdős Problem 292 — mul
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/292.lean:73 (declaration Erdos292.erdos_292.variants.mul)
-- Credit: @GuillaumeBAUD-coder (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Prove closure under multiplication by replacing the last unit fraction with a scaled sum. -/

theorem OMA.solution : type_of% @Erdos292.erdos_292.variants.mul := by
  intro m hm n hn
  obtain ⟨S, hS, hm_mem, hsumS⟩ := hm
  obtain ⟨T, hT, hn_mem, hsumT⟩ := hn
  have hm_pos : 0 < m := by
    have := (Finset.mem_Icc.mp (hS hm_mem)).1
    omega
  have hn_pos : 0 < n := by
    have := (Finset.mem_Icc.mp (hT hn_mem)).1
    omega

  let scale : ℕ ↪ ℕ := ⟨fun k => m * k, fun _ _ h => Nat.eq_of_mul_eq_mul_left hm_pos h⟩
  have hdisj : Disjoint (S.erase m) (T.map scale) := by
    apply Finset.disjoint_left.mpr
    intro d hd hs
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hd
    have hlt := lt_of_le_of_ne (Finset.mem_Icc.mp (hS hmem)).2 hne
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hs
    have hk_one := (Finset.mem_Icc.mp (hT hk)).1
    change m * k < m at hlt
    have hle : m ≤ m * k := by simpa using Nat.mul_le_mul_left m hk_one
    omega

  refine ⟨S.erase m ∪ T.map scale, ?_, ?_, ?_⟩
  · intro d hd
    rcases Finset.mem_union.mp hd with hd | hd
    · obtain ⟨hd_one, hd_le⟩ := Finset.mem_Icc.mp (hS (Finset.mem_erase.mp hd).2)
      have hle : m ≤ m * n := by
        simpa using Nat.mul_le_mul_left m (show 1 ≤ n by omega)
      exact Finset.mem_Icc.mpr ⟨hd_one, hd_le.trans hle⟩
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hd
      obtain ⟨hk_one, hk_le⟩ := Finset.mem_Icc.mp (hT hk)
      change m * k ∈ Finset.Icc 1 (m * n)
      exact Finset.mem_Icc.mpr ⟨Nat.mul_pos hm_pos (by omega), Nat.mul_le_mul_left m hk_le⟩
  · exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨n, hn_mem, rfl⟩)
  · rw [Finset.sum_union hdisj, Finset.sum_map]
    have reciprocal (k : ℕ) : (1 : ℚ) / (scale k : ℚ) = (1 / (m : ℚ)) * (1 / (k : ℚ)) := by
      change (1 : ℚ) / ((m * k : ℕ) : ℚ) = _
      rw [Nat.cast_mul, ← one_div_mul_one_div]
    simp_rw [reciprocal]
    rw [← Finset.mul_sum, hsumT, mul_one, Finset.sum_erase_add S _ hm_mem, hsumS]
