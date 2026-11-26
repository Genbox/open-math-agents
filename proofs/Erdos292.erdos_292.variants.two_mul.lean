import FormalConjectures.ErdosProblems.«292»

-- Problem: Erdős Problem 292 — two mul
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/292.lean:83 (declaration Erdos292.erdos_292.variants.two_mul)
-- Credit: @GuillaumeBAUD-coder (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Double the denominators and insert the new term 1/2. -/

theorem OMA.solution : type_of% @Erdos292.erdos_292.variants.two_mul := by
  intro n hn hn_gt
  obtain ⟨S, hS, hn_mem, hsum⟩ := hn
  have one_not_mem : 1 ∉ S := by
    intro h1
    have hpair : ({1, n} : Finset ℕ) ⊆ S := by
      simp [Finset.insert_subset_iff, h1, hn_mem]
    have hle := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun m : ℕ => (1 : ℚ) / m) hpair (by intros; positivity)
    have hne : 1 ∉ ({n} : Finset ℕ) := by simp [show 1 ≠ n by omega]
    rw [Finset.sum_insert hne, Finset.sum_singleton, hsum] at hle
    have hpos : (0 : ℚ) < 1 / (n : ℚ) := by positivity
    norm_num only [Nat.cast_one, div_one] at hle
    linarith

  let twice : ℕ ↪ ℕ := ⟨fun m => 2 * m, by
    intro a b h
    change 2 * a = 2 * b at h
    omega⟩
  let T := S.map twice
  have two_not_mem : 2 ∉ T := by
    intro h2
    obtain ⟨m, hm, he⟩ := Finset.mem_map.mp h2
    change 2 * m = 2 at he
    exact one_not_mem ((show m = 1 by omega) ▸ hm)

  refine ⟨insert 2 T, ?_, ?_, ?_⟩
  · intro m hm
    rcases Finset.mem_insert.mp hm with rfl | hm
    · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hm
      obtain ⟨hk_pos, hk_le⟩ := Finset.mem_Icc.mp (hS hk)
      change 2 * k ∈ Finset.Icc 1 (2 * n)
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · exact Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨n, hn_mem, rfl⟩)
  · change (∑ m ∈ insert 2 (S.map twice), (1 : ℚ) / m) = 1
    rw [Finset.sum_insert two_not_mem, Finset.sum_map]
    have halve (m : ℕ) : (1 : ℚ) / (twice m : ℚ) = (1 / 2) * (1 / (m : ℚ)) := by
      change (1 : ℚ) / ((2 * m : ℕ) : ℚ) = _
      push_cast
      exact (one_div_mul_one_div (2 : ℚ) (m : ℚ)).symm
    simp_rw [halve]
    rw [← Finset.mul_sum, hsum]
    norm_num
