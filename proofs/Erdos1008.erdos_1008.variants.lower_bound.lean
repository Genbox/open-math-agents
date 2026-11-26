import FormalConjectures.ErdosProblems.«1008»

/-! A maximal forest meets every nonisolated vertex of the original graph. -/

open SimpleGraph

theorem OMA.solution : type_of% @Erdos1008.erdos_1008.variants.lower_bound := by
  classical
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro V _ G
  obtain ⟨F, _, hF⟩ := G.exists_maximal_isAcyclic_of_le_isAcyclic bot_le isAcyclic_bot
  refine ⟨F, hF.prop.1, isAcyclic_iff_free_cycleGraph.mp hF.prop.2 4 (by decide), ?_⟩
  have hsupport : G.support ⊆ F.support := by
    intro v hv
    obtain ⟨w, hw⟩ := G.mem_support.mp hv
    have hreachable : F.Reachable v w := by
      rw [G.reachable_eq_of_maximal_isAcyclic F hF]
      exact hw.reachable
    exact (F.degree_pos_iff_mem_support v).mp (hreachable.degree_pos_left hw.ne)
  have hvertices : Fintype.card F.support ≤ 2 * F.edgeFinset.card := by
    rw [← F.sum_degrees_support_eq_twice_card_edges, ← Set.toFinset_card F.support]
    calc
      F.support.toFinset.card = ∑ v ∈ F.support.toFinset, (1 : ℕ) := by simp
      _ ≤ ∑ v ∈ F.support.toFinset, F.degree v :=
        Finset.sum_le_sum fun v hv => (F.degree_pos_iff_mem_support v).mpr
          (Set.mem_toFinset.mp hv)
  have hedges : G.edgeFinset.card ≤ (2 * F.edgeFinset.card) ^ 2 := by
    calc
      _ = (G.induce F.support).edgeFinset.card :=
        (G.card_edgeFinset_induce_of_support_subset hsupport).symm
      _ ≤ (Fintype.card F.support).choose 2 :=
        (G.induce F.support).card_edgeFinset_le_card_choose_two
      _ ≤ (Fintype.card F.support) ^ 2 := Nat.choose_le_pow _ _
      _ ≤ _ := Nat.pow_le_pow_left hvertices _
  have hedges_real : (G.edgeSet.ncard : ℝ) ≤ (2 * (F.edgeSet.ncard : ℝ)) ^ 2 := by
    rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
    exact_mod_cast hedges
  have hsqrt : Real.sqrt (G.edgeSet.ncard : ℝ) ≤ 2 * (F.edgeSet.ncard : ℝ) :=
    (Real.sqrt_le_left (by positivity)).mpr hedges_real
  rw [← Real.sqrt_eq_rpow]
  linarith