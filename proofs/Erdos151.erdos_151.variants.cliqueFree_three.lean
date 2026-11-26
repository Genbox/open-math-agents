import FormalConjectures.ErdosProblems.«151»

open SimpleGraph

theorem OMA.solution : type_of% @Erdos151.erdos_151.variants.cliqueFree_three := by
  intro n G hG
  let sizes : Set ℕ :=
    {k | ∀ F : SimpleGraph (Fin n), F.CliqueFree 3 → ∃ s, F.IsNIndepSet k s}
  have hnonempty : sizes.Nonempty := by
    refine ⟨0, ?_⟩
    change ∀ F : SimpleGraph (Fin n), F.CliqueFree 3 → ∃ s, F.IsNIndepSet 0 s
    intro F _
    exact ⟨∅, by simp [SimpleGraph.isNIndepSet_iff]⟩
  have hfinite : sizes.Finite := by
    refine (Set.finite_Iic n).subset ?_
    intro k hk
    change (∀ F : SimpleGraph (Fin n), F.CliqueFree 3 → ∃ s, F.IsNIndepSet k s) at hk
    obtain ⟨s, hs⟩ := hk G hG
    simpa [hs.card_eq] using Finset.card_le_univ s
  have hmem : Erdos151.H n ∈ sizes := hnonempty.csSup_mem hfinite
  change (∀ F : SimpleGraph (Fin n), F.CliqueFree 3 →
    ∃ s, F.IsNIndepSet (Erdos151.H n) s) at hmem
  obtain ⟨s, hs⟩ := hmem G hG
  have htransversal : G.IsCliqueTransversal sᶜ := by
    intro t ht
    obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp ht.2
    by_cases hsa : a ∈ s
    · by_cases hsb : b ∈ s
      · exact (hs.isIndepSet hsa hsb hab (ht.1.1 ha hb hab)).elim
      · exact ⟨b, hb, Finset.mem_compl.mpr hsb⟩
    · exact ⟨a, ha, Finset.mem_compl.mpr hsa⟩
  apply csInf_le'
  exact ⟨sᶜ, htransversal, by rw [Finset.card_compl, Fintype.card_fin, hs.card_eq]⟩