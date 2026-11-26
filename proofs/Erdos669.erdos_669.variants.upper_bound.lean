import FormalConjectures.ErdosProblems.«669»

/-! Each counted line contributes disjoint two-element subsets of the point set. -/

open Erdos669
open scoped EuclideanGeometry

lemma OMA.line_pair_count (k : ℕ) (S : Finset ℝ²) (hk : 2 ≤ k) :
    (linesWithAtLeastPointsFor k (S : Set ℝ²)).ncard * k.choose 2 ≤ S.card.choose 2 := by
  classical
  let lines := linesWithAtLeastPointsFor k (S : Set ℝ²)
  have hfin : lines.Finite := by
    refine ((S.finite_toSet.prod S.finite_toSet).image
      (fun pq : ℝ² × ℝ² => affineSpan ℝ {pq.1, pq.2})).subset ?_
    rintro L ⟨⟨p, hp, q, hq, _, rfl⟩, _⟩
    exact ⟨(p, q), Set.mk_mem_prod hp hq, rfl⟩
  let Ls := hfin.toFinset
  let pts (L : AffineSubspace ℝ ℝ²) := S.filter fun p => p ∈ L
  let pairs (L : AffineSubspace ℝ ℝ²) := (pts L).powersetCard 2
  have in_lines (L : AffineSubspace ℝ ℝ²) (hL : L ∈ Ls) : L ∈ lines :=
    hfin.mem_toFinset.mp hL
  have point_count (L : AffineSubspace ℝ ℝ²) (hL : L ∈ Ls) : k ≤ (pts L).card := by
    have heq : ((pts L : Finset ℝ²) : Set ℝ²) = (L : Set ℝ²) ∩ (S : Set ℝ²) := by
      ext p
      simp [pts, and_comm]
    rw [← Set.ncard_coe_finset, heq]
    exact (in_lines L hL).2
  have lies_on (L : AffineSubspace ℝ ℝ²) {U : Finset ℝ²} (hU : U ∈ pairs L)
      {p : ℝ²} (hp : p ∈ U) : p ∈ L :=
    (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp hU).1 hp)).2
  have hdisj : (Ls : Set (AffineSubspace ℝ ℝ²)).PairwiseDisjoint pairs := by
    intro L hL M hM hne
    refine Finset.disjoint_left.mpr ?_
    intro U hUL hUM
    have hcard : U.card = 2 := (Finset.mem_powersetCard.mp hUL).2
    obtain ⟨p, q, hp, hq, hpq⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < U.card)
    obtain ⟨a, _, b, _, _, ha⟩ := (in_lines L hL).1
    obtain ⟨c, _, d, _, _, hc⟩ := (in_lines M hM).1
    have hl : affineSpan ℝ {p, q} = L := by
      rw [← ha]
      exact affineSpan_pair_eq_of_mem_of_mem_of_ne (ha ▸ lies_on L hUL hp)
        (ha ▸ lies_on L hUL hq) hpq
    have hm : affineSpan ℝ {p, q} = M := by
      rw [← hc]
      exact affineSpan_pair_eq_of_mem_of_mem_of_ne (hc ▸ lies_on M hUM hp)
        (hc ▸ lies_on M hUM hq) hpq
    exact hne (hl.symm.trans hm)
  have hsub : Ls.biUnion pairs ⊆ S.powersetCard 2 := by
    intro U hU
    obtain ⟨L, _, hUL⟩ := Finset.mem_biUnion.mp hU
    obtain ⟨hUsub, hcard⟩ := Finset.mem_powersetCard.mp hUL
    exact Finset.mem_powersetCard.mpr ⟨hUsub.trans (Finset.filter_subset _ _), hcard⟩
  change lines.ncard * k.choose 2 ≤ S.card.choose 2
  rw [Set.ncard_eq_toFinset_card lines hfin]
  calc
    Ls.card * k.choose 2 = ∑ _ ∈ Ls, k.choose 2 := by simp
    _ ≤ ∑ L ∈ Ls, (pairs L).card := by
      refine Finset.sum_le_sum fun L hL => ?_
      rw [show (pairs L).card = (pts L).card.choose 2 from Finset.card_powersetCard _ _]
      exact Nat.choose_le_choose 2 (point_count L hL)
    _ = (Ls.biUnion pairs).card := (Finset.card_biUnion hdisj).symm
    _ ≤ S.card.choose 2 := (Finset.card_le_card hsub).trans_eq (Finset.card_powersetCard _ _)

lemma OMA.line_count_bound (k n : ℕ) (hk : 2 ≤ k) :
    (maxLinesAtLeast k n : ℝ) ≤ (n.choose 2 : ℝ) / (k.choose 2 : ℝ) := by
  have hkpos : 0 < k.choose 2 := Nat.choose_pos hk
  have hbound : maxLinesAtLeast k n ≤ n.choose 2 / k.choose 2 := by
    apply csSup_le'
    rintro _ ⟨S, rfl, rfl⟩
    exact (Nat.le_div_iff_mul_le hkpos).mpr (OMA.line_pair_count k S hk)
  apply (le_div_iff₀ (by exact_mod_cast hkpos : 0 < (k.choose 2 : ℝ))).mpr
  exact_mod_cast (Nat.le_div_iff_mul_le hkpos).mp hbound

theorem OMA.solution : type_of% @Erdos669.erdos_669.variants.upper_bound :=
  OMA.line_count_bound