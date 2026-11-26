import FormalConjectures.ErdosProblems.«669»

/-! Two-element subsets determine lines, and points on a parabola give distinct lines. -/

open Erdos669
open scoped EuclideanGeometry

namespace OMA

noncomputable def pairSpan (U : Finset ℝ²) : AffineSubspace ℝ ℝ² :=
  affineSpan ℝ (U : Set ℝ²)

lemma countedLines_subset_pairSpans (S : Finset ℝ²) (k : ℕ) :
    linesWithAtLeastPointsFor k (S : Set ℝ²) ⊆
      pairSpan '' (S.powersetCard 2 : Set (Finset ℝ²)) := by
  classical
  rintro L ⟨⟨p, hp, q, hq, hpq, rfl⟩, _⟩
  refine ⟨{p, q}, ?_, by simp [pairSpan]⟩
  apply Finset.mem_powersetCard.mpr
  refine ⟨?_, Finset.card_pair_eq_two_iff.mpr hpq⟩
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact hp
  · exact hq

lemma twoLineUpperBound (n : ℕ) : maxLinesAtLeast 2 n ≤ n.choose 2 := by
  classical
  apply csSup_le'
  rintro _ ⟨S, rfl, rfl⟩
  let pairs := S.powersetCard 2
  calc
    (linesWithAtLeastPointsFor 2 (S : Set ℝ²)).ncard ≤
        (pairSpan '' (pairs : Set (Finset ℝ²))).ncard :=
      Set.ncard_le_ncard (countedLines_subset_pairSpans S 2) (pairs.finite_toSet.image _)
    _ ≤ (pairs : Set (Finset ℝ²)).ncard := Set.ncard_image_le pairs.finite_toSet
    _ = S.card.choose 2 := by rw [Set.ncard_coe_finset, Finset.card_powersetCard]

def parabolaPoint (x : ℝ) : ℝ² := WithLp.toLp 2 ![x, x ^ 2]

lemma parabolaPoint_injective : Function.Injective parabolaPoint := by
  intro x y h
  have h₀ := congrArg (fun p : ℝ² => p 0) h
  simpa [parabolaPoint] using h₀

lemma parabolaPoint_on_line {x y z : ℝ}
    (h : parabolaPoint z ∈ affineSpan ℝ ({parabolaPoint x, parabolaPoint y} : Set ℝ²)) :
    z = x ∨ z = y := by
  obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp h
  have h₀ := congrArg (fun p : ℝ² => p 0) ht
  have h₁ := congrArg (fun p : ℝ² => p 1) ht
  simp [AffineMap.lineMap_apply_module, parabolaPoint, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul] at h₀ h₁
  have hz : (z - x) * (z - y) = 0 := by
    calc
      (z - x) * (z - y) = z ^ 2 - (x + y) * z + x * y := by ring
      _ = 0 := by rw [← h₁, ← h₀]; ring
  exact (mul_eq_zero.mp hz).imp sub_eq_zero.mp sub_eq_zero.mp

lemma parabolaLine_inter {S : Set ℝ²} (hS : S ⊆ Set.range parabolaPoint)
    {p q : ℝ²} (hp : p ∈ S) (hq : q ∈ S) :
    (↑(affineSpan ℝ ({p, q} : Set ℝ²)) : Set ℝ²) ∩ S = {p, q} := by
  obtain ⟨x, rfl⟩ := hS hp
  obtain ⟨y, rfl⟩ := hS hq
  ext z
  constructor
  · rintro ⟨hz, hzS⟩
    obtain ⟨t, rfl⟩ := hS hzS
    rcases parabolaPoint_on_line hz with rfl | rfl <;> simp
  · intro hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨left_mem_affineSpan_pair _ _ _, hp⟩
    · exact ⟨right_mem_affineSpan_pair _ _ _, hq⟩

lemma exactTwoLineCount_on_parabola (S : Finset ℝ²)
    (hS : (S : Set ℝ²) ⊆ Set.range parabolaPoint) :
    (EuclideanGeometry.linesWithPointsFor 2 (S : Set ℝ²)).ncard = S.card.choose 2 := by
  classical
  let pairs := S.powersetCard 2
  have pairInter {U : Finset ℝ²} (hU : U ∈ pairs) :
      (pairSpan U : Set ℝ²) ∩ (S : Set ℝ²) = (U : Set ℝ²) := by
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hU
    obtain ⟨p, q, _, rfl⟩ := Finset.card_eq_two.mp hcard
    simpa [pairSpan] using parabolaLine_inter hS (hsub (by simp)) (hsub (by simp))
  have inj : Set.InjOn pairSpan (pairs : Set (Finset ℝ²)) := by
    intro U hU V hV h
    apply Finset.coe_injective
    rw [← pairInter hU, ← pairInter hV, h]
  have fromPair : pairSpan '' (pairs : Set (Finset ℝ²)) ⊆
      EuclideanGeometry.linesWithPointsFor 2 (S : Set ℝ²) := by
    rintro L ⟨U, hU, rfl⟩
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hU
    refine ⟨?_, by rw [pairInter hU, Set.ncard_coe_finset, hcard]⟩
    obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hcard
    exact ⟨p, hsub (by simp), q, hsub (by simp), hpq, by simp [pairSpan]⟩
  have toPair : EuclideanGeometry.linesWithPointsFor 2 (S : Set ℝ²) ⊆
      pairSpan '' (pairs : Set (Finset ℝ²)) :=
    (linesWithPointsFor_subset_linesWithAtLeastPointsFor 2 _).trans
      (countedLines_subset_pairSpans S 2)
  rw [Set.Subset.antisymm toPair fromPair, inj.ncard_image, Set.ncard_coe_finset,
    Finset.card_powersetCard]

end OMA

theorem OMA.solution : type_of% @Erdos669.erdos_669.variants.k_two := by
  classical
  intro n
  let embedding : ℕ ↪ ℝ² :=
    ⟨fun j => OMA.parabolaPoint (j : ℝ), by
      intro x y h
      exact_mod_cast OMA.parabolaPoint_injective h⟩
  let S := (Finset.range n).map embedding
  have hSn : S.card = n := by simp [S]
  have hS : (S : Set ℝ²) ⊆ Set.range OMA.parabolaPoint := by
    intro p hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hp
    exact ⟨(j : ℝ), rfl⟩
  have lower : n.choose 2 ≤ maxLinesExactly 2 n := by
    apply le_csSup (lineCountsExactly_bddAbove 2 n)
    exact ⟨S, hSn, hSn ▸ OMA.exactTwoLineCount_on_parabola S hS⟩
  have middle := erdos_669.variants.exactly_le_atLeast 2 n
  have upper := OMA.twoLineUpperBound n
  exact ⟨le_antisymm (middle.trans upper) lower, le_antisymm upper (lower.trans middle)⟩