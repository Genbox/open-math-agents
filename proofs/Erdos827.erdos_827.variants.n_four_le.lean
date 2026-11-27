import FormalConjectures.ErdosProblems.«827»

/-!
Martínez and Roldán-Pensado's counting proof of the four-point circumradius bound.
-/

-- Credit: @Genbox

open Erdos827 EuclideanGeometry
open scoped BigOperators

namespace Erdos827Four

private theorem circle_at_subset {S T : Finset ℝ²} (h : S ⊆ T) {r : ℝ}
    (ht : OnCircleOfRadius T r) : OnCircleOfRadius S r := by
  obtain ⟨c, hc⟩ := ht
  exact ⟨c, fun x hx => hc x (h hx)⟩

private theorem two_distances {a b c d e : ℝ²} {r s : ℝ}
    (hab : a ≠ b) (hcd : c ≠ d)
    (ha : dist c a = r) (hb : dist d a = r) (he : dist e a = r)
    (ha' : dist c b = s) (hb' : dist d b = s) (he' : dist e b = s) :
    e = c ∨ e = d :=
  eq_of_dist_eq_of_dist_eq_of_finrank_eq_two (by simp) hab hcd ha hb he ha' hb' he'

private theorem radius_unique_at_insert {E : Finset ℝ²} (hE : E.card = 2)
    {x : ℝ²} (hx : x ∉ E) {r s : ℝ}
    (h₁ : OnCircleOfRadius (insert x E) r) (h₂ : OnCircleOfRadius (insert x E) s) :
    r = s := by
  classical
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hE
  obtain ⟨c, hc⟩ := h₁
  obtain ⟨d, hd⟩ := h₂
  have hax : a ∈ (insert x {a, b} : Finset ℝ²) := by simp
  have hbx : b ∈ (insert x {a, b} : Finset ℝ²) := by simp
  have hxx : x ∈ (insert x {a, b} : Finset ℝ²) := by simp
  by_cases he : c = d
  · exact (hc x hxx).symm.trans (he ▸ hd x hxx)
  · exact False.elim (hx (by
      rcases two_distances he hab (hc a hax) (hc b hbx) (hc x hxx)
        (hd a hax) (hd b hbx) (hd x hxx) with h | h <;> simp [h]))

private theorem three_insert_impossible {X E : Finset ℝ²}
    (hX : NoFourConcyclic (X : Set ℝ²)) (hEX : E ⊆ X) (hE : E.card = 2)
    {x y z : ℝ²} (hxX : x ∈ X) (hyX : y ∈ X) (hzX : z ∈ X)
    (hx : x ∉ E) (hy : y ∉ E) (hz : z ∉ E)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {r : ℝ}
    (h₁ : OnCircleOfRadius (insert x E) r) (h₂ : OnCircleOfRadius (insert y E) r)
    (h₃ : OnCircleOfRadius (insert z E) r) : False := by
  classical
  have centers_ne {u v c : ℝ²} (huX : u ∈ X) (hvX : v ∈ X)
      (hu : u ∉ E) (hv : v ∉ E) (huv : u ≠ v)
      (huc : ∀ w ∈ insert u E, dist w c = r)
      (hvc : ∀ w ∈ insert v E, dist w c = r) : False := by
    apply hX (↑(insert u (insert v E)) : Set ℝ²)
    · intro w hw
      obtain rfl | hw := Finset.mem_insert.mp (Finset.mem_coe.mp hw)
      · exact huX
      · obtain rfl | hw := Finset.mem_insert.mp hw
        · exact hvX
        · exact hEX hw
    · rw [Set.ncard_coe_finset, Finset.card_insert_of_notMem (by simp [huv, hu]),
        Finset.card_insert_of_notMem hv, hE]
    · refine ⟨c, r, ?_⟩
      intro w hw
      obtain rfl | hw := Finset.mem_insert.mp (Finset.mem_coe.mp hw)
      · exact huc _ (Finset.mem_insert_self ..)
      · exact hvc w hw
  obtain ⟨c, hc⟩ := h₁
  obtain ⟨d, hd⟩ := h₂
  obtain ⟨e, he⟩ := h₃
  have hcd : c ≠ d := fun hh => centers_ne hxX hyX hx hy hxy hc (hh ▸ hd)
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hE
  have ha (w : ℝ²) : a ∈ (insert w {a, b} : Finset ℝ²) := by simp
  have hb (w : ℝ²) : b ∈ (insert w {a, b} : Finset ℝ²) := by simp
  obtain h | h := two_distances hab hcd
    ((dist_comm _ _).trans (hc a (ha x))) ((dist_comm _ _).trans (hd a (ha y)))
    ((dist_comm _ _).trans (he a (ha z))) ((dist_comm _ _).trans (hc b (hb x)))
    ((dist_comm _ _).trans (hd b (hb y))) ((dist_comm _ _).trans (he b (hb z)))
  · exact centers_ne hxX hzX hx hz hxz hc (h ▸ he)
  · exact centers_ne hyX hzX hy hz hyz hd (h ▸ he)

private def SharesRadius (E G : Finset ℝ²) : Prop :=
  E ⊆ G ∧ E.card = 2 ∧ ∃ r, ∀ x ∈ G \ E, OnCircleOfRadius (insert x E) r

private theorem bad_quad_has_edge (G : Finset ℝ²) (hG : G.card = 4)
    (hbad : ¬ HasDistinctCircumradii G) : ∃ E, SharesRadius E G := by
  classical
  unfold HasDistinctCircumradii at hbad
  push Not at hbad
  obtain ⟨T, hT, U, hU, hTc, hUc, hTU, r, hTr, hUr⟩ := hbad
  have hsub : T ∪ U ⊆ G := Finset.union_subset hT hU
  have hcard : (T ∪ U).card = 4 := by
    have hle := Finset.card_le_card hsub
    have hlt : 3 < (T ∪ U).card := by
      by_contra! hc
      exact hTU ((Finset.eq_of_subset_of_card_le Finset.subset_union_left (hTc ▸ hc)).trans
        (Finset.eq_of_subset_of_card_le Finset.subset_union_right (hUc ▸ hc)).symm)
    omega
  have hfull : T ∪ U = G := Finset.eq_of_subset_of_card_le hsub (by omega)
  refine ⟨T ∩ U, (Finset.inter_subset_left.trans hT), ?_, r, ?_⟩
  · have hc := Finset.card_union_add_card_inter T U
    omega
  · intro x hx
    have hx' : x ∈ T ∪ U := hfull ▸ (Finset.mem_sdiff.mp hx).1
    obtain hxT | hxU := Finset.mem_union.mp hx'
    · exact circle_at_subset (Finset.insert_subset hxT Finset.inter_subset_left) hTr
    · exact circle_at_subset (Finset.insert_subset hxU Finset.inter_subset_right) hUr

private theorem rests_disjoint {X E G H : Finset ℝ²}
    (hX : NoFourConcyclic (X : Set ℝ²)) (hGX : G ⊆ X) (hHX : H ⊆ X)
    (hG : G.card = 4) (hH : H.card = 4) (hGH : G ≠ H)
    (hGE : SharesRadius E G) (hHE : SharesRadius E H) :
    Disjoint (G \ E) (H \ E) := by
  classical
  obtain ⟨hEG, hE, r, hr⟩ := hGE
  obtain ⟨hEH, _, s, hs⟩ := hHE
  rw [Finset.disjoint_left]
  intro x hx hx'
  have hEq : r = s := radius_unique_at_insert hE (Finset.mem_sdiff.mp hx).2
    (hr x hx) (hs x hx')
  subst s
  have hgcr : (G \ E).card = 2 := by rw [Finset.card_sdiff_of_subset hEG, hG, hE]
  have hhc : (H \ E).card = 2 := by rw [Finset.card_sdiff_of_subset hEH, hH, hE]
  have exists_other (S : Finset ℝ²) (hc : S.card = 2) (hm : x ∈ S) :
      ∃ a, a ≠ x ∧ a ∈ S ∧ S = {x, a} := by
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hc
    obtain rfl | rfl := by simpa using hm
    · exact ⟨v, huv.symm, by simp, rfl⟩
    · exact ⟨u, huv, by simp, by ext a; simp [or_comm]⟩
  obtain ⟨y, hyx, hy, hyrest⟩ := exists_other (G \ E) hgcr hx
  obtain ⟨z, hzx, hz, hzrest⟩ := exists_other (H \ E) hhc hx'
  have hyz : y ≠ z := by
    intro he
    apply hGH
    calc
      G = (G \ E) ∪ E := (Finset.sdiff_union_of_subset hEG).symm
      _ = (H \ E) ∪ E := by rw [hyrest, hzrest, he]
      _ = H := Finset.sdiff_union_of_subset hEH
  obtain ⟨hxG, hxE⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨hyG, hyE⟩ := Finset.mem_sdiff.mp hy
  obtain ⟨hzH, hzE⟩ := Finset.mem_sdiff.mp hz
  exact three_insert_impossible hX (hEG.trans hGX) hE (hGX hxG) (hGX hyG) (hHX hzH)
    hxE hyE hzE hyx.symm hzx.symm hyz (hr x hx) (hr y hy) (hs z hz)

end Erdos827Four

theorem OMA.solution : type_of% @Erdos827.erdos_827.variants.n_four_le := by
  classical
  apply Erdos827.n_le
  intro X hX hpos
  by_contra! hbad
  let quads := X.powersetCard 4
  let edges := X.powersetCard 2
  have hmatch (G : ↥quads) : ∃ E, Erdos827Four.SharesRadius E G.val := by
    obtain ⟨hGX, hG⟩ := Finset.mem_powersetCard.mp G.property
    exact Erdos827Four.bad_quad_has_edge G.val hG (hbad G.val hGX hG)
  choose f hf using hmatch
  let fiber (E : Finset ℝ²) := quads.attach.filter (fun G => f G = E)
  have he (G : ↥quads) : f G ∈ edges := by
    obtain ⟨hGX, _⟩ := Finset.mem_powersetCard.mp G.property
    exact Finset.mem_powersetCard.mpr ⟨(hf G).1.trans hGX, (hf G).2.1⟩
  have hfiber (E : Finset ℝ²) (hE : E ∈ edges) : (fiber E).card ≤ 3 := by
    obtain ⟨hEX, hEc⟩ := Finset.mem_powersetCard.mp hE
    let rest (G : ↥quads) := G.val \ E
    have hget (G : ↥quads) (hG : G ∈ fiber E) : Erdos827Four.SharesRadius E G.val :=
      (Finset.mem_filter.mp hG).2 ▸ hf G
    have hpair : (fiber E : Set ↥quads).PairwiseDisjoint rest := by
      intro G hG H hH hGH
      obtain ⟨hGX, hGc⟩ := Finset.mem_powersetCard.mp G.property
      obtain ⟨hHX, hHc⟩ := Finset.mem_powersetCard.mp H.property
      exact Erdos827Four.rests_disjoint hpos.2 hGX hHX hGc hHc
        (fun h => hGH (Subtype.ext h)) (hget G hG) (hget H hH)
    have hUnion : (fiber E).biUnion rest ⊆ X \ E := by
      intro x hx
      obtain ⟨G, _, hxG⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨hGX, _⟩ := Finset.mem_powersetCard.mp G.property
      obtain ⟨h₁, h₂⟩ := Finset.mem_sdiff.mp hxG
      exact Finset.mem_sdiff.mpr ⟨hGX h₁, h₂⟩
    have hcard := Finset.card_le_card hUnion
    rw [Finset.card_biUnion hpair, Finset.card_sdiff_of_subset hEX, hX, hEc] at hcard
    have hsum : (∑ G ∈ fiber E, (rest G).card) = (fiber E).card * 2 := by
      calc
        _ = ∑ _G ∈ fiber E, 2 := by
          apply Finset.sum_congr rfl
          intro G hG
          have hGc := (Finset.mem_powersetCard.mp G.property).2
          simp [rest, Finset.card_sdiff_of_subset (hget G hG).1, hGc, hEc]
        _ = _ := by simp
    omega
  have hsum : quads.attach.card = ∑ E ∈ edges, (fiber E).card :=
    Finset.card_eq_sum_card_fiberwise (fun G _ => he G)
  have hbound : (∑ E ∈ edges, (fiber E).card) ≤ ∑ _E ∈ edges, 3 := by
    exact Finset.sum_le_sum hfiber
  have hquads : quads.attach.card = 126 := by
    simp only [Finset.card_attach, quads, Finset.card_powersetCard, hX]
    decide
  have hedges : (∑ _E ∈ edges, 3) = 108 := by
    simp only [Finset.sum_const, nsmul_eq_mul, edges, Finset.card_powersetCard, hX]
    decide
  omega