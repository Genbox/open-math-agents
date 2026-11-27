import FormalConjectures.ErdosProblems.«934»
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! A breadth-first count excludes triangles and four-cycles. The remaining 16-vertex configurations reduce to finite templates, and the subdivided Heawood graph attains 22 edges. Theorem 2 of https://arxiv.org/abs/2103.11898. -/

open Finset SimpleGraph
open scoped BigOperators

namespace CubicEdgeLayers

variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private def firstLayer (u v : V) : Finset V :=
  (G.neighborFinset u).erase v ∪ (G.neighborFinset v).erase u

private def firstOut (u v x : V) : Finset V :=
  G.neighborFinset x \ {u, v}

private def firstEdgesOut (u v x : V) : Finset V :=
  (firstOut G u v x).filter (fun y => y ∉ firstLayer G u v ∨ x < y)

private def secondOut (u v x : V) : Finset V :=
  firstOut G u v x \ firstLayer G u v

private def secondLayer (u v : V) : Finset V :=
  (firstLayer G u v).biUnion (secondOut G u v)

private theorem erase_roots_card (u v : V) (huv : G.Adj u v) :
    ((G.neighborFinset u).erase v).card = G.degree u - 1 := by
  rw [Finset.card_erase_of_mem ((G.mem_neighborFinset u v).2 huv), G.card_neighborFinset_eq_degree]

private theorem outside_degree_card {x p : V} {S : Finset V}
    (hp : p ∈ S) (hxp : G.Adj x p) :
    (G.neighborFinset x \ S).card ≤ G.degree x - 1 := by
  have hs : G.neighborFinset x \ S ⊆ (G.neighborFinset x).erase p := by
    intro y hy
    obtain ⟨hyN, hyS⟩ := Finset.mem_sdiff.mp hy
    exact Finset.mem_erase.mpr ⟨fun h => hyS (h.symm ▸ hp), hyN⟩
  exact (Finset.card_le_card hs).trans_eq (erase_roots_card G x p hxp)

private theorem firstLayer_parent {u v x : V} (hx : x ∈ firstLayer G u v) :
    ∃ p ∈ ({u,v} : Finset V), G.Adj x p := by
  rcases Finset.mem_union.mp hx with hx | hx
  · exact ⟨u, by simp, ((G.mem_neighborFinset u x).mp (Finset.mem_of_mem_erase hx)).symm⟩
  · exact ⟨v, by simp, ((G.mem_neighborFinset v x).mp (Finset.mem_of_mem_erase hx)).symm⟩

private theorem secondLayer_parent {u v x : V} (hx : x ∈ secondLayer G u v) :
    ∃ p ∈ firstLayer G u v, G.Adj x p := by
  obtain ⟨p, hp, hx'⟩ := Finset.mem_biUnion.mp hx
  have hN := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx').1).1
  exact ⟨p, hp, ((G.mem_neighborFinset p x).mp hN).symm⟩

private theorem close_vertex_in_layers {u v r z : V} (hr : r ∈ ({u,v} : Finset V))
    (hz : G.edist r z < 3) :
    z ∈ ({u,v} : Finset V) ∨ z ∈ firstLayer G u v ∨ z ∈ secondLayer G u v := by
  have hnear {a b : V} (ha : a ∈ ({u,v} : Finset V)) (hab : G.Adj a b) :
      b ∈ ({u,v} : Finset V) ∨ b ∈ firstLayer G u v := by
    by_cases hb : b ∈ ({u,v} : Finset V)
    · exact Or.inl hb
    · apply Or.inr
      have hbu : b ≠ u := fun h => hb (by simp [h])
      have hbv : b ≠ v := fun h => hb (by simp [h])
      have hm : a = u ∨ a = v := by simpa using ha
      rcases hm with rfl | rfl
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr
          ⟨hbv, (G.mem_neighborFinset _ _).2 hab⟩)
      · exact Finset.mem_union_right _ (Finset.mem_erase.mpr
          ⟨hbu, (G.mem_neighborFinset _ _).2 hab⟩)
  have hreach : G.Reachable r z := reachable_of_edist_ne_top (hz.trans_le le_top).ne
  obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_edist
  have hlen : p.length < 3 := by
    have hcast : (p.length : ℕ∞) < ((3 : ℕ) : ℕ∞) := hp.trans_lt hz
    exact ENat.natCast_lt_natCast.mp hcast
  cases p with
  | nil => exact Or.inl hr
  | @cons r y z hry p =>
    have hy := hnear hr hry
    cases p with
    | nil => exact hy.imp id Or.inl
    | @cons y w z hyw p =>
      have hp0 : p.length = 0 := by
        simp only [Walk.length_cons] at hlen
        omega
      have he := p.eq_of_length_eq_zero hp0
      subst z
      rcases hy with hy | hy
      · exact (hnear hy hyw).imp id Or.inl
      · by_cases hw₀ : w ∈ ({u,v} : Finset V)
        · exact Or.inl hw₀
        · by_cases hw₁ : w ∈ firstLayer G u v
          · exact Or.inr (Or.inl hw₁)
          · exact Or.inr (Or.inr (Finset.mem_biUnion.mpr ⟨y, hy,
              Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr
                ⟨(G.mem_neighborFinset _ _).2 hyw, hw₀⟩, hw₁⟩⟩))

omit [Fintype V] [LinearOrder V] [DecidableRel G.Adj] in
private theorem no_far_edges_near_either_root {u v x y : V}
    (h : ¬ Erdos934.HasFarEdges G 3) (huv : G.Adj u v) (hxy : G.Adj x y) :
    G.edist u x < 3 ∨ G.edist u y < 3 ∨ G.edist v x < 3 ∨ G.edist v y < 3 := by
  by_contra! hn
  apply h
  refine ⟨u, v, x, y, huv, hxy, ?_⟩
  intro a ha b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact hn.1
  · exact hn.2.1
  · exact hn.2.2.1
  · exact hn.2.2.2

end CubicEdgeLayers

namespace CubicEdgeLayers

private theorem union_image_lt_of_shared_value {α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (S : Finset α) (T : α → Finset β) (f : α → β → γ)
    {i j : α} (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j)
    {x y : β} (hx : x ∈ T i) (hy : y ∈ T j) (hxy : f i x = f j y) :
    (S.biUnion fun a => (T a).image (f a)).card < ∑ a ∈ S, (T a).card := by
  let P : Finset (Σ _ : α, β) := S.sigma T
  let project (p : Σ _ : α, β) := f p.1 p.2
  have hu : S.biUnion (fun a => (T a).image (f a)) = P.image project := by
    ext c
    constructor
    · intro hc
      obtain ⟨a, ha, hca⟩ := Finset.mem_biUnion.mp hc
      obtain ⟨b, hb, hbc⟩ := Finset.mem_image.mp hca
      exact Finset.mem_image.mpr ⟨⟨a,b⟩, Finset.mem_sigma.mpr ⟨ha,hb⟩, hbc⟩
    · intro hc
      obtain ⟨p, hp, hpc⟩ := Finset.mem_image.mp hc
      obtain ⟨ha,hb⟩ := Finset.mem_sigma.mp hp
      exact Finset.mem_biUnion.mpr ⟨p.1, ha, Finset.mem_image.mpr ⟨p.2,hb,hpc⟩⟩
  rw [hu, ← Finset.card_sigma]
  change (P.image project).card < P.card
  apply lt_of_le_of_ne Finset.card_image_le
  intro he
  have hinj := Finset.card_image_iff.mp he
  have hEq : (⟨i,x⟩ : Σ _ : α, β) = ⟨j,y⟩ := hinj
    (Finset.mem_sigma.mpr ⟨hi,hx⟩) (Finset.mem_sigma.mpr ⟨hj,hy⟩) hxy
  exact hij (congrArg Sigma.fst hEq)

end CubicEdgeLayers

namespace CubicEdgeLayers

variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem edge_root_bound_with_deficit {u v : V} (huv : G.Adj u v)
    (hd : ∀ x, G.degree x ≤ 3) (h : ¬ Erdos934.HasFarEdges G 3) :
    let total := 1 + (G.degree u - 1) + (G.degree v - 1) +
      (∑ x ∈ firstLayer G u v, (firstEdgesOut G u v x).card) +
      2 * (secondLayer G u v).card
    G.edgeFinset.card ≤ total ∧
      ((∃ a ∈ secondLayer G u v, ∃ b ∈ secondLayer G u v, G.Adj a b) →
        G.edgeFinset.card + 1 ≤ total) := by
  let B := ({u,v} : Finset V)
  let U := (G.neighborFinset u).erase v
  let W := (G.neighborFinset v).erase u
  let atVertex (x : V) (s : Finset V) := s.image fun y => s(x,y)
  let E₀ := insert s(u,v) (atVertex u U ∪ atVertex v W)
  let E₁ := (firstLayer G u v).biUnion (fun x => atVertex x (firstEdgesOut G u v x))
  let E₂ := (secondLayer G u v).biUnion (fun x => atVertex x (G.neighborFinset x \ firstLayer G u v))
  have h₀ {x y : V} (hx : x ∈ B) (hxy : G.Adj x y) : s(x,y) ∈ E₀ := by
    have hh : x = u ∨ x = v := by simpa [B] using hx
    rcases hh with rfl | rfl
    · by_cases hy : y = v
      · subst y
        exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _
          (Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨hy, (G.mem_neighborFinset _ _).2 hxy⟩)))
    · by_cases hy : y = u
      · subst y
        rw [Sym2.eq_swap]
        exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _
          (Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨hy, (G.mem_neighborFinset _ _).2 hxy⟩)))
  have h₁ {x y : V} (hx : x ∈ firstLayer G u v) (hxy : G.Adj x y) : s(x,y) ∈ E₀ ∪ E₁ := by
    have hmem {a b : V} (ha : a ∈ firstLayer G u v) (hab : G.Adj a b)
        (hb : b ∉ B) (hord : b ∉ firstLayer G u v ∨ a < b) : s(a,b) ∈ E₁ :=
      Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image_of_mem _
        (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).2 hab, hb⟩, hord⟩)⟩
    by_cases hy : y ∈ B
    · exact Finset.mem_union_left _ (Sym2.eq_swap ▸ h₀ hy hxy.symm)
    · apply Finset.mem_union_right
      by_cases hy' : y ∈ firstLayer G u v
      · by_cases hlt : x < y
        · exact hmem hx hxy hy (Or.inr hlt)
        · have hx' : x ∉ B := by
            intro hxB
            have hxuv : x = u ∨ x = v := by simpa [B] using hxB
            rcases Finset.mem_union.mp hx with hu | hv
            · rcases hxuv with rfl | rfl
              · exact ((G.mem_neighborFinset _ _).1 (Finset.mem_of_mem_erase hu)).ne rfl
              · exact Finset.notMem_erase _ _ hu
            · rcases hxuv with rfl | rfl
              · exact Finset.notMem_erase _ _ hv
              · exact ((G.mem_neighborFinset _ _).1 (Finset.mem_of_mem_erase hv)).ne rfl
          have hlt' : y < x := lt_of_le_of_ne (le_of_not_gt hlt) hxy.ne.symm
          exact Sym2.eq_swap ▸ hmem hy' hxy.symm hx' (Or.inr hlt')
      · exact hmem hx hxy hy (Or.inl hy')
  have h₂ {x y : V} (hx : x ∈ secondLayer G u v) (hxy : G.Adj x y) :
      s(x,y) ∈ (E₀ ∪ E₁) ∪ E₂ := by
    by_cases hy : y ∈ firstLayer G u v
    · exact Finset.mem_union_left _ (Sym2.eq_swap ▸ h₁ hy hxy.symm)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image_of_mem _
        (Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).2 hxy, hy⟩)⟩)
  have cover {x y : V} (hxy : G.Adj x y)
      (hx : x ∈ B ∨ x ∈ firstLayer G u v ∨ x ∈ secondLayer G u v) :
      s(x,y) ∈ (E₀ ∪ E₁) ∪ E₂ := by
    rcases hx with hx | hx | hx
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (h₀ hx hxy))
    · exact Finset.mem_union_left _ (h₁ hx hxy)
    · exact h₂ hx hxy
  have hall : G.edgeFinset ⊆ (E₀ ∪ E₁) ∪ E₂ := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
      have hxy : G.Adj x y := SimpleGraph.mem_edgeFinset.mp he
      rcases no_far_edges_near_either_root G h huv hxy with hux | huy | hvx | hvy
      · exact cover hxy (close_vertex_in_layers G (by simp [B] : u ∈ B) hux)
      · exact Sym2.eq_swap ▸ cover hxy.symm (close_vertex_in_layers G (by simp [B] : u ∈ B) huy)
      · exact cover hxy (close_vertex_in_layers G (by simp [B] : v ∈ B) hvx)
      · exact Sym2.eq_swap ▸ cover hxy.symm (close_vertex_in_layers G (by simp [B] : v ∈ B) hvy)
  have hc₀ : E₀.card ≤ U.card + W.card + 1 :=
    (Finset.card_insert_le _ _).trans
      (Nat.add_le_add_right ((Finset.card_union_le _ _).trans
        (Nat.add_le_add Finset.card_image_le Finset.card_image_le)) _)
  have hc₁ : E₁.card ≤ ∑ x ∈ firstLayer G u v, (firstEdgesOut G u v x).card :=
    (Finset.card_biUnion_le).trans (Finset.sum_le_sum (fun _ _ => Finset.card_image_le))
  have hlast : (∑ x ∈ secondLayer G u v, (G.neighborFinset x \ firstLayer G u v).card) ≤
      2 * (secondLayer G u v).card := by
    calc
      _ ≤ ∑ _ ∈ secondLayer G u v, 2 := by
        refine Finset.sum_le_sum (fun x hx => ?_)
        obtain ⟨p, hp, hxp⟩ := secondLayer_parent G hx
        exact (outside_degree_card G hp hxp).trans (by have hd' := hd x; omega)
      _ = _ := by simp [mul_comm]
  have hc₂ : E₂.card ≤ 2 * (secondLayer G u v).card :=
    Finset.card_biUnion_le.trans ((Finset.sum_le_sum (fun _ _ => Finset.card_image_le)).trans hlast)
  have hU : U.card = G.degree u - 1 := erase_roots_card G u v huv
  have hW : W.card = G.degree v - 1 := erase_roots_card G v u huv.symm
  have htot := (Finset.card_le_card hall).trans (Finset.card_union_le _ _)
  have h01 := Finset.card_union_le E₀ E₁
  constructor
  · omega
  · rintro ⟨a, ha, b, hb, hab⟩
    have hout {x : V} (hx : x ∈ secondLayer G u v) : x ∉ firstLayer G u v := by
      obtain ⟨_, _, hmem⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_sdiff.mp hmem).2
    have hba : b ∈ G.neighborFinset a \ firstLayer G u v :=
      Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).2 hab, hout hb⟩
    have hab' : a ∈ G.neighborFinset b \ firstLayer G u v :=
      Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).2 hab.symm, hout ha⟩
    have hlt : E₂.card <
        ∑ x ∈ secondLayer G u v, (G.neighborFinset x \ firstLayer G u v).card :=
      union_image_lt_of_shared_value (secondLayer G u v)
        (fun x => G.neighborFinset x \ firstLayer G u v) (fun x y => s(x,y))
        ha hb hab.ne hba hab' Sym2.eq_swap
    omega

private theorem edge_root_bound {u v : V} (huv : G.Adj u v)
    (hd : ∀ x, G.degree x ≤ 3) (h : ¬ Erdos934.HasFarEdges G 3) :
    G.edgeFinset.card ≤ 1 + (G.degree u - 1) + (G.degree v - 1) +
      (∑ x ∈ firstLayer G u v, (firstEdgesOut G u v x).card) +
      2 * (secondLayer G u v).card :=
  (edge_root_bound_with_deficit G huv hd h).1

end CubicEdgeLayers

namespace CubicEdgeLayers

variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem firstLayer_card_le {u v : V} (huv : G.Adj u v) :
    (firstLayer G u v).card ≤ (G.degree u - 1) + (G.degree v - 1) := by
  unfold firstLayer
  refine (Finset.card_union_le _ _).trans ?_
  rw [erase_roots_card G u v huv, erase_roots_card G v u huv.symm]

private theorem firstOut_card_le {u v x : V} (hx : x ∈ firstLayer G u v) :
    (firstOut G u v x).card ≤ G.degree x - 1 := by
  obtain ⟨p, hp, hxp⟩ := firstLayer_parent G hx
  exact outside_degree_card G hp hxp

private theorem firstOut_sum_le {u v : V} (hd : ∀ x, G.degree x ≤ 3) :
    (∑ x ∈ firstLayer G u v, (firstOut G u v x).card) ≤ 2 * (firstLayer G u v).card := by
  calc
    _ ≤ ∑ _ ∈ firstLayer G u v, 2 := by
      refine Finset.sum_le_sum (fun x hx => (firstOut_card_le G hx).trans ?_)
      have he := hd x
      omega
    _ = _ := by simp [mul_comm]

private theorem firstEdgesOut_sum_le (u v : V) :
    (∑ x ∈ firstLayer G u v, (firstEdgesOut G u v x).card) ≤
      ∑ x ∈ firstLayer G u v, (firstOut G u v x).card :=
  Finset.sum_le_sum (fun _ _ => Finset.card_le_card (Finset.filter_subset _ _))

private theorem secondLayer_card_le (u v : V) :
    (secondLayer G u v).card ≤ ∑ x ∈ firstLayer G u v, (firstOut G u v x).card := by
  unfold secondLayer
  exact Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun _ _ =>
    Finset.card_le_card (Finset.sdiff_subset)))

private theorem edge_root_bound_simple {u v : V} (huv : G.Adj u v)
    (hd : ∀ x, G.degree x ≤ 3) (h : ¬ Erdos934.HasFarEdges G 3) :
    G.edgeFinset.card ≤ 1 + 7 * ((G.degree u - 1) + (G.degree v - 1)) := by
  have hbase := edge_root_bound G huv hd h
  have hfirst := firstLayer_card_le G huv
  have hsum := firstOut_sum_le (G := G) (u := u) (v := v) hd
  have h₁ := firstEdgesOut_sum_le G u v
  have h₂ := secondLayer_card_le G u v
  omega

private theorem degree_three_of_incident {u v : V} (huv : G.Adj u v)
    (hd : ∀ x, G.degree x ≤ 3) (h : ¬ Erdos934.HasFarEdges G 3)
    (hn : 23 ≤ G.edgeFinset.card) : G.degree u = 3 := by
  have hm := edge_root_bound_simple G huv hd h
  have hu := hd u
  have hv := hd v
  omega

/-- When the graph has at least 23 edges, only two orders of its nonisolated part remain. -/
private theorem active_order_eq_sixteen_or_eighteen
    (hd : ∀ x, G.degree x ≤ 3) (h : ¬ Erdos934.HasFarEdges G 3)
    (hn : 23 ≤ G.edgeFinset.card) :
    (Finset.univ.filter (fun x => 0 < G.degree x)).card = 16 ∨
      (Finset.univ.filter (fun x => 0 < G.degree x)).card = 18 := by
  obtain ⟨e, he⟩ := Finset.card_pos.mp (show 0 < G.edgeFinset.card by omega)
  have hm : G.edgeFinset.card ≤ 29 := by
    induction e using Sym2.inductionOn with
    | _ u v =>
      have hAdj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
      have hroot := edge_root_bound_simple G hAdj hd h
      have hu := hd u
      have hv := hd v
      omega
  let S := Finset.univ.filter (fun x => 0 < G.degree x)
  have hdeg (x : V) (hx : x ∈ S) : G.degree x = 3 := by
    have hp := (Finset.mem_filter.mp hx).2
    rw [← G.card_neighborFinset_eq_degree] at hp
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hp
    exact degree_three_of_incident G ((G.mem_neighborFinset _ _).mp hy) hd h hn
  have hsum : ∑ x, G.degree x = 3 * S.card := by
    rw [← Finset.sum_subset (Finset.subset_univ S) (fun x _ hx =>
      Nat.eq_zero_of_not_pos (fun hx' => hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'⟩)))]
    rw [Finset.sum_congr rfl hdeg]
    simp [mul_comm]
  have hhand := G.sum_degrees_eq_twice_card_edges
  change S.card = 16 ∨ S.card = 18
  omega

end CubicEdgeLayers

namespace CubicEdgeLayers

variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem triangle_bounds_edges {u v w : V}
    (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w)
    (hd : ∀ x, G.degree x ≤ 3) (h : ¬ Erdos934.HasFarEdges G 3) :
    G.edgeFinset.card ≤ 20 := by
  let A := (G.neighborFinset u).erase v
  let B := (G.neighborFinset v).erase u
  let S := firstLayer G u v
  have hwA : w ∈ A :=
    Finset.mem_erase.mpr ⟨hvw.ne.symm, (G.mem_neighborFinset _ _).2 huw⟩
  have hwB : w ∈ B :=
    Finset.mem_erase.mpr ⟨huw.ne.symm, (G.mem_neighborFinset _ _).2 hvw⟩
  have hw : w ∈ S := Finset.mem_union_left _ hwA
  have hdiv : 0 < (A ∩ B).card := Finset.card_pos.2 ⟨w, Finset.mem_inter.mpr ⟨hwA, hwB⟩⟩
  have hu := hd u
  have hv := hd v
  have hwdeg := hd w
  have hAc : A.card = G.degree u - 1 := erase_roots_card G u v huv
  have hBc : B.card = G.degree v - 1 := erase_roots_card G v u huv.symm
  have hcard : S.card ≤ 3 := by
    change (A ∪ B).card ≤ 3
    have hab := Finset.card_union_add_card_inter A B
    omega
  have hwu : u ∈ G.neighborFinset w := (G.mem_neighborFinset _ _).2 huw.symm
  have hwv : v ∈ G.neighborFinset w := (G.mem_neighborFinset _ _).2 hvw.symm
  have hwout : (firstOut G u v w).card ≤ 1 := by
    have hset : firstOut G u v w = ((G.neighborFinset w).erase u).erase v := by
      ext x
      simp [firstOut]
      tauto
    rw [hset, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨huv.ne.symm, hwv⟩),
      Finset.card_erase_of_mem hwu, G.card_neighborFinset_eq_degree]
    omega
  have hout : (∑ x ∈ S, (firstOut G u v x).card) ≤ 5 := by
    have hrest : (∑ x ∈ S.erase w, (firstOut G u v x).card) ≤ 2 * (S.card - 1) := by
      calc
        _ ≤ ∑ _ ∈ S.erase w, 2 := by
          refine Finset.sum_le_sum (fun x hx => (firstOut_card_le G (Finset.mem_of_mem_erase hx)).trans ?_)
          have he := hd x
          omega
        _ = _ := by simp [Finset.card_erase_of_mem hw, mul_comm]
    rw [← Finset.sum_erase_add _ _ hw]
    omega
  have hm := edge_root_bound G huv hd h
  have hE₁ := firstEdgesOut_sum_le G u v
  have h₂ := secondLayer_card_le G u v
  change (∑ x ∈ firstLayer G u v, (firstOut G u v x).card) ≤ 5 at hout
  omega

end CubicEdgeLayers

namespace CubicEdgeLayers

variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem firstLayer_avoids_roots {u v x : V} (hx : x ∈ firstLayer G u v) :
    x ∉ ({u,v} : Finset V) := by
  intro hr
  have hr' : x = u ∨ x = v := by simpa using hr
  rcases Finset.mem_union.mp hx with ha | hb
  · rcases hr' with rfl | rfl
    · exact ((G.mem_neighborFinset _ _).1 (Finset.mem_of_mem_erase ha)).ne rfl
    · exact Finset.notMem_erase _ _ ha
  · rcases hr' with rfl | rfl
    · exact Finset.notMem_erase _ _ hb
    · exact ((G.mem_neighborFinset _ _).1 (Finset.mem_of_mem_erase hb)).ne rfl

private def ascending (S : Finset V) (x : V) : Finset V :=
  S.filter fun y => G.Adj x y ∧ x < y

private def descending (S : Finset V) (x : V) : Finset V :=
  S.filter fun y => G.Adj x y ∧ y < x

omit [Fintype V] in
private theorem ascending_sum_eq_descending_sum (S : Finset V) :
    (∑ x ∈ S, (ascending G S x).card) = ∑ x ∈ S, (descending G S x).card := by
  simp only [ascending, descending, Finset.card_filter]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  exact if_congr ⟨fun h => ⟨h.1.symm, h.2⟩, fun h => ⟨h.1.symm, h.2⟩⟩ rfl rfl

private theorem firstOut_partition (u v x : V) :
    (firstOut G u v x).card = (secondOut G u v x).card +
      (ascending G (firstLayer G u v) x).card + (descending G (firstLayer G u v) x).card := by
  let S := firstLayer G u v
  have heq : firstOut G u v x =
      (secondOut G u v x ∪ ascending G S x) ∪ descending G S x := by
    ext y
    by_cases hy : y ∈ S
    · have hB := firstLayer_avoids_roots G hy
      by_cases ha : G.Adj x y
      · rcases lt_or_gt_of_ne ha.ne with hlt | hlt
        · simp [firstOut, secondOut, ascending, descending, S, hy, hB, ha, hlt, hlt.not_gt,
            G.mem_neighborFinset]
        · simp [firstOut, secondOut, ascending, descending, S, hy, hB, ha, hlt, hlt.not_gt,
            G.mem_neighborFinset]
      · simp [firstOut, secondOut, ascending, descending, ha, G.mem_neighborFinset]
    · simp [firstOut, secondOut, ascending, descending, S, hy]
  have hda : Disjoint (secondOut G u v x) (ascending G S x) :=
    Finset.disjoint_left.2 (fun _ hs ha =>
      (Finset.mem_sdiff.mp hs).2 (Finset.mem_filter.mp ha).1)
  have hdd : Disjoint (secondOut G u v x ∪ ascending G S x) (descending G S x) := by
    refine Finset.disjoint_left.2 (fun y hy hd => ?_)
    obtain ⟨hyS, hAdj, hlt⟩ := Finset.mem_filter.mp hd
    rcases Finset.mem_union.mp hy with h₂ | h₁
    · exact (Finset.mem_sdiff.mp h₂).2 hyS
    · exact hlt.not_gt (Finset.mem_filter.mp h₁).2.2
  rw [heq, Finset.card_union_of_disjoint hdd, Finset.card_union_of_disjoint hda]

private theorem firstEdgesOut_partition (u v x : V) :
    (firstEdgesOut G u v x).card = (secondOut G u v x).card +
      (ascending G (firstLayer G u v) x).card := by
  let S := firstLayer G u v
  have heq : firstEdgesOut G u v x = secondOut G u v x ∪ ascending G S x := by
    ext y
    by_cases hy : y ∈ S
    · have hB := firstLayer_avoids_roots G hy
      simp [firstEdgesOut, firstOut, secondOut, ascending, S, hy, hB, G.mem_neighborFinset]
    · simp [firstEdgesOut, firstOut, secondOut, ascending, S, hy]
  rw [heq, Finset.card_union_of_disjoint]
  exact Finset.disjoint_left.2 (fun _ hs ha =>
    (Finset.mem_sdiff.mp hs).2 (Finset.mem_filter.mp ha).1)

private theorem first_layer_counting {u v : V} (huv : G.Adj u v)
    (hd : ∀ x, G.degree x ≤ 3) (h : ¬ Erdos934.HasFarEdges G 3) :
    let S := firstLayer G u v
    let K := ∑ x ∈ S, (ascending G S x).card
    let T := ∑ x ∈ S, (secondOut G u v x).card
    (G.edgeFinset.card + 5 * K ≤ 29) ∧
      (24 ≤ G.edgeFinset.card → 1 ≤ K →
        K = 1 ∧ T = 6 ∧ (secondLayer G u v).card = 6 ∧ S.card = 4 ∧ G.edgeFinset.card = 24) := by
  let S := firstLayer G u v
  let K := ∑ x ∈ S, (ascending G S x).card
  let T := ∑ x ∈ S, (secondOut G u v x).card
  have hp : (∑ x ∈ S, (firstOut G u v x).card) = T + K + K := by
    simp_rw [firstOut_partition G u v, Finset.sum_add_distrib]
    rw [← ascending_sum_eq_descending_sum G S]
  have he : (∑ x ∈ S, (firstEdgesOut G u v x).card) = T + K := by
    simp_rw [firstEdgesOut_partition G u v, Finset.sum_add_distrib]
    rfl
  have ht : (secondLayer G u v).card ≤ T := Finset.card_biUnion_le
  have hc := firstLayer_card_le G huv
  have hU := hd u
  have hV := hd v
  have hs : S.card ≤ 4 := by
    change S.card ≤ (G.degree u - 1) + (G.degree v - 1) at hc
    omega
  have hb : T + K + K ≤ 2 * S.card := by
    rw [← hp]
    exact firstOut_sum_le G hd
  have hm := edge_root_bound G huv hd h
  change _ ≤ 1 + (G.degree u - 1) + (G.degree v - 1) +
    (∑ x ∈ S, (firstEdgesOut G u v x).card) + 2 * (secondLayer G u v).card at hm
  change (G.edgeFinset.card + 5 * K ≤ 29) ∧
    (24 ≤ G.edgeFinset.card → 1 ≤ K →
      K = 1 ∧ T = 6 ∧ (secondLayer G u v).card = 6 ∧ S.card = 4 ∧ G.edgeFinset.card = 24)
  constructor
  · omega
  · intro hm₂ hk
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩

end CubicEdgeLayers

namespace CubicEdgeLayers

private theorem lower_bound_twenty_three_of_witness
    (witness : ∃ G : SimpleGraph (Fin 15),
      (∀ v, (G.neighborSet v).ncard ≤ 3) ∧ G.edgeSet.ncard = 22 ∧
        ¬ Erdos934.HasFarEdges G 3) :
    23 ≤ Erdos934.h 3 3 := by
  classical
  let S := {m : ℕ | ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    (∀ v, (G.neighborSet v).ncard ≤ 3) → m ≤ G.edgeSet.ncard → Erdos934.HasFarEdges G 3}
  have hnonempty : S.Nonempty := by
    refine ⟨30, ?_⟩
    intro n G hdeg he
    by_contra hn
    have hdeg' (v : Fin n) : G.degree v ≤ 3 := by
      simpa only [← G.coe_neighborFinset, Set.ncard_coe_finset, G.card_neighborFinset_eq_degree]
        using hdeg v
    have heq : G.edgeFinset.card = G.edgeSet.ncard := by
      rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
    rw [← heq] at he
    obtain ⟨e, hE⟩ := Finset.card_pos.mp (show 0 < G.edgeFinset.card by omega)
    induction e using Sym2.inductionOn with
    | _ x y =>
      have hxy : G.Adj x y := SimpleGraph.mem_edgeFinset.mp hE
      have hbound := edge_root_bound_simple G hxy hdeg' hn
      have hx := hdeg' x
      have hy := hdeg' y
      omega
  have hmin := Nat.sInf_mem hnonempty
  obtain ⟨G, hdeg, hcard, hn⟩ := witness
  change 23 ≤ sInf S
  by_contra! hsmall
  apply hn
  exact hmin 15 G hdeg (by rw [hcard]; omega)

end CubicEdgeLayers

namespace CubicEdgeLayers

variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem mem_firstLayer_iff {u v x : V} :
    x ∈ firstLayer G u v ↔ x ∉ ({u,v} : Finset V) ∧ (G.Adj u x ∨ G.Adj v x) := by
  constructor
  · intro h
    refine ⟨firstLayer_avoids_roots G h, ?_⟩
    rcases Finset.mem_union.mp h with h | h
    · exact Or.inl ((G.mem_neighborFinset u x).mp (Finset.mem_of_mem_erase h))
    · exact Or.inr ((G.mem_neighborFinset v x).mp (Finset.mem_of_mem_erase h))
  · rintro ⟨h, hu | hv⟩
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr
        ⟨fun he => h (by simp [he]), (G.mem_neighborFinset u x).mpr hu⟩)
    · exact Finset.mem_union_right _ (Finset.mem_erase.mpr
        ⟨fun he => h (by simp [he]), (G.mem_neighborFinset v x).mpr hv⟩)

private theorem mem_secondLayer_iff {u v x : V} :
    x ∈ secondLayer G u v ↔ x ∉ ({u,v} : Finset V) ∧
      x ∉ firstLayer G u v ∧ ∃ p ∈ firstLayer G u v, G.Adj p x := by
  constructor
  · intro hx
    obtain ⟨p, hp, hx'⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hx₁, hx₂⟩ := Finset.mem_sdiff.mp hx'
    obtain ⟨hxp, hx₀⟩ := Finset.mem_sdiff.mp hx₁
    exact ⟨hx₀, hx₂, p, hp, (G.mem_neighborFinset p x).mp hxp⟩
  · rintro ⟨hx₀, hx₁, p, hp, hpx⟩
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_sdiff.mpr
      ⟨Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset p x).mpr hpx, hx₀⟩, hx₁⟩⟩

private def outsideLayers (u v x : V) : Prop :=
  x ∉ ({u,v} : Finset V) ∧ x ∉ firstLayer G u v ∧ x ∉ secondLayer G u v

private theorem outside_only_adj_second {u v x y : V}
    (h : ¬ Erdos934.HasFarEdges G 3) (huv : G.Adj u v)
    (hx : outsideLayers G u v x) (hxy : G.Adj x y) : y ∈ secondLayer G u v := by
  by_contra hy₂
  have hy₁ : y ∉ firstLayer G u v := by
    intro hy
    exact hx.2.2 ((mem_secondLayer_iff G).mpr ⟨hx.1, hx.2.1, y, hy, hxy.symm⟩)
  have hy₀ : y ∉ ({u,v} : Finset V) := by
    intro hy
    have hs : y = u ∨ y = v := by simpa using hy
    rcases hs with rfl | rfl
    · exact hx.2.1 ((mem_firstLayer_iff G).mpr ⟨hx.1, Or.inl hxy.symm⟩)
    · exact hx.2.1 ((mem_firstLayer_iff G).mpr ⟨hx.1, Or.inr hxy.symm⟩)
  have bad {r z : V} (hr : r ∈ ({u,v} : Finset V)) (hz : outsideLayers G u v z)
      (hdist : G.edist r z < 3) : False := by
    rcases close_vertex_in_layers G hr hdist with h₀ | h₁ | h₂
    · exact hz.1 h₀
    · exact hz.2.1 h₁
    · exact hz.2.2 h₂
  rcases no_far_edges_near_either_root G h huv hxy with hu₀ | hu₁ | hv₀ | hv₁
  · exact bad (by simp : u ∈ ({u,v} : Finset V)) hx hu₀
  · exact bad (by simp : u ∈ ({u,v} : Finset V)) ⟨hy₀,hy₁,hy₂⟩ hu₁
  · exact bad (by simp : v ∈ ({u,v} : Finset V)) hx hv₀
  · exact bad (by simp : v ∈ ({u,v} : Finset V)) ⟨hy₀,hy₁,hy₂⟩ hv₁

private theorem unique_first_parent_of_saturation {u v x a b : V}
    (hcard : (secondLayer G u v).card = ∑ y ∈ firstLayer G u v, (secondOut G u v y).card)
    (hx : x ∈ secondLayer G u v) (ha : a ∈ firstLayer G u v) (hb : b ∈ firstLayer G u v)
    (hax : G.Adj a x) (hbx : G.Adj b x) : a = b := by
  by_contra hab
  have hmem {y : V} (h : G.Adj y x) : x ∈ secondOut G u v y := by
    obtain ⟨h₀,h₁,_⟩ := (mem_secondLayer_iff G).1 hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr
      ⟨(G.mem_neighborFinset y x).2 h, h₀⟩, h₁⟩
  have hlt := union_image_lt_of_shared_value (firstLayer G u v)
    (secondOut G u v) (fun _ x => x) ha hb hab (hmem hax) (hmem hbx) rfl
  exact hcard.not_lt (by simpa [secondLayer] using hlt)

private theorem saturated_second_independent {u v : V}
    (huv : G.Adj u v) (hd : ∀ x, G.degree x ≤ 3) (h : ¬ Erdos934.HasFarEdges G 3)
    (hm : 24 ≤ G.edgeFinset.card)
    (hK : 1 ≤ ∑ x ∈ firstLayer G u v, (ascending G (firstLayer G u v) x).card)
    {x y : V} (hx : x ∈ secondLayer G u v) (hy : y ∈ secondLayer G u v) : ¬ G.Adj x y := by
  intro hxy
  obtain ⟨hk, ht, hcard, _, _⟩ := (first_layer_counting G huv hd h).2 hm hK
  have he : (∑ x ∈ firstLayer G u v, (firstEdgesOut G u v x).card) = 7 := by
    simp_rw [firstEdgesOut_partition G u v, Finset.sum_add_distrib]
    omega
  have hdef := (edge_root_bound_with_deficit G huv hd h).2 ⟨x,hx,y,hy,hxy⟩
  change G.edgeFinset.card + 1 ≤ 1 + (G.degree u - 1) + (G.degree v - 1) +
    (∑ x ∈ firstLayer G u v, (firstEdgesOut G u v x).card) + 2 * (secondLayer G u v).card at hdef
  have hu := hd u
  have hv := hd v
  omega

end CubicEdgeLayers

namespace CubicEdgeLayers

variable {V : Type*} [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem internal_edge_eq_of_ascending_sum_le_one (S : Finset V) {a b c d : V}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S) (hab : G.Adj a b)
    (hcd : G.Adj c d) (h : (∑ x ∈ S, (ascending G S x).card) ≤ 1) :
    s(a, b) = s(c, d) := by
  let E : Finset (Σ _ : V, V) := S.sigma (ascending G S)
  have hE : E.card ≤ 1 := by simpa only [E, Finset.card_sigma] using h
  have represent {x y : V} (hx : x ∈ S) (hy : y ∈ S) (hxy : G.Adj x y) :
      ∃ z ∈ E, s(z.1, z.2) = s(x, y) := by
    rcases lt_or_gt_of_ne hxy.ne with hlt | hlt
    · exact ⟨⟨x, y⟩, Finset.mem_sigma.2 ⟨hx, Finset.mem_filter.2 ⟨hy, hxy, hlt⟩⟩, rfl⟩
    · exact ⟨⟨y, x⟩, Finset.mem_sigma.2 ⟨hy, Finset.mem_filter.2 ⟨hx, hxy.symm, hlt⟩⟩,
        Sym2.eq_swap⟩
  obtain ⟨e, he, heq⟩ := represent ha hb hab
  obtain ⟨f, hf, hfq⟩ := represent hc hd hcd
  have hef := Finset.card_le_one_iff.1 hE he hf
  exact heq.symm.trans (hef ▸ hfq)

variable [Fintype V]

theorem four_cycle_opposite_mem_firstLayer {u v c d : V}
    (hvc : G.Adj v c) (hdu : G.Adj d u) (hcu : c ≠ u) (hdv : d ≠ v) :
    c ∈ firstLayer G u v ∧ d ∈ firstLayer G u v :=
  ⟨Finset.mem_union.2 (Or.inr (Finset.mem_erase.2 ⟨hcu, (G.mem_neighborFinset v c).2 hvc⟩)),
    Finset.mem_union.2 (Or.inl (Finset.mem_erase.2 ⟨hdv, (G.mem_neighborFinset u d).2 hdu.symm⟩))⟩

theorem four_cycle_opposite_eq_of_ascending_sum_le_one {u v c d e f : V}
    (hvc : G.Adj v c) (hcd : G.Adj c d) (hdu : G.Adj d u) (hcu : c ≠ u) (hdv : d ≠ v)
    (hve : G.Adj v e) (hef : G.Adj e f) (hfu : G.Adj f u) (heu : e ≠ u) (hfv : f ≠ v)
    (h : (∑ x ∈ firstLayer G u v, (ascending G (firstLayer G u v) x).card) ≤ 1) :
    s(c, d) = s(e, f) := by
  obtain ⟨hc, hd⟩ := four_cycle_opposite_mem_firstLayer G hvc hdu hcu hdv
  obtain ⟨he, hf⟩ := four_cycle_opposite_mem_firstLayer G hve hfu heu hfv
  exact internal_edge_eq_of_ascending_sum_le_one G (firstLayer G u v) hc hd he hf hcd hef h

end CubicEdgeLayers

private theorem OMA.three_le_edist_of_no_common {V : Type*} {G : SimpleGraph V} {u v : V}
    (h : u ≠ v ∧ ¬ G.Adj u v ∧ G.commonNeighbors u v = ∅) :
    (3 : ℕ∞) ≤ G.edist u v := by
  have ht : (2 : ℕ∞) < G.edist u v := G.two_lt_edist_iff.mpr h
  exact Order.add_one_le_of_lt ht

private theorem OMA.edist_lt_three_iff {V : Type*} {G : SimpleGraph V} {u v : V} :
    G.edist u v < (3 : ℕ∞) ↔ u = v ∨ G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj v w := by
  constructor
  · intro h
    by_cases he : u = v
    · exact Or.inl he
    by_cases ha : G.Adj u v
    · exact Or.inr (Or.inl ha)
    have hcommon : (G.commonNeighbors u v).Nonempty := by
      by_contra hn
      have hfar := OMA.three_le_edist_of_no_common
        ⟨he, ha, Set.not_nonempty_iff_eq_empty.mp hn⟩
      exact (not_le_of_gt h) hfar
    obtain ⟨w, hw⟩ := hcommon
    exact Or.inr (Or.inr ⟨w, G.mem_commonNeighbors.mp hw⟩)
  · rintro (rfl | ha | ⟨w, huw, hvw⟩)
    · simp
    · rw [G.edist_eq_one_iff_adj.mpr ha]
      decide
    · by_contra! hn
      have ht : (2 : ℕ∞) < G.edist u v := lt_of_lt_of_le (by decide) hn
      have he := (G.two_lt_edist_iff.mp ht).2.2
      have hw : w ∈ G.commonNeighbors u v := G.mem_commonNeighbors.mpr ⟨huw, hvw⟩
      rw [he] at hw
      exact Set.notMem_empty w hw

private theorem OMA.four_cycle_forced_adj {V : Type*} {G : SimpleGraph V}
    {v c α x c' : V} (hFar : ¬ Erdos934.HasFarEdges G 3)
    (hvc : G.Adj v c) (hαx : G.Adj α x)
    (hvα : v ≠ α ∧ ¬ G.Adj v α ∧ G.commonNeighbors v α = ∅)
    (hvx : v ≠ x ∧ ¬ G.Adj v x ∧ G.commonNeighbors v x = ∅)
    (hcα : c ≠ α ∧ ¬ G.Adj c α ∧ G.commonNeighbors c α = ∅)
    (hcx : c ≠ x ∧ ¬ G.Adj c x) (hunique : G.commonNeighbors c x ⊆ {c'}) :
    G.Adj c' x := by
  have hlt : G.edist c x < (3 : ℕ∞) := by
    by_contra! hge
    apply hFar
    refine ⟨v, c, α, x, hvc, hαx, ?_⟩
    intro u hu w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hw
    rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
    · exact OMA.three_le_edist_of_no_common hvα
    · exact OMA.three_le_edist_of_no_common hvx
    · exact OMA.three_le_edist_of_no_common hcα
    · exact hge
  rcases OMA.edist_lt_three_iff.mp hlt with he | ha | ⟨w, hcw, hxw⟩
  · exact (hcx.1 he).elim
  · exact (hcx.2 ha).elim
  · have hw : w ∈ G.commonNeighbors c x := G.mem_commonNeighbors.mpr ⟨hcw, hxw⟩
    have he : w = c' := Set.mem_singleton_iff.mp (hunique hw)
    exact he ▸ hxw.symm

namespace CubicEdgeLayers

variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem edge_count_at_least_twenty_four
    (hd : ∀ x, G.degree x ≤ 3) (h : ¬ Erdos934.HasFarEdges G 3)
    (hn : 23 ≤ G.edgeFinset.card) : 24 ≤ G.edgeFinset.card := by
  let S := Finset.univ.filter (fun x => 0 < G.degree x)
  have hdeg (x : V) (hx : x ∈ S) : G.degree x = 3 := by
    have hp := (Finset.mem_filter.mp hx).2
    rw [← G.card_neighborFinset_eq_degree] at hp
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hp
    exact degree_three_of_incident G ((G.mem_neighborFinset _ _).mp hy) hd h hn
  have hsum : ∑ x, G.degree x = 3 * S.card := by
    rw [← Finset.sum_subset (Finset.subset_univ S) (fun x _ hx =>
      Nat.eq_zero_of_not_pos (fun hx' => hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'⟩)))]
    rw [Finset.sum_congr rfl hdeg]
    simp [mul_comm]
  have hhand := G.sum_degrees_eq_twice_card_edges
  omega

omit [Fintype V] in
private theorem internal_edge_count_pos (S : Finset V) {a b : V}
    (ha : a ∈ S) (hb : b ∈ S) (hab : G.Adj a b) :
    1 ≤ ∑ x ∈ S, (ascending G S x).card := by
  have step {x y : V} (hx : x ∈ S) (hy : y ∈ S) (hxy : G.Adj x y) (hlt : x < y) :
      1 ≤ ∑ z ∈ S, (ascending G S z).card := by
    have hmem : y ∈ ascending G S x := Finset.mem_filter.mpr ⟨hy,hxy,hlt⟩
    have hpos : 1 ≤ (ascending G S x).card := Finset.card_pos.mpr ⟨y,hmem⟩
    exact hpos.trans (Finset.single_le_sum (f := fun z => (ascending G S z).card) (fun _ _ => Nat.zero_le _) hx)
  rcases lt_or_gt_of_ne hab.ne with hlt | hlt
  · exact step ha hb hab hlt
  · exact step hb ha hab.symm hlt

private theorem cubic_neighbors_besides_one {x a : V} (hxa : G.Adj x a) (hdeg : G.degree x = 3) :
    ∃ b c, b ≠ c ∧ b ≠ a ∧ c ≠ a ∧ G.Adj x b ∧ G.Adj x c := by
  have hc : ((G.neighborFinset x).erase a).card = 2 := by
    rw [erase_roots_card G x a hxa, hdeg]
  obtain ⟨b,c,hbc,heq⟩ := Finset.card_eq_two.mp hc
  have hb : b ∈ (G.neighborFinset x).erase a := by rw [heq]; simp
  have hc' : c ∈ (G.neighborFinset x).erase a := by rw [heq]; simp
  obtain ⟨hba,hbN⟩ := Finset.mem_erase.mp hb
  obtain ⟨hca,hcN⟩ := Finset.mem_erase.mp hc'
  exact ⟨b,c,hbc,hba,hca,(G.mem_neighborFinset _ _).mp hbN,(G.mem_neighborFinset _ _).mp hcN⟩

private theorem cubic_neighbors_besides_two {x a b : V}
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hab : a ≠ b) (hdeg : G.degree x = 3) :
    ∃ c, G.Adj x c ∧ c ≠ a ∧ c ≠ b ∧ ∀ y, G.Adj x y → y = a ∨ y = b ∨ y = c := by
  have hb : b ∈ (G.neighborFinset x).erase a :=
    Finset.mem_erase.mpr ⟨hab.symm, (G.mem_neighborFinset _ _).mpr hxb⟩
  have hN : (((G.neighborFinset x).erase a).erase b).card = 1 := by
    rw [Finset.card_erase_of_mem hb, erase_roots_card G x a hxa, hdeg]
  obtain ⟨c,hc⟩ := Finset.card_eq_one.mp hN
  have hcm : c ∈ ((G.neighborFinset x).erase a).erase b := by rw [hc]; simp
  obtain ⟨hcb,hcm'⟩ := Finset.mem_erase.mp hcm
  obtain ⟨hca,hcN⟩ := Finset.mem_erase.mp hcm'
  refine ⟨c, (G.mem_neighborFinset _ _).mp hcN, hca, hcb, ?_⟩
  intro y hy
  by_cases hya : y = a
  · exact Or.inl hya
  by_cases hyb : y = b
  · exact Or.inr (Or.inl hyb)
  have hym : y ∈ ((G.neighborFinset x).erase a).erase b :=
    Finset.mem_erase.mpr ⟨hyb,Finset.mem_erase.mpr ⟨hya,(G.mem_neighborFinset _ _).mpr hy⟩⟩
  rw [hc] at hym
  exact Or.inr (Or.inr (Finset.mem_singleton.mp hym))

end CubicEdgeLayers

namespace CubicEdgeLayers

variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem no_four_cycle_of_many_edges {u v c d : V}
    (huv : G.Adj u v) (hvc : G.Adj v c) (hcd : G.Adj c d) (hdu : G.Adj d u)
    (hcu : c ≠ u) (hdv : d ≠ v)
    (hd : ∀ x, G.degree x ≤ 3) (hfar : ¬ Erdos934.HasFarEdges G 3)
    (hm : 23 ≤ G.edgeFinset.card) : False := by
  let R := ({u,v} : Finset V)
  let S := firstLayer G u v
  let T := secondLayer G u v
  let O := outsideLayers G u v
  have huR : u ∈ R := by simp [R]
  have hvR : v ∈ R := by simp [R]
  have htriangle {a b c₀ : V} (hab : G.Adj a b) (hac : G.Adj a c₀)
      (hbc : G.Adj b c₀) : False := by
    have h := triangle_bounds_edges G hab hac hbc hd hfar
    omega
  have hdeg {x y : V} (hxy : G.Adj x y) : G.degree x = 3 :=
    degree_three_of_incident G hxy hd hfar hm
  have hm' := edge_count_at_least_twenty_four G hd hfar hm
  obtain ⟨hcS,hdS⟩ := four_cycle_opposite_mem_firstLayer G hvc hdu hcu hdv
  have hK := internal_edge_count_pos G S hcS hdS hcd
  obtain ⟨hKone,hstubs,hTcard,_,_⟩ := (first_layer_counting G huv hd hfar).2 hm' hK
  have hTsum : T.card = ∑ a ∈ S, (secondOut G u v a).card := hTcard.trans hstubs.symm
  have hTin {x : V} (hx : x ∈ T) : x ∉ R ∧ x ∉ S :=
    ⟨((mem_secondLayer_iff G).1 hx).1, ((mem_secondLayer_iff G).1 hx).2.1⟩
  have hRnoT {r x : V} (hr : r ∈ R) (hx : x ∈ T) : ¬ G.Adj r x := by
    intro hAdj
    have hr' : r = u ∨ r = v := by simpa [R] using hr
    rcases hr' with rfl | rfl
    · exact (hTin hx).2 ((mem_firstLayer_iff G).2 ⟨(hTin hx).1, Or.inl hAdj⟩)
    · exact (hTin hx).2 ((mem_firstLayer_iff G).2 ⟨(hTin hx).1, Or.inr hAdj⟩)
  have hsame {x y : V} (hx : x ∈ S) (hy : y ∈ S) (hxy : G.Adj x y) :
      s(x,y) = s(c,d) :=
    internal_edge_eq_of_ascending_sum_le_one G S hx hy hcS hdS hxy hcd hKone.le
  obtain ⟨a,hua,hav,had,_⟩ := cubic_neighbors_besides_two G huv hdu.symm hdv.symm (hdeg huv)
  have hva : ¬ G.Adj v a := fun h => htriangle huv hua h
  have hac : a ≠ c := fun h => hva (h.symm ▸ hvc)
  have haR : a ∉ R := by simp [R, hua.ne.symm, hav]
  have haS : a ∈ S := (mem_firstLayer_iff G).2 ⟨haR,Or.inl hua⟩
  obtain ⟨a₀,a₁,ha₀₁,ha₀u,ha₁u,haa₀,haa₁⟩ := cubic_neighbors_besides_one G hua.symm (hdeg hua.symm)
  have child_in_second {x : V} (hax : G.Adj a x) (hxu : x ≠ u) : x ∈ T := by
    have hxR : x ∉ R := by
      have hxv : x ≠ v := fun he => hva (he ▸ hax.symm)
      simp [R,hxu,hxv]
    have hxS : x ∉ S := by
      intro h
      have hs := hsame haS h hax
      have hmem : a ∈ s(c,d) := by rw [← hs]; simp [Sym2.mem_iff]
      exact (Sym2.mem_iff.mp hmem).elim hac had
    exact (mem_secondLayer_iff G).2 ⟨hxR,hxS,a,haS,hax⟩
  have ha₀T := child_in_second haa₀ ha₀u
  have ha₁T := child_in_second haa₁ ha₁u
  obtain ⟨c',hcc',hc'v,hc'd,hcNeigh⟩ :=
    cubic_neighbors_besides_two G hvc.symm hcd hdv.symm (hdeg hcd)
  have hc'u : c' ≠ u := fun h => htriangle huv (h ▸ hcc'.symm) hvc
  have hc'R : c' ∉ R := by simp [R,hc'u,hc'v]
  have hc'S : c' ∉ S := by
    intro h
    have hs := hsame hcS h hcc'
    have hmem : c' ∈ s(c,d) := by rw [← hs]; simp [Sym2.mem_iff]
    exact (Sym2.mem_iff.mp hmem).elim hcc'.ne.symm hc'd
  have hc'T : c' ∈ T := (mem_secondLayer_iff G).2 ⟨hc'R,hc'S,c,hcS,hcc'⟩
  have hCnear {x : V} (hx : x ∈ T) (hax : G.Adj a x) : ¬ G.Adj c x := by
    intro hcx
    exact hac (unique_first_parent_of_saturation G hTsum hx haS hcS hax hcx)
  have child_neighbors {x y : V} (hx : x ∈ T) (hax : G.Adj a x) (hxy : G.Adj x y) :
      y = a ∨ O y := by
    by_cases hyS : y ∈ S
    · exact Or.inl (unique_first_parent_of_saturation G hTsum hx hyS haS hxy.symm hax)
    · exact Or.inr ⟨fun hyR => hRnoT hyR hx hxy.symm, hyS,
        fun hyT => saturated_second_independent G huv hd hfar hm' hK hx hyT hxy⟩
  have hVnear {y : V} (hy : G.Adj v y) : y ∈ R ∨ y ∈ S := by
    by_cases hyR : y ∈ R
    · exact Or.inl hyR
    · exact Or.inr ((mem_firstLayer_iff G).2 ⟨hyR,Or.inr hy⟩)
  have force {x y : V} (hx : x ∈ T) (hax : G.Adj a x) (hxy : G.Adj x y) (hy : O y) :
      G.Adj c' y := by
    have hyN {z : V} (hyz : G.Adj y z) : z ∈ T :=
      outside_only_adj_second G hfar huv hy hyz
    have hvx : v ≠ x ∧ ¬ G.Adj v x ∧ G.commonNeighbors v x = ∅ := by
      refine ⟨fun h => (hTin hx).1 (h ▸ hvR), hRnoT hvR hx, ?_⟩
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨hvz,hxz⟩ := G.mem_commonNeighbors.mp hz
      rcases child_neighbors hx hax hxz with rfl | hzo
      · exact hva hvz
      · exact (hVnear hvz).elim hzo.1 hzo.2.1
    have hvy : v ≠ y ∧ ¬ G.Adj v y ∧ G.commonNeighbors v y = ∅ := by
      refine ⟨fun h => hy.1 (h ▸ hvR), fun h => (hTin (hyN h.symm)).1 hvR, ?_⟩
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨hvz,hyz⟩ := G.mem_commonNeighbors.mp hz
      exact (hVnear hvz).elim (hTin (hyN hyz)).1 (hTin (hyN hyz)).2
    have hcx : c ≠ x ∧ ¬ G.Adj c x ∧ G.commonNeighbors c x = ∅ := by
      refine ⟨fun h => (hTin hx).2 (h ▸ hcS), hCnear hx hax, ?_⟩
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨hcz,hxz⟩ := G.mem_commonNeighbors.mp hz
      rcases child_neighbors hx hax hxz with rfl | hzo
      · rcases hcNeigh _ hcz with h | h | h
        · exact hav h
        · exact had h
        · exact hc'S (h ▸ haS)
      · rcases hcNeigh _ hcz with rfl | rfl | rfl
        · exact hzo.1 hvR
        · exact hzo.2.1 hdS
        · exact hzo.2.2 hc'T
    have hcy : c ≠ y ∧ ¬ G.Adj c y :=
      ⟨fun h => hy.2.1 (h ▸ hcS), fun h => (hTin (hyN h.symm)).2 hcS⟩
    have huniq : G.commonNeighbors c y ⊆ ({c'} : Set V) := by
      intro z hz
      obtain ⟨hcz,hyz⟩ := G.mem_commonNeighbors.mp hz
      rcases hcNeigh _ hcz with rfl | rfl | rfl
      · exact False.elim ((hTin (hyN hyz)).1 hvR)
      · exact False.elim ((hTin (hyN hyz)).2 hdS)
      · simp
    exact OMA.four_cycle_forced_adj hfar hvc hxy hvx hvy hcx hcy huniq
  let P := (G.neighborFinset c').erase c
  have hP : P.card = 2 := by
    rw [show P = (G.neighborFinset c').erase c from rfl,
      erase_roots_card G c' c hcc'.symm, hdeg hcc'.symm]
  have same_children {x : V} (hx : x ∈ T) (hax : G.Adj a x) :
      (G.neighborFinset x).erase a = P := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨hya,hyx⟩ := Finset.mem_erase.mp hy
      have hxy := (G.mem_neighborFinset x y).mp hyx
      have hyo := (child_neighbors hx hax hxy).resolve_left hya
      have hc'y := force hx hax hxy hyo
      exact Finset.mem_erase.mpr ⟨fun he => hyo.2.1 (he.symm ▸ hcS),
        (G.mem_neighborFinset c' y).mpr hc'y⟩
    · rw [hP, erase_roots_card G x a hax.symm, hdeg hax.symm]
  have ha₀Children := same_children ha₀T haa₀
  have ha₁Children := same_children ha₁T haa₁
  obtain ⟨x,y,hxy,hPair⟩ := Finset.card_eq_two.mp hP
  have hxP : x ∈ P := by rw [hPair]; simp
  have hyP : y ∈ P := by rw [hPair]; simp
  have hChild {w z : V} (hw : (G.neighborFinset w).erase a = P) (hz : z ∈ P) :
      z ≠ a ∧ G.Adj w z := by
    rw [← hw] at hz
    exact ⟨(Finset.mem_erase.mp hz).1, (G.mem_neighborFinset w z).mp (Finset.mem_of_mem_erase hz)⟩
  obtain ⟨hxa,ha₀x⟩ := hChild ha₀Children hxP
  obtain ⟨hya,ha₀y⟩ := hChild ha₀Children hyP
  obtain ⟨_,ha₁x⟩ := hChild ha₁Children hxP
  obtain ⟨_,ha₁y⟩ := hChild ha₁Children hyP
  have hcount : (∑ z ∈ firstLayer G a a₀, (ascending G (firstLayer G a a₀) z).card) ≤ 1 := by
    have hh := (first_layer_counting G haa₀ hd hfar).1
    change G.edgeFinset.card + 5 * (∑ z ∈ firstLayer G a a₀,
      (ascending G (firstLayer G a a₀) z).card) ≤ 29 at hh
    omega
  have he := four_cycle_opposite_eq_of_ascending_sum_le_one G
    ha₀x ha₁x.symm haa₁.symm hxa ha₀₁.symm ha₀y ha₁y.symm haa₁.symm hya ha₀₁.symm hcount
  have hmem : x ∈ s(y,a₁) := by rw [← he]; simp [Sym2.mem_iff]
  exact (Sym2.mem_iff.mp hmem).elim hxy ha₁x.ne.symm

end CubicEdgeLayers

namespace CubicVertexBound

private lemma edist_step {V : Type} {G : SimpleGraph V} {x y z : V}
    (hxy : G.Adj x y) : G.edist x z ≤ 1 + G.edist y z := by
  simpa only [edist_eq_one_iff_adj.mpr hxy] using
    (G.edist_triangle (u := x) (v := y) (w := z))

private lemma edist_step_right {V : Type} {G : SimpleGraph V} {r x y : V}
    (hxy : G.Adj x y) : G.edist r x ≤ G.edist r y + 1 := by
  simpa only [edist_eq_one_iff_adj.mpr hxy.symm] using
    (G.edist_triangle (u := r) (v := y) (w := x))

private lemma geodesic_step {V : Type} {G : SimpleGraph V} {x z : V} {k : ℕ}
    (h : G.edist x z = ((k + 1 : ℕ) : ℕ∞)) :
    ∃ y, G.Adj x y ∧ G.edist y z = (k : ℕ∞) := by
  obtain ⟨p, hp⟩ := exists_walk_of_edist_eq_coe h
  cases p with
  | nil => simp at hp
  | @cons x y z hxy p =>
    refine ⟨y, hxy, le_antisymm ?_ ?_⟩
    · rw [Walk.length_cons] at hp
      have hlen : p.length = k := by omega
      exact hlen ▸ p.edist_le
    · have he := edist_step (z := z) hxy
      rw [h, Nat.cast_add, Nat.cast_one, add_comm (k : ℕ∞)] at he
      exact (ENat.add_le_add_iff_left (by simp : (1 : ℕ∞) ≠ ⊤)).mp he

private lemma edist_eq_of_le_step {a : ℕ∞} {i : ℕ}
    (ha : a ≤ (i : ℕ∞)) (hb : ((i + 1 : ℕ) : ℕ∞) ≤ a + 1) : a = i := by
  apply le_antisymm ha
  exact (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp
    (by simpa only [Nat.cast_add, Nat.cast_one] using hb)

private lemma edist_eq_previous {a : ℕ∞} {i : ℕ}
    (ha : a < ((i + 1 : ℕ) : ℕ∞)) (hb : ((i + 1 : ℕ) : ℕ∞) ≤ a + 1) : a = i := by
  apply edist_eq_of_le_step _ hb
  exact (ENat.lt_add_one_iff (ENat.natCast_ne_top i)).mp
    (by simpa only [Nat.cast_add, Nat.cast_one] using ha)

section Paths

variable {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)

private noncomputable def layer (i : ℕ) : Finset V := by
  classical
  exact univ.filter fun x => G.edist r x = (i : ℕ∞)

omit [DecidableRel G.Adj] in
private lemma mem_layer {i : ℕ} {x : V} :
    x ∈ layer G r i ↔ G.edist r x = (i : ℕ∞) := by
  simp [layer]

private noncomputable def neighborsAt (x : V) (i : ℕ) : Finset V := by
  classical
  exact (G.neighborFinset x).filter fun y => G.edist r y = (i : ℕ∞)

private lemma mem_neighborsAt {x y : V} {i : ℕ} :
    y ∈ neighborsAt G r x i ↔ G.Adj x y ∧ G.edist r y = (i : ℕ∞) := by
  simp [neighborsAt]

/-- Count walks that advance one layer at every step from the root. -/
private noncomputable def paths (i : ℕ) (x : V) : ℕ := by
  classical
  exact match i with
    | 0 => if x = r then 1 else 0
    | k + 1 => ∑ y ∈ neighborsAt G r x k, paths k y

private lemma paths_succ (i : ℕ) (x : V) :
    paths G r (i + 1) x = ∑ y ∈ neighborsAt G r x i, paths G r i y := by
  rw [paths]

private lemma paths_zero (x : V) (h : G.edist r x = 0) : paths G r 0 x = 1 := by
  have hr := edist_eq_zero_iff.mp h
  subst x
  simp [paths]

private lemma paths_pos (i : ℕ) {x : V} (hx : G.edist r x = (i : ℕ∞)) :
    0 < paths G r i x := by
  induction i generalizing x with
  | zero => simpa only [paths_zero G r x hx] using Nat.one_pos
  | succ i ih =>
    obtain ⟨y, hxy, hy⟩ := geodesic_step ((edist_comm (G := G) (u := x) (v := r)).trans hx)
    have hyr : G.edist r y = i := (edist_comm (G := G) (u := r) (v := y)).trans hy
    have hyMem := (mem_neighborsAt G r).mpr ⟨hxy, hyr⟩
    rw [paths_succ]
    exact (ih hyr).trans_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hyMem)

private lemma predecessors_le_paths (i : ℕ) (x : V) :
    (neighborsAt G r x i).card ≤ paths G r (i + 1) x := by
  rw [paths_succ]
  calc
    _ = ∑ y ∈ neighborsAt G r x i, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum fun _ hy =>
      paths_pos G r i ((mem_neighborsAt G r).mp hy).2

private noncomputable def firstNeighbors (i : ℕ) (x : V) : Finset V := by
  classical
  exact (G.neighborFinset r).filter fun u => G.edist u x = (i : ℕ∞)

private lemma mem_firstNeighbors {i : ℕ} {x u : V} :
    u ∈ firstNeighbors G r i x ↔ G.Adj r u ∧ G.edist u x = (i : ℕ∞) := by
  simp [firstNeighbors]

private lemma firstNeighbors_le_paths (i : ℕ) {x : V} (hx : G.edist r x = ((i + 1 : ℕ) : ℕ∞)) :
    (firstNeighbors G r i x).card ≤ paths G r (i + 1) x := by
  classical
  induction i generalizing x with
  | zero =>
    have hsub : firstNeighbors G r 0 x ⊆ {x} := by
      intro u hu
      exact Finset.mem_singleton.mpr (edist_eq_zero_iff.mp ((mem_firstNeighbors G r).mp hu).2)
    exact (Finset.card_le_card hsub).trans (by simpa only [Finset.card_singleton] using Nat.succ_le_of_lt (paths_pos G r 1 hx))
  | succ i ih =>
    have hsub : firstNeighbors G r (i + 1) x ⊆
        (neighborsAt G r x (i + 1)).biUnion (firstNeighbors G r i) := by
      intro u hu
      obtain ⟨hru, hux⟩ := (mem_firstNeighbors G r).mp hu
      obtain ⟨y, hxy, hyu⟩ := geodesic_step ((edist_comm (G := G) (u := x) (v := u)).trans hux)
      have hry : G.edist r y ≤ ((i + 1 : ℕ) : ℕ∞) := by
        simpa only [edist_eq_one_iff_adj.mpr hru, (edist_comm (G := G) (u := u) (v := y)).trans hyu,
          Nat.cast_add, Nat.cast_one, add_comm (1 : ℕ∞)] using
          (G.edist_triangle (u := r) (v := u) (w := y))
      have hyr : G.edist r y = ((i + 1 : ℕ) : ℕ∞) :=
        edist_eq_of_le_step hry (hx ▸ edist_step_right (r := r) hxy)
      exact Finset.mem_biUnion.mpr ⟨y, (mem_neighborsAt G r).mpr ⟨hxy, hyr⟩,
        (mem_firstNeighbors G r).mpr ⟨hru, (edist_comm (G := G) (u := u) (v := y)).trans hyu⟩⟩
    rw [paths_succ]
    exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans
      (Finset.sum_le_sum fun _ hy => ih ((mem_neighborsAt G r).mp hy).2))

end Paths

section Boundary

variable {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)

omit [Fintype V] [DecidableRel G.Adj] in
private lemma first_neighbor_close {k : ℕ} {u x y : V}
    (h : ¬ Erdos934.HasFarEdges G (k + 1)) (hru : G.Adj r u) (hxy : G.Adj x y)
    (hx : ((k + 1 : ℕ) : ℕ∞) ≤ G.edist r x) (hy : ((k + 1 : ℕ) : ℕ∞) ≤ G.edist r y) :
    G.edist u x < ((k + 1 : ℕ) : ℕ∞) ∨ G.edist u y < ((k + 1 : ℕ) : ℕ∞) := by
  by_contra! hh
  apply h
  refine ⟨r, u, x, y, hru, hxy, ?_⟩
  intro a ha b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact hx
  · exact hy
  · exact hh.1
  · exact hh.2

omit [Fintype V] [DecidableRel G.Adj] in
private lemma root_close_of_first_close {k : ℕ} {u x : V} (hru : G.Adj r u)
    (hux : G.edist u x < ((k + 1 : ℕ) : ℕ∞)) :
    G.edist r x ≤ ((k + 1 : ℕ) : ℕ∞) := by
  have hu : G.edist u x ≤ (k : ℕ∞) := ENat.lt_natCast_add_one_iff.mp
    (by simpa only [Nat.cast_add, Nat.cast_one] using hux)
  calc
    _ ≤ 1 + G.edist u x := edist_step hru
    _ ≤ 1 + (k : ℕ∞) := by gcongr
    _ = _ := by simp only [Nat.cast_add, Nat.cast_one, add_comm]

omit [Fintype V] [DecidableRel G.Adj] in
private lemma every_edge_near_root {k : ℕ} {x y : V}
    (h : ¬ Erdos934.HasFarEdges G (k + 1)) (hr : ∃ u, G.Adj r u) (hxy : G.Adj x y) :
    G.edist r x ≤ ((k + 1 : ℕ) : ℕ∞) ∨ G.edist r y ≤ ((k + 1 : ℕ) : ℕ∞) := by
  obtain ⟨u, hu⟩ := hr
  by_contra! hh
  rcases first_neighbor_close G r h hu hxy hh.1.le hh.2.le with hc | hc
  · exact hh.1.not_ge (root_close_of_first_close G r hu hc)
  · exact hh.2.not_ge (root_close_of_first_close G r hu hc)

private lemma root_neighbors_covered [DecidableEq V] {k : ℕ} {x y : V}
    (h : ¬ Erdos934.HasFarEdges G (k + 1)) (hxy : G.Adj x y)
    (hx : ((k + 1 : ℕ) : ℕ∞) ≤ G.edist r x) (hy : ((k + 1 : ℕ) : ℕ∞) ≤ G.edist r y) :
    G.neighborFinset r ⊆ firstNeighbors G r k x ∪ firstNeighbors G r k y := by
  intro u hu
  have hru := (G.mem_neighborFinset r u).mp hu
  have eqdist {v : V} (hv : ((k + 1 : ℕ) : ℕ∞) ≤ G.edist r v)
      (huv : G.edist u v < ((k + 1 : ℕ) : ℕ∞)) : G.edist u v = (k : ℕ∞) :=
    edist_eq_previous huv (by simpa only [add_comm] using hv.trans (edist_step hru))
  rcases first_neighbor_close G r h hru hxy hx hy with hc | hc
  · exact Finset.mem_union_left _ ((mem_firstNeighbors G r).mpr ⟨hru, eqdist hx hc⟩)
  · exact Finset.mem_union_right _ ((mem_firstNeighbors G r).mpr ⟨hru, eqdist hy hc⟩)

private lemma boundary_cover [DecidableEq V] {k : ℕ} {x y : V}
    (h : ¬ Erdos934.HasFarEdges G (k + 1)) (hxy : G.Adj x y)
    (hx : G.edist r x = ((k + 1 : ℕ) : ℕ∞)) (hy : G.edist r y = ((k + 1 : ℕ) : ℕ∞)) :
    G.degree r ≤ paths G r (k + 1) x + paths G r (k + 1) y := by
  rw [← G.card_neighborFinset_eq_degree]
  exact (Finset.card_le_card (root_neighbors_covered G r h hxy hx.ge hy.ge)).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add
      (firstNeighbors_le_paths G r k hx) (firstNeighbors_le_paths G r k hy)))

private lemma boundary_to_outside [DecidableEq V] {k : ℕ} {x y : V}
    (h : ¬ Erdos934.HasFarEdges G (k + 1)) (hxy : G.Adj x y)
    (hx : G.edist r x = ((k + 1 : ℕ) : ℕ∞)) (hy : ((k + 1 : ℕ) : ℕ∞) < G.edist r y) :
    G.degree r ≤ paths G r (k + 1) x := by
  have hempty : firstNeighbors G r k y = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    obtain ⟨hru,huy⟩ := (mem_firstNeighbors G r).mp hu
    have hnear : G.edist u y < ((k + 1 : ℕ) : ℕ∞) := by
      rw [huy]
      exact ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self k)
    exact hy.not_ge (root_close_of_first_close G r hru hnear)
  have hs := root_neighbors_covered G r h hxy hx.ge hy.le
  rw [hempty, Finset.union_empty] at hs
  rw [← G.card_neighborFinset_eq_degree]
  exact (Finset.card_le_card hs).trans (firstNeighbors_le_paths G r k hx)

end Boundary


section Cubic

variable {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)

private abbrev NoFourCycle (G : SimpleGraph V) : Prop :=
  ∀ {a b x y}, a ≠ b → x ≠ y →
    G.Adj a x → G.Adj b x → G.Adj a y → G.Adj b y → False

private abbrev NoTriangle (G : SimpleGraph V) : Prop :=
  ∀ {a b c}, G.Adj a b → G.Adj a c → G.Adj b c → False

omit [DecidableRel G.Adj] in
private lemma layer_zero : layer G r 0 = {r} := by
  classical
  ext x
  simp only [mem_layer, Nat.cast_zero, edist_eq_zero_iff, Finset.mem_singleton]
  exact eq_comm

private lemma layer_one : layer G r 1 = G.neighborFinset r := by
  classical
  ext x
  simp [mem_layer, edist_eq_one_iff_adj]

private lemma neighbors_layer_eq_filter (x : V) (i : ℕ) :
    neighborsAt G r x i = (layer G r i).filter (G.Adj x) := by
  ext y
  simp [mem_neighborsAt, mem_layer, and_comm]

private lemma paths_one_eq {x : V} (hx : G.edist r x = 1) : paths G r 1 x = 1 := by
  classical
  have hN : neighborsAt G r x 0 = {r} := by
    rw [neighbors_layer_eq_filter, layer_zero]
    simp [(edist_eq_one_iff_adj.mp hx).symm]
  rw [show (1 : ℕ) = 0 + 1 by rfl, paths_succ, hN, Finset.sum_singleton]
  exact paths_zero G r r (by simp)

private lemma paths_two_eq (h4 : NoFourCycle G) {x : V} (hx : G.edist r x = 2) :
    paths G r 2 x = 1 := by
  classical
  have hxr : x ≠ r := by
    rintro rfl
    simp at hx
  have hcard : (neighborsAt G r x 1).card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro y z hy hz
    obtain ⟨hyx,hry⟩ := (mem_neighborsAt G r).mp hy
    obtain ⟨hzx,hrz⟩ := (mem_neighborsAt G r).mp hz
    by_contra hyz
    exact h4 hxr hyz hyx (edist_eq_one_iff_adj.mp hry) hzx (edist_eq_one_iff_adj.mp hrz)
  have hpos := paths_pos G r 2 hx
  have heq : paths G r 2 x = (neighborsAt G r x 1).card := by
    rw [show (2 : ℕ) = 1 + 1 by rfl, paths_succ, Finset.card_eq_sum_ones]
    exact Finset.sum_congr rfl (fun y hy => paths_one_eq G r ((mem_neighborsAt G r).mp hy).2)
  omega

private lemma paths_three_eq (h4 : NoFourCycle G) (x : V) :
    paths G r 3 x = (neighborsAt G r x 2).card := by
  rw [show (3 : ℕ) = 2 + 1 by rfl, paths_succ, Finset.card_eq_sum_ones]
  exact Finset.sum_congr rfl (fun y hy => paths_two_eq G r h4 ((mem_neighborsAt G r).mp hy).2)

private lemma first_three_layers (h4 : NoFourCycle G) (h3 : NoTriangle G)
    (reg : ∀ x : V, (∃ y, G.Adj x y) → G.degree x = 3) (hr : ∃ x, G.Adj r x) :
    (layer G r 0).card = 1 ∧ (layer G r 1).card = 3 ∧ (layer G r 2).card = 6 := by
  classical
  refine ⟨by rw [layer_zero, Finset.card_singleton], by rw [layer_one, G.card_neighborFinset_eq_degree, reg r hr], ?_⟩
  have hdecomp : layer G r 2 = (G.neighborFinset r).biUnion (fun x => (G.neighborFinset x).erase r) := by
    ext y
    constructor
    · intro hy
      have hy' : G.edist r y = 2 := (mem_layer G r).mp hy
      obtain ⟨x,hrx,hxy⟩ := geodesic_step (G := G) (k := 1) hy'
      exact Finset.mem_biUnion.mpr ⟨x,(G.mem_neighborFinset r x).mpr hrx,
        Finset.mem_erase.mpr ⟨by
          rintro rfl
          simp at hy', (G.mem_neighborFinset x y).mpr (edist_eq_one_iff_adj.mp hxy)⟩⟩
    · intro hy
      obtain ⟨x,hx,hy⟩ := Finset.mem_biUnion.mp hy
      obtain ⟨hyn,hy⟩ := Finset.mem_erase.mp hy
      have hrx := (G.mem_neighborFinset r x).mp hx
      have hxy := (G.mem_neighborFinset x y).mp hy
      have hno : ¬ G.Adj r y := fun h => h3 hrx h hxy
      have hle : G.edist r y ≤ 2 := by
        calc
          _ ≤ 1 + G.edist x y := edist_step hrx
          _ = 2 := by rw [edist_eq_one_iff_adj.mpr hxy]; rfl
      obtain ⟨n,hn⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt (hle.trans_lt (ENat.natCast_lt_top 2)))
      have hnle : n ≤ 2 := by rw [← hn] at hle; exact_mod_cast hle
      have hnpos : n ≠ 0 := by
        intro h
        subst n
        exact hyn (edist_eq_zero_iff.mp hn.symm).symm
      have hnne : n ≠ 1 := by
        intro h
        subst n
        exact hno (edist_eq_one_iff_adj.mp hn.symm)
      have hn' : n = 2 := by omega
      exact (mem_layer G r).mpr (by simpa only [hn'] using hn.symm)
  have hp : ((G.neighborFinset r : Finset V) : Set V).PairwiseDisjoint
      (fun x => (G.neighborFinset x).erase r) := by
    intro x hx z hz hxz
    apply Finset.disjoint_left.mpr
    intro y hxy hzy
    obtain ⟨hy,hxy⟩ := Finset.mem_erase.mp hxy
    have hzy' := Finset.mem_of_mem_erase hzy
    exact h4 hy.symm hxz ((G.mem_neighborFinset r x).mp hx) ((G.mem_neighborFinset x y).mp hxy).symm
      ((G.mem_neighborFinset r z).mp hz) ((G.mem_neighborFinset z y).mp hzy').symm
  have htwo (x : V) (hx : x ∈ G.neighborFinset r) : ((G.neighborFinset x).erase r).card = 2 := by
    have hrx := (G.mem_neighborFinset r x).mp hx
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset x r).mpr hrx.symm),
      G.card_neighborFinset_eq_degree, reg x ⟨r,hrx.symm⟩]
  rw [hdecomp, Finset.card_biUnion hp]
  simp only [Finset.sum_congr rfl htwo, Finset.sum_const, Nat.nsmul_eq_mul,
    G.card_neighborFinset_eq_degree, reg r hr]

private lemma support_within_three (h4 : NoFourCycle G)
    (hfar : ¬ Erdos934.HasFarEdges G 3)
    (hdeg : ∀ x, G.degree x ≤ 3) (hr : G.degree r = 3) :
    ∀ {x : V}, (∃ y, G.Adj x y) → G.edist r x ≤ 3 := by
  classical
  intro x hx
  by_contra! hbad
  obtain ⟨y,hxy⟩ := hx
  have hr' : ∃ y, G.Adj r y := by
    have hnon : (G.neighborFinset r).Nonempty := by
      apply Finset.card_pos.mp
      rw [G.card_neighborFinset_eq_degree,hr]
      decide
    obtain ⟨z,hz⟩ := hnon
    exact ⟨z,(G.mem_neighborFinset r z).mp hz⟩
  have hy : G.edist r y ≤ 3 := (every_edge_near_root G r (k := 2) hfar hr' hxy).resolve_left (not_le.mpr hbad)
  have he : G.edist r y = 3 := by
    apply edist_eq_of_le_step (i := 3) hy
    have hh : (4 : ℕ∞) ≤ G.edist r x := by
      by_contra! h
      exact hbad.not_ge ((ENat.lt_natCast_add_one_iff (n := 3)).mp h)
    exact hh.trans (edist_step_right (r := r) hxy)
  have hpaths := boundary_to_outside G r (k := 2) hfar hxy.symm he hbad
  rw [hr, paths_three_eq G r h4] at hpaths
  have hsub : neighborsAt G r y 2 ⊆ (G.neighborFinset y).erase x := by
    intro z hz
    obtain ⟨hyz,hrz⟩ := (mem_neighborsAt G r).mp hz
    refine Finset.mem_erase.mpr ⟨?_, (G.mem_neighborFinset y z).mpr hyz⟩
    rintro rfl
    rw [hrz] at hbad
    norm_num at hbad
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem ((G.mem_neighborFinset y x).mpr hxy.symm),
    G.card_neighborFinset_eq_degree] at hcard
  specialize hdeg y
  omega

omit [DecidableRel G.Adj] in
private lemma layer_positive_support {i : ℕ} (hi : 0 < i) {x : V}
    (hx : x ∈ layer G r i) : ∃ y, G.Adj x y := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  have hx' : G.edist x r = ((j + 1 : ℕ) : ℕ∞) := by rw [edist_comm]; exact (mem_layer G r).mp hx
  obtain ⟨y,hy,_⟩ := geodesic_step (G := G) hx'
  exact ⟨y,hy⟩

end Cubic


section Counting

variable {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)

private lemma neighbors_third_layer {x z : V} (hx : x ∈ layer G r 3)
    (hxz : G.Adj x z) (hz : G.edist r z ≤ 3) :
    z ∈ neighborsAt G r x 2 ∨ z ∈ neighborsAt G r x 3 := by
  have hlow := (mem_layer G r).mp hx ▸ edist_step_right (r := r) hxz
  obtain ⟨j,hj⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt (hz.trans_lt (ENat.natCast_lt_top 3)))
  rw [← hj] at hlow hz
  have h1 : 3 ≤ j+1 := by exact_mod_cast hlow
  have h2 : j ≤ 3 := by exact_mod_cast hz
  have hc : j = 2 ∨ j = 3 := by omega
  rcases hc with rfl | rfl
  · exact Or.inl ((mem_neighborsAt G r).mpr ⟨hxz,hj.symm⟩)
  · exact Or.inr ((mem_neighborsAt G r).mpr ⟨hxz,hj.symm⟩)

private lemma third_degrees (h4 : NoFourCycle G) (hfar : ¬ Erdos934.HasFarEdges G 3)
    (reg : ∀ x : V, (∃ y, G.Adj x y) → G.degree x = 3) (hr : G.degree r = 3)
    {x : V} (hx : x ∈ layer G r 3) :
    0 < (neighborsAt G r x 2).card ∧
      (neighborsAt G r x 2).card + (neighborsAt G r x 3).card = 3 := by
  classical
  have hdeg (y : V) : G.degree y ≤ 3 := by
    by_cases hy : ∃ z, G.Adj y z
    · rw [reg _ hy]
    · rw [← G.card_neighborFinset_eq_degree]
      have he : G.neighborFinset y = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        exact fun z hz => hy ⟨z,(G.mem_neighborFinset y z).mp hz⟩
      rw [he, Finset.card_empty]
      decide
  have hn : ∀ {y : V}, (∃ z, G.Adj y z) → G.edist r y ≤ 3 :=
    support_within_three G r h4 hfar hdeg hr
  have hU : neighborsAt G r x 2 ∪ neighborsAt G r x 3 = G.neighborFinset x := by
    ext z
    constructor
    · intro hz
      apply (G.mem_neighborFinset x z).mpr
      rcases Finset.mem_union.mp hz with hz | hz
      · exact ((mem_neighborsAt G r).mp hz).1
      · exact ((mem_neighborsAt G r).mp hz).1
    · intro hz
      have hxz := (G.mem_neighborFinset x z).mp hz
      exact Finset.mem_union.mpr (neighbors_third_layer G r hx hxz (hn ⟨x,hxz.symm⟩))
  have hDis : Disjoint (neighborsAt G r x 2) (neighborsAt G r x 3) := by
    apply Finset.disjoint_left.mpr
    intro z hz2 hz3
    have hrz2 := ((mem_neighborsAt G r).mp hz2).2
    have hrz3 := ((mem_neighborsAt G r).mp hz3).2
    have he : (2 : ℕ∞) = 3 := hrz2.symm.trans hrz3
    norm_num at he
  have hCount := Finset.card_union_of_disjoint hDis
  rw [hU, G.card_neighborFinset_eq_degree, reg x (layer_positive_support G r (by decide) hx)] at hCount
  have hp := paths_pos G r 3 ((mem_layer G r).mp hx)
  rw [paths_three_eq G r h4] at hp
  exact ⟨hp,hCount.symm⟩

private lemma outward_card_le_two (reg : ∀ x : V, (∃ y, G.Adj x y) → G.degree x = 3)
    {x : V} (hx : x ∈ layer G r 2) : (neighborsAt G r x 3).card ≤ 2 := by
  classical
  have hx' : G.edist x r = 2 := by rw [edist_comm]; exact (mem_layer G r).mp hx
  obtain ⟨z,hxz,hrz⟩ := geodesic_step (G := G) (k := 1) hx'
  have hz : G.edist r z = 1 := by simpa only [edist_comm, Nat.cast_one] using hrz
  have hsub : neighborsAt G r x 3 ⊆ (G.neighborFinset x).erase z := by
    intro y hy
    obtain ⟨hxy,hry⟩ := (mem_neighborsAt G r).mp hy
    refine Finset.mem_erase.mpr ⟨?_,(G.mem_neighborFinset x y).mpr hxy⟩
    rintro rfl
    rw [hz] at hry
    norm_num at hry
  have hcard := Finset.card_le_card hsub
  rwa [Finset.card_erase_of_mem ((G.mem_neighborFinset x z).mpr hxz),
    G.card_neighborFinset_eq_degree, reg x ⟨z,hxz⟩] at hcard

private lemma predecessor_sum_le_twelve
    (hL2 : (layer G r 2).card = 6)
    (reg : ∀ x : V, (∃ y, G.Adj x y) → G.degree x = 3) :
    (∑ x ∈ layer G r 3, (neighborsAt G r x 2).card) ≤ 12 := by
  have hs : (∑ x ∈ layer G r 3, (neighborsAt G r x 2).card) =
      ∑ x ∈ layer G r 2, (neighborsAt G r x 3).card := by
    have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := layer G r 3) (t := layer G r 2) G.Adj
    simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at h
    simp only [neighbors_layer_eq_filter]
    simpa only [SimpleGraph.adj_comm (G := G)] using h
  rw [hs]
  calc
    _ ≤ ∑ _ ∈ layer G r 2, 2 :=
      Finset.sum_le_sum (fun x hx => outward_card_le_two G r reg hx)
    _ = _ := by simp [hL2]

private theorem third_layer_statistics (h4 : NoFourCycle G) (hfar : ¬ Erdos934.HasFarEdges G 3)
    (reg : ∀ x : V, (∃ y, G.Adj x y) → G.degree x = 3) (hr : G.degree r = 3)
    (hL2 : (layer G r 2).card = 6) :
    let L := layer G r 3
    let p (x : V) := (neighborsAt G r x 2).card
    let T (i : ℕ) := L.filter fun x => p x = i
    L.card = (T 1).card + (T 2).card + (T 3).card ∧
      2 * (T 1).card ≤ (T 2).card ∧
      (∑ x ∈ L, p x) = (T 1).card * 1 + (T 2).card * 2 + (T 3).card * 3 := by
  classical
  let L := layer G r 3
  let p (x : V) := (neighborsAt G r x 2).card
  let T (i : ℕ) := L.filter fun x => p x = i
  have hp {x : V} (hx : x ∈ L) : 0 < p x ∧ p x + (neighborsAt G r x 3).card = 3 :=
    third_degrees G r h4 hfar reg hr hx
  have hmem {i : ℕ} {x : V} : x ∈ T i ↔ x ∈ L ∧ p x = i := Finset.mem_filter
  have hbound := predecessor_sum_le_twelve G r hL2 reg
  change (∑ x ∈ L, p x) ≤ 12 at hbound
  have hnear {x y : V} (hx : x ∈ L) (hy : y ∈ L) (hxy : G.Adj x y) : 3 ≤ p x + p y := by
    have h := boundary_cover G r (k := 2) hfar hxy ((mem_layer G r).mp hx) ((mem_layer G r).mp hy)
    rwa [hr, paths_three_eq G r h4, paths_three_eq G r h4] at h
  have hsub {x : V} (hx : x ∈ T 1) : neighborsAt G r x 3 ⊆ T 2 := by
    intro y hy
    obtain ⟨hxy,hry⟩ := (mem_neighborsAt G r).mp hy
    have hyL : y ∈ L := (mem_layer G r).mpr hry
    have hpx := (hmem.mp hx).2
    have hpy := hp hyL
    have hy' : x ∈ neighborsAt G r y 3 := (mem_neighborsAt G r).mpr
      ⟨hxy.symm,(mem_layer G r).mp (hmem.mp hx).1⟩
    have hc : 0 < (neighborsAt G r y 3).card := Finset.card_pos.mpr ⟨x,hy'⟩
    have hn := hnear (hmem.mp hx).1 hyL hxy
    exact hmem.mpr ⟨hyL,by omega⟩
  have hdisj : ((T 1 : Finset V) : Set V).PairwiseDisjoint (fun x => neighborsAt G r x 3) := by
    intro x hx z hz hxz
    apply Finset.disjoint_left.mpr
    intro y hxy hzy
    have hyT := hsub hx hxy
    have hcy := hp (hmem.mp hyT).1
    have hy2 := (hmem.mp hyT).2
    have hsmall : (neighborsAt G r y 3).card ≤ 1 := by omega
    have hxY : x ∈ neighborsAt G r y 3 := (mem_neighborsAt G r).mpr
      ⟨((mem_neighborsAt G r).mp hxy).1.symm, (mem_layer G r).mp (hmem.mp hx).1⟩
    have hzY : z ∈ neighborsAt G r y 3 := (mem_neighborsAt G r).mpr
      ⟨((mem_neighborsAt G r).mp hzy).1.symm, (mem_layer G r).mp (hmem.mp hz).1⟩
    exact hxz (Finset.card_le_one_iff.mp hsmall hxY hzY)
  have htwocards : 2 * (T 1).card ≤ (T 2).card := by
    have hU : (T 1).biUnion (fun x => neighborsAt G r x 3) ⊆ T 2 := by
      intro y hy
      obtain ⟨x,hx,hy⟩ := Finset.mem_biUnion.mp hy
      exact hsub hx hy
    have hcard := Finset.card_le_card hU
    rw [Finset.card_biUnion hdisj] at hcard
    have hh : (∑ x ∈ T 1, (neighborsAt G r x 3).card) = (T 1).card * 2 := by
      apply Finset.sum_const_nat
      intro x hx
      have hn := hp (hmem.mp hx).1
      have h1 := (hmem.mp hx).2
      omega
    omega
  have hU : T 1 ∪ T 2 ∪ T 3 = L := by
    ext x
    simp only [Finset.mem_union, hmem]
    constructor
    · tauto
    · intro hx
      have h := hp hx
      have hh : p x = 1 ∨ p x = 2 ∨ p x = 3 := by omega
      tauto
  have hD {i j : ℕ} (hij : i ≠ j) : Disjoint (T i) (T j) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact hij ((hmem.mp hx).2.symm.trans (hmem.mp hy).2)
  have hD' : Disjoint (T 1 ∪ T 2) (T 3) :=
    Finset.disjoint_union_left.mpr ⟨hD (by decide),hD (by decide)⟩
  have hcount : L.card = (T 1).card + (T 2).card + (T 3).card := by
    rw [← hU,Finset.card_union_of_disjoint hD',Finset.card_union_of_disjoint (hD (by decide : (1 : ℕ) ≠ 2))]
  have hsum (k : ℕ) : (∑ x ∈ T k, p x) = (T k).card * k :=
    Finset.sum_const_nat (fun _ hx => (hmem.mp hx).2)
  refine ⟨hcount, htwocards, ?_⟩
  change (∑ x ∈ L, p x) = (T 1).card * 1 + (T 2).card * 2 + (T 3).card * 3
  rw [← hU,Finset.sum_union hD',Finset.sum_union (hD (by decide : (1 : ℕ) ≠ 2))]
  exact congrArg₂ Nat.add (congrArg₂ Nat.add (hsum 1) (hsum 2)) (hsum 3)

private theorem third_layer_at_most_seven (h4 : NoFourCycle G) (hfar : ¬ Erdos934.HasFarEdges G 3)
    (reg : ∀ x : V, (∃ y, G.Adj x y) → G.degree x = 3) (hr : G.degree r = 3)
    (hL2 : (layer G r 2).card = 6) : (layer G r 3).card ≤ 7 := by
  obtain ⟨hc, ht, hs⟩ := third_layer_statistics G r h4 hfar reg hr hL2
  have hb := predecessor_sum_le_twelve G r hL2 reg
  dsimp only at hc ht hs
  omega

end Counting


section SupportCounting

variable {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)

omit [Fintype V] [DecidableRel G.Adj] in
private lemma supported_iff_neighbor {x : V} : x ∈ G.support ↔ ∃ y, G.Adj x y := Iff.rfl

private lemma support_layers [DecidableEq V] (h4 : NoFourCycle G) (hfar : ¬ Erdos934.HasFarEdges G 3)
    (reg : ∀ x : V, (∃ y, G.Adj x y) → G.degree x = 3) (hr : ∃ y, G.Adj r y) :
    G.support.toFinset = (Finset.range 4).biUnion (layer G r) := by
  classical
  have hdeg (y : V) : G.degree y ≤ 3 := by
    by_cases hy : ∃ z, G.Adj y z
    · rw [reg _ hy]
    · rw [← G.card_neighborFinset_eq_degree]
      have he : G.neighborFinset y = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        exact fun z hz => hy ⟨z,(G.mem_neighborFinset y z).mp hz⟩
      rw [he, Finset.card_empty]
      decide
  have hd : ∀ {x : V}, (∃ y, G.Adj x y) → G.edist r x ≤ 3 :=
    support_within_three G r h4 hfar hdeg (reg r hr)
  ext x
  simp only [Set.mem_toFinset, supported_iff_neighbor]
  constructor
  · intro hx
    have hnear := hd hx
    obtain ⟨j,hj⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt (hnear.trans_lt (ENat.natCast_lt_top 3)))
    have hlt : j < 4 := by
      rw [← hj] at hnear
      have hn : j ≤ 3 := by exact_mod_cast hnear
      omega
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_range.mpr hlt,(mem_layer G r).mpr hj.symm⟩
  · intro hx
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hx
    by_cases hz : i = 0
    · subst i
      rw [layer_zero] at hi
      simpa only [Finset.mem_singleton.mp hi] using hr
    · exact layer_positive_support G r (Nat.pos_of_ne_zero hz) hi

private theorem cubic_support_16 (h4 : NoFourCycle G) (h3 : NoTriangle G)
    (hfar : ¬ Erdos934.HasFarEdges G 3)
    (reg : ∀ x : V, (∃ y, G.Adj x y) → G.degree x = 3)
    (hr : ∃ y, G.Adj r y) (hm : 23 ≤ G.edgeFinset.card) :
    G.support.ncard = 16 ∧ (layer G r 3).card = 6 := by
  classical
  obtain ⟨h0,h1,h2⟩ := first_three_layers G r h4 h3 reg hr
  have h7 := third_layer_at_most_seven G r h4 hfar reg (reg r hr) h2
  have hdis : ((Finset.range 4 : Finset ℕ) : Set ℕ).PairwiseDisjoint (layer G r) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro y hy hz
    have h := ((mem_layer G r).mp hy).symm.trans ((mem_layer G r).mp hz)
    exact hij (ENat.natCast_inj.mp h)
  have hcard : G.support.toFinset.card = 10 + (layer G r 3).card := by
    rw [support_layers G r h4 hfar reg hr,Finset.card_biUnion hdis]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0,h1,h2]
  have hsum := G.sum_degrees_support_eq_twice_card_edges
  have hs : (∑ x ∈ G.support.toFinset, G.degree x) = G.support.toFinset.card * 3 := by
    apply Finset.sum_const_nat
    exact fun x hx => reg x (by simpa only [Set.mem_toFinset, supported_iff_neighbor] using hx)
  rw [hs] at hsum
  have hC : G.support.toFinset.card = 16 := by omega
  refine ⟨?_, by omega⟩
  rw [Set.ncard_eq_toFinset_card' G.support]
  exact hC

end SupportCounting


section ThirdShape

variable {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)

private lemma layer_neighbor_partition [DecidableEq V] (h4 : NoFourCycle G) (hfar : ¬ Erdos934.HasFarEdges G 3)
    (hdeg : ∀ x, G.degree x ≤ 3) (hr : G.degree r = 3)
    {i : ℕ} (hi : i = 2 ∨ i = 3) {x : V} (hx : x ∈ layer G r i) :
    neighborsAt G r x (i-1) ∪ neighborsAt G r x i ∪ neighborsAt G r x (i+1) = G.neighborFinset x := by
  classical
  ext y
  simp only [Finset.mem_union,mem_neighborsAt,G.mem_neighborFinset]
  constructor
  · tauto
  · intro hxy
    have hxD := (mem_layer G r).mp hx
    have hdx := edist_step_right (r := r) hxy
    have hdy := edist_step_right (r := r) hxy.symm
    have hy := support_within_three G r h4 hfar hdeg hr ⟨x,hxy.symm⟩
    obtain ⟨j,hj⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt (hy.trans_lt (ENat.natCast_lt_top 3)))
    rw [hxD,← hj] at hdx hdy
    have hj1 : i ≤ j + 1 := by exact_mod_cast hdx
    have hj2 : j ≤ i + 1 := by exact_mod_cast hdy
    have hcases : j = i - 1 ∨ j = i ∨ j = i + 1 := by omega
    rw [← hj]
    rcases hcases with h | h | h
    · exact Or.inl (Or.inl ⟨hxy, congrArg (fun n : ℕ => (n : ℕ∞)) h⟩)
    · exact Or.inl (Or.inr ⟨hxy, congrArg (fun n : ℕ => (n : ℕ∞)) h⟩)
    · exact Or.inr ⟨hxy, congrArg (fun n : ℕ => (n : ℕ∞)) h⟩

private lemma neighborsAt_disjoint (x : V) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (neighborsAt G r x i) (neighborsAt G r x j) := by
  apply Finset.disjoint_left.mpr
  intro y hy hz
  exact hij (ENat.natCast_inj.mp
    (((mem_neighborsAt G r).mp hy).2.symm.trans ((mem_neighborsAt G r).mp hz).2))

private lemma second_degrees (h4 : NoFourCycle G) (hfar : ¬ Erdos934.HasFarEdges G 3)
    (hdeg : ∀ x, G.degree x ≤ 3) (hr : G.degree r = 3)
    (reg : ∀ x : V, (∃ y, G.Adj x y) → G.degree x = 3)
    {x : V} (hx : x ∈ layer G r 2) :
    (neighborsAt G r x 1).card = 1 ∧
      (neighborsAt G r x 2).card + (neighborsAt G r x 3).card = 2 := by
  classical
  have h1 : (neighborsAt G r x 1).card = 1 := by
    have he : paths G r 2 x = (neighborsAt G r x 1).card := by
      rw [show (2 : ℕ) = 1 + 1 by rfl, paths_succ, Finset.card_eq_sum_ones]
      exact Finset.sum_congr rfl (fun y hy => paths_one_eq G r ((mem_neighborsAt G r).mp hy).2)
    rw [← he]
    exact paths_two_eq G r h4 ((mem_layer G r).mp hx)
  have hu : neighborsAt G r x 1 ∪ neighborsAt G r x 2 ∪ neighborsAt G r x 3 =
      G.neighborFinset x := layer_neighbor_partition G r h4 hfar hdeg hr (Or.inl rfl) hx
  have hd := Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
    ⟨neighborsAt_disjoint G r x (by decide : (1 : ℕ) ≠ 3),
      neighborsAt_disjoint G r x (by decide : (2 : ℕ) ≠ 3)⟩)
  rw [hu, Finset.card_union_of_disjoint (neighborsAt_disjoint G r x (by decide : (1 : ℕ) ≠ 2)),
    G.card_neighborFinset_eq_degree, reg x (layer_positive_support G r (by decide) hx), h1] at hd
  exact ⟨h1,by omega⟩

private lemma layer_induced_degree {i : ℕ} [DecidableEq V] (x : (layer G r i : Set V)) :
    (G.induce (layer G r i : Set V)).degree x = (neighborsAt G r x.val i).card := by
  let H := G.induce (layer G r i : Set V)
  change (H.neighborFinset x).card = _
  apply Finset.card_bij (fun y _ => y.val)
  · intro y hy
    have ha := (H.mem_neighborFinset x y).mp hy
    exact (mem_neighborsAt G r).mpr ⟨ha,(mem_layer G r).mp y.property⟩
  · intro y _ z _ hyz
    exact Subtype.ext hyz
  · intro y hy
    obtain ⟨hxy,hry⟩ := (mem_neighborsAt G r).mp hy
    let z : (layer G r i : Set V) := ⟨y,(mem_layer G r).mpr hry⟩
    exact ⟨z,(H.mem_neighborFinset x z).mpr hxy,rfl⟩

private lemma sum_incident_inside_layer (i : ℕ) [DecidableEq V] :
    (∑ x ∈ layer G r i, (neighborsAt G r x i).card) =
      2 * (G.induce (layer G r i : Set V)).edgeFinset.card := by
  classical
  rw [← (G.induce (layer G r i : Set V)).sum_degrees_eq_twice_card_edges]
  simp only [layer_induced_degree]
  exact (Finset.sum_finset_coe (fun x => (neighborsAt G r x i).card) (layer G r i)).symm

private lemma neighbor_total (i j : ℕ) :
    (∑ x ∈ layer G r i, (neighborsAt G r x j).card) =
      ∑ x ∈ layer G r j, (neighborsAt G r x i).card := by
  have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := layer G r i) (t := layer G r j) G.Adj
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at h
  simp only [neighbors_layer_eq_filter]
  simpa only [SimpleGraph.adj_comm (G := G)] using h

open scoped Classical in
private theorem third_layer_shapes (h4 : NoFourCycle G) (hfar : ¬ Erdos934.HasFarEdges G 3)
    (hdeg : ∀ x, G.degree x ≤ 3) (hr : G.degree r = 3)
    (reg : ∀ x : V, (∃ y, G.Adj x y) → G.degree x = 3)
    (hL2 : (layer G r 2).card = 6) (hL3 : (layer G r 3).card = 6) :
    let e := (G.induce (layer G r 2 : Set V)).edgeFinset.card
    let T (i : ℕ) := (layer G r 3).filter (fun x => (neighborsAt G r x 2).card = i)
    ((T 1).card = 0 ∧ (T 2).card = 6 ∧ (T 3).card = 0 ∧ e = 0) ∨
    ((T 1).card = 1 ∧ (T 2).card = 4 ∧ (T 3).card = 1 ∧ e = 0) ∨
    ((T 1).card = 2 ∧ (T 2).card = 4 ∧ (T 3).card = 0 ∧ e = 1) := by
  classical
  let T (i : ℕ) := (layer G r 3).filter (fun x => (neighborsAt G r x 2).card = i)
  let e := (G.induce (layer G r 2 : Set V)).edgeFinset.card
  change ((T 1).card = 0 ∧ (T 2).card = 6 ∧ (T 3).card = 0 ∧ e = 0) ∨
    ((T 1).card = 1 ∧ (T 2).card = 4 ∧ (T 3).card = 1 ∧ e = 0) ∨
    ((T 1).card = 2 ∧ (T 2).card = 4 ∧ (T 3).card = 0 ∧ e = 1)
  obtain ⟨hcounts,hTwo,hSum⟩ := third_layer_statistics G r h4 hfar reg hr hL2
  change (layer G r 3).card = (T 1).card + (T 2).card + (T 3).card at hcounts
  change 2 * (T 1).card ≤ (T 2).card at hTwo
  change (∑ x ∈ layer G r 3, (neighborsAt G r x 2).card) =
    (T 1).card * 1 + (T 2).card * 2 + (T 3).card * 3 at hSum
  have hb : (∑ x ∈ layer G r 2, ((neighborsAt G r x 2).card + (neighborsAt G r x 3).card)) =
      (layer G r 2).card * 2 :=
    Finset.sum_const_nat (fun _ hx => (second_degrees G r h4 hfar hdeg hr reg hx).2)
  rw [Finset.sum_add_distrib, sum_incident_inside_layer, ← neighbor_total G r 3 2, hSum, hL2] at hb
  change 2 * e + ((T 1).card * 1 + (T 2).card * 2 + (T 3).card * 3) = 6 * 2 at hb
  omega

end ThirdShape


section Branches

variable {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)

private lemma first_direction_through_second_layer {x u : V} (h3 : x ∈ layer G r 3)
    (hux : u ∈ firstNeighbors G r 2 x) : ∃ w ∈ neighborsAt G r x 2, G.Adj u w := by
  obtain ⟨hru,hux'⟩ := (mem_firstNeighbors G r).mp hux
  obtain ⟨w,huw,hwx⟩ := geodesic_step (G := G) (k := 1) hux'
  have hwx' := edist_eq_one_iff_adj.mp (by simpa only [Nat.cast_one] using hwx)
  have hrw : G.edist r w ≤ 2 := by
    calc
      _ ≤ 1 + G.edist u w := edist_step hru
      _ = 2 := by rw [edist_eq_one_iff_adj.mpr huw]; rfl
  have hrw' : G.edist r w = 2 := by
    apply edist_eq_of_le_step (i := 2) hrw
    simpa only [(mem_layer G r).mp h3] using (edist_step_right (r := r) hwx'.symm)
  exact ⟨w,(mem_neighborsAt G r).mpr ⟨hwx'.symm,hrw'⟩,huw⟩

private lemma edge_covers_first_directions [DecidableEq V] (hfar : ¬ Erdos934.HasFarEdges G 3)
    {x y u : V} (hx : x ∈ layer G r 3) (hy : y ∈ layer G r 3) (hxy : G.Adj x y)
    (hu : u ∈ layer G r 1) :
    ∃ w ∈ neighborsAt G r x 2 ∪ neighborsAt G r y 2, G.Adj u w := by
  classical
  rw [layer_one] at hu
  have hh := root_neighbors_covered G r (k := 2) hfar hxy
    ((mem_layer G r).mp hx).ge ((mem_layer G r).mp hy).ge hu
  rcases Finset.mem_union.mp hh with hh | hh
  · obtain ⟨w,hw,huw⟩ := first_direction_through_second_layer G r hx hh
    exact ⟨w,Finset.mem_union_left _ hw,huw⟩
  · obtain ⟨w,hw,huw⟩ := first_direction_through_second_layer G r hy hh
    exact ⟨w,Finset.mem_union_right _ hw,huw⟩

private lemma first_direction_unique_child (h4 : NoFourCycle G)
    {x u : V} (hx : x ∈ layer G r 3) (hu : u ∈ layer G r 1) :
    ((neighborsAt G r x 2).filter (G.Adj u)).card ≤ 1 := by
  apply Finset.card_le_one_iff.mpr
  intro a b ha hb
  obtain ⟨ha,hua⟩ := Finset.mem_filter.mp ha
  obtain ⟨hb,hub⟩ := Finset.mem_filter.mp hb
  have hxu : x ≠ u := by
    rintro rfl
    have hh : (1 : ℕ∞) = 3 := ((mem_layer G r).mp hu).symm.trans ((mem_layer G r).mp hx)
    norm_num at hh
  by_contra hab
  exact h4 hxu hab ((mem_neighborsAt G r).mp ha).1 hua
    ((mem_neighborsAt G r).mp hb).1 hub

end Branches


section Labels

variable {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)

private lemma branch_has_two_children (h3 : NoTriangle G)
    (reg : ∀ x : V, (∃ y, G.Adj x y) → G.degree x = 3)
    {x : V} (hx : x ∈ layer G r 1) :
    (neighborsAt G r x 2).card = 2 := by
  classical
  have hrx : G.Adj r x := edist_eq_one_iff_adj.mp ((mem_layer G r).mp hx)
  have he : neighborsAt G r x 2 = (G.neighborFinset x).erase r := by
    ext y
    simp only [mem_neighborsAt,Finset.mem_erase,G.mem_neighborFinset]
    constructor
    · rintro ⟨hxy,hry⟩
      refine ⟨?_,hxy⟩
      rintro rfl
      simp at hry
    · rintro ⟨hy,hxy⟩
      have hle : G.edist r y ≤ 2 := by
        calc
          _ ≤ 1 + G.edist x y := edist_step hrx
          _ = 2 := by rw [edist_eq_one_iff_adj.mpr hxy]; rfl
      obtain ⟨n,hn⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt (hle.trans_lt (ENat.natCast_lt_top 2)))
      have hnle : n ≤ 2 := by rw [← hn] at hle; exact_mod_cast hle
      have hpos : n ≠ 0 := by
        rintro rfl
        exact hy (edist_eq_zero_iff.mp hn.symm).symm
      have hne : n ≠ 1 := by
        rintro rfl
        exact h3 hrx (edist_eq_one_iff_adj.mp hn.symm) hxy
      have hn' : n = 2 := by omega
      exact ⟨hxy,by simpa only [hn'] using hn.symm⟩
  rw [he,Finset.card_erase_of_mem ((G.mem_neighborFinset x r).mpr hrx.symm),
    G.card_neighborFinset_eq_degree,reg x ⟨r,hrx.symm⟩]

private theorem layer_two_labels (h4 : NoFourCycle G) (h3 : NoTriangle G)
    (reg : ∀ x : V, (∃ y, G.Adj x y) → G.degree x = 3) (hr : ∃ y, G.Adj r y)
    (A : Fin 3 ≃ (layer G r 1 : Type)) :
    ∃ B : (Fin 3 × Fin 2) ≃ (layer G r 2 : Type),
      ∀ i j, G.Adj (A i).val (B (i,j)).val := by
  classical
  let N (i : Fin 3) := neighborsAt G r (A i).val 2
  have hN (i : Fin 3) : (N i).card = 2 := branch_has_two_children G r h3 reg (A i).property
  let c (i : Fin 3) : Fin 2 ≃ (N i : Type) := ((N i).equivFin.trans (finCongr (hN i))).symm
  let f (p : Fin 3 × Fin 2) : (layer G r 2 : Type) :=
    ⟨(c p.1 p.2).val,(mem_layer G r).mpr ((mem_neighborsAt G r).mp (c p.1 p.2).property).2⟩
  have hadj (i : Fin 3) (j : Fin 2) : G.Adj (A i).val (f (i,j)).val :=
    ((mem_neighborsAt G r).mp (c i j).property).1
  have hInjective : Function.Injective f := by
    rintro ⟨i,k⟩ ⟨j,l⟩ h
    have hval : (f (i,k)).val = (f (j,l)).val := congrArg Subtype.val h
    have hir : r ≠ (f (i,k)).val := by
      intro he
      have hh := (mem_layer G r).mp (f (i,k)).property
      rw [← he] at hh
      simp at hh
    have hij : i = j := by
      by_contra hn
      have hi : G.Adj r (A i).val := edist_eq_one_iff_adj.mp ((mem_layer G r).mp (A i).property)
      have hj : G.Adj r (A j).val := edist_eq_one_iff_adj.mp ((mem_layer G r).mp (A j).property)
      have hdiff : (A i).val ≠ (A j).val := fun e => hn (A.injective (Subtype.ext e))
      exact h4 hir hdiff hi (hadj i k).symm hj (hval.symm ▸ (hadj j l).symm)
    subst j
    have hl : k = l := (c i).injective (Subtype.ext hval)
    subst l
    rfl
  obtain ⟨_,_,hL⟩ := first_three_layers G r h4 h3 reg hr
  have hcard : Fintype.card (Fin 3 × Fin 2) = Fintype.card (layer G r 2 : Type) := by
    simp [hL]
  have hf : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hInjective,hcard⟩
  exact ⟨Equiv.ofBijective f hf,hadj⟩

end Labels


section AssembleLabels

variable {V : Type} [Fintype V] (G : SimpleGraph V) (r : V)

private abbrev LayerLabel := Fin 1 ⊕ (Fin 3 ⊕ ((Fin 3 × Fin 2) ⊕ Fin 6))

private def labelIndex : LayerLabel ≃ Fin 16 :=
  (Equiv.sumCongr (Equiv.refl _) ((Equiv.sumCongr (Equiv.refl _)
    ((Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv)).trans finSumFinEquiv)).trans
      finSumFinEquiv

private def labelValue (A : Fin 3 ≃ (layer G r 1 : Type))
    (B : (Fin 3 × Fin 2) ≃ (layer G r 2 : Type)) (C : Fin 6 ≃ (layer G r 3 : Type)) :
    LayerLabel → V
  | .inl _ => r
  | .inr (.inl i) => (A i).val
  | .inr (.inr (.inl i)) => (B i).val
  | .inr (.inr (.inr i)) => (C i).val

private def labelLayer : LayerLabel → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr (.inl _)) => 2
  | .inr (.inr (.inr _)) => 3

private lemma labelValue_dist (A : Fin 3 ≃ (layer G r 1 : Type))
    (B : (Fin 3 × Fin 2) ≃ (layer G r 2 : Type)) (C : Fin 6 ≃ (layer G r 3 : Type))
    (i : LayerLabel) : G.edist r (labelValue G r A B C i) = (labelLayer i : ℕ∞) := by
  rcases i with i | (i | (i | i))
  · simp [labelValue,labelLayer]
  · exact (mem_layer G r).mp (A i).property
  · exact (mem_layer G r).mp (B i).property
  · exact (mem_layer G r).mp (C i).property

private lemma labelValue_inj (A : Fin 3 ≃ (layer G r 1 : Type))
    (B : (Fin 3 × Fin 2) ≃ (layer G r 2 : Type)) (C : Fin 6 ≃ (layer G r 3 : Type)) :
    Function.Injective (labelValue G r A B C) := by
  intro i j h
  have he : labelLayer i = labelLayer j := by
    apply ENat.natCast_inj.mp
    rw [← labelValue_dist G r A B C i, ← labelValue_dist G r A B C j, h]
  rcases i with i | (i | (i | i)) <;> rcases j with j | (j | (j | j)) <;>
    norm_num [labelLayer] at he
  · exact congrArg Sum.inl (Subsingleton.elim i j)
  · exact congrArg (fun i => (.inr (.inl i) : LayerLabel)) (A.injective (Subtype.ext h))
  · exact congrArg (fun i => (.inr (.inr (.inl i)) : LayerLabel)) (B.injective (Subtype.ext h))
  · exact congrArg (fun i => (.inr (.inr (.inr i)) : LayerLabel)) (C.injective (Subtype.ext h))

private theorem assemble_labels (A : Fin 3 ≃ (layer G r 1 : Type))
    (B : (Fin 3 × Fin 2) ≃ (layer G r 2 : Type)) (C : Fin 6 ≃ (layer G r 3 : Type)) :
    ∃ f : Fin 16 → V, Function.Injective f ∧
      f (labelIndex (.inl 0)) = r ∧
      (∀ i : Fin 3, f (labelIndex (.inr (.inl i))) = (A i).val) ∧
      (∀ i : Fin 3 × Fin 2, f (labelIndex (.inr (.inr (.inl i)))) = (B i).val) ∧
      (∀ i : Fin 6, f (labelIndex (.inr (.inr (.inr i)))) = (C i).val) := by
  refine ⟨fun i => labelValue G r A B C (labelIndex.symm i),
    (labelValue_inj G r A B C).comp labelIndex.symm.injective, ?_⟩
  simp [labelValue]


private lemma labelIndex_branch (i : Fin 3) :
    (labelIndex (.inr (.inl i))).val = 1 + i.val := rfl

private lemma labelIndex_child (i : Fin 3) (j : Fin 2) :
    (labelIndex (.inr (.inr (.inl (i,j))))).val = 4 + 2*i.val + j.val := by
  change 1 + (3 + (j.val + 2 * i.val)) = _
  omega

private lemma labelIndex_tail (i : Fin 6) :
    (labelIndex (.inr (.inr (.inr i)))).val = 10 + i.val := by
  change 1 + (3 + (6 + i.val)) = _
  omega

end AssembleLabels

end CubicVertexBound

namespace CubicTemplates

private abbrev Label := Fin 16
private abbrev Edge := Label × Label

private def rootEdges : List Edge :=
  [(0,1),(0,2),(0,3),(1,4),(1,5),(2,6),(2,7),(3,8),(3,9)]

private def tailEdges (s : Fin 3) : List Edge :=
  if s = 0 then [(10,11),(12,13),(14,15)]
  else if s = 1 then [(10,11),(10,12),(13,14)]
  else [(10,11),(10,12),(13,14),(13,15),(4,6)]

private def groups (s : Fin 3) : List Label × List Label × List Label :=
  if s = 0 then ([11,13,14,15],[10,12,13,15],[10,11,12,14])
  else if s = 1 then ([10,13,14,15],[11,12,14,15],[11,12,13,15])
  else ([10,14,15],[11,12,13],[11,12,14,15])

private def split (p : Fin 3) : List Label → List Label × List Label
  | [a,b,c,d] => if p = 0 then ([a,b],[c,d])
    else if p = 1 then ([a,c],[b,d]) else ([a,d],[b,c])
  | [a,b,c] => if p = 0 then ([a],[b,c])
    else if p = 1 then ([b],[a,c]) else ([c],[a,b])
  | _ => ([],[])

private def spokes (a b : Label) (p : Fin 3) (l : List Label) : List Edge :=
  let g := split p l
  g.1.map (fun v => (a,v)) ++ g.2.map (fun v => (b,v))

private def edges (s a b c : Fin 3) : List Edge :=
  rootEdges ++ tailEdges s ++
  spokes 4 5 a (groups s).1 ++
  spokes 6 7 b (groups s).2.1 ++
  spokes 8 9 c (groups s).2.2

private def neighbors (E : List Edge) (x : Label) : List Label :=
  E.filterMap (fun (u,v) => if u = x then some v else if v = x then some u else none)

private def adj (E : List Edge) (x y : Label) : Bool := (neighbors E x).contains y

private def near (E : List Edge) (x y : Label) : Bool :=
  (x == y) || adj E x y || (neighbors E x).any (fun z => adj E z y)

private abbrev FourLabels := Label × Label × Label × Label

private def witnesses : List FourLabels :=
  [(1, 5, 6, 10), (1, 5, 6, 10), (1, 5, 6, 10), (1, 5, 6, 10), (1, 5, 6, 10), (1, 5, 6, 10),
   (1, 5, 7, 12), (1, 5, 7, 12), (1, 5, 7, 12), (1, 4, 6, 12), (1, 4, 6, 12), (1, 4, 6, 12),
   (1, 4, 7, 12), (1, 4, 7, 12), (1, 4, 7, 12), (1, 4, 7, 12), (1, 4, 7, 12), (1, 4, 7, 12),
   (1, 4, 6, 12), (1, 4, 6, 12), (1, 4, 6, 12), (1, 4, 9, 12), (1, 4, 8, 12), (4, 15, 6, 13),
   (1, 4, 7, 12), (1, 4, 7, 12), (1, 4, 7, 12), (1, 5, 6, 11), (1, 5, 6, 11), (1, 5, 6, 11),
   (1, 5, 8, 11), (1, 5, 8, 11), (1, 5, 9, 12), (1, 5, 8, 11), (1, 5, 8, 11), (1, 5, 9, 12),
   (1, 5, 6, 11), (1, 5, 6, 11), (1, 5, 6, 11), (1, 5, 6, 11), (1, 5, 6, 11), (1, 5, 6, 11),
   (1, 5, 7, 12), (1, 5, 7, 12), (1, 5, 7, 12), (1, 5, 6, 11), (1, 5, 6, 11), (1, 5, 6, 11),
   (1, 5, 7, 12), (1, 5, 7, 12), (1, 5, 7, 12), (1, 5, 6, 11), (1, 5, 6, 11), (1, 5, 6, 11),
   (1, 4, 7, 13), (1, 4, 7, 13), (1, 4, 7, 13), (1, 4, 7, 13), (1, 4, 7, 13), (1, 4, 7, 13),
   (1, 5, 7, 11), (1, 5, 7, 11), (1, 5, 7, 11), (1, 4, 7, 12), (1, 4, 7, 12), (1, 4, 7, 12),
   (1, 4, 7, 11), (1, 4, 7, 11), (1, 4, 7, 11), (1, 4, 7, 11), (1, 4, 7, 11), (1, 4, 7, 11),
   (1, 4, 7, 12), (1, 4, 7, 12), (1, 4, 7, 12), (1, 4, 7, 11), (1, 4, 7, 11), (1, 4, 7, 11),
   (1, 4, 7, 11), (1, 4, 7, 11), (1, 4, 7, 11)]

private def witness (s a b c : Fin 3) : FourLabels :=
  witnesses[s.val*27 + a.val*9 + b.val*3 + c.val]?.getD (0,0,0,0)

private def valid (s a b c : Fin 3) : Bool :=
  let E := edges s a b c
  let (u,v,w,x) := witness s a b c
  adj E u v && adj E w x &&
    !near E u w && !near E u x && !near E v w && !near E v x

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem valid_all : ∀ s a b c : Fin 3, valid s a b c = true := by
  decide +kernel

private lemma edist_two_has_middle {V : Type} {G : SimpleGraph V} {u v : V}
    (h : G.edist u v = 2) : ∃ z, G.Adj u z ∧ G.Adj z v := by
  have h' : G.edist u v = ((2 : ℕ) : ℕ∞) := h
  obtain ⟨p,hp⟩ := exists_walk_of_edist_eq_coe h'
  cases p with
  | nil => simp at hp
  | @cons u z v h1 p =>
    refine ⟨z,h1,edist_eq_one_iff_adj.mp ?_⟩
    rw [Walk.length_cons] at hp
    have hp1 : p.length = 1 := by omega
    apply le_antisymm
    · have he := p.edist_le
      rwa [hp1,Nat.cast_one] at he
    · by_contra! hh
      have hz : G.edist z v ≤ 0 := ENat.lt_natCast_add_one_iff.mp hh
      have he := G.edist_triangle (u := u) (v := z) (w := v)
      rw [h, edist_eq_one_iff_adj.mpr h1, le_antisymm hz bot_le, add_zero] at he
      norm_num at he

private lemma far_of_near_false {V : Type} {G : SimpleGraph V} (E : List Edge)
    {f : Label → V} (hf : Function.Injective f)
    (hAdj : ∀ i j, G.Adj (f i) (f j) ↔ adj E i j = true)
    (hs : ∀ {i : Label} {x : V}, G.Adj (f i) x → ∃ j, f j = x)
    {i j : Label} (h : near E i j = false) : (3 : ℕ∞) ≤ G.edist (f i) (f j) := by
  by_contra! hh
  have hn : G.edist (f i) (f j) ≤ 2 := ENat.lt_natCast_add_one_iff.mp hh
  obtain ⟨n,hn'⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt (hn.trans_lt (ENat.natCast_lt_top 2)))
  have h2 : n ≤ 2 := by rw [← hn'] at hn; exact_mod_cast hn
  have hnear : near E i j = true := by
    interval_cases n
    · have he : f i = f j := edist_eq_zero_iff.mp hn'.symm
      have hij := hf he
      subst j
      simp [near]
    · have he : G.Adj (f i) (f j) := edist_eq_one_iff_adj.mp hn'.symm
      simp [near,(hAdj i j).mp he]
    · obtain ⟨z,hi,hj⟩ := edist_two_has_middle hn'.symm
      obtain ⟨k,rfl⟩ := hs hi
      have hik : adj E i k = true := (hAdj i k).mp hi
      have hkj : adj E k j = true := (hAdj k j).mp hj
      have hk : k ∈ neighbors E i := List.contains_iff_mem.mp hik
      simp only [near, Bool.or_eq_true]
      exact Or.inr (List.any_eq_true.mpr ⟨k,hk,hkj⟩)
  rw [h] at hnear
  contradiction

private theorem far_of_template_closed {V : Type} {G : SimpleGraph V} (s a b c : Fin 3)
    {f : Label → V} (hf : Function.Injective f)
    (hAdj : ∀ i j, G.Adj (f i) (f j) ↔ adj (edges s a b c) i j = true)
    (hs : ∀ {i : Label} {x : V}, G.Adj (f i) x → ∃ j, f j = x) :
    Erdos934.HasFarEdges G 3 := by
  have h := valid_all s a b c
  unfold valid at h
  rcases he : witness s a b c with ⟨u,v,w,x⟩
  rw [he] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨huv,hwx⟩,huw⟩,hux⟩,hvw⟩,hvx⟩ := h
  have not_false (b : Bool) (hb : (!b) = true) : b = false := by cases b <;> simp_all
  refine ⟨f u,f v,f w,f x,(hAdj u v).mpr huv,(hAdj w x).mpr hwx,?_⟩
  intro p hp q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact far_of_near_false _ hf hAdj hs (not_false _ huw)
  · exact far_of_near_false _ hf hAdj hs (not_false _ hux)
  · exact far_of_near_false _ hf hAdj hs (not_false _ hvw)
  · exact far_of_near_false _ hf hAdj hs (not_false _ hvx)


set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem template_cubic : ∀ s a b c : Fin 3, ∀ x : Label,
    let N := neighbors (edges s a b c) x
    N.Nodup ∧ N.length = 3 := by
  decide +kernel

private lemma adj_of_template_edge {V : Type} {G : SimpleGraph V}
    (E : List Edge) (f : Label → V)
    (h : ∀ e ∈ E, G.Adj (f e.1) (f e.2)) {x y : Label}
    (ha : adj E x y = true) : G.Adj (f x) (f y) := by
  have hy : y ∈ neighbors E x := List.contains_iff_mem.mp ha
  obtain ⟨⟨a,b⟩,he,hy⟩ := List.mem_filterMap.mp hy
  by_cases ha : a = x
  · simp only [ha, ↓reduceIte, Option.some.injEq] at hy
    simpa only [ha, hy] using h (a,b) he
  · by_cases hb : b = x
    · simp only [ha,hb,↓reduceIte,Option.some.injEq] at hy
      simpa only [hb,hy] using (h (a,b) he).symm
    · simp [ha,hb] at hy

-- The template already uses all three incident edges at each vertex.
private theorem far_of_template_subgraph {V : Type} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (s a b c : Fin 3)
    {f : Label → V} (hf : Function.Injective f) (hdeg : ∀ x, G.degree x ≤ 3)
    (hEdges : ∀ e ∈ edges s a b c, G.Adj (f e.1) (f e.2)) :
    Erdos934.HasFarEdges G 3 := by
  classical
  let E := edges s a b c
  let N (x : Label) := (neighbors E x).toFinset
  have hcard (x : Label) : (N x).card = 3 := by
    obtain ⟨hn,hl⟩ := template_cubic s a b c x
    change (neighbors E x).toFinset.card = 3
    rw [List.toFinset_card_of_nodup hn, hl]
  have hNeigh (x : Label) : (N x).image f = G.neighborFinset (f x) := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hy
      apply (G.mem_neighborFinset (f x) (f j)).mpr
      apply adj_of_template_edge E f hEdges
      exact List.contains_iff_mem.mpr (List.mem_toFinset.mp hj)
    · rw [Finset.card_image_of_injective _ hf, hcard, G.card_neighborFinset_eq_degree]
      exact hdeg _
  have hAdj (i j : Label) : G.Adj (f i) (f j) ↔ adj E i j = true := by
    rw [← G.mem_neighborFinset, ← hNeigh]
    constructor
    · intro h
      obtain ⟨k,hk,hkj⟩ := Finset.mem_image.mp h
      exact List.contains_iff_mem.mpr (List.mem_toFinset.mp (hf hkj ▸ hk))
    · intro h
      exact Finset.mem_image_of_mem f (List.mem_toFinset.mpr (List.contains_iff_mem.mp h))
  have hCover {i : Label} {x : V} (h : G.Adj (f i) x) : ∃ j, f j = x := by
    have hm := (G.mem_neighborFinset (f i) x).mpr h
    rw [← hNeigh] at hm
    obtain ⟨j,_,he⟩ := Finset.mem_image.mp hm
    exact ⟨j,he⟩
  exact far_of_template_closed s a b c hf hAdj hCover

end CubicTemplates

namespace CubicTemplates

private def tailLabel (j : Fin 6) : Label :=
  ⟨10 + j.val, by omega⟩

private def groupFor (s i : Fin 3) : List Label :=
  if i = 0 then (groups s).1 else if i = 1 then (groups s).2.1 else (groups s).2.2

private def groupIndices (s i : Fin 3) : List (Fin 6) :=
  (groupFor s i).map (fun v => Fin.ofNat 6 (v.val - 10))

private def shortGroup (s i : Fin 3) : Prop :=
  s = 2 ∧ i ≠ 2

private instance (s i : Fin 3) : Decidable (shortGroup s i) := by
  unfold shortGroup
  infer_instance

private theorem groupIndices_map (s i : Fin 3) :
    (groupIndices s i).map tailLabel = groupFor s i := by
  fin_cases s <;> fin_cases i <;> decide

private theorem groupIndices_card (s i : Fin 3) :
    (groupIndices s i).toFinset.card = (if shortGroup s i then 3 else 4) := by
  fin_cases s <;> fin_cases i <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem child_split_table (s i : Fin 3) :
    ∀ X Y : Finset (Fin 6), X ∪ Y = (groupIndices s i).toFinset →
      X.card = (if shortGroup s i then 1 else 2) → Y.card = 2 →
      ∃ (p : Fin 3) (flip : Bool), (shortGroup s i → flip = false) ∧
        (split p (groupFor s i)).1.toFinset = (if flip then Y else X).image tailLabel ∧
        (split p (groupFor s i)).2.toFinset = (if flip then X else Y).image tailLabel := by
  fin_cases s <;> fin_cases i <;> decide +kernel

end CubicTemplates

namespace CubicVertexBound

variable {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)

omit [DecidableRel G.Adj] in
private theorem child_label_of_adj (h4 : NoFourCycle G)
    (A : Fin 3 ≃ (layer G r 1 : Type))
    (B : (Fin 3 × Fin 2) ≃ (layer G r 2 : Type))
    (hB : ∀ i j, G.Adj (A i).val (B (i,j)).val)
    {i : Fin 3} {x : V} (hx : x ∈ layer G r 2) (hax : G.Adj (A i).val x) :
    ∃ j, (B (i,j)).val = x := by
  obtain ⟨⟨k,j⟩,he⟩ := B.surjective ⟨x,hx⟩
  have hrx : r ≠ x := by
    rintro rfl
    have hh := (mem_layer G r).mp hx
    simp at hh
  have hik : i = k := by
    by_contra hn
    have hri := edist_eq_one_iff_adj.mp ((mem_layer G r).mp (A i).property)
    have hrk := edist_eq_one_iff_adj.mp ((mem_layer G r).mp (A k).property)
    have hik : (A i).val ≠ (A k).val := fun h => hn (A.injective (Subtype.ext h))
    have he' : (B (k,j)).val = x := congrArg Subtype.val he
    have hkx : G.Adj (A k).val x := by rw [← he']; exact hB k j
    exact h4 hrx hik hri hax.symm hrk hkx.symm
  subst k
  exact ⟨j, congrArg Subtype.val he⟩

private def tailSet (C : Fin 6 ≃ (layer G r 3 : Type)) (x : V) : Finset (Fin 6) :=
  Finset.univ.filter (fun j => G.Adj x (C j).val)

private theorem tailSet_card_le (C : Fin 6 ≃ (layer G r 3 : Type)) (x : V) :
    (tailSet G r C x).card ≤ (neighborsAt G r x 3).card := by
  classical
  let f (j : Fin 6) : V := (C j).val
  have hinj : Function.Injective f := fun a b h => C.injective (Subtype.ext h)
  rw [← Finset.card_image_of_injective _ hinj]
  apply Finset.card_le_card
  intro z hz
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
  exact (mem_neighborsAt G r).mpr
    ⟨(Finset.mem_filter.mp hj).2, (mem_layer G r).mp (C j).property⟩

private theorem branch_columns_cover (h4 : NoFourCycle G)
    (A : Fin 3 ≃ (layer G r 1 : Type)) (C : Fin 6 ≃ (layer G r 3 : Type))
    (B : (Fin 3 × Fin 2) ≃ (layer G r 2 : Type))
    (hB : ∀ i j, G.Adj (A i).val (B (i,j)).val)
    (s i : Fin 3)
    (hGroup : ∀ j : Fin 6, (∃ z ∈ neighborsAt G r (C j).val 2, G.Adj (A i).val z) ↔
      j ∈ CubicTemplates.groupIndices s i) :
    tailSet G r C (B (i,0)).val ∪ tailSet G r C (B (i,1)).val =
      (CubicTemplates.groupIndices s i).toFinset := by
  apply Finset.ext
  intro j
  rw [Finset.mem_union, List.mem_toFinset, ← hGroup]
  constructor
  · intro h
    have step (k : Fin 2) (hj : j ∈ tailSet G r C (B (i,k)).val) :
        ∃ z ∈ neighborsAt G r (C j).val 2, G.Adj (A i).val z :=
      ⟨(B (i,k)).val, (mem_neighborsAt G r).mpr
        ⟨(Finset.mem_filter.mp hj).2.symm, (mem_layer G r).mp (B (i,k)).property⟩, hB i k⟩
    exact h.elim (step 0) (step 1)
  · rintro ⟨z,hz,hAz⟩
    obtain ⟨hCz,hzD⟩ := (mem_neighborsAt G r).mp hz
    obtain ⟨k,hk⟩ := child_label_of_adj G r h4 A B hB ((mem_layer G r).mpr hzD) hAz
    have h : j ∈ tailSet G r C (B (i,k)).val :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk.symm ▸ hCz.symm⟩
    fin_cases k
    · exact Or.inl h
    · exact Or.inr h

private theorem choose_child_split (C : Fin 6 ≃ (layer G r 3 : Type)) (s i : Fin 3)
    (x y : V)
    (hUnion : tailSet G r C x ∪ tailSet G r C y = (CubicTemplates.groupIndices s i).toFinset)
    (hx : (neighborsAt G r x 3).card ≤ (if CubicTemplates.shortGroup s i then 1 else 2))
    (hy : (neighborsAt G r y 3).card ≤ 2) :
    ∃ (p : Fin 3) (flip : Bool), (CubicTemplates.shortGroup s i → flip = false) ∧
      (∀ w ∈ (CubicTemplates.split p (CubicTemplates.groupFor s i)).1,
        ∃ j : Fin 6, CubicTemplates.tailLabel j = w ∧ G.Adj (if flip then y else x) (C j).val) ∧
      (∀ w ∈ (CubicTemplates.split p (CubicTemplates.groupFor s i)).2,
        ∃ j : Fin 6, CubicTemplates.tailLabel j = w ∧ G.Adj (if flip then x else y) (C j).val) := by
  classical
  let X := tailSet G r C x
  let Y := tailSet G r C y
  have hX : X.card ≤ (if CubicTemplates.shortGroup s i then 1 else 2) := (tailSet_card_le G r C x).trans hx
  have hY : Y.card ≤ 2 := (tailSet_card_le G r C y).trans hy
  have hcover := Finset.card_union_le X Y
  change (X ∪ Y).card ≤ X.card + Y.card at hcover
  change X ∪ Y = _ at hUnion
  rw [hUnion, CubicTemplates.groupIndices_card] at hcover
  have hxCard : X.card = (if CubicTemplates.shortGroup s i then 1 else 2) := by
    by_cases h : CubicTemplates.shortGroup s i <;> simp [h] at hcover hX ⊢ <;> omega
  have hyCard : Y.card = 2 := by
    by_cases h : CubicTemplates.shortGroup s i <;> simp [h] at hcover hX <;> omega
  obtain ⟨p,flip,hfixed,h1,h2⟩ := CubicTemplates.child_split_table s i X Y hUnion hxCard hyCard
  refine ⟨p,flip,hfixed,?_ ,?_⟩
  · intro w hw
    have hw' : w ∈ (CubicTemplates.split p (CubicTemplates.groupFor s i)).1.toFinset :=
      List.mem_toFinset.mpr hw
    rw [h1] at hw'
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hw'
    refine ⟨j,he,?_⟩
    cases flip
    · exact (Finset.mem_filter.mp hj).2
    · exact (Finset.mem_filter.mp hj).2
  · intro w hw
    have hw' : w ∈ (CubicTemplates.split p (CubicTemplates.groupFor s i)).2.toFinset :=
      List.mem_toFinset.mpr hw
    rw [h2] at hw'
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hw'
    refine ⟨j,he,?_⟩
    cases flip
    · exact (Finset.mem_filter.mp hj).2
    · exact (Finset.mem_filter.mp hj).2

end CubicVertexBound

namespace CubicTemplates

private def branchLabel (i : Fin 3) : Label :=
  ⟨1 + i.val, by omega⟩

private def childLabel (i : Fin 3) (j : Fin 2) : Label :=
  ⟨4 + 2*i.val + j.val, by omega⟩

private theorem root_edges_of_branch_child {V : Type} {G : SimpleGraph V} {f : Label → V}
    (hA : ∀ i, G.Adj (f 0) (f (branchLabel i)))
    (hB : ∀ i j, G.Adj (f (branchLabel i)) (f (childLabel i j))) :
    ∀ e ∈ rootEdges, G.Adj (f e.1) (f e.2) := by
  intro e he
  simp only [rootEdges, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hA 0
  · exact hA 1
  · exact hA 2
  · exact hB 0 0
  · exact hB 0 1
  · exact hB 1 0
  · exact hB 1 1
  · exact hB 2 0
  · exact hB 2 1

private theorem far_from_spokes {V : Type} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {f : Label → V} (hf : Function.Injective f)
    (hdeg : ∀ x, G.degree x ≤ 3) (s : Fin 3) (p : Fin 3 → Fin 3)
    (hRoot : ∀ e ∈ rootEdges, G.Adj (f e.1) (f e.2))
    (hTail : ∀ e ∈ tailEdges s, G.Adj (f e.1) (f e.2))
    (h₀ : ∀ i, ∀ w ∈ (split (p i) (groupFor s i)).1, G.Adj (f (childLabel i 0)) (f w))
    (h₁ : ∀ i, ∀ w ∈ (split (p i) (groupFor s i)).2, G.Adj (f (childLabel i 1)) (f w)) :
    Erdos934.HasFarEdges G 3 := by
  have hs (i : Fin 3) : ∀ e ∈ spokes (childLabel i 0) (childLabel i 1) (p i) (groupFor s i),
      G.Adj (f e.1) (f e.2) := by
    intro e he
    simp only [spokes, List.mem_append, List.mem_map] at he
    rcases he with ⟨w,hw,rfl⟩ | ⟨w,hw,rfl⟩
    · exact h₀ i w hw
    · exact h₁ i w hw
  apply far_of_template_subgraph s (p 0) (p 1) (p 2) hf hdeg
  intro e he
  simp only [edges, List.mem_append] at he
  rcases he with (((hE | hE) | hE) | hE) | hE
  · exact hRoot e hE
  · exact hTail e hE
  · exact hs 0 e hE
  · exact hs 1 e hE
  · exact hs 2 e hE

end CubicTemplates

namespace CubicTemplates

private def tailPairs (s : Fin 3) : List (Fin 6 × Fin 6) :=
  if s = 0 then [(0,1),(2,3),(4,5)]
  else if s = 1 then [(0,1),(0,2),(3,4)]
  else [(0,1),(0,2),(3,4),(3,5)]

private theorem tail_edges_eq (s : Fin 3) :
    tailEdges s = (tailPairs s).map (fun p => (tailLabel p.1, tailLabel p.2)) ++
      (if s = 2 then [(4,6)] else []) := by
  fin_cases s <;> decide

end CubicTemplates

namespace CubicVertexBound

private def branchReindex (flip : Fin 3 → Bool) :
    (Fin 3 × Fin 2) ≃ (Fin 3 × Fin 2) where
  toFun p := (p.1, if flip p.1 then p.2.rev else p.2)
  invFun p := (p.1, if flip p.1 then p.2.rev else p.2)
  left_inv := by
    rintro ⟨i,j⟩
    cases h : flip i <;> simp [h]
  right_inv := by
    rintro ⟨i,j⟩
    cases h : flip i <;> simp [h]

variable {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)

private theorem far_of_canonical_children (h4 : NoFourCycle G) (hdeg : ∀ x, G.degree x ≤ 3)
    (s : Fin 3) (A : Fin 3 ≃ (layer G r 1 : Type)) (C : Fin 6 ≃ (layer G r 3 : Type))
    (B : (Fin 3 × Fin 2) ≃ (layer G r 2 : Type))
    (hB : ∀ i k, G.Adj (A i).val (B (i,k)).val)
    (hGroup : ∀ i j, (∃ z ∈ neighborsAt G r (C j).val 2, G.Adj (A i).val z) ↔
      j ∈ CubicTemplates.groupIndices s i)
    (hTail : ∀ e ∈ CubicTemplates.tailPairs s, G.Adj (C e.1).val (C e.2).val)
    (hMid : s = 2 → G.Adj (B (0,0)).val (B (1,0)).val)
    (hlim₀ : ∀ i, (neighborsAt G r (B (i,0)).val 3).card ≤
      (if CubicTemplates.shortGroup s i then 1 else 2))
    (hlim₁ : ∀ i, (neighborsAt G r (B (i,1)).val 3).card ≤ 2) :
    Erdos934.HasFarEdges G 3 := by
  classical
  have hExist (i : Fin 3) := choose_child_split G r C s i (B (i,0)).val (B (i,1)).val
    (branch_columns_cover G r h4 A C B hB s i (hGroup i)) (hlim₀ i) (hlim₁ i)
  choose p flip hfixed hspoke₀ hspoke₁ using hExist
  let B' := (branchReindex flip).trans B
  obtain ⟨f,hf,hf₀,hfa,hfb,hfc⟩ := assemble_labels G r A B' C
  have h0 : f 0 = r := hf₀
  have hfA (i : Fin 3) : f (CubicTemplates.branchLabel i) = (A i).val := by
    have hlabel : labelIndex (.inr (.inl i)) = CubicTemplates.branchLabel i :=
      Fin.ext (labelIndex_branch i)
    simpa only [hlabel] using hfa i
  have hfB (i : Fin 3) (j : Fin 2) : f (CubicTemplates.childLabel i j) = (B' (i,j)).val := by
    have hlabel : labelIndex (.inr (.inr (.inl (i,j)))) = CubicTemplates.childLabel i j :=
      Fin.ext (labelIndex_child i j)
    simpa only [hlabel] using hfb (i,j)
  have hfC (j : Fin 6) : f (CubicTemplates.tailLabel j) = (C j).val := by
    have hlabel : labelIndex (.inr (.inr (.inr j))) = CubicTemplates.tailLabel j :=
      Fin.ext (labelIndex_tail j)
    simpa only [hlabel] using hfc j
  have hfB₀ (i : Fin 3) : f (CubicTemplates.childLabel i 0) =
      (if flip i then (B (i,1)).val else (B (i,0)).val) := by
    rw [hfB]
    cases h : flip i <;> simp [B', branchReindex, h]
  have hfB₁ (i : Fin 3) : f (CubicTemplates.childLabel i 1) =
      (if flip i then (B (i,0)).val else (B (i,1)).val) := by
    rw [hfB]
    cases h : flip i <;> simp [B', branchReindex, h]
  apply CubicTemplates.far_from_spokes hf hdeg s p
  · apply CubicTemplates.root_edges_of_branch_child
    · intro i
      rw [h0, hfA]
      exact edist_eq_one_iff_adj.mp ((mem_layer G r).mp (A i).property)
    · intro i j
      rw [hfA, hfB]
      exact hB i ((branchReindex flip) (i,j)).2
  · intro e he
    rw [CubicTemplates.tail_edges_eq] at he
    rcases List.mem_append.mp he with hm | hm
    · obtain ⟨e',he',rfl⟩ := List.mem_map.mp hm
      simpa only [hfC] using hTail e' he'
    · by_cases h₂ : s = 2
      · have he' : e = (4,6) := by simpa [h₂] using hm
        subst e
        have hz₀ : flip 0 = false := hfixed 0 (by simp [CubicTemplates.shortGroup,h₂])
        have hz₁ : flip 1 = false := hfixed 1 (by simp [CubicTemplates.shortGroup,h₂])
        change G.Adj (f (CubicTemplates.childLabel 0 0)) (f (CubicTemplates.childLabel 1 0))
        simpa only [hfB₀,hz₀,hz₁,Bool.false_eq_true,if_false] using hMid h₂
      · simp [h₂] at hm
  · intro i w hw
    obtain ⟨j,rfl,hj⟩ := hspoke₀ i w hw
    simpa only [hfB₀,hfC] using hj
  · intro i w hw
    obtain ⟨j,rfl,hj⟩ := hspoke₁ i w hw
    simpa only [hfB₁,hfC] using hj

end CubicVertexBound

namespace CubicVertexBound

variable {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)

private theorem far_from_canonical_layers (h3 : NoTriangle G) (h4 : NoFourCycle G)
    (hdeg : ∀ x, G.degree x ≤ 3) (hfar : ¬ Erdos934.HasFarEdges G 3)
    (hr : G.degree r = 3) (reg : ∀ x : V, (∃ y, G.Adj x y) → G.degree x = 3)
    (s : Fin 3) (A : Fin 3 ≃ (layer G r 1 : Type)) (C : Fin 6 ≃ (layer G r 3 : Type))
    (hGroup : ∀ i j, (∃ z ∈ neighborsAt G r (C j).val 2, G.Adj (A i).val z) ↔
      j ∈ CubicTemplates.groupIndices s i)
    (hTail : ∀ e ∈ CubicTemplates.tailPairs s, G.Adj (C e.1).val (C e.2).val)
    (hMiddle : s = 2 → ∃ x ∈ neighborsAt G r (A 0).val 2,
      ∃ y ∈ neighborsAt G r (A 1).val 2, G.Adj x y) : Erdos934.HasFarEdges G 3 := by
  classical
  have finish (B : (Fin 3 × Fin 2) ≃ (layer G r 2 : Type))
      (hB : ∀ i k, G.Adj (A i).val (B (i,k)).val)
      (hMid : s = 2 → G.Adj (B (0,0)).val (B (1,0)).val) : Erdos934.HasFarEdges G 3 := by
    have hBudget (i : Fin 3) (j : Fin 2) :
        (neighborsAt G r (B (i,j)).val 2).card + (neighborsAt G r (B (i,j)).val 3).card = 2 :=
      (second_degrees G r h4 hfar hdeg hr reg (B (i,j)).property).2
    apply far_of_canonical_children G r h4 hdeg s A C B hB hGroup hTail hMid
    · intro i
      by_cases hShort : CubicTemplates.shortGroup s i
      · simp only [if_pos hShort]
        have hMid' := hMid hShort.1
        have hPos : 0 < (neighborsAt G r (B (i,0)).val 2).card := by
          have h₀ : 0 < (neighborsAt G r (B (0,0)).val 2).card :=
            Finset.card_pos.mpr ⟨(B (1,0)).val, (mem_neighborsAt G r).mpr
              ⟨hMid', (mem_layer G r).mp (B (1,0)).property⟩⟩
          have h₁ : 0 < (neighborsAt G r (B (1,0)).val 2).card :=
            Finset.card_pos.mpr ⟨(B (0,0)).val, (mem_neighborsAt G r).mpr
              ⟨hMid'.symm, (mem_layer G r).mp (B (0,0)).property⟩⟩
          have hcase : i = 0 ∨ i = 1 := by
            have hne : i ≠ 2 := hShort.2
            fin_cases i <;> simp_all
          rcases hcase with rfl | rfl
          · exact h₀
          · exact h₁
        have h := hBudget i 0
        omega
      · simp only [if_neg hShort]
        have h := hBudget i 0
        omega
    · intro i
      have h := hBudget i 1
      omega
  have hrN : 0 < (G.neighborFinset r).card := by rw [G.card_neighborFinset_eq_degree, hr]; decide
  obtain ⟨v,hv⟩ := Finset.card_pos.mp hrN
  obtain ⟨B,hB⟩ := layer_two_labels G r h4 h3 reg ⟨v,(G.mem_neighborFinset _ _).mp hv⟩ A
  by_cases h₂ : s = 2
  · obtain ⟨x,hx,y,hy,hxy⟩ := hMiddle h₂
    obtain ⟨j,hj⟩ := child_label_of_adj G r h4 A B hB
      ((mem_layer G r).mpr ((mem_neighborsAt G r).mp hx).2) ((mem_neighborsAt G r).mp hx).1
    obtain ⟨k,hk⟩ := child_label_of_adj G r h4 A B hB
      ((mem_layer G r).mpr ((mem_neighborsAt G r).mp hy).2) ((mem_neighborsAt G r).mp hy).1
    let flip (i : Fin 3) : Bool := if i = 0 then decide (j = 1) else if i = 1 then decide (k = 1) else false
    let B' := (branchReindex flip).trans B
    apply finish B'
    · intro i t
      exact hB i ((branchReindex flip) (i,t)).2
    · intro _
      have hh : ∀ q : Fin 2, (if decide (q = 1) then (0 : Fin 2).rev else 0) = q := by decide
      have hf₀ : (branchReindex flip) (0,0) = (0,j) := by
        change ((0 : Fin 3), if decide (j = 1) then (0 : Fin 2).rev else 0) = (0,j)
        rw [hh]
      have hf₁ : (branchReindex flip) (1,0) = (1,k) := by
        change ((1 : Fin 3), if decide (k = 1) then (0 : Fin 2).rev else 0) = (1,k)
        rw [hh]
      change G.Adj (B ((branchReindex flip) (0,0))).val (B ((branchReindex flip) (1,0))).val
      simpa only [hf₀,hf₁,hj,hk] using hxy
  · exact finish B hB (fun hs => (h₂ hs).elim)

end CubicVertexBound

namespace CubicVertexBound

section TwoPathShape

variable {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)

private abbrev Links (u x : V) : Prop :=
  ∃ z ∈ neighborsAt G r x 2, G.Adj u z

private noncomputable def directions (x : V) : Finset V := by
  classical
  exact (layer G r 1).filter (fun u => Links G r u x)

private lemma mem_directions {x u : V} :
    u ∈ directions G r x ↔ u ∈ layer G r 1 ∧ Links G r u x := by
  classical
  exact Finset.mem_filter

private noncomputable def branchTail (u : V) : Finset V := by
  classical
  exact (layer G r 3).filter (Links G r u)

private lemma mem_branchTail {u x : V} :
    x ∈ branchTail G r u ↔ x ∈ layer G r 3 ∧ Links G r u x := by
  classical
  exact Finset.mem_filter

private lemma directions_card_eq_predecessors (h4 : NoFourCycle G)
    (hPar : ∀ z ∈ layer G r 2, (neighborsAt G r z 1).card = 1)
    {x : V} (hx : x ∈ layer G r 3) :
    (directions G r x).card = (neighborsAt G r x 2).card := by
  classical
  have hzLayer {z : V} (hz : z ∈ neighborsAt G r x 2) : z ∈ layer G r 2 :=
    (mem_layer G r).mpr ((mem_neighborsAt G r).mp hz).2
  have chooseParent (z : V) (hz : z ∈ neighborsAt G r x 2) :
      ∃ u, u ∈ neighborsAt G r z 1 :=
    Finset.card_pos.mp (by rw [hPar z (hzLayer hz)]; decide)
  let f (z : V) (hz : z ∈ neighborsAt G r x 2) : V := (chooseParent z hz).choose
  have hF (z : V) (hz : z ∈ neighborsAt G r x 2) :
      f z hz ∈ neighborsAt G r z 1 := (chooseParent z hz).choose_spec
  symm
  apply Finset.card_bij f
  · intro z hz
    obtain ⟨hzu, hu⟩ := (mem_neighborsAt G r).mp (hF z hz)
    exact (mem_directions G r).2 ⟨(mem_layer G r).2 hu, z, hz, hzu.symm⟩
  · intro z hz w hw he
    have hfL := (mem_layer G r).2 ((mem_neighborsAt G r).mp (hF z hz)).2
    have hfZ := ((mem_neighborsAt G r).mp (hF z hz)).1.symm
    have hfW : G.Adj (f z hz) w := by
      rw [he]
      exact ((mem_neighborsAt G r).mp (hF w hw)).1.symm
    exact Finset.card_le_one_iff.1 (first_direction_unique_child G r h4 hx hfL)
      (Finset.mem_filter.2 ⟨hz,hfZ⟩) (Finset.mem_filter.2 ⟨hw,hfW⟩)
  · intro u hu
    obtain ⟨huL,z,hz,huz⟩ := (mem_directions G r).1 hu
    have hu' : u ∈ neighborsAt G r z 1 :=
      (mem_neighborsAt G r).2 ⟨huz.symm, (mem_layer G r).1 huL⟩
    exact ⟨z, hz, Finset.card_le_one_iff.1 (le_of_eq (hPar z (hzLayer hz))) (hF z hz) hu'⟩

private lemma internal_second_edge_unique [DecidableEq V]
    (hE : (G.induce (layer G r 2 : Set V)).edgeFinset.card = 1) :
    ∃ p ∈ layer G r 2, ∃ q ∈ layer G r 2, G.Adj p q ∧
      ∀ x ∈ layer G r 2, ∀ y ∈ layer G r 2, G.Adj x y →
        (x = p ∧ y = q) ∨ (x = q ∧ y = p) := by
  classical
  let H := G.induce (layer G r 2 : Set V)
  change H.edgeFinset.card = 1 at hE
  obtain ⟨e, he⟩ := Finset.card_eq_one.1 hE
  obtain ⟨⟨p,q⟩, rfl⟩ := Quot.exists_rep e
  have hpq : H.Adj p q := (H.mem_edgeSet).1
    (SimpleGraph.mem_edgeFinset.1 (by rw [he]; exact Finset.mem_singleton_self _))
  refine ⟨p.val,p.property,q.val,q.property,hpq,?_⟩
  intro x hx y hy hxy
  let X : (layer G r 2 : Type) := ⟨x,hx⟩
  let Y : (layer G r 2 : Type) := ⟨y,hy⟩
  have hEdge : s(X,Y) ∈ H.edgeFinset :=
    SimpleGraph.mem_edgeFinset.2 ((H.mem_edgeSet).2 hxy)
  have hEq : s(X,Y) = s(p,q) := Finset.mem_singleton.1 (he ▸ hEdge)
  exact (Sym2.eq_iff.1 hEq).imp
    (fun ⟨h₁,h₂⟩ => ⟨congrArg Subtype.val h₁,congrArg Subtype.val h₂⟩)
    (fun ⟨h₁,h₂⟩ => ⟨congrArg Subtype.val h₁,congrArg Subtype.val h₂⟩)

private lemma branch_tail_card_eq_sum (h4 : NoFourCycle G) {u : V} (hu : u ∈ layer G r 1) :
    (branchTail G r u).card = ∑ z ∈ neighborsAt G r u 2, (neighborsAt G r z 3).card := by
  classical
  let N := neighborsAt G r u 2
  have hMem {z : V} (hz : z ∈ N) : z ∈ layer G r 2 :=
    (mem_layer G r).2 ((mem_neighborsAt G r).1 hz).2
  have hU : branchTail G r u = N.biUnion (fun z => neighborsAt G r z 3) := by
    ext x
    rw [mem_branchTail, Finset.mem_biUnion]
    constructor
    · rintro ⟨hx,z,hz,huz⟩
      exact ⟨z, (mem_neighborsAt G r).2 ⟨huz, ((mem_neighborsAt G r).1 hz).2⟩,
        (mem_neighborsAt G r).2 ⟨((mem_neighborsAt G r).1 hz).1.symm,(mem_layer G r).1 hx⟩⟩
    · rintro ⟨z,hz,hzx⟩
      exact ⟨(mem_layer G r).2 ((mem_neighborsAt G r).1 hzx).2, z,
        (mem_neighborsAt G r).2 ⟨((mem_neighborsAt G r).1 hzx).1.symm,(mem_layer G r).1 (hMem hz)⟩,
        ((mem_neighborsAt G r).1 hz).1⟩
  have hDisj : (N : Set V).PairwiseDisjoint (fun z => neighborsAt G r z 3) := by
    intro x hx y hy hxy
    apply Finset.disjoint_left.2
    intro z hxz hyz
    have hxN : x ∈ (neighborsAt G r z 2).filter (G.Adj u) := Finset.mem_filter.2
      ⟨(mem_neighborsAt G r).2 ⟨((mem_neighborsAt G r).1 hxz).1.symm,(mem_layer G r).1 (hMem hx)⟩,
        ((mem_neighborsAt G r).1 hx).1⟩
    have hyN : y ∈ (neighborsAt G r z 2).filter (G.Adj u) := Finset.mem_filter.2
      ⟨(mem_neighborsAt G r).2 ⟨((mem_neighborsAt G r).1 hyz).1.symm,(mem_layer G r).1 (hMem hy)⟩,
        ((mem_neighborsAt G r).1 hy).1⟩
    exact hxy (Finset.card_le_one_iff.1
      (first_direction_unique_child G r h4 ((mem_layer G r).2 ((mem_neighborsAt G r).1 hxz).2) hu)
      hxN hyN)
  rw [hU,Finset.card_biUnion hDisj]

private lemma branch_tail_card_of_single_second_edge
    (h4 : NoFourCycle G) (h3 : NoTriangle G) (hfar : ¬ Erdos934.HasFarEdges G 3)
    (hdeg : ∀ x, G.degree x ≤ 3) (hr : G.degree r = 3)
    (reg : ∀ x : V, (∃ y, G.Adj x y) → G.degree x = 3)
    {p q : V} (hp : p ∈ layer G r 2) (hq : q ∈ layer G r 2) (hpq : G.Adj p q)
    (he : ∀ x ∈ layer G r 2, ∀ y ∈ layer G r 2, G.Adj x y →
      (x = p ∧ y = q) ∨ (x = q ∧ y = p))
    {u : V} (hu : u ∈ layer G r 1) :
    (branchTail G r u).card = if G.Adj u p ∨ G.Adj u q then 3 else 4 := by
  classical
  let N := neighborsAt G r u 2
  have hN : N.card = 2 := branch_has_two_children G r h3 reg hu
  have hMem {z : V} (hz : z ∈ N) : z ∈ layer G r 2 :=
    (mem_layer G r).2 ((mem_neighborsAt G r).1 hz).2
  have hsum : (∑ z ∈ N, ((neighborsAt G r z 2).card + (neighborsAt G r z 3).card)) =
      N.card * 2 :=
    Finset.sum_const_nat (fun z hz => (second_degrees G r h4 hfar hdeg hr reg (hMem hz)).2)
  rw [Finset.sum_add_distrib,hN,← branch_tail_card_eq_sum G r h4 hu] at hsum
  have hX {z : V} (hz : z ∈ N) (hzp : z ≠ p) (hzq : z ≠ q) :
      (neighborsAt G r z 2).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨hzw,hwl⟩ := (mem_neighborsAt G r).1 hw
    exact (he z (hMem hz) w ((mem_layer G r).2 hwl) hzw).elim (fun h => hzp h.1) (fun h => hzq h.1)
  have hP : (neighborsAt G r p 2).card = 1 := by
    rw [show neighborsAt G r p 2 = {q} by
      ext w
      rw [Finset.mem_singleton,mem_neighborsAt]
      constructor
      · rintro ⟨hpw,hw2⟩
        rcases he p hp w ((mem_layer G r).2 hw2) hpw with h | h
        · exact h.2
        · exact (hpq.ne h.1).elim
      · rintro rfl
        exact ⟨hpq,(mem_layer G r).1 hq⟩,Finset.card_singleton]
  have hQ : (neighborsAt G r q 2).card = 1 := by
    rw [show neighborsAt G r q 2 = {p} by
      ext w
      rw [Finset.mem_singleton,mem_neighborsAt]
      constructor
      · rintro ⟨hqw,hw2⟩
        rcases he q hq w ((mem_layer G r).2 hw2) hqw with h | h
        · exact (hpq.ne h.1.symm).elim
        · exact h.2
      · rintro rfl
        exact ⟨hpq.symm,(mem_layer G r).1 hp⟩,Finset.card_singleton]
  have hpMem : p ∈ N ↔ G.Adj u p := ⟨fun h => ((mem_neighborsAt G r).1 h).1,
    fun h => (mem_neighborsAt G r).2 ⟨h,(mem_layer G r).1 hp⟩⟩
  have hqMem : q ∈ N ↔ G.Adj u q := ⟨fun h => ((mem_neighborsAt G r).1 h).1,
    fun h => (mem_neighborsAt G r).2 ⟨h,(mem_layer G r).1 hq⟩⟩
  by_cases hup : G.Adj u p
  · have hnq : ¬G.Adj u q := fun h => h3 hup h hpq
    rw [if_pos (Or.inl hup)]
    have hs₁ : (∑ z ∈ N, (neighborsAt G r z 2).card) = 1 := by
      rw [Finset.sum_eq_single_of_mem p (hpMem.2 hup),hP]
      intro z hz hzp
      exact hX hz hzp (fun h => hnq (hqMem.1 (h ▸ hz)))
    omega
  by_cases huq : G.Adj u q
  · rw [if_pos (Or.inr huq)]
    have hs₁ : (∑ z ∈ N, (neighborsAt G r z 2).card) = 1 := by
      rw [Finset.sum_eq_single_of_mem q (hqMem.2 huq),hQ]
      intro z hz hzq
      exact hX hz (fun h => hup (hpMem.1 (h ▸ hz))) hzq
    omega
  · rw [if_neg (not_or_intro hup huq)]
    have hs₀ : (∑ z ∈ N, (neighborsAt G r z 2).card) = 0 :=
      Finset.sum_eq_zero (fun z hz => hX hz (fun h => hup (hpMem.1 (h ▸ hz)))
        (fun h => huq (hqMem.1 (h ▸ hz))))
    omega


private abbrev PathEdges (C : Fin 6 ≃ (layer G r 3 : Type)) : Prop :=
  G.Adj (C 0).val (C 1).val ∧ G.Adj (C 0).val (C 2).val ∧
    G.Adj (C 3).val (C 4).val ∧ G.Adj (C 3).val (C 5).val

private def tailPredCount (j : Fin 6) : ℕ :=
  if j = 0 ∨ j = 3 then 1 else 2

private theorem two_path_tail_labels (h4 : NoFourCycle G) (hfar : ¬ Erdos934.HasFarEdges G 3)
    (reg : ∀ x : V, (∃ y, G.Adj x y) → G.degree x = 3) (hr : G.degree r = 3)
    (hL3 : (layer G r 3).card = 6)
    (hTwo : ((layer G r 3).filter (fun x => (neighborsAt G r x 2).card = 1)).card = 2) :
    ∃ C : Fin 6 ≃ (layer G r 3 : Type), PathEdges G r C ∧
      ∀ j, (neighborsAt G r (C j).val 2).card = tailPredCount j := by
  classical
  let T := (layer G r 3).filter (fun x => (neighborsAt G r x 2).card = 1)
  obtain ⟨x,y,hxy,hT⟩ := Finset.card_eq_two.1 (show T.card = 2 from hTwo)
  obtain ⟨hx,hx1⟩ := Finset.mem_filter.1 (show x ∈ T by rw [hT]; simp)
  obtain ⟨hy,hy1⟩ := Finset.mem_filter.1 (show y ∈ T by rw [hT]; simp)
  have center {z : V} (hz : z ∈ layer G r 3) (hz1 : (neighborsAt G r z 2).card = 1) :
      (neighborsAt G r z 3).card = 2 := by
    have he := (third_degrees G r h4 hfar reg hr hz).2
    omega
  obtain ⟨x₁,x₂,hx12,hX⟩ := Finset.card_eq_two.1 (center hx hx1)
  obtain ⟨y₁,y₂,hy12,hY⟩ := Finset.card_eq_two.1 (center hy hy1)
  have hx₁ : x₁ ∈ neighborsAt G r x 3 := by rw [hX]; simp
  have hx₂ : x₂ ∈ neighborsAt G r x 3 := by rw [hX]; simp
  have hy₁ : y₁ ∈ neighborsAt G r y 3 := by rw [hY]; simp
  have hy₂ : y₂ ∈ neighborsAt G r y 3 := by rw [hY]; simp
  have leaf {z w : V} (hz : z ∈ layer G r 3) (hz1 : (neighborsAt G r z 2).card = 1)
      (hw : w ∈ neighborsAt G r z 3) : (neighborsAt G r w 2).card = 2 := by
    obtain ⟨hzw,hwD⟩ := (mem_neighborsAt G r).1 hw
    have hWL := (mem_layer G r).2 hwD
    have hWdeg := (third_degrees G r h4 hfar reg hr hWL).2
    have hW3 : 0 < (neighborsAt G r w 3).card := Finset.card_pos.2
      ⟨z,(mem_neighborsAt G r).2 ⟨hzw.symm,(mem_layer G r).1 hz⟩⟩
    have hc := boundary_cover G r (k := 2) hfar hzw ((mem_layer G r).1 hz) hwD
    rw [hr,paths_three_eq G r h4, paths_three_eq G r h4,hz1] at hc
    omega
  have hNoCenter {z w : V} (hz : (neighborsAt G r z 2).card = 1)
      (hw : (neighborsAt G r w 2).card = 2) : z ≠ w := by rintro rfl; omega
  have hCross {u v : V} (hu : u ∈ neighborsAt G r x 3) (hv : v ∈ neighborsAt G r y 3) :
      u ≠ v := by
    rintro rfl
    obtain ⟨hxu,huD⟩ := (mem_neighborsAt G r).1 hu
    obtain ⟨hyu,_⟩ := (mem_neighborsAt G r).1 hv
    have hW := (third_degrees G r h4 hfar reg hr ((mem_layer G r).2 huD)).2
    have hW2 := leaf hx hx1 hu
    have hW3 : (neighborsAt G r u 3).card ≤ 1 := by omega
    have hxU : x ∈ neighborsAt G r u 3 :=
      (mem_neighborsAt G r).2 ⟨hxu.symm,(mem_layer G r).1 hx⟩
    have hyU : y ∈ neighborsAt G r u 3 :=
      (mem_neighborsAt G r).2 ⟨hyu.symm,(mem_layer G r).1 hy⟩
    exact hxy (Finset.card_le_one_iff.1 hW3 hxU hyU)
  let root₀ : (layer G r 3 : Type) := ⟨x,hx⟩
  let leaf₁ : (layer G r 3 : Type) := ⟨x₁,(mem_layer G r).2 ((mem_neighborsAt G r).1 hx₁).2⟩
  let leaf₂ : (layer G r 3 : Type) := ⟨x₂,(mem_layer G r).2 ((mem_neighborsAt G r).1 hx₂).2⟩
  let root₃ : (layer G r 3 : Type) := ⟨y,hy⟩
  let leaf₄ : (layer G r 3 : Type) := ⟨y₁,(mem_layer G r).2 ((mem_neighborsAt G r).1 hy₁).2⟩
  let leaf₅ : (layer G r 3 : Type) := ⟨y₂,(mem_layer G r).2 ((mem_neighborsAt G r).1 hy₂).2⟩
  let c : Fin 6 → (layer G r 3 : Type) := ![root₀,leaf₁,leaf₂,root₃,leaf₄,leaf₅]
  have hI : Function.Injective c := by
    apply List.nodup_ofFn.1
    change [root₀,leaf₁,leaf₂,root₃,leaf₄,leaf₅].Nodup
    simp [root₀,leaf₁,leaf₂,root₃,leaf₄,leaf₅, hxy,hx12,hy12,
      hNoCenter hx1 (leaf hx hx1 hx₁), hNoCenter hx1 (leaf hx hx1 hx₂),
      hNoCenter hx1 (leaf hy hy1 hy₁), hNoCenter hx1 (leaf hy hy1 hy₂),
      Ne.symm (hNoCenter hy1 (leaf hx hx1 hx₁)), Ne.symm (hNoCenter hy1 (leaf hx hx1 hx₂)),
      hNoCenter hy1 (leaf hy hy1 hy₁), hNoCenter hy1 (leaf hy hy1 hy₂),
      hCross hx₁ hy₁,hCross hx₁ hy₂,hCross hx₂ hy₁,hCross hx₂ hy₂]
  have hCard : Fintype.card (Fin 6) = Fintype.card (layer G r 3 : Type) := by simp [hL3]
  let C := Equiv.ofBijective c ((Fintype.bijective_iff_injective_and_card c).2 ⟨hI,hCard⟩)
  refine ⟨C,?_,?_⟩
  · exact ⟨((mem_neighborsAt G r).1 hx₁).1,((mem_neighborsAt G r).1 hx₂).1,
      ((mem_neighborsAt G r).1 hy₁).1,((mem_neighborsAt G r).1 hy₂).1⟩
  · intro j
    fin_cases j
    · exact hx1
    · exact leaf hx hx1 hx₁
    · exact leaf hx hx1 hx₂
    · exact hy1
    · exact leaf hy hy1 hy₁
    · exact leaf hy hy1 hy₂

private lemma branch_tail_card_via_labels (C : Fin 6 ≃ (layer G r 3 : Type)) (u : V) :
    (branchTail G r u).card = (Finset.univ.filter (fun j => Links G r u (C j).val)).card := by
  classical
  symm
  apply Finset.card_bij (fun j _ => (C j).val)
  · intro j hj
    exact (mem_branchTail G r).2 ⟨(C j).property,(Finset.mem_filter.1 hj).2⟩
  · intro i _ j _ hij
    exact C.injective (Subtype.ext hij)
  · intro x hx
    obtain ⟨hL,hx⟩ := (mem_branchTail G r).1 hx
    let j := C.symm ⟨x,hL⟩
    have hj : (C j).val = x := congrArg Subtype.val (C.apply_symm_apply ⟨x,hL⟩)
    exact ⟨j,Finset.mem_filter.2 ⟨Finset.mem_univ j,by rw [hj]; exact hx⟩,hj⟩

private lemma center_direction (h4 : NoFourCycle G)
    (hPar : ∀ z ∈ layer G r 2, (neighborsAt G r z 1).card = 1)
    {x : V} (hx : x ∈ layer G r 3) (hp : (neighborsAt G r x 2).card = 1) :
    ∃ a ∈ layer G r 1, ∀ u ∈ layer G r 1, Links G r u x ↔ u = a := by
  classical
  have h := directions_card_eq_predecessors G r h4 hPar hx
  rw [hp] at h
  obtain ⟨a,ha⟩ := Finset.card_eq_one.1 h
  have ham : a ∈ directions G r x := ha.symm ▸ Finset.mem_singleton_self a
  refine ⟨a,((mem_directions G r).1 ham).1,?_⟩
  intro u hu
  rw [← Finset.mem_singleton,← ha,mem_directions, and_iff_right hu]

private lemma leaf_direction (h4 : NoFourCycle G) (hfar : ¬ Erdos934.HasFarEdges G 3)
    (hPar : ∀ z ∈ layer G r 2, (neighborsAt G r z 1).card = 1)
    (hL1 : (layer G r 1).card = 3)
    {x y a : V} (hx : x ∈ layer G r 3) (hy : y ∈ layer G r 3) (hxy : G.Adj x y)
    (ha : a ∈ layer G r 1) (hp : (neighborsAt G r y 2).card = 2)
    (hCenter : ∀ u ∈ layer G r 1, Links G r u x ↔ u = a) :
    ∀ u ∈ layer G r 1, Links G r u y ↔ u ≠ a := by
  classical
  have hSub : (layer G r 1).erase a ⊆ directions G r y := by
    intro u hu
    obtain ⟨hne,huL⟩ := Finset.mem_erase.1 hu
    obtain ⟨z,hz,huz⟩ := edge_covers_first_directions G r hfar hx hy hxy huL
    rcases Finset.mem_union.1 hz with hz | hz
    · exact (hne ((hCenter u huL).1 ⟨z,hz,huz⟩)).elim
    · exact (mem_directions G r).2 ⟨huL,z,hz,huz⟩
  have hEq := Finset.eq_of_subset_of_card_le hSub (by
    rw [directions_card_eq_predecessors G r h4 hPar hy, hp, Finset.card_erase_of_mem ha,hL1])
  intro u hu
  calc
    _ ↔ u ∈ directions G r y := ((mem_directions G r).trans (and_iff_right hu)).symm
    _ ↔ u ∈ (layer G r 1).erase a := by rw [hEq]
    _ ↔ _ := Finset.mem_erase.trans (and_iff_left hu)

private def PathBranchUse (a b u : V) (j : Fin 6) : Prop :=
  if j = 0 then u = a else if j = 3 then u = b else if j = 1 ∨ j = 2 then u ≠ a else u ≠ b

private def twoPathBranchIndices (i : Fin 3) : Finset (Fin 6) :=
  ![{0,4,5}, {1,2,3}, {1,2,4,5}] i

private lemma twoPathBranchIndices_spec : ∀ (i : Fin 3) (j : Fin 6),
    (if j = 0 then i = 0 else if j = 3 then i = 1 else if j = 1 ∨ j = 2 then i ≠ 0 else i ≠ 1)
      ↔ j ∈ twoPathBranchIndices i := by
  decide +kernel

open scoped Classical in
theorem two_path_shape_canonical_labels (h4 : NoFourCycle G) (h3 : NoTriangle G)
    (hfar : ¬ Erdos934.HasFarEdges G 3)
    (hdeg : ∀ x, G.degree x ≤ 3) (hr : G.degree r = 3)
    (reg : ∀ x : V, (∃ y, G.Adj x y) → G.degree x = 3)
    (hL3 : (layer G r 3).card = 6)
    (hTwo : ((layer G r 3).filter (fun x => (neighborsAt G r x 2).card = 1)).card = 2)
    (hE : (G.induce (layer G r 2 : Set V)).edgeFinset.card = 1) :
    ∃ (A : Fin 3 ≃ (layer G r 1 : Type)) (C : Fin 6 ≃ (layer G r 3 : Type)),
      PathEdges G r C ∧
      (∀ (i : Fin 3) (j : Fin 6), Links G r (A i).val (C j).val ↔ j ∈ twoPathBranchIndices i) ∧
      ∃ x ∈ neighborsAt G r (A 0).val 2,
        ∃ y ∈ neighborsAt G r (A 1).val 2, G.Adj x y := by
  classical
  have hL1 : (layer G r 1).card = 3 := by
    rw [layer_one, G.card_neighborFinset_eq_degree, hr]
  have hPar (z : V) (hz : z ∈ layer G r 2) : (neighborsAt G r z 1).card = 1 :=
    (second_degrees G r h4 hfar hdeg hr reg hz).1
  obtain ⟨p,hp,q,hq,hpq,hUnique⟩ := internal_second_edge_unique G r hE
  obtain ⟨C, hC, hCount⟩ := two_path_tail_labels G r h4 hfar reg hr hL3 hTwo
  obtain ⟨a,ha,hA⟩ := center_direction G r h4 hPar (C 0).property (hCount 0)
  obtain ⟨b,hb,hB⟩ := center_direction G r h4 hPar (C 3).property (hCount 3)
  have h₁ := leaf_direction G r h4 hfar hPar hL1 (C 0).property (C 1).property hC.1 ha
    (hCount 1) hA
  have h₂ := leaf_direction G r h4 hfar hPar hL1 (C 0).property (C 2).property hC.2.1 ha
    (hCount 2) hA
  have h₄ := leaf_direction G r h4 hfar hPar hL1 (C 3).property (C 4).property hC.2.2.1 hb
    (hCount 4) hB
  have h₅ := leaf_direction G r h4 hfar hPar hL1 (C 3).property (C 5).property hC.2.2.2 hb
    (hCount 5) hB
  have hUse (u : V) (hu : u ∈ layer G r 1) (j : Fin 6) :
      Links G r u (C j).val ↔ PathBranchUse a b u j := by
    fin_cases j
    · exact hA u hu
    · exact h₁ u hu
    · exact h₂ u hu
    · exact hB u hu
    · exact h₄ u hu
    · exact h₅ u hu
  have hBranch (u : V) (hu : u ∈ layer G r 1) :
      (branchTail G r u).card = if G.Adj u p ∨ G.Adj u q then 3 else 4 :=
    branch_tail_card_of_single_second_edge G r h4 h3 hfar hdeg hr reg hp hq hpq hUnique hu
  have hab : a ≠ b := by
    intro he
    have hSet : (Finset.univ.filter (fun j => Links G r a (C j).val)) ⊆ ({0,3} : Finset (Fin 6)) := by
      intro j hj
      have hu := (hUse a ha j).1 (Finset.mem_filter.1 hj).2
      subst b
      fin_cases j
      · exact Finset.mem_insert_self 0 _
      · exact ((show a ≠ a from hu) rfl).elim
      · exact ((show a ≠ a from hu) rfl).elim
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self 3)
      · exact ((show a ≠ a from hu) rfl).elim
      · exact ((show a ≠ a from hu) rfl).elim
    have hSmall := Finset.card_le_card hSet
    rw [← branch_tail_card_via_labels] at hSmall
    change (branchTail G r a).card ≤ 2 at hSmall
    have hag := hBranch a ha
    split at hag <;> omega
  have hPair : ({a,b} : Finset V) ⊆ layer G r 1 := by simp [Finset.insert_subset_iff,ha,hb]
  have hPairCard : ({a,b} : Finset V).card = 2 := Finset.card_eq_two.2 ⟨a,b,hab,rfl⟩
  have hDif := Finset.card_sdiff_add_card_eq_card hPair
  rw [hPairCard,hL1] at hDif
  obtain ⟨c,hc⟩ : ((layer G r 1) \ {a,b}).Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨hc,hcab⟩ := Finset.mem_sdiff.1 hc
  have hac : a ≠ c := fun h => hcab (by simp [← h])
  have hbc : b ≠ c := fun h => hcab (by simp [← h])
  let vA : (layer G r 1 : Type) := ⟨a,ha⟩
  let vB : (layer G r 1 : Type) := ⟨b,hb⟩
  let vC : (layer G r 1 : Type) := ⟨c,hc⟩
  let f : Fin 3 → (layer G r 1 : Type) := ![vA,vB,vC]
  have hInj : Function.Injective f := by
    apply List.nodup_ofFn.1
    change [vA,vB,vC].Nodup
    simp [vA,vB,vC,hab,hac,hbc]
  have hCard : Fintype.card (Fin 3) = Fintype.card (layer G r 1 : Type) := by simp [hL1]
  let A := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨hInj,hCard⟩)
  have hAidx (i : Fin 3) : (A i).val = a ↔ i = 0 := by
    change (A i).val = (A 0).val ↔ i = 0
    exact ⟨fun h => A.injective (Subtype.ext h), fun h => h ▸ rfl⟩
  have hBidx (i : Fin 3) : (A i).val = b ↔ i = 1 := by
    change (A i).val = (A 1).val ↔ i = 1
    exact ⟨fun h => A.injective (Subtype.ext h), fun h => h ▸ rfl⟩
  have hLabels (i : Fin 3) (j : Fin 6) :
      Links G r (A i).val (C j).val ↔ j ∈ twoPathBranchIndices i := by
    rw [hUse (A i).val (A i).property j]
    simpa only [PathBranchUse,ne_eq,hAidx,hBidx] using twoPathBranchIndices_spec i j
  have hBranchCard (i : Fin 3) : (branchTail G r (A i).val).card = (twoPathBranchIndices i).card := by
    rw [branch_tail_card_via_labels G r C]
    congr 1
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,hLabels]
  have hEndpoint (u : V) (hu : u ∈ layer G r 1) (h : (branchTail G r u).card = 3) :
      G.Adj u p ∨ G.Adj u q := by
    by_contra hn
    have he := hBranch u hu
    rw [if_neg hn,h] at he
    exact (by decide : (3 : ℕ) ≠ 4) he
  have hAP := hEndpoint a ha (hBranchCard 0)
  have hBP := hEndpoint b hb (hBranchCard 1)
  have hOneParent {z : V} (hz : z ∈ layer G r 2) (haz : G.Adj a z) (hbz : G.Adj b z) : False := by
    have haZ : a ∈ neighborsAt G r z 1 := (mem_neighborsAt G r).2 ⟨haz.symm,(mem_layer G r).1 ha⟩
    have hbZ : b ∈ neighborsAt G r z 1 := (mem_neighborsAt G r).2 ⟨hbz.symm,(mem_layer G r).1 hb⟩
    exact hab (Finset.card_le_one_iff.1 (le_of_eq (hPar z hz)) haZ hbZ)
  refine ⟨A,C,hC,hLabels,?_⟩
  rcases hAP with haP | haQ <;> rcases hBP with hbP | hbQ
  · exact (hOneParent hp haP hbP).elim
  · exact ⟨p,(mem_neighborsAt G r).2 ⟨haP,(mem_layer G r).1 hp⟩,
      q,(mem_neighborsAt G r).2 ⟨hbQ,(mem_layer G r).1 hq⟩,hpq⟩
  · exact ⟨q,(mem_neighborsAt G r).2 ⟨haQ,(mem_layer G r).1 hq⟩,
      p,(mem_neighborsAt G r).2 ⟨hbP,(mem_layer G r).1 hp⟩,hpq.symm⟩
  · exact (hOneParent hq haQ hbQ).elim
end TwoPathShape

section PathEdgeShape

variable {T : Type} [Fintype T] [DecidableEq T] (H : SimpleGraph T) [DecidableRel H.Adj]

private theorem pathEdgeTailOrder (hcard : Fintype.card T = 6)
    (p q : T) (hp : H.degree p = 2)
    (hsmall : ∀ x : T, x ≠ p → H.degree x ≤ 1)
    (hq : H.degree q = 0) (hpos : ∀ x : T, x ≠ q → 0 < H.degree x) :
    ∃ C : Fin 6 ≃ T, C 0 = p ∧ C 5 = q ∧
      H.Adj (C 0) (C 1) ∧ H.Adj (C 0) (C 2) ∧ H.Adj (C 3) (C 4) := by
  classical
  have hp' : (H.neighborFinset p).card = 2 := (H.card_neighborFinset_eq_degree p).trans hp
  obtain ⟨u, v, huv, hpN⟩ := Finset.card_eq_two.mp hp'
  have hpu : H.Adj p u := (H.mem_neighborFinset p u).mp (hpN ▸ by simp)
  have hpv : H.Adj p v := (H.mem_neighborFinset p v).mp (hpN ▸ by simp)
  have hqN : H.neighborFinset q = ∅ :=
    Finset.card_eq_zero.mp ((H.card_neighborFinset_eq_degree q).trans hq)
  have hq' (x : T) : ¬ H.Adj x q := by
    intro hx
    have hm := (H.mem_neighborFinset q x).mpr hx.symm
    simp [hqN] at hm
  have hpu' : p ≠ u := hpu.ne
  have hpv' : p ≠ v := hpv.ne
  have hpq : p ≠ q := by
    intro e
    rw [e, hq] at hp
    omega
  have huq : u ≠ q := fun e => hq' p (e ▸ hpu)
  have hvq : v ≠ q := fun e => hq' p (e ▸ hpv)
  let excluded : Finset T := {p, u, v, q}
  have hEx : excluded.card = 4 := by simp [excluded, hpu', hpv', hpq, huv, huq, hvq]
  have hxExists : (Finset.univ \ excluded).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hcard, hEx]
    decide
  obtain ⟨x, hx⟩ := hxExists
  have ho : ∀ z ∉ excluded, z ≠ p ∧ z ≠ u ∧ z ≠ v ∧ z ≠ q := by
    intro z hz
    simpa [excluded] using hz
  obtain ⟨hxp, hxu, hxv, hxq⟩ := ho x (Finset.mem_sdiff.mp hx).2
  obtain ⟨y, hy⟩ := Finset.card_pos.mp ((H.card_neighborFinset_eq_degree x).symm ▸ hpos x hxq)
  have hxy : H.Adj x y := (H.mem_neighborFinset x y).mp hy
  have hyp : y ≠ p := by
    intro e
    have hm := (H.mem_neighborFinset p x).mpr (e ▸ hxy.symm)
    simp [hpN, hxu, hxv] at hm
  have hyOne {w : T} (hw : H.Adj p w) : y ≠ w := by
    intro e
    have hc : (H.neighborFinset w).card ≤ 1 :=
      (H.card_neighborFinset_eq_degree w).trans_le (hsmall w hw.ne.symm)
    exact hxp (Finset.card_le_one_iff.mp hc
      ((H.mem_neighborFinset w x).mpr (e ▸ hxy.symm))
      ((H.mem_neighborFinset w p).mpr hw.symm))
  have hyu := hyOne hpu
  have hyv := hyOne hpv
  have hyq : y ≠ q := fun e => hq' x (e ▸ hxy)
  let f : Fin 6 → T := ![p, u, v, x, y, q]
  have hf : Function.Injective f := by
    intro i j he
    fin_cases i <;> fin_cases j
    all_goals try rfl
    all_goals
      exfalso
      simp only [f, Matrix.cons_val_zero', Matrix.cons_val_succ'] at he
      solve_by_elim [Ne.symm, hxy.ne]
  have hf' : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr
    ⟨hf, (Fintype.card_fin 6).trans hcard.symm⟩
  exact ⟨Equiv.ofBijective f hf', rfl, rfl, hpu, hpv, hxy⟩

end PathEdgeShape

section PathEdgeDirections

variable {A T : Type} [Fintype A] [DecidableEq A]

private theorem pathEdgeDirectionOrder (hcard : Fintype.card A = 3)
    (C : Fin 6 ≃ T) (D : T → Finset A)
    (h0 : (D (C 0)).card = 1) (h1 : (D (C 1)).card = 2)
    (h2 : (D (C 2)).card = 2) (h3 : (D (C 3)).card = 2)
    (h4 : (D (C 4)).card = 2) (h5 : (D (C 5)).card = 3)
    (cov01 : ∀ u, u ∈ D (C 0) ∨ u ∈ D (C 1))
    (cov02 : ∀ u, u ∈ D (C 0) ∨ u ∈ D (C 2))
    (cov34 : ∀ u, u ∈ D (C 3) ∨ u ∈ D (C 4))
    (hrow : ∀ u, (Finset.univ.filter (fun j : Fin 6 => u ∈ D (C j))).card = 4) :
    ∃ B : Fin 3 ≃ A, ∀ (i : Fin 3) (j : Fin 6),
      B i ∈ D (C j) ↔ j ∈ (![({0,3,4,5} : Finset (Fin 6)), {1,2,4,5}, {1,2,3,5}] i) := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h0
  have hd5 : D (C 5) = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp [hcard, h5])
  have herase {S : Finset A} (hS : S.card = 2)
      (hcov : ∀ u : A, u ∈ D (C 0) ∨ u ∈ S) : S = Finset.univ.erase a := by
    apply Eq.symm
    apply Finset.eq_of_subset_of_card_le
    · intro u hu
      have hua := (Finset.mem_erase.mp hu).1
      exact (hcov u).resolve_left (by simpa [ha] using hua)
    · simp [hS, hcard]
  have hd1 := herase h1 cov01
  have hd2 := herase h2 cov02
  let row : Finset (Fin 6) := Finset.univ.filter (fun j => a ∈ D (C j))
  have hrow' : row = {0,3,4,5} := by
    apply Finset.eq_of_subset_of_card_le
    · intro j hj
      have h1' : (1 : Fin 6) ∉ row := by simp [row, hd1]
      have h2' : (2 : Fin 6) ∉ row := by simp [row, hd2]
      fin_cases j <;> first | decide | exact False.elim (h1' hj) | exact False.elim (h2' hj)
    · rw [hrow a]
      decide
  have ha3 : a ∈ D (C 3) := (Finset.mem_filter.mp (show (3 : Fin 6) ∈ row by rw [hrow']; decide)).2
  have ha4 : a ∈ D (C 4) := (Finset.mem_filter.mp (show (4 : Fin 6) ∈ row by rw [hrow']; decide)).2
  have homit {S : Finset A} (hS : S.card = 2) : ∃ b : A, S = Finset.univ.erase b := by
    have hb : (Finset.univ \ S).card = 1 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hcard, hS]
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hb
    refine ⟨b, ?_⟩
    ext u
    have hh : u ∉ S ↔ u = b := by
      simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton]
        using Iff.of_eq (congrArg (fun U : Finset A => u ∈ U) hb)
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    tauto
  obtain ⟨b, hb⟩ := homit h3
  obtain ⟨c, hc⟩ := homit h4
  have hab : a ≠ b := by simpa [hb] using ha3
  have hac : a ≠ c := by simpa [hc] using ha4
  have hbc : b ≠ c := by
    intro he
    simpa [hb, hc, he] using cov34 c
  let f : Fin 3 → A := ![a, b, c]
  have hf : Function.Injective f := by
    intro i j he
    fin_cases i <;> fin_cases j
    all_goals try rfl
    all_goals
      exfalso
      simp only [f, Matrix.cons_val_zero', Matrix.cons_val_succ'] at he
      solve_by_elim [Ne.symm]
  let e := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr
    ⟨hf, (Fintype.card_fin 3).trans hcard.symm⟩)
  refine ⟨e, ?_⟩
  intro i j
  change f i ∈ D (C j) ↔ _
  fin_cases i <;> fin_cases j <;>
    simp [f, ha, hb, hc, hd1, hd2, hd5, hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]

end PathEdgeDirections

section PathEdgeGraph

variable {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)

open scoped Classical in
private lemma branch_tail_card_of_no_second_edge (h4 : NoFourCycle G) (h3 : NoTriangle G)
    (hfar : ¬ Erdos934.HasFarEdges G 3) (hMax : ∀ x, G.degree x ≤ 3)
    (hr : G.degree r = 3) (reg : ∀ x : V, (∃ y, G.Adj x y) → G.degree x = 3)
    (he : (G.induce (layer G r 2 : Set V)).edgeFinset.card = 0)
    {u : V} (hu : u ∈ layer G r 1) : (branchTail G r u).card = 4 := by
  classical
  have hs := sum_incident_inside_layer G r 2
  rw [he, Nat.mul_zero] at hs
  have hz2 (z : V) (hz : z ∈ layer G r 2) : (neighborsAt G r z 2).card = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hs z hz
  rw [branch_tail_card_eq_sum G r h4 hu]
  calc
    _ = (neighborsAt G r u 2).card * 2 := by
      apply Finset.sum_const_nat
      intro z hz
      have hzL := (mem_layer G r).mpr ((mem_neighborsAt G r).mp hz).2
      have hh := (second_degrees G r h4 hfar hMax hr reg hzL).2
      rw [hz2 z hzL, zero_add] at hh
      exact hh
    _ = 4 := by rw [branch_has_two_children G r h3 reg hu]

open scoped Classical in
private theorem pathEdgeCanonicalLabels (h4 : NoFourCycle G)
    (h3 : NoTriangle G) (hfar : ¬ Erdos934.HasFarEdges G 3)
    (hMax : ∀ x, G.degree x ≤ 3) (hr : G.degree r = 3)
    (reg : ∀ x : V, (∃ y, G.Adj x y) → G.degree x = 3)
    (hL3 : (layer G r 3).card = 6)
    (hx : ((layer G r 3).filter (fun x => (neighborsAt G r x 2).card = 1)).card = 1)
    (hz : ((layer G r 3).filter (fun x => (neighborsAt G r x 2).card = 3)).card = 1)
    (he : (G.induce (layer G r 2 : Set V)).edgeFinset.card = 0) :
    ∃ (A : Fin 3 ≃ (layer G r 1 : Type)) (C : Fin 6 ≃ (layer G r 3 : Type)),
      G.Adj (C 0).val (C 1).val ∧ G.Adj (C 0).val (C 2).val ∧ G.Adj (C 3).val (C 4).val ∧
      ∀ (i : Fin 3) (j : Fin 6), (∃ z ∈ neighborsAt G r (C j).val 2, G.Adj (A i).val z) ↔
        j ∈ (![({0,3,4,5} : Finset (Fin 6)), {1,2,4,5}, {1,2,3,5}] i) := by
  classical
  have hPar (z : V) (hz : z ∈ layer G r 2) : (neighborsAt G r z 1).card = 1 :=
    (second_degrees G r h4 hfar hMax hr reg hz).1
  have hD (x : V) (hx : x ∈ layer G r 3) :
      (directions G r x).card = (neighborsAt G r x 2).card :=
    directions_card_eq_predecessors G r h4 hPar hx
  have hB (u : V) (hu : u ∈ layer G r 1) : (branchTail G r u).card = 4 :=
    branch_tail_card_of_no_second_edge G r h4 h3 hfar hMax hr reg he hu
  obtain ⟨p, hpS⟩ := Finset.card_eq_one.mp hx
  obtain ⟨q, hqS⟩ := Finset.card_eq_one.mp hz
  have hp := Finset.mem_filter.mp (show p ∈ (layer G r 3).filter
      (fun x => (neighborsAt G r x 2).card = 1) by simp [hpS])
  have hq := Finset.mem_filter.mp (show q ∈ (layer G r 3).filter
      (fun x => (neighborsAt G r x 2).card = 3) by simp [hqS])
  let P : (layer G r 3 : Type) := ⟨p, hp.1⟩
  let Q : (layer G r 3 : Type) := ⟨q, hq.1⟩
  let H := G.induce (layer G r 3 : Set V)
  have hdeg (x : (layer G r 3 : Type)) :
      0 < (neighborsAt G r x.val 2).card ∧ (neighborsAt G r x.val 2).card + H.degree x = 3 := by
    rw [show H.degree x = (neighborsAt G r x.val 3).card from layer_induced_degree G r x]
    exact third_degrees G r h4 hfar reg hr x.property
  have hp2 : H.degree P = 2 := by
    have hh := (hdeg P).2
    change (neighborsAt G r p 2).card + H.degree P = 3 at hh
    omega
  have hq0 : H.degree Q = 0 := by
    have hh := (hdeg Q).2
    change (neighborsAt G r q 2).card + H.degree Q = 3 at hh
    omega
  have hpUnique (x : (layer G r 3 : Type)) (h : (neighborsAt G r x.val 2).card = 1) : x = P := by
    apply Subtype.ext
    have hm : x.val ∈ (layer G r 3).filter
        (fun y => (neighborsAt G r y 2).card = 1) := Finset.mem_filter.mpr ⟨x.property, h⟩
    rwa [hpS, Finset.mem_singleton] at hm
  have hqUnique (x : (layer G r 3 : Type)) (h : (neighborsAt G r x.val 2).card = 3) : x = Q := by
    apply Subtype.ext
    have hm : x.val ∈ (layer G r 3).filter
        (fun y => (neighborsAt G r y 2).card = 3) := Finset.mem_filter.mpr ⟨x.property, h⟩
    rwa [hqS, Finset.mem_singleton] at hm
  have hsmall (x : (layer G r 3 : Type)) (hxp : x ≠ P) : H.degree x ≤ 1 := by
    have ⟨h1, h2⟩ := hdeg x
    have hn : (neighborsAt G r x.val 2).card ≠ 1 := fun e => hxp (hpUnique x e)
    omega
  have hpos (x : (layer G r 3 : Type)) (hxq : x ≠ Q) : 0 < H.degree x := by
    have h2 := (hdeg x).2
    have hn : (neighborsAt G r x.val 2).card ≠ 3 := fun e => hxq (hqUnique x e)
    omega
  obtain ⟨C, hc0, hc5, h01, h02, h34⟩ :=
    pathEdgeTailOrder H (by simpa using hL3) P Q hp2 hsmall hq0 hpos
  let D (x : (layer G r 3 : Type)) : Finset (layer G r 1 : Type) :=
    Finset.univ.filter (fun u => ∃ z ∈ neighborsAt G r x.val 2, G.Adj u.val z)
  have hmem {x : (layer G r 3 : Type)} {u : (layer G r 1 : Type)} :
      u ∈ D x ↔ ∃ z ∈ neighborsAt G r x.val 2, G.Adj u.val z := by simp [D]
  have hDcard (x : (layer G r 3 : Type)) :
      (D x).card = (neighborsAt G r x.val 2).card := by
    rw [← hD x.val x.property]
    apply Finset.card_bij (fun u _ => u.val)
    · intro u hu
      exact (mem_directions G r).mpr ⟨u.property, hmem.mp hu⟩
    · intro u _ v _ he
      exact Subtype.ext he
    · intro u hu
      obtain ⟨hu1, hul⟩ := (mem_directions G r).mp hu
      exact ⟨⟨u, hu1⟩, hmem.mpr hul, rfl⟩
  have hAcard : Fintype.card (layer G r 1 : Type) = 3 := by
    rw [Fintype.card_coe, layer_one, G.card_neighborFinset_eq_degree, hr]
  have hBcard (u : (layer G r 1 : Type)) :
      (Finset.univ.filter (fun j : Fin 6 => u ∈ D (C j))).card = 4 := by
    rw [← hB u.val u.property]
    apply Finset.card_bij (fun j _ => (C j).val)
    · intro j hj
      exact (mem_branchTail G r).mpr ⟨(C j).property, hmem.mp (Finset.mem_filter.mp hj).2⟩
    · intro i _ j _ he
      exact C.injective (Subtype.ext he)
    · intro v hv
      obtain ⟨hv3, hvl⟩ := (mem_branchTail G r).mp hv
      obtain ⟨j, hj⟩ := C.surjective ⟨v, hv3⟩
      refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem.mpr ?_⟩, congrArg Subtype.val hj⟩
      rw [hj]
      exact hvl
  have hcover {i j : Fin 6} (hij : H.Adj (C i) (C j)) (u : (layer G r 1 : Type)) :
      u ∈ D (C i) ∨ u ∈ D (C j) := by
    obtain ⟨z, hz, huz⟩ := edge_covers_first_directions G r hfar
      (C i).property (C j).property hij u.property
    rcases Finset.mem_union.mp hz with hz | hz
    · exact Or.inl (hmem.mpr ⟨z, hz, huz⟩)
    · exact Or.inr (hmem.mpr ⟨z, hz, huz⟩)
  have hmid (j : Fin 6) (hj0 : j ≠ 0) (hj5 : j ≠ 5) : (D (C j)).card = 2 := by
    rw [hDcard]
    have h := hdeg (C j)
    have h1 := hsmall (C j) (fun he => hj0 (C.injective (he.trans hc0.symm)))
    have h2 := hpos (C j) (fun he => hj5 (C.injective (he.trans hc5.symm)))
    omega
  have hd0 : (D (C 0)).card = 1 := by
    rw [hDcard, hc0]
    exact hp.2
  have hd5 : (D (C 5)).card = 3 := by
    rw [hDcard, hc5]
    exact hq.2
  obtain ⟨A, hA⟩ := pathEdgeDirectionOrder hAcard C D hd0
    (hmid 1 (by decide) (by decide)) (hmid 2 (by decide) (by decide))
    (hmid 3 (by decide) (by decide)) (hmid 4 (by decide) (by decide)) hd5
    (hcover h01) (hcover h02) (hcover h34) hBcard
  exact ⟨A, C, h01, h02, h34, fun i j => hmem.symm.trans (hA i j)⟩

end PathEdgeGraph

section PerfectTail

variable {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)

private noncomputable def tailDirections (x : V) : Finset V := by
  classical
  exact (neighborsAt G r x 2).biUnion (fun z => neighborsAt G r z 1)

private lemma mem_tailDirections {x u : V} (hu : u ∈ layer G r 1) :
    u ∈ tailDirections G r x ↔ ∃ z ∈ neighborsAt G r x 2, G.Adj u z := by
  classical
  simp only [tailDirections, Finset.mem_biUnion, mem_neighborsAt G r (x := _)]
  have hu' := (mem_layer G r).mp hu
  constructor
  · rintro ⟨z,⟨hxz,hrz⟩,hzu,_⟩
    exact ⟨z,⟨hxz,hrz⟩,hzu.symm⟩
  · rintro ⟨z,⟨hxz,hrz⟩,huz⟩
    exact ⟨z,⟨hxz,hrz⟩,huz.symm,hu'⟩

open scoped Classical in
private lemma tailDirections_subset (x : V) :
    tailDirections G r x ⊆ layer G r 1 := by
  intro u hu
  obtain ⟨_,_,hz⟩ := Finset.mem_biUnion.mp hu
  exact (mem_layer G r).mpr ((mem_neighborsAt G r).mp hz).2

private lemma tailDirections_card (h4 : NoFourCycle G)
    (hfar : ¬ Erdos934.HasFarEdges G 3) (hdeg : ∀ x, G.degree x ≤ 3)
    (hr : G.degree r = 3) (reg : ∀ x : V, (∃ y, G.Adj x y) → G.degree x = 3)
    {x : V} (hx : x ∈ layer G r 3) :
    (tailDirections G r x).card = (neighborsAt G r x 2).card := by
  classical
  have hp : ((neighborsAt G r x 2 : Finset V) : Set V).PairwiseDisjoint
      (fun z => neighborsAt G r z 1) := by
    intro y hy z hz hyz
    apply Finset.disjoint_left.mpr
    intro u huy huz
    obtain ⟨hyu,hru⟩ := (mem_neighborsAt G r).mp huy
    obtain ⟨hzu,_⟩ := (mem_neighborsAt G r).mp huz
    have hc := first_direction_unique_child G r h4 hx ((mem_layer G r).mpr hru)
    exact hyz (Finset.card_le_one_iff.mp hc
      (Finset.mem_filter.mpr ⟨hy,hyu.symm⟩) (Finset.mem_filter.mpr ⟨hz,hzu.symm⟩))
  unfold tailDirections
  rw [Finset.card_biUnion hp]
  have h : (∑ z ∈ neighborsAt G r x 2, (neighborsAt G r z 1).card) =
      (neighborsAt G r x 2).card * 1 := by
    apply Finset.sum_const_nat
    intro z hz
    exact (second_degrees G r h4 hfar hdeg hr reg
      ((mem_layer G r).mpr ((mem_neighborsAt G r).mp hz).2)).1
  simpa only [Nat.mul_one] using h

open scoped Classical in
private lemma tails_seen_from_branch (h4 : NoFourCycle G) (h3 : NoTriangle G)
    (hfar : ¬ Erdos934.HasFarEdges G 3) (hdeg : ∀ x, G.degree x ≤ 3)
    (hr : G.degree r = 3) (reg : ∀ x : V, (∃ y, G.Adj x y) → G.degree x = 3)
    (hNo22 : ∀ x ∈ layer G r 2, ∀ y ∈ layer G r 2, ¬ G.Adj x y)
    {u : V} (hu : u ∈ layer G r 1) :
    ((layer G r 3).filter (fun x => u ∈ tailDirections G r x)).card = 4 := by
  classical
  let T := (layer G r 3).filter (fun x => u ∈ tailDirections G r x)
  let P := neighborsAt G r u 2
  have he : T = P.biUnion (fun z => neighborsAt G r z 3) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hx,hux⟩ := Finset.mem_filter.mp hx
      obtain ⟨z,hxz,huz⟩ := (mem_tailDirections G r hu).mp hux
      have hz := (mem_neighborsAt G r).mp hxz
      exact Finset.mem_biUnion.mpr ⟨z,(mem_neighborsAt G r).mpr ⟨huz,hz.2⟩,
        (mem_neighborsAt G r).mpr ⟨hz.1.symm,(mem_layer G r).mp hx⟩⟩
    · intro hx
      obtain ⟨z,hz,hx⟩ := Finset.mem_biUnion.mp hx
      have hzu := (mem_neighborsAt G r).mp hz
      have hxz := (mem_neighborsAt G r).mp hx
      exact Finset.mem_filter.mpr ⟨(mem_layer G r).mpr hxz.2,
        (mem_tailDirections G r hu).mpr
          ⟨z,(mem_neighborsAt G r).mpr ⟨hxz.1.symm,hzu.2⟩,hzu.1⟩⟩
  have hd : (P : Set V).PairwiseDisjoint (fun z => neighborsAt G r z 3) := by
    intro y hy z hz hyz
    apply Finset.disjoint_left.mpr
    intro x hxy hxz
    have hym := (mem_neighborsAt G r).mp hy
    have hzm := (mem_neighborsAt G r).mp hz
    have hxy' := (mem_neighborsAt G r).mp hxy
    have hxz' := (mem_neighborsAt G r).mp hxz
    have hx := (mem_layer G r).mpr hxy'.2
    have hc := first_direction_unique_child G r h4 hx hu
    exact hyz (Finset.card_le_one_iff.mp hc
      (Finset.mem_filter.mpr ⟨(mem_neighborsAt G r).mpr ⟨hxy'.1.symm,hym.2⟩,hym.1⟩)
      (Finset.mem_filter.mpr ⟨(mem_neighborsAt G r).mpr ⟨hxz'.1.symm,hzm.2⟩,hzm.1⟩))
  have hs : (∑ z ∈ P, (neighborsAt G r z 3).card) = P.card * 2 := by
    apply Finset.sum_const_nat
    intro z hz
    have hz' := (mem_layer G r).mpr ((mem_neighborsAt G r).mp hz).2
    have h0 : neighborsAt G r z 2 = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      have hm := (mem_neighborsAt G r).mp hw
      exact hNo22 z hz' w ((mem_layer G r).mpr hm.2) hm.1
    have hh := (second_degrees G r h4 hfar hdeg hr reg hz').2
    simpa only [h0,Finset.card_empty,Nat.zero_add] using hh
  change T.card = 4
  rw [he,Finset.card_biUnion hd,hs]
  change (neighborsAt G r u 2).card * 2 = 4
  rw [branch_has_two_children G r h3 reg hu]

end PerfectTail

section MatchingRelabel

private def matchingPairs : List (Fin 6 × Fin 6) :=
  [(0,1),(1,0),(2,3),(3,2),(4,5),(5,4)]

private def matchingRead (μ : Fin 6 → Fin 3) (a b : Fin 3) : Fin 6 × Fin 6 :=
  (matchingPairs.find? (fun (i,j) => μ i == a && μ j == b)).getD (0,0)

private def matchingOrder (μ : Fin 6 → Fin 3) : Fin 6 → Fin 6 :=
  ![(matchingRead μ 0 1).1,(matchingRead μ 0 1).2,
    (matchingRead μ 0 2).1,(matchingRead μ 0 2).2,
    (matchingRead μ 1 2).1,(matchingRead μ 1 2).2]

private def expectedMissing : Fin 6 → Fin 3 := ![0,1,0,2,1,2]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem matchingOrder_checked :
    ∀ μ : Fin 6 → Fin 3,
      (∀ a : Fin 3, (Finset.univ.filter fun i => μ i = a).card = 2) →
      (μ 0 ≠ μ 1 ∧ μ 2 ≠ μ 3 ∧ μ 4 ≠ μ 5) →
      (∀ i j : Fin 6, matchingOrder μ i = matchingOrder μ j → i = j) ∧
      (matchingOrder μ 0, matchingOrder μ 1) ∈ matchingPairs ∧
      (matchingOrder μ 2, matchingOrder μ 3) ∈ matchingPairs ∧
      (matchingOrder μ 4, matchingOrder μ 5) ∈ matchingPairs ∧
      (∀ i : Fin 6, μ (matchingOrder μ i) = expectedMissing i) := by
  decide +kernel

private def seenList (i : Fin 3) : List (Fin 6) :=
  if i = 0 then [1,3,4,5]
  else if i = 1 then [0,2,3,5] else [0,1,2,4]

private theorem seenList_spec : ∀ (i : Fin 3) (j : Fin 6),
    i ≠ expectedMissing j ↔ j ∈ seenList i := by decide +kernel

private lemma pair_complement_exhaust {X : Type*} [Fintype X] (hX : Fintype.card X = 6)
    (g : X → X) (hg : Function.Involutive g) (hne : ∀ x, x ≠ g x) :
    ∃ q : Fin 6 ≃ X, g (q 0) = q 1 ∧ g (q 2) = q 3 ∧ g (q 4) = q 5 := by
  classical
  let small (S : Finset X) (x : X) := insert x (insert (g x) S)
  have hClosed (S : Finset X) (h : ∀ x ∈ S, g x ∈ S) (x : X) :
      ∀ y ∈ small S x, g y ∈ small S x := by
    intro y hy
    simp only [small,Finset.mem_insert] at hy ⊢
    rcases hy with rfl | rfl | hy
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (hg x)
    · exact Or.inr (Or.inr (h y hy))
  have hSmallCard (S : Finset X) (x : X) : (small S x).card ≤ S.card + 2 := by
    dsimp [small]
    have h₁ := Finset.card_insert_le x (insert (g x) S)
    have h₂ := Finset.card_insert_le (g x) S
    omega
  have outside (S : Finset X) (hS : S.card < 6) : ∃ x, x ∉ S := by
    by_contra! hh
    have he : S = Finset.univ := Finset.eq_univ_iff_forall.mpr hh
    rw [he,Finset.card_univ,hX] at hS
    omega
  have hm (S : Finset X) (hS : ∀ x ∈ S, g x ∈ S) {x : X} (hx : x ∉ S) :
      g x ∉ S := by
    intro hh
    exact hx (hg x ▸ hS (g x) hh)
  obtain ⟨x,_⟩ := outside ∅ (by simp)
  let S := small ∅ x
  have hS : ∀ y ∈ S, g y ∈ S := hClosed ∅ (by simp) x
  have hs := hSmallCard ∅ x
  change S.card ≤ 0 + 2 at hs
  obtain ⟨y,hy⟩ := outside S (by omega)
  have hy' := hm S hS hy
  let T := small S y
  have hT : ∀ z ∈ T, g z ∈ T := hClosed S hS y
  have ht := hSmallCard S y
  change T.card ≤ S.card + 2 at ht
  obtain ⟨z,hz⟩ := outside T (by omega)
  have hz' := hm T hT hz
  simp only [S,T,small,Finset.mem_insert,Finset.notMem_empty,or_false,not_or] at hy hy' hz hz'
  have hxy := hne x
  have hyy := hne y
  have hzz := hne z
  let q : Fin 6 → X := ![x,g x,y,g y,z,g z]
  have hInjective : Function.Injective q := by
    apply List.nodup_ofFn.mp
    simp only [q, Matrix.vecCons, List.ofFn_cons, List.ofFn_zero, List.nodup_cons,
      List.nodup_nil, List.mem_cons, List.not_mem_nil, or_false, not_or, and_true]
    simp_all [ne_comm]
  have hc : Fintype.card (Fin 6) = Fintype.card X := by simp [hX]
  let Q := Equiv.ofBijective q ((Fintype.bijective_iff_injective_and_card q).mpr ⟨hInjective,hc⟩)
  exact ⟨Q,rfl,rfl,rfl⟩

end MatchingRelabel

section PerfectTailResult

variable {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)

open scoped Classical in
private theorem canonical_matching_labels (h4 : NoFourCycle G) (h3 : NoTriangle G)
    (hfar : ¬ Erdos934.HasFarEdges G 3) (hdeg : ∀ x, G.degree x ≤ 3)
    (hr : ∃ y, G.Adj r y) (reg : ∀ x : V, (∃ y, G.Adj x y) → G.degree x = 3)
    (hL3 : (layer G r 3).card = 6)
    (hTwo : ((layer G r 3).filter (fun x => (neighborsAt G r x 2).card = 2)).card = 6)
    (hE2 : (G.induce (layer G r 2 : Set V)).edgeFinset.card = 0) :
    ∃ (A : Fin 3 ≃ (layer G r 1 : Type)) (C : Fin 6 ≃ (layer G r 3 : Type)),
      G.Adj (C 0).val (C 1).val ∧ G.Adj (C 2).val (C 3).val ∧
      G.Adj (C 4).val (C 5).val ∧
      ∀ (i : Fin 3) (j : Fin 6),
        (∃ z ∈ neighborsAt G r (C j).val 2, G.Adj (A i).val z) ↔ j ∈ seenList i := by
  classical
  let X := (layer G r 3 : Type)
  let Y := (layer G r 1 : Type)
  have hhr := reg r hr
  have hNo22 : ∀ x ∈ layer G r 2, ∀ y ∈ layer G r 2, ¬ G.Adj x y := by
    intro x hx y hy hxy
    let H := G.induce (layer G r 2 : Set V)
    have hAdj : H.Adj ⟨x,hx⟩ ⟨y,hy⟩ := hxy
    have hEdge : s(⟨x,hx⟩,⟨y,hy⟩) ∈ H.edgeSet := hAdj
    have he := Finset.card_pos.mpr ⟨_, (SimpleGraph.mem_edgeFinset (G := H)).mpr hEdge⟩
    change 0 < (G.induce (layer G r 2 : Set V)).edgeFinset.card at he
    exact (Nat.ne_of_gt he) hE2
  have p2 (x : X) : (neighborsAt G r x.val 2).card = 2 := by
    have he : (layer G r 3).filter (fun x => (neighborsAt G r x 2).card = 2) = layer G r 3 :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [hL3,hTwo])
    have hx : x.val ∈ (layer G r 3).filter (fun y => (neighborsAt G r y 2).card = 2) := by
      rw [he]
      exact x.property
    exact (Finset.mem_filter.mp hx).2
  have hCount1 := (first_three_layers G r h4 h3 reg hr).2.1
  let A : Fin 3 ≃ Y := ((layer G r 1).equivFinOfCardEq hCount1).symm
  have hMate (x : X) : ∃! y : X, G.Adj x.val y.val := by
    have h1 : (neighborsAt G r x.val 3).card = 1 := by
      have h := (third_degrees G r h4 hfar reg hhr x.property).2
      rw [p2 x] at h
      omega
    obtain ⟨y,hy,huniq⟩ := Finset.card_eq_one_iff_existsUnique.mp h1
    obtain ⟨hxy,hry⟩ := (mem_neighborsAt G r).mp hy
    refine ⟨⟨y,(mem_layer G r).mpr hry⟩,hxy,?_⟩
    intro z hz
    exact Subtype.ext (huniq z.val ((mem_neighborsAt G r).mpr ⟨hz,(mem_layer G r).mp z.property⟩))
  let mate (x : X) : X := Classical.choose (hMate x)
  have hadj (x : X) : G.Adj x.val (mate x).val := (Classical.choose_spec (hMate x)).1
  have hInv : Function.Involutive mate := by
    intro x
    exact ((Classical.choose_spec (hMate (mate x))).2 x (hadj x).symm).symm
  have hne (x : X) : x ≠ mate x := fun h => (hadj x).ne (congrArg Subtype.val h)
  have hX : Fintype.card X = 6 := by simp [X,hL3]
  obtain ⟨q,h01,h23,h45⟩ := pair_complement_exhaust hX mate hInv hne
  have hEdge : ∀ i j : Fin 6, (i,j) ∈ matchingPairs → G.Adj (q i).val (q j).val := by
    intro i j hij
    simp only [matchingPairs,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hij
    rcases hij with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · simpa only [h01] using hadj (q 0)
    · simpa only [h01] using (hadj (q 0)).symm
    · simpa only [h23] using hadj (q 2)
    · simpa only [h23] using (hadj (q 2)).symm
    · simpa only [h45] using hadj (q 4)
    · simpa only [h45] using (hadj (q 4)).symm
  have missing (x : X) : ∃! u : Y, u.val ∉ tailDirections G r x.val := by
    let D := layer G r 1 \ tailDirections G r x.val
    have hc : D.card = 1 := by
      have ht := Finset.card_sdiff_add_card_eq_card (tailDirections_subset G r x.val)
      change D.card + (tailDirections G r x.val).card = (layer G r 1).card at ht
      rw [hCount1,tailDirections_card G r h4 hfar hdeg hhr reg x.property,p2 x] at ht
      omega
    obtain ⟨u,hu,huniq⟩ := Finset.card_eq_one_iff_existsUnique.mp hc
    obtain ⟨hmem,hn⟩ := Finset.mem_sdiff.mp hu
    refine ⟨⟨u,hmem⟩,hn,?_⟩
    intro v hv
    exact Subtype.ext (huniq v.val (Finset.mem_sdiff.mpr ⟨v.property,hv⟩))
  let μ (x : X) : Fin 3 := A.symm (Classical.choose (missing x))
  have hMissing (x : X) :
      (A (μ x)).val ∉ tailDirections G r x.val := by
    dsimp [μ]
    rw [Equiv.apply_symm_apply]
    exact (Classical.choose_spec (missing x)).1
  have hSeen (x : X) (i : Fin 3) :
      (A i).val ∈ tailDirections G r x.val ↔ i ≠ μ x := by
    constructor
    · intro hi he
      exact hMissing x (he ▸ hi)
    · intro hi
      by_contra! hm
      have h := (Classical.choose_spec (missing x)).2 (A i) hm
      apply hi
      change i = A.symm (Classical.choose (missing x))
      rw [← h,Equiv.symm_apply_apply]
  have hColor (x y : X) (hxy : G.Adj x.val y.val) : μ x ≠ μ y := by
    intro he
    let u := (A (μ x)).val
    have hu : u ∈ layer G r 1 := (A (μ x)).property
    obtain ⟨w,hw,huw⟩ := edge_covers_first_directions G r hfar x.property y.property hxy hu
    rcases Finset.mem_union.mp hw with hw | hw
    · exact hMissing x ((mem_tailDirections G r hu).mpr ⟨w,hw,huw⟩)
    · have h := (mem_tailDirections G r hu).mpr ⟨w,hw,huw⟩
      exact ((hSeen y (μ x)).mp h) he
  let μq (i : Fin 6) := μ (q i)
  have hBal (a : Fin 3) : (Finset.univ.filter (fun i : Fin 6 => μq i = a)).card = 2 := by
    let T := Finset.univ.filter (fun i : Fin 6 => ¬ μq i = a)
    let S := (layer G r 3).filter (fun x => (A a).val ∈ tailDirections G r x)
    have hs : S.card = 4 :=
      tails_seen_from_branch G r h4 h3 hfar hdeg hhr reg hNo22 (A a).property
    have heq : T.card = S.card := by
      apply Finset.card_bij (fun i _ => (q i).val)
      · intro i hi
        have hn := (Finset.mem_filter.mp hi).2
        exact Finset.mem_filter.mpr ⟨(q i).property,(hSeen (q i) a).mpr (Ne.symm hn)⟩
      · intro i _ j _ h
        exact q.injective (Subtype.ext h)
      · intro x hx
        obtain ⟨hx3,hxSeen⟩ := Finset.mem_filter.mp hx
        let v : X := ⟨x,hx3⟩
        refine ⟨q.symm v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
        · change μ (q (q.symm v)) ≠ a
          rw [Equiv.apply_symm_apply]
          exact Ne.symm ((hSeen v a).mp hxSeen)
        · rw [Equiv.apply_symm_apply]
    have hc := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin 6))) (fun i => μq i = a)
    change (Finset.univ.filter (fun i => μq i = a)).card + T.card =
      (Finset.univ : Finset (Fin 6)).card at hc
    rw [heq,hs,Finset.card_univ,Fintype.card_fin] at hc
    omega
  have hμ : μq 0 ≠ μq 1 ∧ μq 2 ≠ μq 3 ∧ μq 4 ≠ μq 5 := by
    exact ⟨hColor _ _ (hEdge 0 1 (by decide)),hColor _ _ (hEdge 2 3 (by decide)),
      hColor _ _ (hEdge 4 5 (by decide))⟩
  obtain ⟨hInj,hAB,hAC,hBC,hLabels⟩ := matchingOrder_checked μq hBal hμ
  let B := Equiv.ofBijective (matchingOrder μq)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hInj,rfl⟩)
  let C : Fin 6 ≃ X := B.trans q
  refine ⟨A,C,hEdge _ _ hAB,hEdge _ _ hAC,hEdge _ _ hBC,?_⟩
  intro i j
  rw [← mem_tailDirections G r (A i).property, hSeen (C j) i]
  change (i ≠ μq (matchingOrder μq j)) ↔ j ∈ seenList i
  rw [hLabels]
  exact seenList_spec i j

end PerfectTailResult

end CubicVertexBound

namespace SubdividedHeawood

private def forward (u v : Fin 15) : Bool :=
  decide ((u.val < 7 ∧ 7 ≤ v.val ∧ v.val < 14 ∧
      ((u.val + 7 - (v.val - 7)) % 7 ∈ ([0, 1, 3] : List ℕ)) ∧
      ¬(u = 0 ∧ v = 7)) ∨
    (v = 14 ∧ (u = 0 ∨ u = 7)))

private def adjacent (u v : Fin 15) : Bool := forward u v || forward v u

private lemma adjacent_loopless : ∀ u : Fin 15, adjacent u u = false := by
  decide +kernel

private def graph : SimpleGraph (Fin 15) where
  Adj u v := adjacent u v = true
  symm := ⟨by intro u v; simp only [adjacent, Bool.or_comm]; exact id⟩
  loopless := ⟨fun u h => by rw [adjacent_loopless u] at h; cases h⟩

private instance : DecidableRel graph.Adj :=
  fun u v => inferInstanceAs (Decidable (adjacent u v = true))

private abbrev Near (u v : Fin 15) : Prop :=
  u = v ∨ graph.Adj u v ∨ ∃ z : Fin 15, graph.Adj u z ∧ graph.Adj z v

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private lemma covering : ∀ u v w x : Fin 15, graph.Adj u v → graph.Adj w x →
    Near u w ∨ Near u x ∨ Near v w ∨ Near v x := by
  decide +kernel

private lemma dist_of_near {u v : Fin 15} (h : Near u v) : graph.edist u v ≤ 2 := by
  rcases h with rfl | h | ⟨z, huz, hzv⟩
  · simp
  · rw [SimpleGraph.edist_eq_one_iff_adj.2 h]
    decide
  · exact (SimpleGraph.Walk.cons huz (.cons hzv .nil)).edist_le

private lemma no_far_edges : ¬Erdos934.HasFarEdges graph 3 := by
  rintro ⟨u, v, w, x, huv, hwx, h⟩
  have impossible {a b : Fin 15} (ha : a ∈ ({u, v} : Set (Fin 15)))
      (hb : b ∈ ({w, x} : Set (Fin 15))) (hn : Near a b) : False :=
    (by decide : ¬(3 : ℕ∞) ≤ 2) ((h a ha b hb).trans (dist_of_near hn))
  rcases covering u v w x huv hwx with hn | hn | hn | hn
  · exact impossible (by simp) (by simp) hn
  · exact impossible (by simp) (by simp) hn
  · exact impossible (by simp) (by simp) hn
  · exact impossible (by simp) (by simp) hn

private lemma max_degree : ∀ v : Fin 15, graph.degree v ≤ 3 := by
  decide +kernel

private lemma degree_sum : ∑ v : Fin 15, graph.degree v = 44 := by
  decide +kernel

theorem witness : ∃ G : SimpleGraph (Fin 15),
    (∀ v, (G.neighborSet v).ncard ≤ 3) ∧ G.edgeSet.ncard = 22 ∧
      ¬Erdos934.HasFarEdges G 3 := by
  refine ⟨graph, ?_, ?_, no_far_edges⟩
  · intro v
    rw [← graph.coe_neighborFinset v, Set.ncard_coe_finset, SimpleGraph.card_neighborFinset_eq_degree]
    exact max_degree v
  · have h := graph.sum_degrees_eq_twice_card_edges
    rw [degree_sum] at h
    rw [← graph.coe_edgeFinset, Set.ncard_coe_finset]
    omega

end SubdividedHeawood

namespace CubicVertexBound

private theorem matching_groups_agree : ∀ (i : Fin 3) (j : Fin 6),
    j ∈ seenList i ↔ j ∈ CubicTemplates.groupIndices 0 i := by decide

private theorem path_edge_groups_agree : ∀ (i : Fin 3) (j : Fin 6),
    j ∈ (![({0,3,4,5} : Finset (Fin 6)), {1,2,4,5}, {1,2,3,5}] i) ↔
      j ∈ CubicTemplates.groupIndices 1 i := by decide

private theorem two_path_groups_agree : ∀ (i : Fin 3) (j : Fin 6),
    j ∈ twoPathBranchIndices i ↔ j ∈ CubicTemplates.groupIndices 2 i := by decide

private theorem far_of_large_subcubic {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hd : ∀ x, G.degree x ≤ 3)
    (hm : 23 ≤ G.edgeFinset.card) : Erdos934.HasFarEdges G 3 := by
  classical
  by_contra hfar
  have reg (x : V) (hx : ∃ y, G.Adj x y) : G.degree x = 3 := by
    obtain ⟨y,hxy⟩ := hx
    exact CubicEdgeLayers.degree_three_of_incident G hxy hd hfar hm
  have h3 : NoTriangle G := by
    intro a b c hab hac hbc
    have h := CubicEdgeLayers.triangle_bounds_edges G hab hac hbc hd hfar
    omega
  have h4 : NoFourCycle G := by
    intro a b x y hab hxy hax hbx hay hby
    exact CubicEdgeLayers.no_four_cycle_of_many_edges G hax hbx.symm hby hay.symm
      hab.symm hxy.symm hd hfar hm
  obtain ⟨e,he⟩ := Finset.card_pos.mp (show 0 < G.edgeFinset.card by omega)
  induction e using Sym2.inductionOn with
  | _ r v =>
    have hrv : G.Adj r v := SimpleGraph.mem_edgeFinset.mp he
    have hrExists : ∃ w, G.Adj r w := ⟨v,hrv⟩
    have hr := reg r hrExists
    obtain ⟨_,_,hL2⟩ := first_three_layers G r h4 h3 reg hrExists
    have hL3 := (cubic_support_16 G r h4 h3 hfar reg hrExists hm).2
    rcases third_layer_shapes G r h4 hfar hd hr reg hL2 hL3 with
      ⟨_,hTwo,_,he₂⟩ | ⟨hOne,_,hThree,he₂⟩ | ⟨hOne,_,_,he₂⟩
    · obtain ⟨A,C,h01,h23,h45,hInc⟩ :=
        canonical_matching_labels G r h4 h3 hfar hd hrExists reg hL3 hTwo he₂
      apply hfar
      refine far_from_canonical_layers G r h3 h4 hd hfar hr reg 0 A C
        (fun i j => (hInc i j).trans (matching_groups_agree i j)) ?_ ?_
      · intro e he
        change e ∈ ([(0,1),(2,3),(4,5)] : List (Fin 6 × Fin 6)) at he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl
        · exact h01
        · exact h23
        · exact h45
      · intro h
        exact ((by decide : (0 : Fin 3) ≠ 2) h).elim
    · obtain ⟨A,C,h01,h02,h34,hInc⟩ :=
        pathEdgeCanonicalLabels G r h4 h3 hfar hd hr reg hL3 hOne hThree he₂
      apply hfar
      refine far_from_canonical_layers G r h3 h4 hd hfar hr reg 1 A C
        (fun i j => (hInc i j).trans (path_edge_groups_agree i j)) ?_ ?_
      · intro e he
        change e ∈ ([(0,1),(0,2),(3,4)] : List (Fin 6 × Fin 6)) at he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl
        · exact h01
        · exact h02
        · exact h34
      · intro h
        exact ((by decide : (1 : Fin 3) ≠ 2) h).elim
    · obtain ⟨A,C,hPath,hInc,x,hx,y,hy,hxy⟩ :=
        two_path_shape_canonical_labels G r h4 h3 hfar hd hr reg hL3 hOne he₂
      obtain ⟨h01,h02,h34,h35⟩ := hPath
      apply hfar
      refine far_from_canonical_layers G r h3 h4 hd hfar hr reg 2 A C
        (fun i j => (hInc i j).trans (two_path_groups_agree i j)) ?_ (fun _ => ⟨x,hx,y,hy,hxy⟩)
      intro e he
      change e ∈ ([(0,1),(0,2),(3,4),(3,5)] : List (Fin 6 × Fin 6)) at he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact h01
      · exact h02
      · exact h34
      · exact h35

end CubicVertexBound

theorem OMA.solution : type_of% @Erdos934.erdos_934.variants.h_three_three := by
  classical
  apply le_antisymm
  · apply Erdos934.h_le
    intro n G hdeg hm
    have hd (v : Fin n) : G.degree v ≤ 3 := by
      simpa only [← G.coe_neighborFinset, Set.ncard_coe_finset, G.card_neighborFinset_eq_degree]
        using hdeg v
    have hc : G.edgeFinset.card = G.edgeSet.ncard := by
      rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
    exact CubicVertexBound.far_of_large_subcubic G hd (hc ▸ hm)
  · exact CubicEdgeLayers.lower_bound_twenty_three_of_witness SubdividedHeawood.witness