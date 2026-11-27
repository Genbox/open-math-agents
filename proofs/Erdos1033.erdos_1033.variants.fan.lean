import FormalConjectures.ErdosProblems.«1033»
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! Genghua Fan, Degree sum for a triangle in a graph (1988).
https://doi.org/10.1002/jgt.3190120216 -/

open Finset SimpleGraph
open scoped Classical

namespace FanTriangle

-- The three vertices of the relaxed region c + d ≤ n suffice for the optimization.
private lemma fan_arithmetic {n e c d s δ τ : ℝ}
    (_hn : 0 < n) (he : n ^ 2 < 4 * e) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hcd : c + d ≤ n) (hδ : e < n * δ) (hτ : 4 * n * τ ≤ 21 * e)
    (hpack : 2 * e ≤ n ^ 2 / 2 + c * (τ / 3 - n / 2 + s / 4)
       + d * ((4 * τ - 5 * n - δ) / 10) - s ^ 2 / 2) :
    False := by
  let x := τ / 3 - n / 2 + s / 4
  let y := (4 * τ - 5 * n - δ) / 10
  change 2 * e ≤ n ^ 2 / 2 + c * x + d * y - s ^ 2 / 2 at hpack
  by_cases hx : y ≤ x ∧ 0 ≤ x
  · have hcxdy : c * x + d * y ≤ n * x := by
      calc
        _ ≤ c * x + d * x := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hx.1 hd)
        _ = (c + d) * x := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hcd hx.2
    have hs := sq_nonneg (s - n / 4)
    have hx' : n * x = n * τ / 3 - n ^ 2 / 2 + n * s / 4 := by dsimp [x]; ring
    nlinarith only [hpack, hcxdy, hx', hτ, he, hs, sq_nonneg n]
  by_cases hy : 0 ≤ y
  · have hyx : x ≤ y := by
      by_contra! h
      exact hx ⟨h.le, hy.trans h.le⟩
    have hcxdy : c * x + d * y ≤ n * y := by
      calc
        _ ≤ c * y + d * y := by gcongr
        _ = (c + d) * y := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hcd hy
    have hy' : n * y = 2 * (n * τ) / 5 - n ^ 2 / 2 - n * δ / 10 := by dsimp [y]; ring
    nlinarith only [hpack, hcxdy, hy', hτ, hδ, sq_nonneg s]
  have hnx : x ≤ 0 := by
    by_contra! h
    exact hx ⟨(lt_of_not_ge hy).le.trans h.le, h.le⟩
  have hcx := mul_nonpos_of_nonneg_of_nonpos hc hnx
  have hdy := mul_nonpos_of_nonneg_of_nonpos hd (lt_of_not_ge hy).le
  nlinarith only [hpack, hcx, hdy, he, sq_nonneg s]

universe u

private lemma degree_induce_le {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Set V) [DecidablePred (· ∈ S)] (y : S) :
    (G.induce S).degree y ≤ G.degree y := by
  have h := G.map_neighborFinset_induce (s := S) y
  have h' := congrArg Finset.card h
  rw [Finset.card_map, SimpleGraph.card_neighborFinset_eq_degree] at h'
  rw [h', ← SimpleGraph.card_neighborFinset_eq_degree]
  exact Finset.card_le_card Finset.inter_subset_left

-- Deleting a vertex of degree at most e/n preserves both density and the ratio e/n.
private lemma reduce_min_degree
    (hbase : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V ^ 2 < 4 * G.edgeFinset.card →
      (∀ x, G.edgeFinset.card < Fintype.card V * G.degree x) →
      ∃ t, G.IsNClique 3 t ∧ 21 * G.edgeFinset.card ≤
        4 * (Fintype.card V) * (∑ v ∈ t, G.degree v)) :
    ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V ^ 2 < 4 * G.edgeFinset.card →
      ∃ t, G.IsNClique 3 t ∧ 21 * G.edgeFinset.card ≤
        4 * (Fintype.card V) * (∑ v ∈ t, G.degree v) := by
  let P (k : ℕ) := ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V = k → k ^ 2 < 4 * G.edgeFinset.card →
    ∃ t, G.IsNClique 3 t ∧ 21 * G.edgeFinset.card ≤ 4 * k * (∑ v ∈ t, G.degree v)
  have hind (n : ℕ) : P n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V inst G instG hn hG
      have hG' : Fintype.card V ^ 2 < 4 * G.edgeFinset.card := by simpa only [hn] using hG
      by_cases hm : ∀ x, G.edgeFinset.card < Fintype.card V * G.degree x
      · simpa only [hn] using hbase G hG' hm
      push Not at hm
      obtain ⟨x, hx⟩ := hm
      let S : Set V := {x}ᶜ
      let H := G.induce S
      let e := G.edgeFinset.card
      let f := H.edgeFinset.card
      let k := Fintype.card S
      have hnpos : 0 < n := by
        rw [← hn]
        let _ : Nonempty V := ⟨x⟩
        exact Fintype.card_pos
      have hk : k + 1 = n := by
        have hc : k = n - 1 := by
          dsimp [k, S]
          have h₁ : Fintype.card ({x} : Set V) = 1 := Fintype.card_unique
          rw [Fintype.card_compl_set ({x} : Set V), h₁, hn]
        omega
      have he : f + G.degree x = e := by
        have hh : G.degree x ≤ e := by
          rw [← G.card_incidenceFinset_eq_degree]
          exact Finset.card_le_card (G.incidenceFinset_subset x)
        have hf : f = e - G.degree x := by
          dsimp [f, H, S, e]
          rw [G.card_edgeFinset_induce_compl_singleton, G.card_edgeFinset_deleteIncidenceSet]
        omega
      have hx' : n * G.degree x ≤ e := by simpa only [hn] using hx
      change n ^ 2 < 4 * e at hG
      have hkpos : 0 < k := by
        by_contra! hz
        have hn1 : n = 1 := by omega
        have hedge := G.card_edgeFinset_le_card_choose_two
        rw [hn, hn1] at hedge
        change e ≤ 0 at hedge
        omega
      have hratio : k * e ≤ n * f := by
        nlinarith only [hx', congrArg (fun z => n * z) he, congrArg (fun z => z * e) hk]
      have hH : k ^ 2 < 4 * f := by
        by_contra! hbad
        have hh₁ := Nat.mul_le_mul_left n hbad
        have hh₂ := Nat.mul_le_mul_left 4 hratio
        have hh₃ := Nat.mul_lt_mul_of_pos_left hG hkpos
        have hh₄ := Nat.mul_le_mul_left (k * n) (by omega : k ≤ n)
        nlinarith only [hh₁, hh₂, hh₃, hh₄]
      obtain ⟨t, ht, hsum⟩ := ih k (by omega) H rfl hH
      let i : S ↪ V := Function.Embedding.subtype _
      refine ⟨t.map i, (SimpleGraph.isNClique_induce_iff (G := G) S t 3).mp ht, ?_⟩
      have hmono : (∑ v ∈ t, H.degree v) ≤ ∑ v ∈ t.map i, G.degree v := by
        rw [Finset.sum_map]
        exact Finset.sum_le_sum (fun v _ => degree_induce_le G S v)
      have h₁ := Nat.mul_le_mul_left 21 hratio
      have h₂ := Nat.mul_le_mul_left n hsum
      have h₃ := Nat.mul_le_mul_left (4 * k * n) hmono
      apply Nat.le_of_mul_le_mul_left _ hkpos
      calc
        _ ≤ 21 * (n * f) := by convert h₁ using 1; ring
        _ ≤ n * (4 * k * ∑ v ∈ t, H.degree v) := by convert h₂ using 1; ring
        _ ≤ _ := by
          convert h₃ using 1 <;> ring
  intro V inst G instG hG
  exact hind (Fintype.card V) G rfl hG

variable {V : Type*}

private def Bow (G : SimpleGraph V) (B : Finset V) (z : V) : Prop :=
  ∃ P Q : Finset V, P.card = 2 ∧ Q.card = 2 ∧ Disjoint P Q ∧ z ∉ P ∧ z ∉ Q ∧
    B = insert z (P ∪ Q) ∧ G.IsClique (insert z (P : Set V)) ∧ G.IsClique (insert z (Q : Set V))

private def Large (G : SimpleGraph V) (B : Finset V) : Prop :=
  (3 ≤ B.card ∧ G.IsClique (B : Set V)) ∨ ∃ z, Bow G B z

private noncomputable def cover (P : Finset (Finset V)) : Finset V := P.biUnion id

private def Packing (G : SimpleGraph V) (P : Finset (Finset V)) : Prop :=
  (P : Set (Finset V)).PairwiseDisjoint id ∧ ∀ B ∈ P, Large G B

private lemma exists_max_packing [Fintype V] (G : SimpleGraph V) :
    ∃ P, Packing G P ∧ ∀ T, Packing G T → (cover T).card ≤ (cover P).card := by
  let S : Finset (Finset (Finset V)) := Finset.univ.filter (Packing G)
  have hS {T : Finset (Finset V)} : T ∈ S ↔ Packing G T := by simp [S]
  have he : Packing G ∅ := by simp [Packing]
  obtain ⟨P, hP, hmax⟩ := Finset.exists_max_image S (fun T => (cover T).card) ⟨∅, hS.mpr he⟩
  exact ⟨P, hS.mp hP, fun T hT => hmax T (hS.mpr hT)⟩

private lemma member_in_cover {x : V} {B : Finset V} {P : Finset (Finset V)}
    (hB : B ∈ P) (hx : x ∈ B) : x ∈ cover P :=
  Finset.mem_biUnion.mpr ⟨B, hB, hx⟩

private lemma cover_mono {P Q : Finset (Finset V)} (hPQ : P ⊆ Q) : cover P ⊆ cover Q := by
  intro x hx
  obtain ⟨B, hB, hxB⟩ := Finset.mem_biUnion.mp hx
  exact member_in_cover (hPQ hB) hxB

private lemma cover_union (P Q : Finset (Finset V)) : cover (P ∪ Q) = cover P ∪ cover Q := by
  ext x
  simp [cover, or_and_right, exists_or]

private lemma cover_single (B : Finset V) : cover {B} = B := by simp [cover]

private lemma cover_disjoint {P Q : Finset (Finset V)}
    (h : ∀ B ∈ P, ∀ C ∈ Q, Disjoint B C) : Disjoint (cover P) (cover Q) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  obtain ⟨B, hB, hxB⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hy
  exact Finset.disjoint_left.mp (h B hB C hC) hxB hxC

private lemma append_packing {G : SimpleGraph V} {P Q : Finset (Finset V)}
    (hP : Packing G P) (hQ : Packing G Q) (hPQ : Disjoint (cover P) (cover Q)) :
    Packing G (P ∪ Q) := by
  refine ⟨?_, ?_⟩
  · rw [Finset.coe_union]
    refine Set.pairwiseDisjoint_union.mpr ⟨hP.1, hQ.1, ?_⟩
    intro B hB C hC _
    exact Finset.disjoint_left.mpr fun x hxB hxC =>
      Finset.disjoint_left.mp hPQ (member_in_cover hB hxB) (member_in_cover hC hxC)
  · intro B hB
    exact (Finset.mem_union.mp hB).elim (hP.2 B) (hQ.2 B)

private lemma single_packing {G : SimpleGraph V} {B : Finset V} (hB : Large G B) :
    Packing G {B} := by simp [Packing, hB]

private lemma two_packing {G : SimpleGraph V} {B C : Finset V}
    (hB : Large G B) (hC : Large G C) (hBC : Disjoint B C) :
    Packing G {B, C} := by
  have hh : Disjoint (cover {B}) (cover {C}) := by simpa only [cover_single] using hBC
  have h : Packing G ({B} ∪ {C}) := append_packing (single_packing hB) (single_packing hC) hh
  simpa only [Finset.singleton_union] using h

private lemma max_erase [Fintype V] {G : SimpleGraph V} {P : Finset (Finset V)} (hP : Packing G P)
    (hmax : ∀ T, Packing G T → (cover T).card ≤ (cover P).card)
    {B : Finset V} (hB : B ∈ P) {Q : Finset (Finset V)} (hQ : Packing G Q)
    (hcover : cover Q ⊆ B ∪ (Finset.univ \ cover P)) :
    (cover Q).card ≤ B.card := by
  have hsub : P.erase B ⊆ P := Finset.erase_subset _ _
  have hPE : Packing G (P.erase B) :=
    ⟨hP.1.subset hsub, fun C hC => hP.2 C (hsub hC)⟩
  have hEB : Disjoint (cover (P.erase B)) B := by
    conv_rhs => rw [← cover_single B]
    apply cover_disjoint
    intro C hC D hD
    rw [Finset.mem_singleton.mp hD]
    exact hP.1 (hsub hC) hB (Finset.mem_erase.mp hC).1
  have hEQ : Disjoint (cover (P.erase B)) (cover Q) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    rcases Finset.mem_union.mp (hcover hy) with hyB | hyL
    · exact Finset.disjoint_left.mp hEB hx hyB
    · exact (Finset.mem_sdiff.mp hyL).2 (cover_mono hsub hx)
  have hs : cover P = cover (P.erase B) ∪ B := by
    conv_lhs => rw [← Finset.insert_erase hB]
    simp [cover, Finset.biUnion_insert, Finset.union_comm]
  have hh := hmax (P.erase B ∪ Q) (append_packing hPE hQ hEQ)
  rw [cover_union, Finset.card_union_of_disjoint hEQ, hs, Finset.card_union_of_disjoint hEB] at hh
  omega

private lemma max_no_add [Fintype V] {G : SimpleGraph V} {P : Finset (Finset V)} (hP : Packing G P)
    (hmax : ∀ T, Packing G T → (cover T).card ≤ (cover P).card)
    {B : Finset V} (hB : Large G B) (hcard : 0 < B.card)
    (hBU : B ⊆ Finset.univ \ cover P) : False := by
  have hPQ : Disjoint (cover P) (cover {B}) := by
    rw [cover_single]
    exact Finset.disjoint_left.mpr fun x hx hy => (Finset.mem_sdiff.mp (hBU hy)).2 hx
  have hh := hmax (P ∪ {B}) (append_packing hP (single_packing hB) hPQ)
  rw [cover_union, Finset.card_union_of_disjoint hPQ, cover_single] at hh
  omega

private lemma remainder_triangle_free [Fintype V] {G : SimpleGraph V} {P : Finset (Finset V)} (hP : Packing G P)
    (hmax : ∀ T, Packing G T → (cover T).card ≤ (cover P).card)
    {x y z : V} (hx : x ∉ cover P) (hy : y ∉ cover P) (hz : z ∉ cover P)
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hzx : G.Adj z x) : False := by
  have hB : G.IsNClique 3 ({x, y, z} : Finset V) :=
    (SimpleGraph.is3Clique_iff).mpr ⟨x, y, z, hxy, hzx.symm, hyz, rfl⟩
  apply max_no_add hP hmax (.inl ⟨hB.card_eq.ge, hB.isClique⟩) (by rw [hB.card_eq]; decide)
  intro v hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl <;> simp [hx, hy, hz]
private lemma adj_triangle {G : SimpleGraph V} {x y z : V}
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z) :
    G.IsNClique 3 ({x, y, z} : Finset V) :=
  SimpleGraph.is3Clique_iff.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩

private lemma large_of_three {G : SimpleGraph V} {B : Finset V} (h : G.IsNClique 3 B) :
    Large G B := .inl ⟨h.card_eq.ge, h.isClique⟩

private lemma max_one [Fintype V] {G : SimpleGraph V} {P : Finset (Finset V)} (hP : Packing G P)
    (hmax : ∀ T, Packing G T → (cover T).card ≤ (cover P).card)
    {B : Finset V} (hB : B ∈ P) {C : Finset V} (hC : Large G C)
    (hsub : C ⊆ B ∪ (Finset.univ \ cover P)) : C.card ≤ B.card := by
  have hh := max_erase hP hmax hB (single_packing hC) (by simpa only [cover_single] using hsub)
  simpa only [cover_single] using hh

private lemma max_two [Fintype V] {G : SimpleGraph V} {P : Finset (Finset V)} (hP : Packing G P)
    (hmax : ∀ T, Packing G T → (cover T).card ≤ (cover P).card)
    {B : Finset V} (hB : B ∈ P) {C D : Finset V} (hC : Large G C) (hD : Large G D)
    (hCD : Disjoint C D) (hsub : C ∪ D ⊆ B ∪ (Finset.univ \ cover P)) :
    C.card + D.card ≤ B.card := by
  have hc : cover {C, D} = C ∪ D := by simp [cover, Finset.biUnion_insert]
  have hh := max_erase hP hmax hB (two_packing hC hD hCD) (by simpa only [hc] using hsub)
  rwa [hc, Finset.card_union_of_disjoint hCD] at hh

private lemma bow_card {G : SimpleGraph V} {B : Finset V} {z : V} (h : Bow G B z) :
    B.card = 5 := by
  obtain ⟨A, C, hA, hC, hAC, hzA, hzC, rfl, _, _⟩ := h
  rw [Finset.card_insert_of_notMem (by simp [hzA, hzC]),
    Finset.card_union_of_disjoint hAC, hA, hC]

private lemma large_card {G : SimpleGraph V} {B : Finset V} (h : Large G B) : 3 ≤ B.card := by
  rcases h with h | ⟨z, hz⟩
  · exact h.1
  · rw [bow_card hz]; decide

variable [Fintype V]

-- Two adjacent outside vertices cannot have a shared neighbor in a clique block.
private lemma no_common_in_clique {G : SimpleGraph V} {P : Finset (Finset V)} (hP : Packing G P)
    (hmax : ∀ T, Packing G T → (cover T).card ≤ (cover P).card)
    {B : Finset V} (hB : B ∈ P) (hc : G.IsClique (B : Set V)) {x y z : V}
    (hx : x ∉ cover P) (hy : y ∉ cover P) (hz : z ∈ B)
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z) : False := by
  have hxb : x ∉ B := fun hh => hx (member_in_cover hB hh)
  have hyb : y ∉ B := fun hh => hy (member_in_cover hB hh)
  have hcard := large_card (hP.2 B hB)
  have ht := adj_triangle hxy hxz hyz
  have hsub : ({x,y,z} : Finset V) ⊆ B ∪ (Finset.univ \ cover P) := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> simp [hx, hy, hz]
  let R := B.erase z
  have hRsub : R ⊆ B := Finset.erase_subset _ _
  have hRcard : R.card = B.card - 1 := Finset.card_erase_of_mem hz
  have hRt : Disjoint ({x, y, z} : Finset V) R := by
    refine Finset.disjoint_left.mpr ?_
    intro v hv hvR
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact hxb (hRsub hvR)
    · exact hyb (hRsub hvR)
    · exact (Finset.mem_erase.mp hvR).1 rfl
  by_cases h4 : 4 ≤ B.card
  · have hlarge : Large G R := .inl ⟨by omega, hc.subset hRsub⟩
    have hh := max_two hP hmax hB (large_of_three ht) hlarge hRt
      (Finset.union_subset hsub (hRsub.trans Finset.subset_union_left))
    rw [ht.card_eq] at hh
    omega
  let D : Finset V := B ∪ {x,y}
  have hBF : Disjoint B ({x,y} : Finset V) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hxb hv
    · exact hyb (Finset.mem_singleton.mp hw ▸ hv)
  have hDcard : D.card = B.card + 2 := by
    rw [Finset.card_union_of_disjoint hBF, Finset.card_pair hxy.ne]
  have hBow : Bow G D z := by
    refine ⟨R, {x,y}, by omega, Finset.card_pair hxy.ne, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hBF.mono_left hRsub
    · simp [R]
    · simp [hxz.ne.symm, hyz.ne.symm]
    · rw [← Finset.insert_union, Finset.insert_erase hz]
    · rw [← Finset.coe_insert, Finset.insert_erase hz]
      exact hc
    · rw [← Finset.coe_insert]
      exact (adj_triangle hxz.symm hyz.symm hxy).isClique
  have hDsub : D ⊆ B ∪ (Finset.univ \ cover P) := by
    refine Finset.union_subset Finset.subset_union_left ?_
    exact (show ({x,y} : Finset V) ⊆ {x,y,z} by simp [Finset.insert_subset_iff]).trans hsub
  have hh := max_one hP hmax hB (.inr ⟨z, hBow⟩) hDsub
  omega

private noncomputable def neighborsIn (G : SimpleGraph V) (B : Finset V) (x : V) : Finset V :=
  B.filter (G.Adj x)

private lemma neighbors_clique_le {G : SimpleGraph V} {P : Finset (Finset V)} (hP : Packing G P)
    (hmax : ∀ T, Packing G T → (cover T).card ≤ (cover P).card)
    {B : Finset V} (hB : B ∈ P) (hc : G.IsClique (B : Set V)) {x : V} (hx : x ∉ cover P) :
    4 * (neighborsIn G B x).card ≤ 3 * B.card := by
  have hxb : x ∉ B := fun hh => hx (member_in_cover hB hh)
  have h3 := large_card (hP.2 B hB)
  have hin : x ∈ Finset.univ \ cover P := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩
  have hsub : neighborsIn G B x ⊆ B := Finset.filter_subset _ _
  by_cases h5 : 5 ≤ B.card
  · have hsmall : (neighborsIn G B x).card ≤ 1 := by
      apply Finset.card_le_one_iff.mpr
      intro y z hy hz
      by_contra hne
      have hyB := hsub hy
      have hzB := hsub hz
      have hxy := (Finset.mem_filter.mp hy).2
      have hxz := (Finset.mem_filter.mp hz).2
      have ht := adj_triangle hxy hxz (hc hyB hzB hne)
      let W : Finset V := {y,z}
      let R := B \ W
      have hW : W ⊆ B := Finset.insert_subset hyB (Finset.singleton_subset_iff.mpr hzB)
      have hCard : R.card + 2 = B.card := by
        simpa only [W, Finset.card_pair hne] using Finset.card_sdiff_add_card_eq_card hW
      have hR : Large G R := .inl ⟨by omega, hc.subset (Finset.sdiff_subset : R ⊆ B)⟩
      have hdis : Disjoint ({x,y,z} : Finset V) R := by
        refine Finset.disjoint_left.mpr ?_
        intro v hv hvR
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl
        · exact hxb (Finset.mem_sdiff.mp hvR).1
        · exact (Finset.mem_sdiff.mp hvR).2 (by simp [W])
        · exact (Finset.mem_sdiff.mp hvR).2 (by simp [W])
      have htSub : ({x,y,z} : Finset V) ⊆ B ∪ (Finset.univ \ cover P) :=
        Finset.insert_subset (Finset.mem_union_right _ hin) (hW.trans Finset.subset_union_left)
      have hh := max_two hP hmax hB (large_of_three ht) hR hdis
        (Finset.union_subset htSub (Finset.sdiff_subset.trans Finset.subset_union_left))
      rw [ht.card_eq] at hh
      omega
    omega
  have hne : neighborsIn G B x ≠ B := by
    intro he
    have hlarge : Large G (insert x B) := by
      refine .inl ⟨by rw [Finset.card_insert_of_notMem hxb]; omega, ?_⟩
      rw [Finset.coe_insert]
      exact (SimpleGraph.isClique_insert_of_notMem hxb).mpr
        ⟨hc, fun v hv => (Finset.mem_filter.mp (show v ∈ neighborsIn G B x by rw [he]; exact hv)).2⟩
    have hh := max_one hP hmax hB hlarge
      (Finset.insert_subset (Finset.mem_union_right _ hin) Finset.subset_union_left)
    rw [Finset.card_insert_of_notMem hxb] at hh
    omega
  have hh := Finset.card_lt_card (ssubset_of_subset_of_ne hsub hne)
  omega

-- Each outer pair of a bowtie contributes at most one neighbor of an outside vertex.
private lemma neighbors_bow_pair_le {G : SimpleGraph V} {P : Finset (Finset V)} (hP : Packing G P)
    (hmax : ∀ T, Packing G T → (cover T).card ≤ (cover P).card)
    {B A C : Finset V} (hB : B ∈ P) {z x : V}
    (hx : x ∉ cover P) (hA : A.card = 2) (hC : C.card = 2) (hAC : Disjoint A C)
    (hzA : z ∉ A) (hzC : z ∉ C) (hBC : B = insert z (A ∪ C))
    (hAc : G.IsClique (A : Set V)) (hCc : G.IsClique (insert z (C : Set V))) :
    (neighborsIn G A x).card ≤ 1 := by
  have hin : x ∈ Finset.univ \ cover P := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩
  have haB : A ⊆ B := by rw [hBC]; exact Finset.subset_union_left.trans (Finset.subset_insert _ _)
  have hcB : insert z C ⊆ B := by
    rw [hBC]
    exact Finset.insert_subset (Finset.mem_insert_self _ _)
      (Finset.subset_union_right.trans (Finset.subset_insert _ _))
  have hxb : x ∉ B := fun h => hx (member_in_cover hB h)
  have hxA : x ∉ A := fun h => hxb (haB h)
  have hxC : x ∉ insert z C := fun h => hxb (hcB h)
  by_contra! hbad
  have hEq : neighborsIn G A x = A :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  have h₁ : (insert x A).card = 3 := by rw [Finset.card_insert_of_notMem hxA, hA]
  have h₂ : (insert z C).card = 3 := by rw [Finset.card_insert_of_notMem hzC, hC]
  have h₃ : B.card = 5 := by
    rw [hBC, Finset.card_insert_of_notMem (by simp [hzA, hzC]),
      Finset.card_union_of_disjoint hAC, hA, hC]
  have hIc : G.IsClique ((insert x A : Finset V) : Set V) := by
    rw [Finset.coe_insert]
    exact (SimpleGraph.isClique_insert_of_notMem hxA).mpr
      ⟨hAc, fun v hv => (Finset.mem_filter.mp (show v ∈ neighborsIn G A x by rw [hEq]; exact hv)).2⟩
  have hsub : insert x A ∪ insert z C ⊆ B ∪ (Finset.univ \ cover P) :=
    Finset.union_subset (Finset.insert_subset (Finset.mem_union_right _ hin)
      (haB.trans Finset.subset_union_left)) (hcB.trans Finset.subset_union_left)
  have hdis : Disjoint (insert x A) (insert z C) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    rcases Finset.mem_insert.mp hv with rfl | hvA
    · exact hxC hw
    rcases Finset.mem_insert.mp hw with rfl | hvC
    · exact hzA hvA
    · exact Finset.disjoint_left.mp hAC hvA hvC
  have hh := max_two hP hmax hB (.inl ⟨h₁.ge, hIc⟩)
    (.inl ⟨h₂.ge, by simpa only [Finset.coe_insert] using hCc⟩) hdis hsub
  omega
private structure MatchingOn (G : SimpleGraph V) (U : Finset V) (M : Finset (Finset V)) : Prop where
  disj : (M : Set (Finset V)).PairwiseDisjoint id
  edges : ∀ B ∈ M, G.IsNClique 2 B
  inside : cover M ⊆ U

private lemma exists_max_matching (G : SimpleGraph V) (U : Finset V) :
    ∃ M, MatchingOn G U M ∧
      ∀ x ∈ U \ cover M, ∀ y ∈ U \ cover M, ¬ G.Adj x y := by
  let X : Finset (Finset (Finset V)) := Finset.univ.filter (MatchingOn G U)
  have hX {M : Finset (Finset V)} : M ∈ X ↔ MatchingOn G U M := by simp [X]
  have he : MatchingOn G U ∅ := ⟨by simp, by simp, by simp [cover]⟩
  obtain ⟨M, hM, hmax⟩ := Finset.exists_max_image X (fun M => (cover M).card) ⟨∅, hX.mpr he⟩
  have hM' := hX.mp hM
  refine ⟨M, hM', ?_⟩
  intro x hx y hy hxy
  let B : Finset V := {x,y}
  have hB : G.IsNClique 2 B := by
    refine ⟨?_, Finset.card_pair hxy.ne⟩
    rw [Finset.coe_insert, Finset.coe_singleton]
    exact SimpleGraph.isClique_pair.mpr (fun _ => hxy)
  have hdis : Disjoint (cover M) B := by
    refine Finset.disjoint_left.mpr ?_
    intro z hz hzB
    simp only [B, Finset.mem_insert, Finset.mem_singleton] at hzB
    rcases hzB with rfl | rfl
    · exact (Finset.mem_sdiff.mp hx).2 hz
    · exact (Finset.mem_sdiff.mp hy).2 hz
  have hsplit : cover (insert B M) = B ∪ cover M := by simp [cover, Finset.biUnion_insert]
  have hIns : MatchingOn G U (insert B M) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [Finset.coe_insert]
      refine Set.pairwiseDisjoint_insert.mpr ⟨hM'.disj, ?_⟩
      intro T hT _
      exact hdis.symm.mono_right (fun _ ht => member_in_cover hT ht)
    · intro T hT
      rcases Finset.mem_insert.mp hT with rfl | hT
      · exact hB
      · exact hM'.edges T hT
    · rw [hsplit]
      exact Finset.union_subset (Finset.insert_subset (Finset.mem_sdiff.mp hx).1
        (Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mp hy).1)) hM'.inside
  have hh := hmax _ (hX.mpr hIns)
  rw [hsplit, Finset.card_union_of_disjoint hdis.symm, hB.card_eq] at hh
  omega

private noncomputable def adjWeight (G : SimpleGraph V) (x y : V) : ℝ :=
  if G.Adj x y then 1 else 0

private noncomputable def between (G : SimpleGraph V) (A B : Finset V) : ℝ :=
  ∑ x ∈ A, ∑ y ∈ B, adjWeight G x y

private noncomputable def degreeSum (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) : ℝ :=
  ∑ v ∈ A, (G.degree v : ℝ)

omit [Fintype V] in
private lemma adjWeight_symm (G : SimpleGraph V) (x y : V) :
    adjWeight G x y = adjWeight G y x := by
  simp only [adjWeight]
  by_cases h : G.Adj x y
  · simp [h, h.symm]
  · have h' : ¬ G.Adj y x := fun hyx => h hyx.symm
    simp [h, h']

omit [Fintype V] in
private lemma between_comm (G : SimpleGraph V) (A B : Finset V) :
    between G A B = between G B A := by
  unfold between
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => adjWeight_symm G x y

omit [Fintype V] in
private lemma between_union_left (G : SimpleGraph V) {A B C : Finset V} (h : Disjoint A B) :
    between G (A ∪ B) C = between G A C + between G B C := by
  unfold between
  exact Finset.sum_union h

omit [Fintype V] in
private lemma between_cover_left (G : SimpleGraph V) {P : Finset (Finset V)} (T : Finset V)
    (hP : (P : Set (Finset V)).PairwiseDisjoint id) :
    between G (cover P) T = ∑ B ∈ P, between G B T := by
  unfold between cover
  exact Finset.sum_biUnion hP

omit [Fintype V] in
private lemma between_pair_le (G : SimpleGraph V) {x y : V} (hne : x ≠ y) (B : Finset V)
    (h : ∀ z ∈ B, G.Adj x z → ¬ G.Adj y z) :
    between G {x,y} B ≤ B.card := by
  unfold between
  rw [Finset.sum_pair hne, ← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ z ∈ B, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro z hz
      by_cases hxz : G.Adj x z
      · simp [adjWeight, hxz, h z hz hxz]
      · by_cases hyz : G.Adj y z <;> simp [adjWeight, hxz, hyz]
    _ = _ := by simp

omit [Fintype V] in
private lemma between_matching_le {G : SimpleGraph V} {U : Finset V} {M : Finset (Finset V)}
    (hM : MatchingOn G U M) (B : Finset V)
    (h : ∀ x y, ({x,y} : Finset V) ∈ M → ∀ z ∈ B, G.Adj x z → ¬ G.Adj y z) :
    2 * between G (cover M) B ≤ (cover M).card * (B.card : ℝ) := by
  have hCard : ((cover M).card : ℝ) = ∑ K ∈ M, (K.card : ℝ) := by
    unfold cover
    rw [Finset.card_biUnion hM.disj, Nat.cast_sum]
    rfl
  rw [between_cover_left G _ hM.disj, Finset.mul_sum, hCard, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro K hK
  have hkc := (hM.edges K hK).card_eq
  obtain ⟨x, y, hne, rfl⟩ := Finset.card_eq_two.mp hkc
  rw [hkc, Nat.cast_ofNat]
  exact mul_le_mul_of_nonneg_left (between_pair_le G hne B (h x y hK)) (by norm_num)

omit [Fintype V] in
private lemma between_singleton_left (G : SimpleGraph V) (B : Finset V) (x : V) :
    between G {x} B = (neighborsIn G B x).card := by
  unfold between neighborsIn adjWeight
  rw [Finset.sum_singleton, ← Finset.sum_filter]
  simp

private lemma sum_degree_eq_between (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    degreeSum G A = between G A Finset.univ := by
  unfold degreeSum between
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_singleton (a := x) (f := fun x => ∑ y ∈ (Finset.univ : Finset V), adjWeight G x y)]
  change (G.degree x : ℝ) = between G {x} Finset.univ
  rw [between_singleton_left]
  congr 1
  rw [← G.card_neighborFinset_eq_degree]
  congr 1
  ext y
  simp [neighborsIn]

omit [Fintype V] in
private lemma card_eq_biUnion_real {P : Finset (Finset V)}
    (hp : (P : Set (Finset V)).PairwiseDisjoint id) :
    ((cover P).card : ℝ) = ∑ B ∈ P, (B.card : ℝ) := by
  unfold cover
  rw [Finset.card_biUnion hp, Nat.cast_sum]
  rfl

private lemma sum_degree_cover (G : SimpleGraph V) [DecidableRel G.Adj] {P : Finset (Finset V)}
    (hp : (P : Set (Finset V)).PairwiseDisjoint id) :
    degreeSum G (cover P) = ∑ B ∈ P, degreeSum G B := by
  unfold degreeSum cover
  exact Finset.sum_biUnion hp


private lemma degree_sum_clique_le (G : SimpleGraph V) [DecidableRel G.Adj] {B : Finset V} {τ : ℝ}
    (hτ : ∀ T, G.IsNClique 3 T → degreeSum G T ≤ τ)
    (hB3 : 3 ≤ B.card) (hBc : G.IsClique (B : Set V)) :
    degreeSum G B ≤ (B.card : ℝ) * τ / 3 := by
  let f (x : V) := G.degree x
  have hn : (B.powersetCard 3).Nonempty := Finset.powersetCard_nonempty.mpr hB3
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image (B.powersetCard 3) (fun s => ∑ x ∈ s, f x) hn
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hT
  let R := B \ T
  have hpair (x : V) (hx : x ∈ T) (y : V) (hy : y ∈ R) : f y ≤ f x := by
    have hy' := Finset.mem_sdiff.mp hy
    let T' := insert y (T.erase x)
    have hT's : T' ⊆ B := Finset.insert_subset hy'.1 ((Finset.erase_subset _ _).trans hsub)
    have hn' : y ∉ T.erase x := fun h => hy'.2 (Finset.mem_of_mem_erase h)
    have hT'c : T'.card = 3 := by
      rw [Finset.card_insert_of_notMem hn', Finset.card_erase_of_mem hx, hcard]
    have h := hmax T' (Finset.mem_powersetCard.mpr ⟨hT's, hT'c⟩)
    change (∑ x ∈ insert y (T.erase x), f x) ≤ ∑ x ∈ T, f x at h
    rw [Finset.sum_insert hn'] at h
    have hh := Finset.sum_erase_add _ f hx
    omega
  have hp : (T.card : ℝ) * degreeSum G R ≤ R.card * degreeSum G T := by
    unfold degreeSum
    calc
      _ = ∑ x ∈ T, ∑ y ∈ R, (f y : ℝ) := by simp [Finset.sum_const, f]
      _ ≤ ∑ x ∈ T, ∑ y ∈ R, (f x : ℝ) :=
        Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => by exact_mod_cast hpair x hx y hy
      _ = _ := by simp [Finset.mul_sum, f]
  have hrc : (R.card : ℝ) + T.card = B.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hsub
  have hs : degreeSum G R + degreeSum G T = degreeSum G B :=
    Finset.sum_sdiff hsub
  have hTτ := hτ T ⟨hBc.subset hsub, hcard⟩
  have hh := mul_le_mul_of_nonneg_left hTτ (by positivity : 0 ≤ (B.card : ℝ))
  rw [hcard, Nat.cast_ofNat] at hp hrc
  rw [← hrc] at hh ⊢
  rw [← hs]
  nlinarith only [hp, hh]

private lemma clique_contribution (G : SimpleGraph V) [DecidableRel G.Adj]
    {P M : Finset (Finset V)} {U S B : Finset V} {τ : ℝ}
    (hP : Packing G P) (hmax : ∀ T, Packing G T → (cover T).card ≤ (cover P).card)
    (hM : MatchingOn G U M) (hU : U = Finset.univ \ cover P)
    (hUS : cover M ∪ S = U) (hMS : Disjoint (cover M) S)
    (hB : B ∈ P) (hc : G.IsClique (B : Set V))
    (hτ : ∀ T, G.IsNClique 3 T → degreeSum G T ≤ τ) :
    between G U B + degreeSum G B ≤
      (B.card : ℝ) * (τ / 3 + (U.card : ℝ) / 2 + (S.card : ℝ) / 4) := by
  have hMx := between_matching_le hM B (fun x y hxy z hz hxz hyz => by
    have hx : x ∉ cover P := (Finset.mem_sdiff.mp (hU ▸ hM.inside
      (member_in_cover hxy (Finset.mem_insert_self _ _)))).2
    have hy : y ∉ cover P := (Finset.mem_sdiff.mp (hU ▸ hM.inside
      (member_in_cover hxy (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))).2
    have hxy' := (hM.edges _ hxy).isClique
      (show x ∈ (({x,y} : Finset V) : Set V) by simp)
      (show y ∈ (({x,y} : Finset V) : Set V) by simp)
      (by
        intro he
        have hcard := (hM.edges _ hxy).card_eq
        subst y
        simp at hcard)
    exact no_common_in_clique hP hmax hB hc hx hy hz hxy' hxz hyz)
  have hSx : 4 * between G S B ≤ 3 * (S.card : ℝ) * (B.card : ℝ) := by
    have he : between G S B = ∑ x ∈ S, between G {x} B := by simp [between]
    rw [he, Finset.mul_sum]
    calc
      _ ≤ ∑ _ ∈ S, 3 * (B.card : ℝ) := by
        apply Finset.sum_le_sum
        intro x hx
        rw [between_singleton_left]
        have hx' := Finset.mem_union_right (cover M) hx
        rw [hUS, hU] at hx'
        exact_mod_cast neighbors_clique_le hP hmax hB hc (Finset.mem_sdiff.mp hx').2
      _ = _ := by simp; ring
  have hsum := degree_sum_clique_le G hτ (large_card (hP.2 B hB)) hc
  have hcU : ((U.card : ℕ) : ℝ) = ((cover M).card : ℝ) + S.card := by
    rw [← hUS, Finset.card_union_of_disjoint hMS, Nat.cast_add]
  rw [hcU]
  conv_lhs => rw [← hUS, between_union_left G hMS]
  nlinarith only [hMx, hSx, hsum]

private lemma bow_contribution (G : SimpleGraph V) [DecidableRel G.Adj]
    {P : Finset (Finset V)} {B : Finset V} {z : V} {δ τ : ℝ}
    (hP : Packing G P) (hmax : ∀ T, Packing G T → (cover T).card ≤ (cover P).card)
    (hB : B ∈ P) (hBow : Bow G B z) (hδ : ∀ x, δ ≤ G.degree x)
    (hτ : ∀ T, G.IsNClique 3 T → degreeSum G T ≤ τ) :
    let U := (Finset.univ \ cover P)
    between G U B + degreeSum G B ≤ (B.card : ℝ) * ((U.card : ℝ) / 2 + 2 * τ / 5 - δ / 10) := by
  dsimp only
  let U := (Finset.univ \ cover P)
  change between G U B + degreeSum G B ≤ (B.card : ℝ) * ((U.card : ℝ) / 2 + 2 * τ / 5 - δ / 10)
  have hBcard := bow_card hBow
  obtain ⟨A, C, hA, hC, hAC, hzA, hzC, hBC, hAcl, hCcl⟩ := hBow
  have hD : degreeSum G B ≤ 2 * τ - G.degree z := by
    have hA' : G.IsNClique 3 (insert z A) := ⟨by rwa [Finset.coe_insert],
      by rw [Finset.card_insert_of_notMem hzA, hA]⟩
    have hC' : G.IsNClique 3 (insert z C) := ⟨by rwa [Finset.coe_insert],
      by rw [Finset.card_insert_of_notMem hzC, hC]⟩
    have ha := hτ _ hA'
    have hc := hτ _ hC'
    unfold degreeSum at ha hc ⊢
    rw [Finset.sum_insert hzA] at ha
    rw [Finset.sum_insert hzC] at hc
    rw [hBC, Finset.sum_insert (by simp [hzA, hzC]), Finset.sum_union hAC]
    linarith only [ha,hc]
  have hE : 2 * between G U B ≤ (U.card : ℝ) * (B.card : ℝ) + between G U {z} := by
    have hsingle (x : V) : between G {x} B =
        adjWeight G x z + between G {x} A + between G {x} C := by
      simp only [between, Finset.sum_singleton]
      rw [hBC, Finset.sum_insert (by simp [hzA, hzC]), Finset.sum_union hAC, add_assoc]
    have hre (T : Finset V) : between G U T = ∑ x ∈ U, between G {x} T := by simp [between]
    rw [hre B, hre {z}, Finset.mul_sum]
    calc
      _ ≤ ∑ x ∈ U, ((B.card : ℝ) + between G {x} {z}) := by
        apply Finset.sum_le_sum
        intro x hx
        rw [hsingle x, between_singleton_left G A, between_singleton_left G C]
        have hx' := (Finset.mem_sdiff.mp hx).2
        have hAone := neighbors_bow_pair_le hP hmax hB hx' hA hC hAC hzA hzC hBC
          (hAcl.subset (Set.subset_insert _ _)) hCcl
        have hCone := neighbors_bow_pair_le hP hmax hB hx' hC hA hAC.symm hzC hzA
          (by simpa only [Finset.union_comm] using hBC) (hCcl.subset (Set.subset_insert _ _)) hAcl
        have hA1 : ((neighborsIn G A x).card : ℝ) ≤ 1 := by exact_mod_cast hAone
        have hC1 : ((neighborsIn G C x).card : ℝ) ≤ 1 := by exact_mod_cast hCone
        have hwt : adjWeight G x z ≤ 1 := by unfold adjWeight; split <;> norm_num
        simp only [between, Finset.sum_singleton, hBcard, Nat.cast_ofNat]
        linarith only [hA1,hC1,hwt]
      _ = _ := by simp [Finset.sum_add_distrib]
  have hEz : between G U {z} ≤ (G.degree z : ℝ) := by
    have hdegree := sum_degree_eq_between G {z}
    simp only [degreeSum, Finset.sum_singleton] at hdegree
    rw [between_comm G U, hdegree]
    unfold between
    simp only [Finset.sum_singleton]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
      intro x _ _
      unfold adjWeight
      split <;> positivity)
  rw [hBcard, Nat.cast_ofNat] at hE ⊢
  linarith only [hE,hD,hEz,hδ z]

omit [Fintype V] in
private lemma matched_pair_adj {G : SimpleGraph V} {U : Finset V} {M : Finset (Finset V)}
    (hM : MatchingOn G U M) {x y : V} (hxy : ({x,y} : Finset V) ∈ M) : G.Adj x y := by
  apply (hM.edges _ hxy).isClique (by simp) (by simp)
  intro he
  have hc := (hM.edges _ hxy).card_eq
  subst y
  simp at hc

private lemma remainder_contribution {G : SimpleGraph V} {P M : Finset (Finset V)} {U S : Finset V}
    (hP : Packing G P) (hmax : ∀ T, Packing G T → (cover T).card ≤ (cover P).card)
    (hU : U = Finset.univ \ cover P) (hM : MatchingOn G U M)
    (hS : ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y)
    (hUS : cover M ∪ S = U) (hMS : Disjoint (cover M) S) :
    between G U U ≤ (U.card : ℝ) ^ 2 / 2 - (S.card : ℝ) ^ 2 / 2 := by
  have houtside {x : V} (hx : x ∈ U) : x ∉ cover P := by
    rw [hU] at hx
    exact (Finset.mem_sdiff.mp hx).2
  have hp {B : Finset V} (hB : B ⊆ U) :
      2 * between G (cover M) B ≤ ((cover M).card : ℝ) * (B.card : ℝ) := by
    refine between_matching_le hM B fun x y hxy z hz hxz hyz => ?_
    refine remainder_triangle_free hP hmax (houtside (hM.inside (member_in_cover hxy ?_)))
      (houtside (hM.inside (member_in_cover hxy ?_))) (houtside (hB hz))
      (matched_pair_adj hM hxy) hyz hxz.symm
    · simp
    · simp
  have hMU := hp (Finset.Subset.rfl : U ⊆ U)
  have hSU : 2 * between G S U ≤ (S.card : ℝ) * ((cover M).card : ℝ) := by
    have hpoint (x : V) (hx : x ∈ S) :
        2 * between G {x} U ≤ ((cover M).card : ℝ) := by
      have hxU : x ∈ U := hUS ▸ Finset.mem_union_right _ hx
      have hMx := hp (Finset.singleton_subset_iff.mpr hxU)
      simp only [Finset.card_singleton, Nat.cast_one, mul_one] at hMx
      have hzero : between G S {x} = 0 := by
        unfold between
        simp only [Finset.sum_singleton]
        apply Finset.sum_eq_zero
        intro y hy
        simp [adjWeight, hS y hy x hx]
      rw [between_comm, ← hUS, between_union_left G hMS, hzero, add_zero]
      exact hMx
    have hre : between G S U = ∑ x ∈ S, between G {x} U := by simp [between]
    rw [hre, Finset.mul_sum]
    simpa using Finset.sum_le_sum (s := S) (fun x hx => hpoint x hx)
  have hsplit : ((U.card : ℕ) : ℝ) = ((cover M).card : ℝ) + S.card := by
    rw [← hUS, Finset.card_union_of_disjoint hMS, Nat.cast_add]
  have heq := between_union_left G (C := U) hMS
  rw [hUS] at heq
  rw [heq]
  rw [hsplit] at hMU ⊢
  nlinarith only [hMU,hSU]

set_option maxHeartbeats 600000 in
private lemma packing_bound (G : SimpleGraph V) [DecidableRel G.Adj] {δ τ : ℝ}
    (hδ : ∀ x, δ ≤ G.degree x)
    (hτ : ∀ T, G.IsNClique 3 T → degreeSum G T ≤ τ) :
    ∃ c d s : ℝ, 0 ≤ c ∧ 0 ≤ d ∧ c + d ≤ Fintype.card V ∧
      2 * (G.edgeFinset.card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 2 +
        c * (τ / 3 - (Fintype.card V : ℝ) / 2 + s / 4) +
        d * ((4 * τ - 5 * (Fintype.card V : ℝ) - δ) / 10) - s ^ 2 / 2 := by
  obtain ⟨P,hP,hmax⟩ := exists_max_packing G
  let U := Finset.univ \ cover P
  obtain ⟨M,hM,hs⟩ := exists_max_matching G U
  let S := U \ cover M
  have hUS : cover M ∪ S = U := Finset.union_sdiff_of_subset hM.inside
  have hMS : Disjoint (cover M) S := Finset.sdiff_disjoint.symm
  let C := P.filter (fun (B : Finset V) => G.IsClique (B : Set V))
  let D := P.filter (fun (B : Finset V) => ¬ G.IsClique (B : Set V))
  let c : ℝ := ∑ B ∈ C, (B.card : ℝ)
  let d : ℝ := ∑ B ∈ D, (B.card : ℝ)
  let n : ℝ := Fintype.card V
  let u : ℝ := U.card
  let s : ℝ := S.card
  have hc : 0 ≤ c := Finset.sum_nonneg fun B _ => Nat.cast_nonneg B.card
  have hd : 0 ≤ d := Finset.sum_nonneg fun B _ => Nat.cast_nonneg B.card
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hUP : cover P ∪ U = Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ _)
  have hUPD : Disjoint (cover P) U := Finset.sdiff_disjoint.symm
  have hsum : c + d = ((cover P).card : ℝ) := by
    dsimp [c,d,C,D]
    rw [Finset.sum_filter_add_sum_filter_not, ← card_eq_biUnion_real hP.1]
  have hsum' : c + d + u = n := by
    dsimp [u,n]
    rw [hsum, ← Nat.cast_add, ← Finset.card_union_of_disjoint hUPD, hUP, Finset.card_univ]
  have htotal : degreeSum G Finset.univ =
      between G U U + ∑ B ∈ P, (between G U B + degreeSum G B) := by
    conv_lhs => rw [← hUP]
    unfold degreeSum
    rw [Finset.sum_union hUPD]
    change degreeSum G (cover P) + degreeSum G U = _
    rw [sum_degree_cover G hP.1, sum_degree_eq_between G U, ← hUP,
      between_comm G U _, between_union_left G hUPD,
      between_cover_left G U hP.1, Finset.sum_add_distrib]
    simp_rw [between_comm G _ U]
    unfold degreeSum
    ring
  have hC :
      (∑ B ∈ C, (between G U B + degreeSum G B)) ≤ c * (τ / 3 + u / 2 + s / 4) := by
    unfold c
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun B hB => ?_
    obtain ⟨hBP,hBc⟩ := Finset.mem_filter.mp hB
    exact clique_contribution G hP hmax hM rfl hUS hMS hBP hBc hτ
  have hD :
      (∑ B ∈ D, (between G U B + degreeSum G B)) ≤ d * (u / 2 + 2 * τ / 5 - δ / 10) := by
    unfold d
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun B hB => ?_
    obtain ⟨hBP,hBnc⟩ := Finset.mem_filter.mp hB
    rcases hP.2 B hBP with hBc | ⟨z,hz⟩
    · exact (hBnc hBc.2).elim
    · exact bow_contribution G hP hmax hBP hz hδ hτ
  have hSumSplit : (∑ B ∈ C, (between G U B + degreeSum G B)) +
      (∑ B ∈ D, (between G U B + degreeSum G B)) =
      ∑ B ∈ P, (between G U B + degreeSum G B) := by
    exact Finset.sum_filter_add_sum_filter_not P _ _
  have hUineq := remainder_contribution hP hmax rfl hM hs hUS hMS
  change between G U U ≤ u ^ 2 / 2 - s ^ 2 / 2 at hUineq
  have heq : degreeSum G Finset.univ = 2 * (G.edgeFinset.card : ℝ) := by
    unfold degreeSum
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  rw [heq, ← hSumSplit] at htotal
  refine ⟨c,d,s,hc,hd,by linarith only [hsum',hu],?_⟩
  change 2 * (G.edgeFinset.card : ℝ) ≤ n ^ 2 / 2 + c * (τ / 3 - n / 2 + s / 4) +
    d * ((4 * τ - 5 * n - δ) / 10) - s ^ 2 / 2
  have halg : u ^ 2 / 2 + c * (τ / 3 + u / 2 + s / 4) +
      d * (u / 2 + 2 * τ / 5 - δ / 10) =
      n ^ 2 / 2 + c * (τ / 3 - n / 2 + s / 4) + d * ((4 * τ - 5 * n - δ) / 10) := by
    rw [← hsum']
    ring
  linarith only [htotal,hUineq,hC,hD,halg]

private lemma dense_min_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Fintype.card V ^ 2 < 4 * G.edgeFinset.card)
    (hdeg : ∀ x, G.edgeFinset.card < Fintype.card V * G.degree x) :
    ∃ t, G.IsNClique 3 t ∧ 21 * G.edgeFinset.card ≤
      4 * Fintype.card V * ∑ v ∈ t, G.degree v := by
  have hN : 0 < Fintype.card V := by
    by_contra! hh
    have he := G.card_edgeFinset_le_card_choose_two
    have hzero : Fintype.card V = 0 := by omega
    rw [hzero] at he hG
    have hEdgeZero : G.edgeFinset.card = 0 := Nat.eq_zero_of_le_zero he
    omega
  let _ : Nonempty V := Fintype.card_pos_iff.mp hN
  let n : ℝ := Fintype.card V
  let e : ℝ := G.edgeFinset.card
  let δ : ℝ := G.minDegree
  let τ : ℝ := 21 * e / (4 * n)
  have hn : 0 < n := by dsimp [n]; exact_mod_cast hN
  have he : n ^ 2 < 4 * e := by dsimp [n,e]; exact_mod_cast hG
  have hδ : ∀ x, δ ≤ G.degree x := by
    intro x
    dsimp [δ]
    exact_mod_cast G.minDegree_le_degree x
  have hδ' : e < n * δ := by
    obtain ⟨v,hv⟩ := G.exists_minimal_degree_vertex
    dsimp [e,n,δ]
    rw [hv]
    exact_mod_cast hdeg v
  have h4n : 0 < 4 * n := by positivity
  have heq : (4 * n) * τ = 21 * e := by
    dsimp [τ]
    rw [mul_comm, div_mul_cancel₀ _ h4n.ne']
  by_contra! h
  have hτ (B : Finset V) (hB : G.IsNClique 3 B) : degreeSum G B ≤ τ := by
    have hh : 4 * n * degreeSum G B < 21 * e := by
      dsimp [n,e,degreeSum]
      exact_mod_cast h B hB
    dsimp [τ]
    apply (le_div_iff₀ h4n).mpr
    rw [mul_comm]
    exact hh.le
  obtain ⟨c,d,s,hc,hd,hcd,hPack⟩ := packing_bound G hδ hτ
  exact fan_arithmetic hn he hc hd hcd hδ' heq.le hPack

end FanTriangle

theorem OMA.solution : type_of% @Erdos1033.erdos_1033.variants.fan := by
  intro n G _ hG
  have hG' : Fintype.card (Fin n) ^ 2 < 4 * G.edgeFinset.card := by simpa only [Fintype.card_fin]
  obtain ⟨t, ht, h⟩ := FanTriangle.reduce_min_degree FanTriangle.dense_min_degree G hG'
  refine ⟨t, ht, ?_⟩
  rw [Fintype.card_fin] at h
  by_contra! hh
  have h' := Nat.mul_lt_mul_of_pos_left hG (by decide : 0 < 21)
  have hh' := Nat.mul_le_mul_left n hh.le
  nlinarith only [h, h', hh']