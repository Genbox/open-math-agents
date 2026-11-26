import FormalConjectures.Arxiv.«2507.17780».«2»

/-! A counterexample from Fischer, with the lower bound certified by forts. -/

namespace FischerGraph

open SimpleGraph Arxiv.«2507.17780»

abbrev Vertex := Fin 3 ⊕ (Fin 3 × Fin 7)

def center (j : Fin 3) : Vertex := .inl j

def branch (j : Fin 3) (i : Fin 7) : Vertex := .inr (j, i)

def attachment (t : Fin 2) : Fin 7 :=
  if t = 0 then 1 else 4

def leaf (t e : Fin 2) : Fin 7 :=
  if t = 0 then (if e = 0 then 2 else 3) else (if e = 0 then 5 else 6)

def block : Vertex → Fin 3 × Fin 3
  | .inl j => (j, 0)
  | .inr (j, i) => (j, if i = 0 then 0 else if i.val ≤ 3 then 1 else 2)

def ascendingEdges : Vertex → Vertex → Bool
  | .inl j, .inl k => j != k
  | .inl j, .inr (k, i) => j == k && i == 0
  | .inr (j, i), .inr (k, l) =>
      j == k && ((i == 0 && (l == 1 || l == 4)) ||
        (i != l && ((i.val > 0 && i.val ≤ 3 && l.val > 0 && l.val ≤ 3) ||
          (i.val > 3 && l.val > 3))))
  | _, _ => false

def graph : SimpleGraph Vertex where
  Adj x y := (ascendingEdges x y || ascendingEdges y x) = true
  symm := by
    constructor
    intro x y h
    simpa only [Bool.or_comm] using h
  loopless := by
    constructor
    exact (show ∀ x : Vertex, ¬ (ascendingEdges x x || ascendingEdges x x) = true from by decide)

instance graphAdjDecidable : DecidableRel graph.Adj := by
  unfold graph
  infer_instance

theorem graphConnected : graph.Connected := by
  refine (connected_iff_exists_forall_reachable graph).mpr ⟨center 0, ?_⟩
  have hc : ∀ j, graph.Reachable (center 0) (center j) := by
    intro j
    fin_cases j
    · exact Reachable.refl _
    · exact Adj.reachable (by decide)
    · exact Adj.reachable (by decide)
  have hr (j : Fin 3) : graph.Reachable (center j) (branch j 0) :=
    Adj.reachable ((show ∀ j : Fin 3, graph.Adj (center j) (branch j 0) from by decide) j)
  have hattach (j : Fin 3) (t : Fin 2) :
      graph.Reachable (branch j 0) (branch j (attachment t)) :=
    Adj.reachable ((show ∀ j t, graph.Adj (branch j 0) (branch j (attachment t)) from by decide) j t)
  have hleaf (j : Fin 3) (t e : Fin 2) :
      graph.Reachable (branch j (attachment t)) (branch j (leaf t e)) :=
    Adj.reachable ((show ∀ j t e,
      graph.Adj (branch j (attachment t)) (branch j (leaf t e)) from by decide) j t e)
  rintro (j | ⟨j, i⟩)
  · exact hc j
  · apply (hc j).trans
    apply (hr j).trans
    fin_cases i
    · exact Reachable.refl _
    · exact hattach j 0
    · exact (hattach j 0).trans (hleaf j 0 0)
    · exact (hattach j 0).trans (hleaf j 0 1)
    · exact hattach j 1
    · exact (hattach j 1).trans (hleaf j 1 0)
    · exact (hattach j 1).trans (hleaf j 1 1)

theorem degreeBound : graph.maxDegree ≤ 3 :=
  graph.maxDegree_le_of_forall_degree_le _ (by decide)

theorem indepBound : graph.indepNum ≤ 9 := by
  obtain ⟨s, hs⟩ := graph.exists_isNIndepSet_indepNum
  have hc : ∀ x y : Vertex, block x = block y → x ≠ y → graph.Adj x y := by decide
  have hcard : s.card ≤ (Finset.univ : Finset (Fin 3 × Fin 3)).card := by
    refine Finset.card_le_card_of_injOn block (fun _ _ => Finset.mem_univ _) ?_
    intro x hx y hy hxy
    by_contra hne
    exact (hs.1 hx hy hne) (hc x y hxy hne)
  rw [hs.2] at hcard
  simpa using hcard

def Fort (F : Finset Vertex) : Prop :=
  F.Nonempty ∧ ∀ v ∉ F, ∀ w ∈ F, graph.Adj v w →
    ∃ u ∈ F, graph.Adj v u ∧ u ≠ w

theorem step_disjoint_fort {F S : Finset Vertex} (hF : Fort F) (hSF : Disjoint S F) :
    Disjoint (zeroForcingStep graph S) F := by
  apply Finset.disjoint_left.mpr
  intro w hw hwF
  simp only [zeroForcingStep, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  rcases hw with hw | ⟨_, v, hv, hadj, hu⟩
  · exact Finset.disjoint_left.mp hSF hw hwF
  · have hvF : v ∉ F := fun h => Finset.disjoint_left.mp hSF hv h
    obtain ⟨u, huF, huv, hne⟩ := hF.2 v hvF w hwF hadj
    have huS : u ∉ S := fun h => Finset.disjoint_left.mp hSF h huF
    exact hne (hu u huv huS)

theorem force_hits_fort {F S : Finset Vertex} (hF : Fort F) (hS : IsZeroForcingSet graph S) :
    ¬ Disjoint S F := by
  intro hSF
  have hiter (n : ℕ) : Disjoint ((zeroForcingStep graph)^[n] S) F := by
    induction n with
    | zero => exact hSF
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact step_disjoint_fort hF ih
  have hd := hiter (Fintype.card Vertex)
  change Disjoint (zeroForcingClosure graph S) F at hd
  rw [hS] at hd
  obtain ⟨w, hw⟩ := hF.1
  exact Finset.disjoint_left.mp hd (Finset.mem_univ w) hw

def leafPair (j : Fin 3) (t : Fin 2) : Finset Vertex :=
  {branch j (leaf t 0), branch j (leaf t 1)}

def branchPair (j : Fin 3) (t e : Fin 2) : Finset Vertex :=
  {branch j (attachment t), branch j (leaf t e)}

def twoLeaves (j : Fin 3) (a b : Fin 2) : Finset Vertex :=
  branchPair j 0 a ∪ branchPair j 1 b

def acrossBranches (j k : Fin 3) (a b c d : Fin 2) : Finset Vertex :=
  {center j, center k} ∪ branchPair j a b ∪ branchPair k c d

instance fortDecidable (F : Finset Vertex) : Decidable (Fort F) := by
  unfold Fort
  letI (v w : Vertex) : Decidable (∃ u : Vertex, u ∈ F ∧ graph.Adj v u ∧ u ≠ w) :=
    Fintype.decidableExistsFintype
  infer_instance

set_option maxRecDepth 100000 in
theorem leafPair_fort : ∀ j t, Fort (leafPair j t) := by decide

set_option maxRecDepth 100000 in
theorem twoLeaves_fort : ∀ j a b, Fort (twoLeaves j a b) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem acrossBranches_fort : ∀ j k a b c d, j ≠ k → Fort (acrossBranches j k a b c d) := by
  decide

def centerSeeds (S : Finset Vertex) : Finset (Fin 3) :=
  Finset.univ.filter fun j => center j ∈ S

def branchSeeds (S : Finset Vertex) (j : Fin 3) : Finset (Fin 7) :=
  Finset.univ.filter fun i => branch j i ∈ S

def zone : Vertex → Fin 4
  | .inl _ => 0
  | .inr (j, _) => j.succ

theorem seedCount (S : Finset Vertex) :
    S.card = (centerSeeds S).card + (branchSeeds S 0).card +
      (branchSeeds S 1).card + (branchSeeds S 2).card := by
  have hc : (S.filter fun v => zone v = 0).card = (centerSeeds S).card := by
    let e : Fin 3 ↪ Vertex := ⟨center, Sum.inl_injective⟩
    have hfilter : S.filter (fun v => zone v = 0) = (centerSeeds S).map e := by
      apply Finset.ext
      intro v
      rw [Finset.mem_filter, Finset.mem_map]
      rcases v with j | ⟨j, i⟩
      · constructor
        · rintro ⟨hm, _⟩
          exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩, rfl⟩
        · rintro ⟨k, hk, heq⟩
          have hm : e k ∈ S := (Finset.mem_filter.mp hk).2
          exact ⟨heq ▸ hm, rfl⟩
      · constructor
        · rintro ⟨_, heq⟩
          exact (Fin.succ_ne_zero j heq).elim
        · rintro ⟨k, _, heq⟩
          change Sum.inl k = Sum.inr (j, i) at heq
          cases heq
    rw [hfilter, Finset.card_map]
  have hb (j : Fin 3) : (S.filter fun v => zone v = j.succ).card =
      (branchSeeds S j).card := by
    let e : Fin 7 ↪ Vertex := ⟨branch j, fun x y h =>
      congrArg Prod.snd (Sum.inr_injective h)⟩
    have hfilter : S.filter (fun v => zone v = j.succ) = (branchSeeds S j).map e := by
      apply Finset.ext
      intro v
      rw [Finset.mem_filter, Finset.mem_map]
      rcases v with k | ⟨k, i⟩
      · constructor
        · rintro ⟨_, heq⟩
          exact (Fin.succ_ne_zero j heq.symm).elim
        · rintro ⟨a, _, heq⟩
          change Sum.inr (j, a) = Sum.inl k at heq
          cases heq
      · constructor
        · rintro ⟨hm, heq⟩
          have hkj : k = j := Fin.succ_inj.mp heq
          subst k
          exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩, rfl⟩
        · rintro ⟨a, ha, heq⟩
          have hm : e a ∈ S := (Finset.mem_filter.mp ha).2
          have hzone : zone (e a) = j.succ := rfl
          exact ⟨heq ▸ hm, heq ▸ hzone⟩
    rw [hfilter, Finset.card_map]
  have hsum := Finset.sum_card_fiberwise_eq_card_filter S Finset.univ zone
  simp only [Finset.mem_univ, Finset.filter_true, Fin.sum_univ_four] at hsum
  rw [hc, show (1 : Fin 4) = (0 : Fin 3).succ by decide,
    show (2 : Fin 4) = (1 : Fin 3).succ by decide,
    show (3 : Fin 4) = (2 : Fin 3).succ by decide, hb, hb, hb] at hsum
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem profile_two :
    ∀ S : Finset (Fin 7), S.card ≤ 2 → (∀ t, ∃ e, leaf t e ∈ S) →
      ∀ t, ∃ e, attachment t ∉ S ∧ leaf t e ∉ S := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem profile_three :
    ∀ S : Finset (Fin 7), S.card ≤ 3 → (∀ t, ∃ e, leaf t e ∈ S) →
      ∃ t e, attachment t ∉ S ∧ leaf t e ∉ S := by decide

theorem force_hits_leaf {S : Finset Vertex} (hS : IsZeroForcingSet graph S)
    (j : Fin 3) (t : Fin 2) : ∃ e, leaf t e ∈ branchSeeds S j := by
  have hd := force_hits_fort (leafPair_fort j t) hS
  by_contra! hn
  apply hd
  apply Finset.disjoint_left.mpr
  intro v hv hleaf
  simp only [leafPair, Finset.mem_insert, Finset.mem_singleton] at hleaf
  rcases hleaf with rfl | rfl
  · exact hn 0 (by simp [branchSeeds, hv])
  · exact hn 1 (by simp [branchSeeds, hv])

theorem branch_has_three {S : Finset Vertex} (hS : IsZeroForcingSet graph S)
    (j : Fin 3) : 3 ≤ (branchSeeds S j).card := by
  by_contra hcard
  have hp := profile_two (branchSeeds S j) (by omega) (force_hits_leaf hS j)
  obtain ⟨a, ha, ha'⟩ := hp 0
  obtain ⟨b, hb, hb'⟩ := hp 1
  have hd := force_hits_fort (twoLeaves_fort j a b) hS
  apply hd
  apply Finset.disjoint_left.mpr
  intro v hv hv'
  simp only [twoLeaves, branchPair, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton] at hv'
  rcases hv' with (rfl | rfl) | (rfl | rfl)
  · exact ha (by simp [branchSeeds, hv])
  · exact ha' (by simp [branchSeeds, hv])
  · exact hb (by simp [branchSeeds, hv])
  · exact hb' (by simp [branchSeeds, hv])

theorem two_light_branches (C : Finset (Fin 3)) (n : Fin 3 → ℕ)
    (hmin : ∀ j, 3 ≤ n j) (hcard : C.card + n 0 + n 1 + n 2 ≤ 10) :
    ∃ j k : Fin 3, j ≠ k ∧ j ∉ C ∧ k ∉ C ∧ n j ≤ 3 ∧ n k ≤ 3 := by
  have h0 := hmin 0
  have h1 := hmin 1
  have h2 := hmin 2
  by_cases hc : C.card = 0
  · have he := Finset.card_eq_zero.mp hc
    by_cases hl0 : n 0 ≤ 3
    · by_cases hl1 : n 1 ≤ 3
      · exact ⟨0, 1, by decide, by simp [he], by simp [he], hl0, hl1⟩
      · exact ⟨0, 2, by decide, by simp [he], by simp [he], hl0, by omega⟩
    · exact ⟨1, 2, by decide, by simp [he], by simp [he], by omega, by omega⟩
  · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp (show C.card = 1 by omega)
    have hs : ({j} : Finset (Fin 3)).card = 1 := by simp
    fin_cases j
    · exact ⟨1, 2, by decide, by decide, by decide, by omega, by omega⟩
    · exact ⟨0, 2, by decide, by decide, by decide, by omega, by omega⟩
    · exact ⟨0, 1, by decide, by decide, by decide, by omega, by omega⟩

theorem no_small_force {S : Finset Vertex} (hS : IsZeroForcingSet graph S) :
    11 ≤ S.card := by
  by_contra hcard
  have hcnt := seedCount S
  obtain ⟨j, k, hjk, hj, hk, hjcard, hkcard⟩ :=
    two_light_branches (centerSeeds S) (fun j => (branchSeeds S j).card)
      (branch_has_three hS) (by omega)
  obtain ⟨a, b, hab, hab'⟩ := profile_three (branchSeeds S j) hjcard (force_hits_leaf hS j)
  obtain ⟨c, d, hcd, hcd'⟩ := profile_three (branchSeeds S k) hkcard (force_hits_leaf hS k)
  apply force_hits_fort (acrossBranches_fort j k a b c d hjk) hS
  apply Finset.disjoint_left.mpr
  intro v hv hv'
  simp only [acrossBranches, branchPair, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton] at hv'
  rcases hv' with (((rfl | rfl) | (rfl | rfl)) | (rfl | rfl))
  · exact hj (by simp [centerSeeds, hv])
  · exact hk (by simp [centerSeeds, hv])
  · exact hab (by simp [branchSeeds, hv])
  · exact hab' (by simp [branchSeeds, hv])
  · exact hcd (by simp [branchSeeds, hv])
  · exact hcd' (by simp [branchSeeds, hv])

theorem univ_forces : IsZeroForcingSet graph Finset.univ := by
  have hstep : zeroForcingStep graph Finset.univ = Finset.univ := by simp [zeroForcingStep]
  have hiter (n : ℕ) : (zeroForcingStep graph)^[n] Finset.univ = Finset.univ := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, hstep]
  exact hiter _

theorem forcingBound : 11 ≤ zeroForcingNumber graph := by
  apply le_csInf
  · exact ⟨Fintype.card Vertex, Finset.univ, Finset.card_univ, univ_forces⟩
  · rintro _ ⟨S, rfl, hs⟩
    exact no_small_force hs

end FischerGraph

theorem OMA.solution : type_of% @Arxiv.«2507.17780».tx_graffiti_conjecture_2 := by
  intro h
  have hb := h FischerGraph.Vertex FischerGraph.graph FischerGraph.graphConnected
    FischerGraph.degreeBound (fun _ => by decide)
  have hindep := FischerGraph.indepBound
  have hforce := FischerGraph.forcingBound
  omega