import FormalConjectures.ErdosProblems.«1182»

/-! A sparse rectangle-hitting graph gives a linear upper bound on `Erdos1182.F`. -/

-- Credit: @Genbox

open SimpleGraph Filter Asymptotics
open scoped BigOperators

namespace TriangleGoodLinear

private theorem half_block {M Q t : ℕ} (hQM : Q ≤ M) (h : M ≤ t * Q) (ht : 0 < t) :
    2 * (M - Q) ^ t ≤ M ^ t := by
  let R := M - Q
  have hRQ : R + Q = M := Nat.sub_add_cancel hQM
  have hB := pow_add_mul_le_add_pow (show 0 ≤ R by omega) (show 0 ≤ 2 * R + Q by omega) t
  have hr : R ≤ t * Q := (Nat.sub_le _ _).trans h
  have hfast : R ^ t ≤ t * R ^ (t - 1) * Q := by
    calc
      R ^ t = R * R ^ (t - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel ht]
      _ ≤ (t * Q) * R ^ (t - 1) := Nat.mul_le_mul_right _ hr
      _ = _ := by ac_rfl
  calc
    2 * (M - Q) ^ t = R ^ t + R ^ t := by simp [R, two_mul]
    _ ≤ R ^ t + t * R ^ (t - 1) * Q := Nat.add_le_add_left hfast _
    _ ≤ (R + Q) ^ t := hB
    _ = M ^ t := by rw [hRQ]

private theorem budget_lt {n M Q : ℕ} (hn : 0 < n) (hM : 0 < M)
    (hQ : Q ≤ M) (hcov : M ≤ 1600 * Q) :
    2 ^ (2 * n) * (M - Q) ^ (4800 * n) < M ^ (4800 * n) := by
  have hpow := Nat.pow_le_pow_left (half_block hQ hcov (by decide)) (3 * n)
  rw [mul_pow, ← pow_mul, ← pow_mul, show 1600 * (3 * n) = 4800 * n by omega] at hpow
  have hp : 2 ^ (2*n) < 2 ^ (3*n) := Nat.pow_lt_pow_right (by decide) (by omega)
  by_cases hR : M - Q = 0
  · rw [hR, zero_pow (by omega), mul_zero]
    exact Nat.pow_pos hM
  · exact (Nat.mul_lt_mul_of_pos_right hp (Nat.pow_pos (Nat.pos_of_ne_zero hR))).trans_le hpow

private theorem rectangle_sequence {n k : ℕ} (hn : 0 < n) (hkn : k ≤ n)
    (hnk : n ≤ 40 * k) :
    ∃ f : Fin (4800 * n) → Fin n × Fin n,
      ∀ S T : Finset (Fin n), k ≤ S.card → k ≤ T.card →
        ∃ i, (f i).1 ∈ S ∧ (f i).2 ∈ T := by
  classical
  let I := Fin (4800 * n)
  let E := Fin n × Fin n
  let U : Finset (I → E) := Finset.univ
  let bad (ST : Finset (Fin n) × Finset (Fin n)) : Finset (I → E) :=
    if k ≤ ST.1.card ∧ k ≤ ST.2.card then
      U.filter (fun f => ∀ i, f i ∉ ST.1.product ST.2)
    else ∅
  have hbad (ST : Finset (Fin n) × Finset (Fin n)) :
      (bad ST).card ≤ (n ^ 2 - k ^ 2) ^ (4800 * n) := by
    by_cases hsize : k ≤ ST.1.card ∧ k ≤ ST.2.card
    · let A : Finset E := Finset.univ \ ST.1.product ST.2
      let g (f : ↥(bad ST)) (i : I) : ↥A :=
        ⟨f.val i, by
          have hf : f.val ∈ U.filter (fun g => ∀ i, g i ∉ ST.1.product ST.2) := by
            simpa only [bad, if_pos hsize] using f.property
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hf).2 i⟩⟩
      have hg : Function.Injective g := by
        intro f f' h
        apply Subtype.ext
        funext i
        exact congrArg (fun h : I → ↥A => (h i).val) h
      have hc := Fintype.card_le_of_injective g hg
      simp only [Fintype.card_coe, Fintype.card_fun, I, Fintype.card_fin] at hc
      apply hc.trans
      apply Nat.pow_le_pow_left
      have hmul := Nat.mul_le_mul hsize.1 hsize.2
      unfold A E
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_prod, Fintype.card_fin, Finset.product_eq_sprod, Finset.card_product, pow_two, pow_two]
      exact Nat.sub_le_sub_left hmul _
    · simp [bad, if_neg hsize]
  have hlt : ((Finset.univ : Finset (Finset (Fin n) × Finset (Fin n))).biUnion bad).card < U.card := by
    have hrect : n ^ 2 ≤ 1600 * k ^ 2 := by
      calc
        n ^ 2 ≤ (40*k) ^ 2 := Nat.pow_le_pow_left hnk _
        _ = _ := by ring
    have hb := budget_lt hn (Nat.pow_pos hn) (Nat.pow_le_pow_left hkn 2) hrect
    refine (Finset.card_biUnion_le_card_mul _ _ _ (fun ST _ => hbad ST)).trans_lt ?_
    simpa only [U, Finset.card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_finset,
      Fintype.card_fin, ← pow_add, ← two_mul, pow_two, I, E] using hb
  obtain ⟨f, _, hf⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨f, fun S T hS hT => ?_⟩
  by_contra! h
  apply hf
  refine Finset.mem_biUnion.mpr ⟨(S, T), Finset.mem_univ _, ?_⟩
  have hnot (i : I) : f i ∉ S.product T :=
    fun hi => h i (Finset.mem_product.mp hi).1 (Finset.mem_product.mp hi).2
  simpa [bad, hS, hT, U] using hnot

private theorem sparse_graph {n k : ℕ} (hn : 0 < n) (hkn : k ≤ n) (hnk : n ≤ 40*k) :
    ∃ G : SimpleGraph (Fin n), G.Connected ∧ G.edgeSet.ncard ≤ 4801 * n ∧
      ∀ S T : Finset (Fin n), k ≤ S.card → k ≤ T.card → Disjoint S T →
        ∃ u ∈ S, ∃ v ∈ T, G.Adj u v := by
  classical
  obtain ⟨f, hf⟩ := rectangle_sequence hn hkn hnk
  let o : Fin n := ⟨0, hn⟩
  let edges : Finset (Sym2 (Fin n)) := Finset.univ.image (fun i => s((f i).1, (f i).2))
  let star : Finset (Sym2 (Fin n)) := Finset.univ.image (fun v => s(o, v))
  let G : SimpleGraph (Fin n) := fromEdgeSet (↑(edges ∪ star) : Set (Sym2 (Fin n)))
  refine ⟨G, ?_, ?_, ?_⟩
  · apply Connected.of_isUniversal (v := o)
    intro v hv
    exact (fromEdgeSet_adj _).mpr ⟨Finset.mem_coe.mpr
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩)), hv⟩
  · have hsub : G.edgeSet ⊆ (↑(edges ∪ star) : Set (Sym2 (Fin n))) := by
      change (fromEdgeSet _).edgeSet ⊆ _
      rw [edgeSet_fromEdgeSet]
      exact Set.sdiff_subset
    have hE : edges.card ≤ 4800*n := by
      exact (Finset.card_image_le).trans_eq (by simp)
    have hS : star.card ≤ n := by
      exact (Finset.card_image_le).trans_eq (by simp)
    calc
      _ ≤ (↑(edges ∪ star) : Set (Sym2 (Fin n))).ncard := Set.ncard_le_ncard hsub
      _ ≤ edges.card + star.card := by simpa only [Set.ncard_coe_finset] using Finset.card_union_le edges star
      _ ≤ _ := by omega
  · intro S T hS hT hdis
    obtain ⟨i, hi, hj⟩ := hf S T hS hT
    refine ⟨(f i).1, hi, (f i).2, hj, (fromEdgeSet_adj _).mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_coe.mpr
        (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
    · exact fun he => Finset.disjoint_left.mp hdis hi (he.symm ▸ hj)

private def cycle : SimpleGraph (Fin 5) where
  Adj i j := i + 1 = j ∨ j + 1 = i
  symm.symm _ _ h := h.symm
  loopless.irrefl i :=
    (by decide : ∀ a : Fin 5, ¬ (a + 1 = a ∨ a + 1 = a)) i

private instance : DecidableRel cycle.Adj :=
  fun i j => inferInstanceAs (Decidable (i + 1 = j ∨ j + 1 = i))

private lemma cycle_no_triangle :
    ∀ a b c : Fin 5, cycle.Adj a b → cycle.Adj b c → ¬ cycle.Adj a c := by
  decide +kernel

private lemma cycle_sparse :
    ∀ b : Fin 5 → Bool, (∀ i j, cycle.Adj i j → b i = false ∨ b j = false) →
      (Finset.univ.filter (fun i => b i = true)).card ≤ 2 := by
  decide +kernel

private def label {m : ℕ} (i : Fin m) : Fin 5 :=
  ⟨i.val % 5, Nat.mod_lt _ (by decide)⟩

private theorem not_good_of_sparse {n k : ℕ} (hn : 100 ≤ n) (hk : k = (n+39)/40)
    {G : SimpleGraph (Fin n)}
    (hhit : ∀ S T : Finset (Fin n), k ≤ S.card → k ≤ T.card → Disjoint S T →
      ∃ u ∈ S, ∃ v ∈ T, G.Adj u v) :
    ¬ Erdos1182.IsTriangleGood G := by
  classical
  let C : SimpleGraph (Fin (2*n-1)) := cycle.comap label
  have htri : ¬ ((⊤ : SimpleGraph (Fin 3)) ⊑ C) := by
    rintro ⟨f⟩
    have hadj (a b : Fin 3) (h : a ≠ b) : cycle.Adj (label (f a)) (label (f b)) :=
      f.toHom.map_adj (show (⊤ : SimpleGraph (Fin 3)).Adj a b from h)
    exact cycle_no_triangle _ _ _ (hadj 0 1 (by decide)) (hadj 1 2 (by decide)) (hadj 0 2 (by decide))
  have hcopy : ¬ G ⊑ Cᶜ := by
    rintro ⟨f⟩
    let B := (2*n+3)/5
    let U (a : Fin 5) : Finset (Fin n) := Finset.univ.filter (fun i => label (f i) = a)
    have label_of_mem {i : Fin n} {a : Fin 5} (h : i ∈ U a) : label (f i) = a :=
      (Finset.mem_filter.mp h).2
    have hsize (a : Fin 5) : (U a).card ≤ B := by
      let g (i : ↥(U a)) : Fin B := ⟨(f i.val).val / 5, by
        have hi := (f i.val).isLt
        dsimp [B]
        omega⟩
      have hg : Function.Injective g := by
        intro i j h
        apply Subtype.ext
        apply f.injective
        apply Fin.ext
        change (f i.val).val = (f j.val).val
        have hdiv : (f i.val).val / 5 = (f j.val).val / 5 :=
          congrArg (fun t : Fin B => t.val) h
        have hi := congrArg Fin.val (label_of_mem i.property)
        have hj := congrArg Fin.val (label_of_mem j.property)
        change (f i.val).val % 5 = a.val at hi
        change (f j.val).val % 5 = a.val at hj
        omega
      simpa using Fintype.card_le_of_injective g hg
    let big (a : Fin 5) : Bool := decide (k ≤ (U a).card)
    have hindep (a b : Fin 5) (hab : cycle.Adj a b) : big a = false ∨ big b = false := by
      by_contra! h
      have ha : k ≤ (U a).card := by simpa [big] using h.1
      have hb : k ≤ (U b).card := by simpa [big] using h.2
      have hdis : Disjoint (U a) (U b) := Finset.disjoint_left.mpr fun _ hs ht =>
        hab.ne ((label_of_mem hs).symm.trans (label_of_mem ht))
      obtain ⟨u, hu, v, hv, huv⟩ := hhit (U a) (U b) ha hb hdis
      have hf := f.toHom.map_adj huv
      apply hf.2
      change cycle.Adj (label (f u)) (label (f v))
      rwa [label_of_mem hu, label_of_mem hv]
    have bigCard := cycle_sparse big hindep
    have hsum : n = ∑ a : Fin 5, (U a).card := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        (Finset.card_eq_sum_card_fiberwise
          (s := (Finset.univ : Finset (Fin n))) (t := (Finset.univ : Finset (Fin 5)))
          (f := fun i => label (f i)) (fun _ _ => Finset.mem_univ _))
    have hu : n ≤ 2*B + 5*k := by
      calc
        n = ∑ a : Fin 5, (U a).card := hsum
        _ ≤ ∑ a : Fin 5, ((if big a = true then B else 0) + k) := by
          apply Finset.sum_le_sum
          intro a _
          split_ifs with ha
          · exact (hsize a).trans (Nat.le_add_right _ _)
          · have hh : ¬ k ≤ (U a).card := by simpa [big] using ha
            omega
        _ = (Finset.univ.filter fun a => big a = true).card * B + 5*k := by
          rw [Finset.sum_add_distrib, ← Finset.sum_filter]
          simp
        _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_right _ bigCard) _
    dsimp [B] at hu
    omega
  intro he
  let good : Set ℕ := { N | ∀ H : SimpleGraph (Fin N), (⊤ : SimpleGraph (Fin 3)) ⊑ H ∨ G ⊑ Hᶜ }
  change sInf good = 2*n - 1 at he
  have hne : good.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h, Nat.sInf_empty] at he
    omega
  have hgood := csInf_mem hne
  rw [he] at hgood
  exact (hgood C).elim htri hcopy

private theorem upper_linear (n : ℕ) (hn : 100 ≤ n) :
    Erdos1182.F n ≤ 4801 * n := by
  let k := (n+39)/40
  have hkn : k ≤ n := by dsimp [k]; omega
  have hnk : n ≤ 40*k := by dsimp [k]; omega
  obtain ⟨G, hc, hb, hg⟩ := sparse_graph (by omega : 0 < n) hkn hnk
  have hnot := not_good_of_sparse hn (k := k) rfl hg
  let P : Set ℕ := {q | q ≤ n.choose 2 ∧
    ∀ H : SimpleGraph (Fin n), H.Connected → H.edgeSet.ncard ≤ q → Erdos1182.IsTriangleGood H}
  change sSup P ≤ _
  by_cases hP : P.Nonempty
  · apply csSup_le hP
    rintro q ⟨_, hq⟩
    by_contra! h
    exact hnot (hq G hc (hb.trans h.le))
  · simp [Set.not_nonempty_iff_eq_empty.mp hP]


-- The tree lower bound uses the previously merged Genbox proof in PR #104.
private lemma tree_copy_of_degree {V : Type} [Fintype V] [Nonempty V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (U : Type) [Fintype U] (T : SimpleGraph U)
    (hT : T.IsTree) (hd : ∀ v, Fintype.card U - 1 ≤ H.degree v) : T ⊑ H := by
  classical
  have hall (k : ℕ) : ∀ (A : Type) [Fintype A] (G : SimpleGraph A),
      Fintype.card A = k → G.IsTree → (∀ v, k - 1 ≤ H.degree v) → G ⊑ H := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro A _ G hcard hG hdeg
      by_cases hk : k ≤ 1
      · let : Subsingleton A := Fintype.card_le_one_iff_subsingleton.mp (hcard.trans_le hk)
        obtain ⟨w⟩ := ‹Nonempty V›
        refine ⟨⟨⟨fun _ => w, ?_⟩, ?_⟩⟩
        · intro a b hab
          exact (hab.ne (Subsingleton.elim a b)).elim
        · intro a b _
          exact Subsingleton.elim a b
      have hk' : 1 < k := by omega
      let : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (hcard.symm ▸ hk')
      obtain ⟨v, hv⟩ := hG.exists_vert_degree_one_of_nontrivial
      obtain ⟨u, hu, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hv
      let S : Set A := {v}ᶜ
      have hS : (G.induce S).IsTree :=
        ⟨hG.connected.induce_compl_singleton_of_degree_eq_one hv, hG.isAcyclic.induce S⟩
      have hS_card : Fintype.card S = k - 1 := by
        change Fintype.card (({v} : Set A)ᶜ : Set A) = k - 1
        rw [Fintype.card_compl_set, hcard]
        simp
      obtain ⟨f⟩ := ih (Fintype.card S) (by omega) S (G.induce S) rfl hS
        (fun w => (Nat.sub_le _ _).trans (hS_card.symm ▸ hdeg w))
      let u' : S := ⟨u, hu.ne.symm⟩
      let used : Finset V := Finset.univ.image (fun a : S => f a)
      have hused : used.card = Fintype.card S := by
        calc
          used.card = (Finset.univ : Finset S).card :=
            Finset.card_image_of_injective _ f.injective
          _ = _ := Finset.card_univ
      have hcenter : f u' ∈ used := Finset.mem_image.mpr ⟨u', Finset.mem_univ _, rfl⟩
      let N := H.neighborFinset (f u')
      have hN : N.card = H.degree (f u') := H.card_neighborFinset_eq_degree _
      have hNself : f u' ∉ N := H.notMem_neighborFinset_self _
      have hlarge : used.card < (insert (f u') N).card := by
        rw [Finset.card_insert_of_notMem hNself, hused, hS_card, hN]
        exact Nat.lt_succ_of_le (hdeg _)
      obtain ⟨w, hw, hnew⟩ := Finset.exists_mem_notMem_of_card_lt_card hlarge
      have hwN : w ∈ N := (Finset.mem_insert.mp hw).resolve_left
        (fun h => hnew (h.symm ▸ hcenter))
      have hwadj : H.Adj (f u') w := (H.mem_neighborFinset _ _).mp hwN
      let g (a : A) : V := if ha : a = v then w else f ⟨a, ha⟩
      have gv : g v = w := by simp [g]
      have gn (a : A) (ha : a ≠ v) : g a = f ⟨a, ha⟩ := by simp [g, ha]
      refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
      · intro a b hab
        by_cases ha : a = v
        · subst a
          have hbu : b = u := huniq b hab
          rw [hbu, gv, gn u hu.ne.symm]
          exact hwadj.symm
        · by_cases hb : b = v
          · subst b
            have hau : a = u := huniq a hab.symm
            rw [hau, gn u hu.ne.symm, gv]
            exact hwadj
          · rw [gn a ha, gn b hb]
            exact f.toHom.map_adj (show (G.induce S).Adj ⟨a, ha⟩ ⟨b, hb⟩ from hab)
      · intro a b heq
        change g a = g b at heq
        by_cases ha : a = v
        · by_cases hb : b = v
          · exact ha.trans hb.symm
          · subst a
            exfalso
            apply hnew
            exact Finset.mem_image.mpr ⟨⟨b, hb⟩, Finset.mem_univ _,
              by simpa only [gv, gn b hb] using heq.symm⟩
        · by_cases hb : b = v
          · subst b
            exfalso
            apply hnew
            exact Finset.mem_image.mpr ⟨⟨a, ha⟩, Finset.mem_univ _,
              by simpa only [gv, gn a ha] using heq⟩
          · rw [gn a ha, gn b hb] at heq
            exact congrArg Subtype.val (f.injective heq)
  exact hall (Fintype.card U) U T rfl hT hd

private lemma tree_ramsey_upper (n : ℕ) (hn : 2 ≤ n) {T : SimpleGraph (Fin n)}
    (hT : T.IsTree) (C : SimpleGraph (Fin (2 * n - 1))) :
    (⊤ : SimpleGraph (Fin 3)) ⊑ C ∨ T ⊑ Cᶜ := by
  classical
  by_cases htri : (⊤ : SimpleGraph (Fin 3)) ⊑ C
  · exact Or.inl htri
  right
  have hcf : C.CliqueFree 3 := by
    by_contra hc
    exact htri (by simpa only [completeGraph_eq_top] using
      (not_cliqueFree_iff_top_isContained 3).mp hc)
  by_cases hdegree : ∀ v, n - 1 ≤ Cᶜ.degree v
  · have : Nonempty (Fin (2 * n - 1)) := ⟨⟨0, by omega⟩⟩
    exact tree_copy_of_degree Cᶜ (Fin n) T hT (by simpa using hdegree)
  push Not at hdegree
  obtain ⟨v, hv⟩ := hdegree
  let S := C.neighborFinset v
  have hcard : n ≤ Fintype.card S := by
    have h := C.degree_compl v
    rw [Fintype.card_fin] at h
    rw [Fintype.card_coe, C.card_neighborFinset_eq_degree]
    omega
  have hclique : Cᶜ.IsClique (S : Set (Fin (2 * n - 1))) := by
    rw [isClique_compl]
    simpa only [S, coe_neighborFinset] using isIndepSet_neighborSet_of_triangleFree C hcf v
  let f : Fin n ↪ S := (Fin.castLEEmb hcard).trans (Fintype.equivFin S).symm.toEmbedding
  refine ⟨⟨⟨fun a => (f a).val, ?_⟩, ?_⟩⟩
  · intro a b hab
    exact hclique (f a).property (f b).property
      (fun he => hab.ne (f.injective (Subtype.ext he)))
  · intro a b he
    exact f.injective (Subtype.ext he)

private lemma tree_ramsey_lower_witness (n N : ℕ) (hn : 2 ≤ n) (hN : N < 2 * n - 1)
    (T : SimpleGraph (Fin n)) (hT : T.Connected) :
    ∃ C : SimpleGraph (Fin N), ¬ ((⊤ : SimpleGraph (Fin 3)) ⊑ C) ∧ ¬ (T ⊑ Cᶜ) := by
  classical
  let color (v : Fin N) : Bool := decide (v.val < n - 1)
  let C : SimpleGraph (Fin N) := (⊤ : SimpleGraph Bool).comap color
  refine ⟨C, ?_, ?_⟩
  · rintro ⟨f⟩
    have hinj : Function.Injective (fun i : Fin 3 => color (f i)) := by
      intro i j he
      by_contra hij
      have hadj : (⊤ : SimpleGraph (Fin 3)).Adj i j := hij
      have himg : C.Adj (f i) (f j) := f.toHom.map_adj hadj
      exact himg he
    have hcard := Fintype.card_le_of_injective _ hinj
    norm_num at hcard
  · rintro ⟨f⟩
    have hlab (i j : Fin n) : color (f i) = color (f j) := by
      obtain ⟨w⟩ := hT.preconnected i j
      induction w with
      | nil => rfl
      | cons h _ ih =>
        exact (not_ne_iff.mp (f.toHom.map_adj h).2).trans ih
    have hclass (i j : Fin n) : ((f i).val < n - 1) ↔ ((f j).val < n - 1) :=
      decide_eq_decide.mp (hlab i j)
    let g (i : Fin n) : Fin (n - 1) :=
      ⟨if (f i).val < n - 1 then (f i).val else (f i).val - (n - 1), by
        have hi := (f i).isLt
        split <;> omega⟩
    have hg : Function.Injective g := by
      intro i j he
      have heq := congrArg Fin.val he
      change (if (f i).val < n - 1 then (f i).val else (f i).val - (n - 1)) =
        (if (f j).val < n - 1 then (f j).val else (f j).val - (n - 1)) at heq
      apply f.injective
      change f i = f j
      apply Fin.ext
      by_cases hi : (f i).val < n - 1
      · simpa only [if_pos hi, if_pos ((hclass i j).mp hi)] using heq
      · have hj : ¬ (f j).val < n - 1 := fun h => hi ((hclass i j).mpr h)
        simp only [if_neg hi, if_neg hj] at heq
        omega
    have hcard := Fintype.card_le_of_injective g hg
    simp only [Fintype.card_fin] at hcard
    omega

private lemma tree_triangle_good (n : ℕ) (hn : 2 ≤ n) (T : SimpleGraph (Fin n))
    (hT : T.IsTree) : Erdos1182.IsTriangleGood T := by
  unfold Erdos1182.IsTriangleGood graphRamsey
  let good : Set ℕ := {N | ∀ C : SimpleGraph (Fin N), (⊤ : SimpleGraph (Fin 3)) ⊑ C ∨ T ⊑ Cᶜ}
  change sInf good = 2 * n - 1
  have h : 2 * n - 1 ∈ good := tree_ramsey_upper n hn (T := T) hT
  apply le_antisymm (Nat.sInf_le h)
  refine le_csInf ⟨2 * n - 1, h⟩ ?_
  intro N hN
  by_contra! hlt
  obtain ⟨C, hC1, hC2⟩ := tree_ramsey_lower_witness n N hn hlt T hT.connected
  change ∀ C : SimpleGraph (Fin N), (⊤ : SimpleGraph (Fin 3)) ⊑ C ∨ T ⊑ Cᶜ at hN
  exact (hN C).elim hC1 hC2

private theorem lower_pred : type_of% @Erdos1182.erdos_1182.variants.F_ge_pred := by
  classical
  intro n hn
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  apply Erdos1182.le_F
  · have htop := (connected_top (V := Fin n)).card_vert_le_card_edgeSet_add_one
    rw [Nat.card_fin, Nat.card_coe_set_eq] at htop
    have hcard : (⊤ : SimpleGraph (Fin n)).edgeSet.ncard = n.choose 2 := by
      rw [Set.ncard_eq_toFinset_card']
      change (⊤ : SimpleGraph (Fin n)).edgeFinset.card = n.choose 2
      rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
    change n ≤ (⊤ : SimpleGraph (Fin n)).edgeSet.ncard + 1 at htop
    rw [hcard] at htop
    omega
  · intro T hconn hbound
    have hmin := hconn.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_fin, Nat.card_coe_set_eq] at hmin
    apply tree_triangle_good n hn T
    apply isTree_iff_connected_and_card.mpr
    refine ⟨hconn, ?_⟩
    rw [Nat.card_fin, Nat.card_coe_set_eq]
    omega

end TriangleGoodLinear

theorem OMA.solution : type_of% @Erdos1182.erdos_1182.parts.ii := by
  change (fun n : ℕ => (Erdos1182.F n : ℝ)) =Θ[atTop] (fun n : ℕ => (n : ℝ))
  constructor
  · refine IsBigO.of_bound 4801 ?_
    filter_upwards [eventually_ge_atTop (100 : ℕ)] with n hn
    simp only [Real.norm_natCast]
    exact_mod_cast TriangleGoodLinear.upper_linear n hn
  · refine IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    simp only [Real.norm_natCast]
    exact_mod_cast (show n ≤ 2 * Erdos1182.F n by
      have := TriangleGoodLinear.lower_pred (n := n) hn
      omega)