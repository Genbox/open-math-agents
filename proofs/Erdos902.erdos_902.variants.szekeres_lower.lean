import FormalConjectures.ErdosProblems.«902»

/-!
# The Szekeres tournament bound

The lower bound uses the argument recorded in Moon, Topics on Tournaments, §11.
Two applications of the original domination property force many dominators of
every smaller set. Restriction to an in-neighborhood and a count of the incoming
arcs then give the bound by induction.
-/

namespace OMA

open Erdos902 Finset
open scoped BigOperators

private noncomputable def dominators {V : Type*} [Fintype V] (G : Digraph V)
    (A : Finset V) : Finset V := by
  classical
  exact univ.filter (fun v => ∀ a ∈ A, G.Adj v a)

private lemma mem_dominators {V : Type*} [Fintype V] {G : Digraph V} {A : Finset V} {v : V} :
    v ∈ dominators G A ↔ ∀ a ∈ A, G.Adj v a := by
  classical
  simp [dominators]

private lemma domination_le {V : Type*} [Fintype V] (G : Digraph V) {k : ℕ}
    (hk : k ≤ Fintype.card V) (hS : HasPropertyS G k) {A : Finset V} (hA : A.card ≤ k) :
    ∃ v ∉ A, ∀ a ∈ A, G.Adj v a := by
  classical
  obtain ⟨B, hAB, _, hB⟩ :=
    exists_subsuperset_card_eq (subset_univ A) hA (by simpa using hk)
  obtain ⟨v, hv, hd⟩ := hS B hB
  exact ⟨v, fun hvA => hv (hAB hvA), fun a ha => hd a (hAB ha)⟩

private def Many {V : Type*} [Fintype V] (G : Digraph V) (k m : ℕ) : Prop :=
  ∀ A : Finset V, A.card ≤ k → m ≤ (dominators G A).card

private lemma many_of_property {V : Type*} [Fintype V] (G : Digraph V) (hG : G.IsTournament)
    {k : ℕ} (hk : k + 1 ≤ Fintype.card V) (hS : HasPropertyS G (k + 1)) :
    Many G k (k + 2) := by
  classical
  intro A hA
  by_contra! hsmall
  obtain ⟨x, hx, hxd⟩ := domination_le G hk hS (show (dominators G A).card ≤ k + 1 by omega)
  have hcardInsert := (card_insert_le x A).trans (Nat.add_le_add_right hA 1)
  obtain ⟨y, hy, hyd⟩ := domination_le G hk hS hcardInsert
  have hyx : G.Adj y x := hyd _ (mem_insert_self _ _)
  have hyA : y ∈ dominators G A :=
    mem_dominators.mpr fun z hz => hyd z (mem_insert_of_mem hz)
  have hxy : G.Adj x y := hxd _ hyA
  have hne : x ≠ y := fun he => hx (he ▸ hyA)
  exact ((hG.2 x y hne).mp hxy) hyx

private lemma average_bound {V : Type*} [Fintype V] (G : Digraph V)
    (hg : G.IsTournament) (hpos : 0 < Fintype.card V) {d : ℕ}
    (h : ∀ v : V, d ≤ (dominators G {v}).card + 1) : 2 * d ≤ Fintype.card V + 1 := by
  classical
  let q := Fintype.card V
  let I (x y : V) : ℕ := if G.Adj x y then 1 else 0
  let total := ∑ v : V, (dominators G {v}).card
  have hins (v : V) : (∑ x : V, I x v) = (dominators G {v}).card := by
    simp [I, dominators]
  have hpair (x y : V) : I x y + I y x + (if x = y then 1 else 0) = 1 := by
    by_cases he : x = y
    · subst y
      simp [I, hg.1]
    · by_cases hxy : G.Adj x y
      · simp [I, he, hxy, (hg.2 x y he).mp hxy]
      · have hyx : G.Adj y x := (hg.2 y x (fun he' => he he'.symm)).mpr hxy
        simp [I, he, hxy, hyx]
  have hsum : total + total + q = q * q := by
    calc
      _ = ∑ y : V, ∑ x : V, (I x y + I y x + (if x = y then 1 else 0)) := by
        simp only [sum_add_distrib, hins, sum_ite_eq', mem_univ, if_true, sum_const, card_univ,
          nsmul_eq_mul, mul_one]
        rw [sum_comm (f := fun y x => I y x)]
        simp only [hins, total, q, Nat.cast_id]
      _ = _ := by simp [hpair, q]
  have hlower : q * d ≤ total + q := by
    have hs : (∑ _v : V, d) ≤ ∑ v : V, ((dominators G {v}).card + 1) :=
      sum_le_sum fun v _ => h v
    simpa [sum_add_distrib, nsmul_eq_mul, q, total] using hs
  apply Nat.le_of_mul_le_mul_left _ hpos
  calc
    q * (2 * d) = 2 * (q * d) := by ring
    _ ≤ 2 * (total + q) := Nat.mul_le_mul_left 2 hlower
    _ = (total + total + q) + q := by ring
    _ = q * (q + 1) := by rw [hsum]; ring

private lemma many_lower (k m : ℕ) (hm : 0 < m) {V : Type} [Fintype V]
    (G : Digraph V) (hG : G.IsTournament) (h : Many G k m) :
    2 ^ k * (m + 1) ≤ Fintype.card V + 1 := by
  classical
  induction k generalizing V with
  | zero =>
    have hcard : m ≤ Fintype.card V := by simpa [dominators] using h ∅ (by simp)
    simpa using Nat.add_le_add_right hcard 1
  | succ k ih =>
    have hdegree (v : V) : 2 ^ k * (m + 1) ≤ (dominators G {v}).card + 1 := by
      let S := dominators G {v}
      let e : S ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
      let H : Digraph S := ⟨fun x y => G.Adj x.val y.val⟩
      have ht : H.IsTournament :=
        ⟨fun x => hG.1 x.val, fun x y hne => hG.2 x.val y.val (fun he => hne (Subtype.ext he))⟩
      have hm' : Many H k m := by
        intro A hA
        have hcardA : (insert v (A.map e)).card ≤ k + 1 := by
          exact (card_insert_le _ _).trans (by simpa using Nat.add_le_add_right hA 1)
        have hd : (dominators H A).map e = dominators G (insert v (A.map e)) := by
          ext x
          rw [mem_map, mem_dominators]
          constructor
          · rintro ⟨⟨u, hu⟩, hdu, rfl⟩ a ha
            change G.Adj u a
            rcases mem_insert.mp ha with he | ha
            · simpa only [he] using (mem_dominators.mp hu) v (mem_singleton_self _)
            · obtain ⟨a', ha', rfl⟩ := mem_map.mp ha
              exact mem_dominators.mp hdu a' ha'
          · intro hx
            have hxs : x ∈ S := mem_dominators.mpr fun y hy =>
              hx y (by simpa only [mem_singleton.mp hy] using mem_insert_self v (A.map e))
            refine ⟨⟨x, hxs⟩, mem_dominators.mpr ?_, rfl⟩
            intro y hy
            exact hx (e y) (mem_insert_of_mem (mem_map_of_mem _ hy))
        rw [← card_map (f := e), hd]
        exact h (insert v (A.map e)) hcardA
      simpa [Fintype.card_coe, S] using ih H ht hm'
    have hcard : m ≤ Fintype.card V := by simpa [dominators] using h ∅ (by simp)
    have hpos : 0 < Fintype.card V := hm.trans_le hcard
    have hb := average_bound G hG hpos hdegree
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hb

private lemma szekeres_bound {n m : ℕ} (hnt : n ≤ m) (hn : 1 ≤ n)
    (G : Digraph (Fin m)) (ht : G.IsTournament) (hS : HasPropertyS G n) :
    2 ^ (n - 1) * (n + 2) ≤ m + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hmany := many_of_property G ht (by simpa using hnt) hS
  simpa only [Nat.add_sub_cancel, Fintype.card_fin, Nat.add_assoc, Nat.add_comm 2 1] using
    many_lower k (k + 2) (by omega) G ht hmany

/-- A finite tournament with the required domination property exists for every order. -/
private lemma property_exists (n : ℕ) :
    {m : ℕ | n ≤ m ∧ ∃ G : Digraph (Fin m), G.IsTournament ∧ HasPropertyS G n}.Nonempty := by
  classical
  let M := n * (n + 1) + 1
  let V := Fin M × {S : Finset (Fin M) // S.card ≤ n}
  let idx := Fintype.equivFin V
  let selected (x y : V) : Prop := y.1 ∈ x.2.val ∧ x.1 ∉ y.2.val
  let H : Digraph V := ⟨fun x y => selected x y ∨ (¬ selected y x ∧ idx x < idx y)⟩
  have hsel (x y : V) : selected x y → ¬ selected y x := fun h h' => h.2 h'.1
  have hHt : H.IsTournament := by
    constructor
    · intro x
      change ¬ (selected x x ∨ (¬ selected x x ∧ idx x < idx x))
      simp [selected]
    · intro x y hne
      change (selected x y ∨ (¬ selected y x ∧ idx x < idx y)) ↔
        ¬ (selected y x ∨ (¬ selected x y ∧ idx y < idx x))
      by_cases hxy : selected x y
      · simp [hxy, hsel x y hxy]
      by_cases hyx : selected y x
      · simp [hxy, hyx]
      have hneq : idx x ≠ idx y := fun he => hne (idx.injective he)
      rcases lt_or_gt_of_ne hneq with h | h
      · simp [hxy, hyx, h, not_lt_of_ge h.le]
      · simp [hxy, hyx, h, not_lt_of_ge h.le]
  have hHs : HasPropertyS H n := by
    intro A hA
    let U := A.biUnion fun v => insert v.1 v.2.val
    have hU : U.card ≤ n * (n + 1) := by
      rw [← hA]
      refine card_biUnion_le_card_mul A _ _ fun v _ => ?_
      exact (card_insert_le _ _).trans (Nat.add_le_add_right (v.2.property.trans_eq hA.symm) 1)
    have hi : ∃ i : Fin M, i ∉ U := by
      by_contra! hall
      rw [eq_univ_of_forall hall, card_univ, Fintype.card_fin] at hU
      dsimp [M] at hU
      omega
    obtain ⟨i, hi⟩ := hi
    let S := A.image Prod.fst
    have hS : S.card ≤ n := card_image_le.trans_eq hA
    let x : V := (i, ⟨S, hS⟩)
    have hd : ∀ y ∈ A, H.Adj x y := by
      intro y hy
      left
      refine ⟨mem_image_of_mem Prod.fst hy, ?_⟩
      intro hiy
      exact hi (mem_biUnion.mpr ⟨y, hy, mem_insert_of_mem hiy⟩)
    exact ⟨x, fun hx => hHt.1 x (hd x hx), hd⟩
  have hM : M ≤ Fintype.card V := by
    let e : Fin M → V := fun i => (i, ⟨∅, by simp⟩)
    simpa using Fintype.card_le_of_injective e (fun _ _ he => congrArg Prod.fst he)
  have hnM : n ≤ M := by
    have h := Nat.mul_le_mul_left n (show 1 ≤ n + 1 by omega)
    simp only [mul_one] at h
    exact h.trans (Nat.le_succ _)
  let K : Digraph (Fin (Fintype.card V)) := ⟨fun x y => H.Adj (idx.symm x) (idx.symm y)⟩
  refine ⟨Fintype.card V, hnM.trans hM, K, ?_, ?_⟩
  · exact ⟨fun x => hHt.1 (idx.symm x), fun x y hne => hHt.2 _ _
      (fun he => hne (idx.symm.injective he))⟩
  · intro A hA
    let A' := A.map idx.symm.toEmbedding
    obtain ⟨x, hx, hd⟩ := hHs A' (by simpa [A'] using hA)
    refine ⟨idx x, ?_, ?_⟩
    · intro hx'
      apply hx
      simpa [A'] using mem_map_of_mem idx.symm.toEmbedding hx'
    · intro a ha
      change H.Adj (idx.symm (idx x)) (idx.symm a)
      rw [Equiv.symm_apply_apply]
      exact hd _ (mem_map_of_mem idx.symm.toEmbedding ha)

private lemma eventual_szekeres (n : ℕ) (hn : 1 ≤ n) : n * 2 ^ n ≤ 2 * Erdos902.f n := by
  have hmem : Erdos902.f n ∈ {m : ℕ | n ≤ m ∧ ∃ G : Digraph (Fin m),
      G.IsTournament ∧ HasPropertyS G n} :=
    Nat.sInf_mem (property_exists n)
  obtain ⟨hm, G, ht, hS⟩ := hmem
  have hbound := szekeres_bound hm hn G ht hS
  have hpow : 1 ≤ (2 : ℕ) ^ (n - 1) := one_le_pow₀ (by decide)
  rw [mul_add, mul_comm (2 ^ (n - 1)) n] at hbound
  have hlower : n * 2 ^ (n - 1) ≤ Erdos902.f n := by omega
  have he : 2 ^ n = 2 ^ (n - 1) * 2 := by
    conv_lhs => rw [show n = n - 1 + 1 by omega]
    rw [pow_succ]
  rw [he, ← mul_assoc, mul_comm _ 2]
  exact Nat.mul_le_mul_left _ hlower

end OMA

theorem OMA.solution : type_of% @Erdos902.erdos_902.variants.szekeres_lower := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have h : (n : ℝ) * (2 : ℝ) ^ n ≤ 2 * (Erdos902.f n : ℝ) := by
    exact_mod_cast OMA.eventual_szekeres n hn
  linarith