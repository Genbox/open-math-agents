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

private def paley : Digraph (Fin 19) where
  Adj a b := (b - a).val ∈ ([1, 4, 5, 6, 7, 9, 11, 16, 17] : List ℕ)

private instance : DecidableRel paley.Adj := fun a b => by
  unfold paley
  infer_instance

private lemma paley_tournament : paley.IsTournament := by
  constructor
  · decide +kernel
  · decide +kernel

private lemma paley_translate (u v a : Fin 19) : paley.Adj (u + a) v ↔ paley.Adj u (v - a) := by
  unfold paley
  change (v - (u + a)).val ∈ _ ↔ (v - a - u).val ∈ _
  rw [show v - (u + a) = v - a - u by abel]

private lemma paley_property : HasPropertyS paley 3 := by
  have hcheck : ∀ b c : Fin 19, ∃ x : Fin 19, paley.Adj x 0 ∧ paley.Adj x b ∧ paley.Adj x c := by
    decide +kernel
  intro A hA
  obtain ⟨a, b, c, _, _, _, rfl⟩ := card_eq_three.mp hA
  obtain ⟨x, hx0, hxb, hxc⟩ := hcheck (b - a) (c - a)
  have hd : ∀ e ∈ ({a, b, c} : Finset (Fin 19)), paley.Adj (x + a) e := by
    intro e he
    simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · apply (paley_translate _ _ _).mpr
      simpa using hx0
    · exact (paley_translate _ _ _).mpr hxb
    · exact (paley_translate _ _ _).mpr hxc
  exact ⟨x + a, fun hx => paley_tournament.1 _ (hd _ hx), hd⟩

end OMA

theorem OMA.solution : type_of% @Erdos902.erdos_902.variants.szekeres_f_three := by
  have hw : 19 ∈ {m : ℕ | 3 ≤ m ∧ ∃ G : Digraph (Fin m),
      G.IsTournament ∧ Erdos902.HasPropertyS G 3} :=
    ⟨by decide, OMA.paley, OMA.paley_tournament, OMA.paley_property⟩
  apply le_antisymm (Nat.sInf_le hw)
  apply le_csInf ⟨19, hw⟩
  rintro m ⟨hm, G, ht, hS⟩
  have h := OMA.szekeres_bound hm (by decide) G ht hS
  norm_num at h
  omega