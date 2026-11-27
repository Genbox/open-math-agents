import FormalConjectures.Wikipedia.AlonSaksSeymourConjecture
import Mathlib.Tactic

/-! The seven-coordinate construction of Huang and Sudakov, Combinatorica 32 (2012), 205–219.
The 30 disjoint squares in the table are checked on the binary cube. -/

open Finset SimpleGraph AlonSaksSeymourConjecture
open scoped BigOperators Classical

namespace SevenCoordinates

private abbrev V (n : ℕ) := Fin 7 → Fin n
private def front (i : Fin 4) : Fin 7 := Fin.castAdd 3 i
private def back (i : Fin 3) : Fin 7 := Fin.natAdd 4 i
private def delta {n : ℕ} (x y : V n) (i : Fin 7) : Bool := decide (x i ≠ y i)
private lemma delta_comm {n : ℕ} (x y : V n) : delta x y = delta y x := by
  funext i; simp only [delta,ne_comm]
private def forbidden (d : Fin 7 → Bool) : Prop :=
  ((∀ i, d (front i) = false) ∧ ((∀ i, d (back i) = false) ∨ (∀ i, d (back i) = true))) ∨
  ((∀ i, d (front i) = true) ∧ (∃ i, d (back i) = false) ∧ (∃ i, d (back i) = true))
private def graph (n : ℕ) : SimpleGraph (V n) where
  Adj x y := ¬ forbidden (delta x y)
  symm.symm x y h := by rw [delta_comm]; exact h
  loopless := ⟨fun x h ↦ h (Or.inl ⟨by simp [delta],Or.inl (by simp [delta])⟩)⟩

private lemma independent_card {n : ℕ} (S : Finset (V n))
    (h : ∀ x ∈ S, ∀ y ∈ S, forbidden (delta x y)) : S.card ≤ 3*n := by
  classical
  have fixed {x y : V n} (hx : x ∈ S) (hy : y ∈ S)
      (he : x (front 0) = y (front 0)) {i : Fin 3} (hb : x (back i) = y (back i)) : x=y := by
    rcases h x hx y hy with ⟨hf,ht|ht⟩|⟨hf,_,_⟩
    · funext k
      refine Fin.addCases (m:=4) (n:=3) (motive:=fun k ↦ x k = y k) (fun j ↦ ?_) (fun j ↦ ?_) k
      · exact Classical.not_not.mp (of_decide_eq_false (hf j))
      · exact Classical.not_not.mp (of_decide_eq_false (ht j))
    · have hh := ht i
      simp [delta,hb] at hh
    · have hh := hf 0
      simp [delta,he] at hh
  have cross {x y : V n} (hx : x ∈ S) (hy : y ∈ S) (he : x (front 0) ≠ y (front 0)) :
      ∃ i, x (back i) = y (back i) := by
    rcases h x hx y hy with ⟨hf,_⟩|⟨_,⟨i,hi⟩,_⟩
    · have hh := hf 0
      simp [delta,he] at hh
    · exact ⟨i,by simpa [delta] using hi⟩
  by_cases hs : ∀ x ∈ S, ∀ y ∈ S, x (front 0) = y (front 0)
  · have inj : Function.Injective (fun x : S ↦ x.val (back 0)) :=
      fun x y he ↦ Subtype.ext (fixed x.2 y.2 (hs _ x.2 _ y.2) he)
    have hb := Fintype.card_le_of_injective _ inj
    simp only [Fintype.card_coe,Fintype.card_fin] at hb
    omega
  · push Not at hs
    obtain ⟨u,hu,v,hv,huv⟩ := hs
    let other (a : Fin n) := if a = u (front 0) then v else u
    have witness (x : S) : ∃ i, x.val (back i) = other (x.val (front 0)) (back i) := by
      by_cases hx : x.val (front 0) = u (front 0)
      · simpa [other,hx] using cross x.2 hv (hx ▸ huv)
      · simpa [other,hx] using cross x.2 hu hx
    let coord (x : S) : Fin 3 := Classical.choose (witness x)
    let code (x : S) := (x.val (front 0),coord x)
    have inj : Function.Injective code := by
      intro x y he
      have hfirst : x.val (front 0) = y.val (front 0) := congrArg Prod.fst he
      have hsecond : coord x = coord y := congrArg Prod.snd he
      apply Subtype.ext
      apply fixed x.2 y.2 hfirst (i:=coord x)
      have h1 := Classical.choose_spec (witness x)
      have h2 := Classical.choose_spec (witness y)
      change x.val (back (coord x)) = other (x.val (front 0)) (back (coord x)) at h1
      change y.val (back (coord y)) = other (y.val (front 0)) (back (coord y)) at h2
      rw [hfirst,hsecond] at h1
      rw [hsecond]
      exact h1.trans h2.symm
    have hb := Fintype.card_le_of_injective _ inj
    simpa [Fintype.card_prod,Nat.mul_comm] using hb

private lemma count_colors {n k : ℕ} (c : (graph n).Coloring (Fin k)) : n^7 ≤ k*(3*n) := by
  let fiber := fun a ↦ univ.filter (fun x : V n ↦ c x = a)
  have h (a : Fin k) : (fiber a).card ≤ 3*n := by
    apply independent_card
    intro x hx y hy
    by_contra hf
    exact c.valid (show (graph n).Adj x y from hf) ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm)
  have hs := card_eq_sum_card_fiberwise (s:=univ) (t:=univ) (f:=fun x : V n ↦ c x) (fun _ _ ↦ mem_univ _)
  calc
    n^7 = (univ : Finset (V n)).card := by simp [V]
    _ = ∑ a, (fiber a).card := hs
    _ ≤ ∑ _a : Fin k, 3*n := sum_le_sum fun a _ ↦ h a
    _ = _ := by simp

private def pos : Fin 30 → Fin 5 → Fin 7 := ![
  ![0,1,2,4,6],
  ![0,1,2,5,6],
  ![0,1,2,4,5],
  ![1,2,3,4,6],
  ![1,2,3,5,6],
  ![1,2,3,4,5],
  ![0,1,3,4,6],
  ![0,1,3,5,6],
  ![0,1,3,4,5],
  ![0,2,3,4,6],
  ![0,2,3,5,6],
  ![0,2,3,4,5],
  ![0,3,4,5,6],
  ![0,3,4,5,6],
  ![0,3,4,5,6],
  ![0,3,4,5,6],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4],
  ![0,1,2,3,4]]

private def bits : Fin 30 → Fin 5 → Bool := ![
  ![false,false,false,false,true],
  ![false,false,false,true,false],
  ![false,false,false,true,false],
  ![false,true,true,false,true],
  ![false,true,true,true,false],
  ![false,true,true,true,false],
  ![false,true,true,false,true],
  ![false,true,true,true,false],
  ![false,true,true,true,false],
  ![true,false,true,false,true],
  ![true,false,true,true,false],
  ![true,false,true,true,false],
  ![true,true,false,false,false],
  ![true,true,true,true,true],
  ![false,true,false,false,false],
  ![false,true,true,true,true],
  ![false,false,true,false,false],
  ![false,false,true,false,true],
  ![false,true,false,false,false],
  ![false,true,false,false,true],
  ![true,false,false,false,false],
  ![true,false,false,false,true],
  ![false,true,true,false,false],
  ![false,true,true,false,true],
  ![true,false,true,false,false],
  ![true,false,true,false,true],
  ![true,true,false,false,false],
  ![true,true,false,false,true],
  ![true,true,true,false,false],
  ![true,true,true,false,true]]

private def matchesSquare (i : Fin 30) (d : Fin 7 → Bool) : Prop :=
  ∀ j, d (pos i j) = bits i j
private instance (i d) : Decidable (matchesSquare i d) := by unfold matchesSquare; infer_instance
private instance (d) : Decidable (forbidden d) := by unfold forbidden; infer_instance

set_option maxHeartbeats 2000000 in
private theorem cover : ∀ d : Fin 7 → Bool, (¬ forbidden d) ↔ ∃ i, matchesSquare i d := by
  decide +kernel

set_option maxHeartbeats 2000000 in
private theorem only_square : ∀ (d : Fin 7 → Bool) (i j : Fin 30), matchesSquare i d →
    matchesSquare j d → i=j := by decide +kernel

private theorem positive_bit : ∀ i, ∃ j, bits i j = true := by decide +kernel

private abbrev Slice (n : ℕ) := Fin 5 → Fin n
private def project {n : ℕ} (i : Fin 30) (x : V n) : Slice n := fun j ↦ x (pos i j)
private def agrees {n : ℕ} (i : Fin 30) (u v : Slice n) : Prop := ∀ j, decide (u j ≠ v j) = bits i j
private lemma agrees_symm {n : ℕ} {i : Fin 30} {u v : Slice n} (h : agrees i u v) : agrees i v u := by
  intro j
  by_cases he : u j = v j
  · simpa [he] using h j
  · simpa [he,Ne.symm he] using h j
private lemma agrees_ne {n : ℕ} {i : Fin 30} {u v : Slice n} (h : agrees i u v) : u ≠ v := by
  rintro rfl
  obtain ⟨j,hj⟩ := positive_bit i
  have hh := h j
  simp [hj] at hh

private abbrev Label (n : ℕ) := Fin (Fintype.card (Slice n))
private noncomputable def ranked {n : ℕ} (i : Fin 30) (x : V n) : Label n :=
  Fintype.equivFin (Slice n) (project i x)
private noncomputable def leftSide {n : ℕ} (i : Fin 30) (a : Label n) : Finset (V n) :=
  univ.filter (fun x ↦ ranked i x = a)
private noncomputable def rightSide {n : ℕ} (i : Fin 30) (a : Label n) : Finset (V n) :=
  univ.filter (fun x ↦ a < ranked i x ∧ agrees i ((Fintype.equivFin (Slice n)).symm a) (project i x))
private lemma biclique_spec {n : ℕ} (i : Fin 30) (a : Label n) (x y : V n) :
    InBiclique (leftSide i a) (rightSide i a) x y ↔
      matchesSquare i (delta x y) ∧ min (ranked i x) (ranked i y) = a := by
  classical
  have decoded (z : V n) : (Fintype.equivFin (Slice n)).symm (ranked i z) = project i z :=
    Equiv.symm_apply_apply _ _
  change _ ↔ agrees i (project i x) (project i y) ∧ _
  simp only [InBiclique,leftSide,rightSide,mem_filter,mem_univ,true_and]
  constructor
  · rintro (⟨rfl,hlt,hh⟩|⟨⟨hlt,hh⟩,rfl⟩)
    · exact ⟨decoded x ▸ hh,min_eq_left hlt.le⟩
    · exact ⟨agrees_symm (decoded y ▸ hh),min_eq_right hlt.le⟩
  · rintro ⟨h,rfl⟩
    have hne : ranked i x ≠ ranked i y := fun he ↦ agrees_ne h ((Fintype.equivFin _).injective he)
    rcases lt_or_gt_of_ne hne with hlt|hlt
    · rw [min_eq_left hlt.le,decoded x]
      exact Or.inl ⟨rfl,hlt,h⟩
    · rw [min_eq_right hlt.le,decoded y]
      exact Or.inr ⟨⟨hlt,agrees_symm h⟩,rfl⟩

private theorem part_bound (n : ℕ) : bicliquePartitionNumber (graph n) ≤ 30*n^5 := by
  let E : (Fin 30 × Label n) ≃ Fin (30*n^5) := Fintype.equivFinOfCardEq (by simp [Label,Slice])
  let A (s : Fin (30*n^5)) := leftSide (E.symm s).1 (E.symm s).2
  let B (s : Fin (30*n^5)) := rightSide (E.symm s).1 (E.symm s).2
  apply Nat.sInf_le
  refine ⟨A,B,?_⟩
  constructor
  · intro s; apply Finset.disjoint_left.mpr
    intro x hx hy
    have h1 := (mem_filter.mp hx).2
    have h2 := (mem_filter.mp hy).2.1
    exact (ne_of_gt h2) h1
  · intro x y
    constructor
    · intro ha
      obtain ⟨i,hi⟩ := (cover (delta x y)).mp ha
      refine ⟨E (i,min (ranked i x) (ranked i y)),?_⟩
      simp only [A,B,Equiv.symm_apply_apply]
      exact (biclique_spec _ _ _ _).mpr ⟨hi,rfl⟩
    · rintro ⟨s,hs⟩
      exact (cover _).mpr ⟨_,((biclique_spec _ _ _ _).mp hs).1⟩
  · intro x y s t hs ht
    obtain ⟨hsi,hsa⟩ := (biclique_spec _ _ _ _).mp hs
    obtain ⟨hti,hta⟩ := (biclique_spec _ _ _ _).mp ht
    have he : (E.symm s).1 = (E.symm t).1 := only_square _ _ _ hsi hti
    apply E.symm.injective
    exact Prod.ext he (by rw [he] at hsa; exact hsa.symm.trans hta)

private theorem counterexample : type_of% @AlonSaksSeymourConjecture.alon_saks_seymour_conjecture := by
  intro universal
  let G := graph 100
  have hb := part_bound 100
  have hh := universal G
  have hχ : G.chromaticNumber ≤ ((30*100^5+1 : ℕ) : ℕ∞) := by
    rw [Nat.cast_add_one]
    exact hh.trans (add_le_add (show (bicliquePartitionNumber G : ℕ∞) ≤ ((30*100^5:ℕ):ℕ∞) by exact_mod_cast hb) le_rfl)
  obtain ⟨c⟩ := SimpleGraph.chromaticNumber_le_iff_colorable.mp hχ
  have h := count_colors c
  norm_num at h

end SevenCoordinates

theorem OMA.solution : type_of% @AlonSaksSeymourConjecture.alon_saks_seymour_conjecture := SevenCoordinates.counterexample