import FormalConjectures.ErdosProblems.«1092»
import Mathlib.Tactic

/-! A generalized Mycielski graph on an odd cycle. The signed color change around the
bottom cycle is odd. It is invariant up the cylinder and vanishes at its cap. -/

open Finset SimpleGraph Filter Asymptotics
open scoped BigOperators Classical

namespace GridColoring

private abbrev Row (t : ℕ) := Fin (t+1)
private abbrev Col (t : ℕ) := Fin (2*t+3)
private abbrev Vertex (t : ℕ) := Option (Row t × Col t)

private def levels {t : ℕ} (i j : Row t) : Prop :=
  (i.val=0 ∧ j.val=0) ∨ i.val+1=j.val ∨ j.val+1=i.val

private def near {t : ℕ} (x y : Col t) : Prop := x+1=y ∨ y+1=x

private def adj {t : ℕ} : Vertex t → Vertex t → Prop
  | none, none => False
  | none, some (i,_) | some (i,_), none => i.val=t
  | some (i,x), some (j,y) => levels i j ∧ near x y

private lemma shift_ne {t : ℕ} (x : Col t) : x+1≠x := by
  intro h
  have h' : (1:Col t)=0 := add_left_cancel (a:=x) (by rw [add_zero]; exact h)
  have := congrArg Fin.val h'
  change 1%(2*t+3)=0 at this
  rw [Nat.mod_eq_of_lt (by omega)] at this
  omega

private def grid (t : ℕ) : SimpleGraph (Vertex t) where
  Adj := adj
  symm.symm x y h := by
    cases x with
    | none => cases y <;> exact h
    | some x =>
      cases y with
      | none => exact h
      | some y =>
        obtain ⟨i,x⟩ := x; obtain ⟨j,y⟩ := y
        obtain ⟨hl,hn⟩ := h
        exact ⟨by unfold levels at *; tauto, hn.symm⟩
  loopless := ⟨fun x ↦ by
    cases x with
    | none => exact id
    | some x =>
      rintro ⟨_,h|h⟩ <;> exact shift_ne x.2 h⟩

private def changeColor (a b : Fin 3) : ℤ :=
  if a=b then 0 else if a+1=b then 1 else -1

private def changePair (a c : Fin 3) : ℤ := -2*changeColor a c

private lemma opposite (a b : Fin 3) : changeColor a b = -changeColor b a := by
  decide +revert

private lemma two_changes (a b c : Fin 3) (ab : a ≠ b) (bc : b ≠ c) :
    changePair a c = changeColor a b + changeColor b c := by decide +revert

private lemma shifted_sum {t : ℕ} (f : Col t → ℤ) :
    ∑ x, f (x+1) = ∑ x, f x := Equiv.sum_comp (Equiv.addRight (1:Col t)) f

private def winding {t : ℕ} (c : Col t → Fin 3) : ℤ :=
  ∑ i, changePair (c i) (c (i+1+1))

private lemma wind_equal {t : ℕ} (f g : Col t → Fin 3)
    (fg : ∀ i, f i ≠ g (i+1)) (gf : ∀ i, g i ≠ f (i+1)) : winding f = winding g := by
  let A := fun i ↦ changeColor (f i) (g (i+1))
  let B := fun i ↦ changeColor (g i) (f (i+1))
  calc
    _ = ∑ i, (A i+B (i+1)) := sum_congr rfl fun i _ ↦ two_changes _ _ _ (fg i) (gf (i+1))
    _ = (∑ i, A i)+(∑ i, B i) := by rw [sum_add_distrib,shifted_sum B]
    _ = ∑ i, (B i+A (i+1)) := by rw [sum_add_distrib,shifted_sum A,add_comm]
    _ = _ := sum_congr rfl fun i _ ↦ (two_changes _ _ _ (gf i) (fg (i+1))).symm

private lemma wind_top {t : ℕ} (f : Col t → Fin 3) (a : Fin 3) (h : ∀ i, f i ≠ a) :
    winding f = 0 := by
  let A := fun i ↦ changeColor (f i) a
  calc
    _ = ∑ i, (A i - A (i+1+1)) := by
      apply sum_congr rfl
      intro i hi
      rw [two_changes _ _ _ (h i) (h _).symm, opposite a]
      rfl
    _ = 0 := by rw [sum_sub_distrib,shifted_sum (fun i ↦ A (i+1)),shifted_sum A,sub_self]

private lemma wind_bottom {t : ℕ} (f : Col t → Fin 3) (hf : ∀ i, f i ≠ f (i+1)) :
    winding f ≠ 0 := by
  let A := fun i ↦ changeColor (f i) (f (i+1))
  have eq : winding f = 2*(∑ i, A i) := by
    calc
      _ = ∑ i, (A i+A (i+1)) := sum_congr rfl fun i _ ↦ two_changes _ _ _ (hf i) (hf (i+1))
      _ = _ := by rw [sum_add_distrib,shifted_sum A]; ring
  have one (a b : Fin 3) (h : a ≠ b) : Odd (changeColor a b) := by decide +revert
  have parity : Odd (∑ i, A i) := by
    have aux (s : Finset (Col t)) : (∑ i ∈ s, A i) % 2 = (s.card : ℤ) % 2 := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
        obtain ⟨z,hz⟩ := one _ _ (hf i)
        change A i = _ at hz
        rw [sum_insert hi,card_insert_of_notMem hi,Nat.cast_add_one,hz]; omega
    have h := aux univ
    simp only [card_univ,Fintype.card_fin,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at h
    exact Int.odd_iff.mpr (by omega)
  intro h
  rw [eq] at h
  obtain ⟨z,hz⟩ := parity
  omega

private lemma not_three (t : ℕ) : ¬(grid t).Colorable 3 := by
  rintro ⟨C⟩
  let c := fun (i : Row t) (x : Col t) ↦ C (some (i,x))
  have same (i : Row t) : winding (c i) = winding (c 0) := by
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih =>
      apply Eq.trans _ ih
      apply wind_equal
      · intro x; apply C.valid; exact ⟨Or.inr (Or.inr rfl), Or.inl rfl⟩
      · intro x; apply C.valid; exact ⟨Or.inr (Or.inl rfl), Or.inl rfl⟩
  have hb := wind_bottom (c 0) (fun x ↦ C.valid (show (grid t).Adj (some (0,x)) (some (0,x+1)) from
    ⟨Or.inl ⟨rfl,rfl⟩,Or.inl rfl⟩))
  have ht := wind_top (c (Fin.last t)) (C none) (fun x ↦ C.valid (show
    (grid t).Adj (some (Fin.last t,x)) none from rfl))
  exact hb ((same (Fin.last t)).symm.trans ht)

private lemma small_fiber {J : Type*} [Fintype J] {k : ℕ} (hk : 0 < k) (f : J → Fin k) :
    ∃ b, (univ.filter (fun v ↦ f v = b)).card * k ≤ Fintype.card J := by
  obtain ⟨b,hb⟩ := Fintype.exists_card_fiber_lt_of_card_lt_mul f
    (n := Fintype.card J / k + 1) (by simpa using Nat.lt_mul_div_succ (Fintype.card J) hk)
  exact ⟨b,(Nat.mul_le_mul_right k (Nat.le_of_lt_succ hb)).trans (Nat.div_mul_le_self _ _)⟩

private lemma degree_grid {t : ℕ} (i : Row t) (x : Col t) : (grid t).degree (some (i,x)) ≤ 7 := by
  classical
  let R := univ.filter (levels i)
  let S : Finset (Col t) := {x-1,x+1}
  have rsub : R.image Fin.val ⊆ {i.val-1,i.val,i.val+1} := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hj
    have hk := (mem_filter.mp hk).2
    simp only [mem_insert,mem_singleton]
    unfold levels at hk
    omega
  have rcard : R.card ≤ 3 := by
    have h := card_le_card rsub
    rw [card_image_of_injective _ Fin.val_injective] at h
    exact h.trans ((card_insert_le _ _).trans (by have := card_le_two (a:=i.val) (b:=i.val+1); omega))
  let T := insert (none : Vertex t) ((R ×ˢ S).image some)
  have nt : (grid t).neighborFinset (some (i,x)) ⊆ T := by
    intro z hz
    have ha := ((grid t).mem_neighborFinset _ _).mp hz
    cases z with
    | none => exact mem_insert_self _ _
    | some z =>
      obtain ⟨j,y⟩ := z
      obtain ⟨hl,hn⟩ := ha
      apply mem_insert_of_mem
      apply mem_image_of_mem
      apply mem_product.mpr
      refine ⟨mem_filter.mpr ⟨mem_univ _,hl⟩,?_⟩
      rcases hn with h|h
      · exact mem_insert_of_mem (mem_singleton.mpr h.symm)
      · exact mem_insert.mpr (Or.inl (eq_sub_iff_add_eq.mpr h))
  have hS : S.card ≤ 2 := card_le_two
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine (card_le_card nt).trans ((card_insert_le _ _).trans ?_)
  have h := card_image_le (s:=R ×ˢ S) (f:=some)
  rw [card_product] at h
  nlinarith [Nat.mul_le_mul rcard hS]

private def rowOf {t : ℕ} : Vertex t → Row t := fun v ↦ v.elim 0 Prod.fst
private def colOf {t : ℕ} : Vertex t → Col t := fun v ↦ v.elim 0 Prod.snd

private def protectedAt {t : ℕ} (k : Row t) (b : Col t) : Vertex t → Prop
  | none => True
  | some (i,x) => i ≠ k ∧ x ≠ b

private def paint {t : ℕ} (k : Row t) (b : Col t) : Vertex t → Fin 2
  | none => Fin.ofNat 2 (t+1)
  | some (i,x) => Fin.ofNat 2 (if i.val < k.val then (x-b).val else i.val)

private lemma col_succ {t : ℕ} {x y b : Col t} (h : x+1=y) (hy : y≠b) :
    (y-b).val = (x-b).val+1 := by
  have heq : (x-b)+1 = y-b := by rw [←h]; abel
  have hn := sub_ne_zero.mpr hy
  have hv := congrArg Fin.val heq
  rw [Fin.val_add_one] at hv
  split at hv
  · exact False.elim (hn (Fin.ext hv.symm))
  · exact hv.symm

private lemma paint_valid {t : ℕ} {k : Row t} {b : Col t} {u v : Vertex t}
    (hu : protectedAt k b u) (hv : protectedAt k b v) (h : (grid t).Adj u v) :
    paint k b u ≠ paint k b v := by
  have cap (i : Row t) (x : Col t) (hi : i ≠ k) (ht : i.val=t) :
      paint k b none ≠ paint k b (some (i,x)) := by
    have hk := k.isLt
    have hg : ¬ i.val < k.val := by omega
    intro he
    apply_fun Fin.val at he
    simp only [paint,hg,if_false,Fin.ofNat] at he
    rw [ht] at he
    omega
  cases u with
  | none =>
    cases v with
    | none => exact False.elim h
    | some v => exact cap v.1 v.2 hv.1 h
  | some u =>
    cases v with
    | none => exact (cap u.1 u.2 hu.1 h).symm
    | some v =>
      obtain ⟨i,x⟩ := u; obtain ⟨j,y⟩ := v
      obtain ⟨hl,hn⟩ := h
      obtain ⟨hik,hxb⟩ := hu
      obtain ⟨hjk,hyb⟩ := hv
      have hi : i.val ≠ k.val := fun h ↦ hik (Fin.ext h)
      have hj : j.val ≠ k.val := fun h ↦ hjk (Fin.ext h)
      unfold levels at hl
      intro he
      apply_fun Fin.val at he
      by_cases hk : i.val < k.val
      · have hjk : j.val < k.val := by omega
        simp only [paint,hk,hjk,if_true,Fin.ofNat] at he
        rcases hn with h|h
        · have := col_succ h hyb; omega
        · have := col_succ h hxb; omega
      · have hjk : ¬ j.val < k.val := by omega
        simp only [paint,hk,hjk,if_false,Fin.ofNat] at he
        omega

private lemma delete_small {t : ℕ} {J : Type*} [Fintype J]
    (F : SimpleGraph J) (f : J → Vertex t) (hf : Function.Injective f)
    (hadj : ∀ ⦃v w⦄, F.Adj v w → (grid t).Adj (f v) (f w)) :
    ∃ E : Finset (Sym2 J), E ⊆ F.edgeFinset ∧ E.card*(t+1) ≤ 14*Fintype.card J ∧
      (F.deleteEdges E).Colorable 2 := by
  classical
  obtain ⟨k,hk⟩ := small_fiber (by omega : 0 < t+1) (fun v ↦ rowOf (f v))
  obtain ⟨b,hb⟩ := small_fiber (by omega : 0 < 2*t+3) (fun v ↦ colOf (f v))
  let B := univ.filter (fun v ↦ ¬protectedAt k b (f v))
  let E := B.biUnion (fun v ↦ F.incidenceFinset v)
  have sub : B ⊆ (univ.filter (fun v ↦ rowOf (f v) = k)) ∪
      (univ.filter (fun v ↦ colOf (f v) = b)) := by
    intro v hv
    have h := (mem_filter.mp hv).2
    change ¬protectedAt k b (f v) at h
    cases hfv : f v with
    | none => exact False.elim (h (by simp [hfv,protectedAt]))
    | some p =>
      obtain ⟨i,x⟩ := p
      simp [hfv,protectedAt] at h
      apply mem_union.mpr
      by_cases hi : i = k
      · left
        apply mem_filter.mpr
        exact ⟨mem_univ _,by rw [hfv]; exact hi⟩
      · right
        apply mem_filter.mpr
        exact ⟨mem_univ _,by rw [hfv]; exact h hi⟩
  have bcard : B.card*(t+1) ≤ 2*Fintype.card J := by
    have h := (card_le_card sub).trans (card_union_le _ _)
    have hl := Nat.mul_le_mul_right (t+1) h
    rw [Nat.add_mul] at hl
    have hc := (Nat.mul_le_mul_left ((univ.filter (fun v ↦ colOf (f v) = b)).card)
      (by omega : t+1 ≤ 2*t+3)).trans hb
    omega
  have deg (v) (hv : v ∈ B) : F.degree v ≤ 7 := by
    have h := (mem_filter.mp hv).2
    cases hfv : f v with
    | none => exact False.elim (h (by simp [hfv,protectedAt]))
    | some p =>
      obtain ⟨i,x⟩ := p
      have hs : (F.neighborFinset v).image f ⊆ (grid t).neighborFinset (some (i,x)) := by
        rintro _ hy
        obtain ⟨w,hw,rfl⟩ := mem_image.mp hy
        apply ((grid t).mem_neighborFinset _ _).mpr
        rw [←hfv]
        exact hadj ((F.mem_neighborFinset _ _).mp hw)
      have hle := card_le_card hs
      rw [card_image_of_injective _ hf,SimpleGraph.card_neighborFinset_eq_degree,
        SimpleGraph.card_neighborFinset_eq_degree] at hle
      exact hle.trans (degree_grid i x)
  have ec : E.card ≤ B.card*7 := by
    calc
      E.card ≤ ∑ v ∈ B, (F.incidenceFinset v).card := card_biUnion_le
      _ ≤ ∑ _v ∈ B, 7 := sum_le_sum fun v hv ↦ (F.card_incidenceFinset_eq_degree v).le.trans (deg v hv)
      _ = _ := by simp
  have es : E ⊆ F.edgeFinset := by
    intro e he
    obtain ⟨v,hv,he⟩ := mem_biUnion.mp he
    exact F.incidenceFinset_subset v he
  refine ⟨E,es,?_,?_⟩
  · calc
      _ ≤ (B.card*7)*(t+1) := Nat.mul_le_mul_right _ ec
      _ = 7*(B.card*(t+1)) := by ring
      _ ≤ 7*(2*Fintype.card J) := Nat.mul_le_mul_left _ bcard
      _ = _ := by ring
  · refine ⟨SimpleGraph.Coloring.mk (fun v ↦ paint k b (f v)) ?_⟩
    intro v w hva
    obtain ⟨hvw,hout⟩ := SimpleGraph.deleteEdges_adj.mp hva
    apply paint_valid (h := hadj hvw)
    · by_contra hp
      apply hout
      exact mem_biUnion.mpr ⟨v,mem_filter.mpr ⟨mem_univ _,hp⟩,
        (F.mem_incidenceFinset _ _).mpr (F.mk'_mem_incidenceSet_left_iff.mpr hvw)⟩
    · by_contra hp
      apply hout
      exact mem_biUnion.mpr ⟨w,mem_filter.mpr ⟨mem_univ _,hp⟩,
        (F.mem_incidenceFinset _ _).mpr (F.mk'_mem_incidenceSet_right_iff.mpr hvw)⟩

private theorem no_linear : ¬ ∃ g : ℕ → ℕ, Erdos1092.IsAdmissible 2 g ∧
    (fun n : ℕ ↦ (n : ℝ)) =O[atTop] (fun n : ℕ ↦ (g n : ℝ)) := by
  classical
  rintro ⟨g,hg,hbig⟩
  obtain ⟨C,hC⟩ := hbig.bound
  obtain ⟨N,hN⟩ := eventually_atTop.1 hC
  obtain ⟨B,hB⟩ := exists_nat_ge C
  let t := 14*(N+B+1)
  let e := (Fintype.equivFin (Vertex t)).symm
  let G := (grid t).comap e
  have hcol : G.chromaticNumber ≤ (3 : ℕ∞) := by
    apply hg
    intro H
    obtain ⟨E,hes,hee,hec⟩ := delete_small H.coe (fun v ↦ e v.val)
      (e.injective.comp Subtype.val_injective) (fun {_ _} h ↦ H.adj_sub h)
    let m := Fintype.card H.verts
    change E.card*(t+1) ≤ 14*m at hee
    refine ⟨E,hes,?_,SimpleGraph.chromaticNumber_le_iff_colorable.mpr hec⟩
    change E.card ≤ g m
    by_cases hn : N ≤ m
    · have h := hN m hn
      simp only [Real.norm_eq_abs,Nat.abs_cast] at h
      have hz : (m:ℝ) ≤ (B:ℝ)*(g m:ℝ) := h.trans (mul_le_mul_of_nonneg_right hB (by positivity))
      have hnat : m ≤ B*g m := by exact_mod_cast hz
      have ht : 14*B ≤ t+1 := by dsimp [t]; omega
      apply (Nat.mul_le_mul_right_iff (by omega : 0 < t+1)).mp
      calc
        _ ≤ 14*m := hee
        _ ≤ 14*(B*g m) := Nat.mul_le_mul_left 14 hnat
        _ = (14*B)*g m := by ring
        _ ≤ (t+1)*g m := Nat.mul_le_mul_right _ ht
        _ = _ := Nat.mul_comm _ _
    · have hsmall : 14*m < t+1 := by dsimp [t]; omega
      have hzero : E.card = 0 := by
        by_contra hz
        have := Nat.mul_le_mul_right (t+1) (show 1 ≤ E.card by omega)
        omega
      simp [hzero]
  obtain ⟨c⟩ := (SimpleGraph.chromaticNumber_le_iff_colorable (n:=3)).mp hcol
  apply not_three t
  refine ⟨SimpleGraph.Coloring.mk (fun v ↦ c (e.symm v)) ?_⟩
  intro v w hvw
  apply c.valid
  change (grid t).Adj (e (e.symm v)) (e (e.symm w))
  simpa using hvw

end GridColoring

theorem OMA.solution : type_of% @Erdos1092.f_asymptotic_general := fun h ↦ GridColoring.no_linear (h 2 (by decide))