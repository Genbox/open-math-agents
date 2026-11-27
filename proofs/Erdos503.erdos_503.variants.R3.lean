import FormalConjectures.ErdosProblems.«503»
import Mathlib.Data.Sym.Card
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
Croft's bound for isosceles sets in three dimensions
(https://doi.org/10.1112/plms/s3-12.1.400). The equidistant decomposition
follows Yi (https://arxiv.org/abs/2611.05421). The three-dimensional
two-distance bound uses Gram determinants and a finite rational
polynomial certificate. A regular pentagon with its center and two poles
attains the bound.
-/

open scoped BigOperators EuclideanGeometry
open Finset Module

namespace IsoscelesMoments

private def dot {K : Type*} [Fintype K] (x y : K → ℝ) : ℝ := ∑ k, x k * y k

private def rad {K : Type*} [Fintype K] (x : K → ℝ) : ℝ := ∑ k, (x k)^2

private def d2 {K : Type*} [Fintype K] (x y : K → ℝ) : ℝ := ∑ k, (x k - y k)^2

private theorem dot_comm {K : Type*} [Fintype K] (x y : K → ℝ) : dot x y = dot y x := by
  unfold dot
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

private theorem d2_eq {K : Type*} [Fintype K] (x y : K → ℝ) :
    d2 x y = rad x + rad y - 2 * dot x y := by
  unfold d2 rad dot
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

private def kernel {K : Type*} [Fintype K] (a b : ℝ) (x y : K → ℝ) : ℝ :=
  (d2 x y - a) * (d2 x y - b)

theorem weights_zero {I K : Type*} [Fintype I] [Fintype K] (p : I → K → ℝ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hD : ∀ i j, i ≠ j → (∑ k, (p i k - p j k)^2) = a ∨ (∑ k, (p i k - p j k)^2) = b)
    (w : I → ℝ) (h0 : ∑ i, w i = 0)
    (h1 : ∀ k, ∑ i, w i * p i k = 0)
    (h2 : ∀ k l, ∑ i, w i * (p i k * p i l) = 0) :
    ∀ i, w i = 0 := by
  classical
  have hlin (q : K → ℝ) : ∑ i, w i * dot q (p i) = 0 := by
    unfold dot
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro k _
    calc
      _ = ∑ i, q k * (w i * p i k) := Finset.sum_congr rfl (fun i _ => by ring)
      _ = 0 := by rw [← Finset.mul_sum, h1, mul_zero]
  have hrad : ∑ i, w i * rad (p i) = 0 := by
    unfold rad
    simp_rw [Finset.mul_sum, pow_two]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero (fun k _ => h2 k k)
  have hsq (q : K → ℝ) : ∑ i, w i * (dot q (p i))^2 = 0 := by
    calc
      _ = ∑ i, ∑ k, ∑ l, (q k * q l) * (w i * (p i k * p i l)) := by
        apply Finset.sum_congr rfl
        intro i _
        unfold dot
        rw [pow_two, Finset.sum_mul]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = ∑ k, ∑ l, ∑ i, (q k * q l) * (w i * (p i k * p i l)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_comm]
      _ = 0 := by simp only [← Finset.mul_sum, h2, mul_zero, Finset.sum_const_zero]
  let A := ∑ i, w i * (rad (p i))^2
  let C (k : K) := ∑ i, w i * (rad (p i) * p i k)
  have hCross (q : K → ℝ) :
      (∑ i, w i * (rad (p i) * dot q (p i))) = dot q C := by
    calc
      _ = ∑ i, ∑ k, q k * (w i * (rad (p i) * p i k)) := by
        apply Finset.sum_congr rfl
        intro i _
        unfold dot
        simp_rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      _ = _ := by
        rw [Finset.sum_comm]
        unfold dot
        simp only [← Finset.mul_sum, C]
  have hexpand (q z : K → ℝ) (u : ℝ) :
      u * kernel a b q z =
        ((rad q - a) * (rad q - b)) * u +
        (2 * rad q - a - b) * (u * rad z) +
        (2 * (a+b) - 4 * rad q) * (u * dot q z) +
        4 * (u * (dot q z)^2) +
        u * (rad z)^2 +
        (-4) * (u * (rad z * dot q z)) := by
    unfold kernel
    rw [d2_eq]
    ring
  have hrow (q : K → ℝ) : ∑ j, w j * kernel a b q (p j) = A + (-4) * dot q C := by
    simp_rw [hexpand]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, h0, hrad, hlin, hsq,
      hCross, mul_zero, zero_add, A]
  have hdiag (i : I) :
      ∑ j, w j * kernel a b (p i) (p j) = w i * (a*b) := by
    rw [Finset.sum_eq_single i]
    · simp [kernel, d2]
    · intro j _ hji
      rcases hD i j (Ne.symm hji) with h | h <;> simp [kernel, d2, h]
    · simp
  have hW (i : I) : w i * (w i * (a*b)) = A * w i + (-4) * (w i * dot C (p i)) := by
    rw [(hdiag i).symm.trans (hrow (p i)), dot_comm (p i) C]
    ring
  have hsum : ∑ i, w i * (w i * (a*b)) = 0 := by
    simp_rw [hW]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, h0, hlin, mul_zero, add_zero]
  have hnonneg (i : I) : 0 ≤ w i * (w i * (a*b)) := by
    rw [← mul_assoc]
    exact mul_nonneg (mul_self_nonneg _) (mul_nonneg ha.le hb.le)
  intro i
  have hzero : w i * (w i * (a*b)) = 0 :=
    congrFun ((Fintype.sum_eq_zero_iff_of_nonneg hnonneg).1 hsum) i
  rcases mul_eq_zero.mp hzero with hz | hz
  · exact hz
  · exact (mul_eq_zero.mp hz).resolve_right (mul_ne_zero ha.ne' hb.ne')

end IsoscelesMoments

namespace IsoscelesTwoDistances

private def quadraticFeature {K : Type*} (x : K → ℝ) : Sym2 K → ℝ :=
  Sym2.lift ⟨fun k l => x k * x l, fun _ _ => mul_comm _ _⟩

private def features {K : Type*} (x : K → ℝ) : K ⊕ Sym2 K → ℝ
  | .inl k => x k
  | .inr q => quadraticFeature x q

private def affineFeatures {K : Type*} (x : K → ℝ) : Option (K ⊕ Sym2 K) → ℝ
  | none => 1
  | some j => features x j

private def MomentCriterion {I K : Type*} [Fintype I] (p : I → K → ℝ) : Prop :=
  ∀ w : I → ℝ, (∑ i, w i = 0) →
    (∀ k, ∑ i, w i * p i k = 0) →
    (∀ k l, ∑ i, w i * (p i k * p i l) = 0) → ∀ i, w i = 0

private lemma coord_moment {I J : Type*} [Fintype I] {v : I → J → ℝ} {w : I → ℝ}
    (h : ∑ i, w i • v i = 0) (j : J) : ∑ i, w i * v i j = 0 := by
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using congrFun h j

private lemma affine_independent {I K : Type*} [Fintype I] (p : I → K → ℝ)
    (criterion : MomentCriterion p) : LinearIndependent ℝ (fun i => affineFeatures (p i)) := by
  rw [Fintype.linearIndependent_iff]
  intro w hw
  apply criterion w
  · simpa [affineFeatures] using coord_moment hw none
  · intro k
    simpa only [affineFeatures, features] using coord_moment hw (some (Sum.inl k))
  · intro k l
    simpa only [affineFeatures, features, quadraticFeature, Sym2.lift_mk] using
      coord_moment hw (some (Sum.inr s(k, l)))

private lemma spherical_independent {I K : Type*} [Fintype I] [Fintype K] (p : I → K → ℝ)
    {r : ℝ} (hr : r ≠ 0) (hSphere : ∀ i, ∑ k, p i k ^ 2 = r)
    (criterion : MomentCriterion p) : LinearIndependent ℝ (fun i => features (p i)) := by
  rw [Fintype.linearIndependent_iff]
  intro w hw
  have h2 (k l : K) : ∑ i, w i * (p i k * p i l) = 0 := by
    simpa only [features, quadraticFeature, Sym2.lift_mk] using coord_moment hw (Sum.inr s(k, l))
  have hR : (∑ i, w i) * r = 0 := by
    calc
      _ = ∑ i, w i * (∑ k, p i k ^ 2) := by rw [Finset.sum_mul]; simp_rw [hSphere]
      _ = ∑ k, ∑ i, w i * (p i k * p i k) := by
        simp_rw [Finset.mul_sum, pow_two]
        exact Finset.sum_comm
      _ = 0 := by simp [h2]
  apply criterion w ((mul_eq_zero.1 hR).resolve_right hr) _ h2
  intro k
  simpa only [features] using coord_moment hw (Sum.inl k)

private lemma feature_card (d : ℕ) :
    Fintype.card (Fin d ⊕ Sym2 (Fin d)) + 1 = (d + 2).choose 2 := by
  rw [Fintype.card_sum, Sym2.card, Fintype.card_fin]
  rw [show d + 2 = (d + 1) + 1 by omega, Nat.choose_succ_succ' (d + 1) 1, Nat.choose_one_right]
  change d + (d + 1).choose 2 + 1 = d + 1 + (d + 1).choose 2
  omega

private def centered {d : ℕ} (c x : EuclideanSpace ℝ (Fin d)) (k : Fin d) :=
  x k - c k

private lemma centered_sqdist {d : ℕ} (c x y : EuclideanSpace ℝ (Fin d)) :
    (∑ k, (centered c x k - centered c y k) ^ 2) = dist x y ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  apply Finset.sum_congr rfl
  intro k _
  simp only [centered, Real.dist_eq, sq_abs]
  ring

private lemma two_distance_criterion {d : ℕ}
    {S : Finset (EuclideanSpace ℝ (Fin d))} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y = a ∨ dist x y = b)
    (c : EuclideanSpace ℝ (Fin d)) :
    MomentCriterion (fun i : S => centered c i) := by
  apply IsoscelesMoments.weights_zero (fun i : S => centered c i) (sq_pos_of_pos ha) (sq_pos_of_pos hb)
  intro i j hij
  rw [centered_sqdist]
  rcases h i i.property j j.property (fun he => hij (Subtype.ext he)) with hd | hd
  · exact Or.inl (congrArg (· ^ 2) hd)
  · exact Or.inr (congrArg (· ^ 2) hd)

theorem general {d : ℕ}
    {S : Finset (EuclideanSpace ℝ (Fin d))} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y = a ∨ dist x y = b) :
    S.card ≤ (d + 2).choose 2 := by
  classical
  let p (i : S) : Fin d → ℝ := centered 0 i.val
  have hp : MomentCriterion p := two_distance_criterion ha hb h 0
  have hI := affine_independent p hp
  have hCard := hI.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_option, feature_card] at hCard
  simpa using hCard

theorem sphericalGeneral {d : ℕ} (hDim : 1 ≤ d)
    {S : Finset (EuclideanSpace ℝ (Fin d))} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y = a ∨ dist x y = b)
    (c : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hSphere : ∀ x ∈ S, dist x c = r) :
    S.card + 1 ≤ (d + 2).choose 2 := by
  classical
  by_cases hr : r = 0
  · subst r
    have hCard : S.card ≤ 1 := Finset.card_le_one_iff.2 fun hx hy =>
      (dist_eq_zero.1 (hSphere _ hx)).trans (dist_eq_zero.1 (hSphere _ hy)).symm
    have hChoose : 2 ≤ (d + 2).choose 2 := by
      exact (show 2 ≤ (3 : ℕ).choose 2 by decide).trans
        (Nat.choose_le_choose 2 (Nat.add_le_add_right hDim 2))
    omega
  have hRadius (i : S) : ∑ k, centered c i k ^ 2 = r ^ 2 := by
    calc
      _ = ∑ k, (centered c i k - centered c c k) ^ 2 := by simp [centered]
      _ = dist (i : EuclideanSpace ℝ (Fin d)) c ^ 2 := centered_sqdist c i c
      _ = r ^ 2 := by rw [hSphere i i.property]
  have hI := spherical_independent (fun i : S => centered c i) (pow_ne_zero 2 hr) hRadius
    (two_distance_criterion ha hb h c)
  have hCard := hI.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at hCard
  rw [← feature_card d]
  simpa using Nat.add_le_add_right hCard 1

end IsoscelesTwoDistances

namespace GeneralIsosceles


section Coloring

open Finset SimpleGraph

variable {α β : Type*}

private def Used (D : α → α → β) (S : Finset α) (c : β) : Prop :=
  ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ D x y = c

private def NoRainbow (D : α → α → β) (S : Finset α) : Prop :=
  ∀ ⦃x y z⦄, x ∈ S → y ∈ S → z ∈ S → D x y = D y z ∨ D y z = D z x ∨ D z x = D x y

private def colorGraph (D : α → α → β) (hsym : ∀ x y, D x y = D y x) (S : Finset α)
    (c : β) : SimpleGraph S where
  Adj x y := x ≠ y ∧ D x.val y.val = c
  symm := ⟨fun _ _ h => ⟨h.1.symm, (hsym _ _).trans h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private lemma color_of_unreachable_ne {D : α → α → β} {hsym : ∀ x y, D x y = D y x}
    {S : Finset α} {c : β} {x y : S} (h : ¬ (colorGraph D hsym S c).Reachable x y) :
    D x.val y.val ≠ c := by
  intro he
  have hne : x ≠ y := fun heq => h (heq ▸ SimpleGraph.Reachable.rfl)
  exact h (show (colorGraph D hsym S c).Adj x y from ⟨hne, he⟩).reachable

private lemma color_constant_on_component {D : α → α → β} {hsym : ∀ x y, D x y = D y x}
    {S : Finset α} {c : β} (hn : NoRainbow D S) {x y z : S}
    (hxy : ¬ (colorGraph D hsym S c).Reachable x y)
    (hyz : (colorGraph D hsym S c).Reachable y z) :
    D x.val y.val = D x.val z.val := by
  obtain ⟨w⟩ := hyz
  induction w with
  | nil => rfl
  | @cons y t z he w ih =>
    have hxt : ¬ (colorGraph D hsym S c).Reachable x t :=
      fun h => hxy (h.trans he.reachable.symm)
    have h1 := color_of_unreachable_ne hxy
    have h2 := color_of_unreachable_ne hxt
    have hcol : D y.val t.val = c := he.2
    have hNo := hn x.property y.property t.property
    rw [hcol, hsym t.val x.val] at hNo
    exact (hNo.resolve_left h1 |>.resolve_left (Ne.symm h2)).symm.trans (ih hxt)

private lemma color_disconnected [DecidableEq α] (D : α → α → β)
    (hsym : ∀ x y, D x y = D y x) (S : Finset α) :
    NoRainbow D S → ∀ a b c : β, a ≠ b → a ≠ c → b ≠ c →
      Used D S a → Used D S b → Used D S c →
      ∃ e, Used D S e ∧ ¬ (colorGraph D hsym S e).Preconnected := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hn a b c hab hac hbc hA hB hC
    by_contra hnd
    have conn {d : β} (hD : Used D S d) : (colorGraph D hsym S d).Preconnected := by
      by_contra h
      exact hnd ⟨d, hD, h⟩
    have hA' := hA
    obtain ⟨v, hv, w, hw, hvw, _⟩ := hA'
    let sv : S := ⟨v, hv⟩
    let sw : S := ⟨w, hw⟩
    let hNontrivial : Nontrivial S := ⟨⟨sv, sw, fun he => hvw (congrArg Subtype.val he)⟩⟩
    let T := S.erase v
    let lift (u : T) : S := ⟨u.val, Finset.mem_of_mem_erase u.property⟩
    have hT : T ⊂ S :=
      Finset.ssubset_iff_subset_ne.2 ⟨Finset.erase_subset _ _, fun h =>
        (Finset.notMem_erase v S) ((show S ⊆ T from h.ge) hv)⟩
    have htn : NoRainbow D T := by
      intro x y z hx hy hz
      exact hn (Finset.mem_of_mem_erase hx) (Finset.mem_of_mem_erase hy) (Finset.mem_of_mem_erase hz)
    have incident {d : β} (hd : Used D S d) : ∃ u : T, D v u.val = d := by
      obtain ⟨u, hu⟩ := (conn hd).exists_adj_of_nontrivial sv
      have hne : u.val ≠ v := fun h => hu.1 (Subtype.ext h.symm)
      exact ⟨⟨u.val, Finset.mem_erase.2 ⟨hne, u.property⟩⟩, hu.2⟩
    have stillUsed {d : β} (hd : Used D S d) : Used D T d := by
      by_contra hnil
      obtain ⟨e, hne, he⟩ : ∃ e, e ≠ d ∧ Used D S e := by
        by_cases h : a = d
        · exact ⟨b, fun h' => hab (h.trans h'.symm), hB⟩
        · exact ⟨a, h, hA⟩
      obtain ⟨u, hu⟩ := incident he
      obtain ⟨z, hz⟩ := (conn hd).exists_adj_of_nontrivial (lift u)
      by_cases h : z.val = v
      · have hz' : D u.val z.val = d := hz.2
        rw [h, hsym u.val v, hu] at hz'
        exact hne hz'
      · have hn' : u.val ≠ z.val := fun heq => hz.1 (Subtype.ext heq)
        exact hnil ⟨u.val, u.property, z.val, Finset.mem_erase.2 ⟨h, z.property⟩, hn', hz.2⟩
    obtain ⟨e, he, hend⟩ := ih T hT htn a b c hab hac hbc (stillUsed hA) (stillUsed hB) (stillUsed hC)
    let G := colorGraph D hsym T e
    have heS : Used D S e := by
      obtain ⟨x, hx, y, hy, hxy, heq⟩ := he
      exact ⟨x, Finset.mem_of_mem_erase hx, y, Finset.mem_of_mem_erase hy, hxy, heq⟩
    obtain ⟨x₀, y₀, hxy₀⟩ : ∃ x y : T, ¬ G.Reachable x y := by
      change ¬ (∀ x y : T, G.Reachable x y) at hend
      push Not at hend
      exact hend
    have touches (x : T) : ∃ u : T, G.Reachable x u ∧ D v u.val = e := by
      let Z : Set S := {u | ∃ hu : u.val ∈ T, G.Reachable x ⟨u.val, hu⟩}
      have hxZ : lift x ∈ Z := ⟨x.property, SimpleGraph.Reachable.rfl⟩
      have hvZ : sv ∉ Z := fun ⟨h, _⟩ => Finset.notMem_erase v S h
      obtain ⟨p⟩ := conn heS (lift x) sv
      obtain ⟨d, _, hdZ, hnZ⟩ := p.exists_boundary_dart Z hxZ hvZ
      obtain ⟨hdT, hr⟩ := hdZ
      have hv' : d.snd.val = v := by
        by_contra hx
        have hu : d.snd.val ∈ T := Finset.mem_erase.2 ⟨hx, d.snd.property⟩
        have ha : G.Adj ⟨d.fst.val, hdT⟩ ⟨d.snd.val, hu⟩ :=
          ⟨fun heq => d.adj.1 (Subtype.ext (congrArg (fun z : T => z.val) heq)), d.adj.2⟩
        exact hnZ ⟨hu, hr.trans ha.reachable⟩
      have hcol : D d.fst.val d.snd.val = e := d.adj.2
      rw [hv', hsym d.fst.val v] at hcol
      exact ⟨⟨d.fst.val, hdT⟩, hr, hcol⟩
    have cross {x y : T} (hx : D v x.val ≠ e) (hxy : ¬ G.Reachable x y) :
        D x.val y.val = D v x.val := by
      obtain ⟨z, hyz, hz⟩ := touches y
      have hxz : ¬ G.Reachable x z := fun h => hxy (h.trans hyz.symm)
      have hne := color_of_unreachable_ne hxz
      have hcol := hn hv (lift x).property (lift z).property
      change D v x.val = D x.val z.val ∨ D x.val z.val = D z.val v ∨ D z.val v = D v x.val at hcol
      rw [hsym z.val v, hz] at hcol
      exact (color_constant_on_component htn hxy hyz).trans
        (hcol.resolve_right (not_or_intro hne (Ne.symm hx))).symm
    have eqColors {x y : T} (hx : D v x.val ≠ e) (hy : D v y.val ≠ e) :
        D v x.val = D v y.val := by
      by_cases hr : G.Reachable x y
      · have hOut : ∃ z : T, ¬ G.Reachable x z := by
          by_cases h : G.Reachable x x₀
          · exact ⟨y₀, fun hy => hxy₀ (h.symm.trans hy)⟩
          · exact ⟨x₀, h⟩
        obtain ⟨z, hz⟩ := hOut
        have hyz : ¬ G.Reachable y z := fun h => hz (hr.trans h)
        have hzx : ¬ G.Reachable z x := fun h => hz h.symm
        calc
          D v x.val = D x.val z.val := (cross hx hz).symm
          _ = D z.val x.val := hsym _ _
          _ = D z.val y.val := color_constant_on_component htn hzx hr
          _ = D y.val z.val := hsym _ _
          _ = D v y.val := cross hy hyz
      · have h' : ¬ G.Reachable y x := fun h => hr h.symm
        exact (cross hx hr).symm.trans ((hsym _ _).trans (cross hy h'))
    have same {d f : β} (hd : Used D S d) (hf : Used D S f) (hd' : d ≠ e) (hf' : f ≠ e) :
        d = f := by
      obtain ⟨x, hx⟩ := incident hd
      obtain ⟨y, hy⟩ := incident hf
      have hx' : D v x.val ≠ e := fun h => hd' (hx.symm.trans h)
      have hy' : D v y.val ≠ e := fun h => hf' (hy.symm.trans h)
      exact hx.symm.trans ((eqColors hx' hy').trans hy)
    by_cases hae : a = e
    · exact hbc (same hB hC (fun h => hab (hae.trans h.symm)) (fun h => hac (hae.trans h.symm)))
    by_cases hbe : b = e
    · exact hac (same hA hC hae (fun h => hbc (hbe.trans h.symm)))
    · exact hab (same hA hB hae hbe)


private lemma split_equal_distances [DecidableEq α] (D : α → α → β)
    (hsym : ∀ x y, D x y = D y x) (S : Finset α) (hn : NoRainbow D S)
    {a b c : β} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : Used D S a) (hb : Used D S b) (hc : Used D S c) :
    ∃ X ⊆ S, 2 ≤ X.card ∧ (S \ X).Nonempty ∧
      ∀ y ∈ S \ X, ∀ x ∈ X, ∀ x' ∈ X, D y x = D y x' := by
  classical
  obtain ⟨d, hd, hdisc⟩ := color_disconnected D hsym S hn a b c hab hac hbc ha hb hc
  obtain ⟨u, hu, v, hv, hne, huv⟩ := hd
  let G := colorGraph D hsym S d
  let u₀ : S := ⟨u, hu⟩
  let v₀ : S := ⟨v, hv⟩
  let X := S.filter fun x => ∃ h : x ∈ S, G.Reachable u₀ ⟨x, h⟩
  have hX : X ⊆ S := Finset.filter_subset _ _
  have memX (x : S) : x.val ∈ X ↔ G.Reachable u₀ x := by
    simp [X, x.property]
  have huv' : G.Adj u₀ v₀ := ⟨fun h => hne (congrArg Subtype.val h), huv⟩
  have huX := (memX u₀).2 SimpleGraph.Reachable.rfl
  have hvX := (memX v₀).2 huv'.reachable
  have hs : (S \ X).Nonempty := by
    by_contra hn'
    have hAll (x : S) : G.Reachable u₀ x := by
      by_contra he
      exact hn' ⟨x.val, Finset.mem_sdiff.2 ⟨x.property, fun h => he ((memX x).1 h)⟩⟩
    exact hdisc (fun x y => (hAll x).symm.trans (hAll y))
  refine ⟨X, hX, ?_, hs, ?_⟩
  · have hh := Finset.one_lt_card.2 ⟨u, huX, v, hvX, hne⟩
    omega
  · intro y hy x hx x' hx'
    obtain ⟨hyS, hyX⟩ := Finset.mem_sdiff.1 hy
    let y₀ : S := ⟨y, hyS⟩
    let x₀ : S := ⟨x, hX hx⟩
    let x₁ : S := ⟨x', hX hx'⟩
    have hyu : ¬ G.Reachable y₀ u₀ := fun h => hyX ((memX y₀).2 h.symm)
    have hux := (memX x₀).1 hx
    have hux' := (memX x₁).1 hx'
    exact (color_constant_on_component hn hyu hux).symm.trans
      (color_constant_on_component hn hyu hux')

end Coloring

private def TwoDistance {E : Type*} [MetricSpace E] (S : Finset E) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y = a ∨ dist x y = b

private def Equidistant {E : Type*} [MetricSpace E] (X Y : Finset E) : Prop :=
  ∀ y ∈ Y, ∀ x ∈ X, ∀ x' ∈ X, dist y x = dist y x'

private lemma noRainbow_mono {D : α → α → β} {S T : Finset α}
    (h : NoRainbow D S) (hT : T ⊆ S) : NoRainbow D T :=
  fun _ _ _ hx hy hz => h (hT hx) (hT hy) (hT hz)

private lemma two_dist_or_split {E : Type*} [MetricSpace E] [DecidableEq E] (S : Finset E)
    (hn : NoRainbow dist S) :
    TwoDistance S ∨ ∃ X ⊆ S, 2 ≤ X.card ∧ (S \ X).Nonempty ∧ Equidistant X (S \ X) := by
  classical
  by_cases h : ∃ a b c : ℝ, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Used dist S a ∧
      Used dist S b ∧ Used dist S c
  · obtain ⟨a, b, c, hab, hac, hbc, ha, hb, hc⟩ := h
    exact Or.inr (split_equal_distances dist dist_comm S hn hab hac hbc ha hb hc)
  left
  have positive {a : ℝ} (ha : Used dist S a) : 0 < a := by
    obtain ⟨x, _, y, _, hxy, rfl⟩ := ha
    exact dist_pos.2 hxy
  by_cases hA : ∃ a : ℝ, Used dist S a
  · obtain ⟨a, ha⟩ := hA
    by_cases hB : ∃ b : ℝ, a ≠ b ∧ Used dist S b
    · obtain ⟨b, hab, hb⟩ := hB
      refine ⟨a, b, positive ha, positive hb, ?_⟩
      intro x hx y hy hxy
      by_contra! hdist
      exact h ⟨a, b, dist x y, hab, Ne.symm hdist.1, Ne.symm hdist.2,
        ha, hb, x, hx, y, hy, hxy, rfl⟩
    · refine ⟨a, a, positive ha, positive ha, ?_⟩
      intro x hx y hy hxy
      exact Or.inl (by
        by_contra he
        exact hB ⟨dist x y, Ne.symm he, x, hx, y, hy, hxy, rfl⟩)
  · refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_⟩
    intro x hx y hy hxy
    exact (hA ⟨dist x y, x, hx, y, hy, hxy, rfl⟩).elim

private lemma two_dist_or_minimal_split {E : Type*} [MetricSpace E] [DecidableEq E] (S : Finset E)
    (hn : NoRainbow dist S) :
    TwoDistance S ∨ ∃ X ⊆ S, 2 ≤ X.card ∧ (S \ X).Nonempty ∧ Equidistant X (S \ X) ∧
      TwoDistance X := by
  classical
  let Good (X : Finset E) := X ⊆ S ∧ 2 ≤ X.card ∧ (S \ X).Nonempty ∧ Equidistant X (S \ X)
  rcases two_dist_or_split S hn with h | h
  · exact Or.inl h
  have H : ∃ n, ∃ X : Finset E, X.card = n ∧ Good X := by
    obtain ⟨X, hX⟩ := h
    exact ⟨X.card, X, rfl, hX⟩
  obtain ⟨X, hcard, hXS, hXcard, hY, hcross⟩ := Nat.find_spec H
  refine Or.inr ⟨X, hXS, hXcard, hY, hcross, ?_⟩
  rcases two_dist_or_split X (noRainbow_mono hn hXS) with hX | ⟨Z, hZX, hZcard, hXZ, hzCross⟩
  · exact hX
  have hZS : Z ⊆ S := hZX.trans hXS
  have hSmall : Z.card < X.card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.2 ⟨hZX, ?_⟩
    rintro rfl
    simp at hXZ
  have hZY : (S \ Z).Nonempty := by
    obtain ⟨x, hx⟩ := hY
    obtain ⟨hxS, hxX⟩ := Finset.mem_sdiff.1 hx
    exact ⟨x, Finset.mem_sdiff.2 ⟨hxS, fun hxZ => hxX (hZX hxZ)⟩⟩
  have hCross : Equidistant Z (S \ Z) := by
    intro y hy x hx x' hx'
    obtain ⟨hyS, hyZ⟩ := Finset.mem_sdiff.1 hy
    by_cases hyX : y ∈ X
    · exact hzCross y (Finset.mem_sdiff.2 ⟨hyX, hyZ⟩) x hx x' hx'
    · exact hcross y (Finset.mem_sdiff.2 ⟨hyS, hyX⟩) x (hZX hx) x' (hZX hx')
  have hle : Nat.find H ≤ Z.card := Nat.find_min' H ⟨Z, rfl, hZS, hZcard, hZY, hCross⟩
  omega


section Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def direction (S : Finset E) (o : E) : Submodule ℝ E :=
  Submodule.span ℝ ((fun x : E => x - o) '' (S : Set E))

private lemma sub_mem_direction {S : Finset E} {o x : E} (hx : x ∈ S) :
    x - o ∈ direction S o :=
  Submodule.subset_span ⟨x, hx, rfl⟩

private lemma inner_of_equidistant {x o y : E} (h : dist y x = dist y o) :
    ‖x - o‖ ^ 2 = 2 * inner ℝ (x - o) (y - o) := by
  have hd : ‖(x - o) - (y - o)‖ = ‖y - o‖ := by
    rw [show (x - o) - (y - o) = x - y by abel, ← dist_eq_norm, dist_comm, h, dist_eq_norm]
  have hs := congrArg (fun t : ℝ => t ^ 2) hd
  rw [norm_sub_sq_real] at hs
  linarith only [hs]

private lemma equidistant_orthogonal {X Y : Finset E} {o q : E} (ho : o ∈ X) (hq : q ∈ Y)
    (h : Equidistant X Y) : direction Y q ≤ (direction X o)ᗮ := by
  apply Submodule.span_le.2
  rintro _ ⟨y, hy, rfl⟩
  apply ((direction X o).mem_orthogonal (y - q)).2
  intro u hu
  change u ∈ Submodule.span ℝ ((fun x : E => x - o) '' (X : Set E)) at hu
  refine Submodule.span_induction (p := fun v _ => inner ℝ v (y - q) = 0) ?_ ?_ ?_ ?_ hu
  · rintro _ ⟨x, hx, rfl⟩
    have hyx := inner_of_equidistant (h y hy x hx o ho)
    have hqx := inner_of_equidistant (h q hq x hx o ho)
    rw [show y - q = (y - o) - (q - o) by abel, inner_sub_right]
    linarith only [hyx, hqx]
  · simp
  · intro u v _ _ hu hv
    rw [inner_add_left, hu, hv, add_zero]
  · intro t u _ hu
    simp [inner_smul_left, hu]

variable [FiniteDimensional ℝ E]

private lemma direction_pos {X : Finset E} {o : E} (h : 2 ≤ X.card) :
    0 < finrank ℝ (direction X o) := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < X.card)
  obtain ⟨x, hx, hxo⟩ : ∃ x ∈ X, x ≠ o := by
    by_cases he : a = o
    · exact ⟨b, hb, fun hbo => hab (he.trans hbo.symm)⟩
    · exact ⟨a, ha, he⟩
  apply Module.finrank_pos_iff_exists_ne_zero.2
  refine ⟨⟨x - o, sub_mem_direction hx⟩, fun he => hxo ?_⟩
  exact sub_eq_zero.1 (congrArg (fun v : direction X o => (v : E)) he)

private def anchoredVector (S : Finset E) (o : E) (x : S) : direction S o :=
  ⟨x.val - o, sub_mem_direction x.property⟩

private noncomputable def alignedPoint (S : Finset E) (o : E) :
    S ↪ EuclideanSpace ℝ (Fin (finrank ℝ (direction S o))) where
  toFun x := (stdOrthonormalBasis ℝ (direction S o)).repr (anchoredVector S o x)
  inj' := by
    intro x y h
    have he := (stdOrthonormalBasis ℝ (direction S o)).repr.injective h
    apply Subtype.ext
    exact sub_left_inj.mp (congrArg (fun v : direction S o => (v : E)) he)

private lemma alignedPoint_dist (S : Finset E) (o : E) (x y : S) :
    dist (alignedPoint S o x) (alignedPoint S o y) = dist x.val y.val := by
  change dist ((stdOrthonormalBasis ℝ (direction S o)).repr (anchoredVector S o x))
    ((stdOrthonormalBasis ℝ (direction S o)).repr (anchoredVector S o y)) = _
  rw [LinearIsometryEquiv.dist_map]
  change dist (x.val - o) (y.val - o) = _
  rw [dist_eq_norm, dist_eq_norm, show (x.val - o) - (y.val - o) = x.val - y.val by abel]

private noncomputable def aligned (S : Finset E) (o : E) :
    Finset (EuclideanSpace ℝ (Fin (finrank ℝ (direction S o)))) :=
  S.attach.map (alignedPoint S o)

@[simp] private lemma card_aligned (S : Finset E) (o : E) : (aligned S o).card = S.card := by
  simp [aligned]

private lemma aligned_noRainbow {S : Finset E} (o : E) (h : NoRainbow dist S) :
    NoRainbow dist (aligned S o) := by
  intro x y z hx hy hz
  obtain ⟨x, _, rfl⟩ := Finset.mem_map.1 hx
  obtain ⟨y, _, rfl⟩ := Finset.mem_map.1 hy
  obtain ⟨z, _, rfl⟩ := Finset.mem_map.1 hz
  simpa only [alignedPoint_dist] using h x.property y.property z.property

private lemma aligned_twoDistance {S : Finset E} (o : E) (h : TwoDistance S) :
    TwoDistance (aligned S o) := by
  obtain ⟨a, b, ha, hb, hdist⟩ := h
  refine ⟨a, b, ha, hb, ?_⟩
  intro x hx y hy hxy
  obtain ⟨x, _, rfl⟩ := Finset.mem_map.1 hx
  obtain ⟨y, _, rfl⟩ := Finset.mem_map.1 hy
  rw [alignedPoint_dist]
  exact hdist x.val x.property y.val y.property (fun he => hxy (congrArg _ (Subtype.ext he)))

private lemma aligned_spherical (S : Finset E) (o y : E)
    (h : ∀ x ∈ S, dist y x = dist y o) :
    ∃ c r, ∀ x ∈ aligned S o, dist x c = r := by
  let P := direction S o
  let c := P.orthogonalProjectionOnto (y - o)
  refine ⟨(stdOrthonormalBasis ℝ P).repr c, ‖(c : E)‖, ?_⟩
  intro x hx
  obtain ⟨x, _, rfl⟩ := Finset.mem_map.1 hx
  change dist ((stdOrthonormalBasis ℝ P).repr (anchoredVector S o x))
    ((stdOrthonormalBasis ℝ P).repr c) = _
  rw [LinearIsometryEquiv.dist_map]
  change dist (x.val - o) (c : E) = ‖(c : E)‖
  rw [dist_eq_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  have hz := P.inner_right_of_mem_orthogonal (sub_mem_direction x.property)
    (P.sub_starProjection_mem_orthogonal (y - o))
  rw [inner_sub_right] at hz
  change inner ℝ (x.val - o) (y - o) - inner ℝ (x.val - o) (c : E) = 0 at hz
  rw [norm_sub_sq_real]
  linarith only [hz, inner_of_equidistant (h x.val x.property)]

end Geometry

private lemma bound_add (a b : ℕ) :
    (a + 2).choose 2 + (b + 2).choose 2 ≤ (a + b + 2).choose 2 + 1 := by
  induction b with
  | zero => simp
  | succ b ih =>
    have h₁ : (b + 2 + 1).choose 2 = b + 2 + (b + 2).choose 2 := by
      rw [Nat.choose_succ_succ' (b + 2) 1, Nat.choose_one_right]
    have h₂ : (a + b + 2 + 1).choose 2 = a + b + 2 + (a + b + 2).choose 2 := by
      rw [Nat.choose_succ_succ' (a + b + 2) 1, Nat.choose_one_right]
    have h₃ : a + (b + 1) + 2 = a + b + 2 + 1 := by omega
    have h₄ : b + 1 + 2 = b + 2 + 1 := by omega
    rw [h₃, h₄]
    omega


private abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

private lemma noRainbow_of_isosceles {E : Type} [MetricSpace E] (S : Finset E)
    (hIso : (S : Set E).IsIsosceles) : NoRainbow dist S := by
  intro x y z hx hy hz
  by_cases hxy : x = y
  · subst y
    exact Or.inr (Or.inl (dist_comm x z))
  by_cases hyz : y = z
  · subst z
    exact Or.inr (Or.inr (dist_comm y x))
  by_cases hxz : x = z
  · subst z
    exact Or.inl (dist_comm x y)
  exact hIso.2 hx hy hz hxy hyz hxz

private theorem general_card
    (d : ℕ) (S : Finset (Space d)) (hn : NoRainbow dist S) :
    S.card ≤ (d + 2).choose 2 := by
  classical
  suffices H : ∀ (k d : ℕ) (S : Finset (Space d)), S.card = k →
      NoRainbow dist S → S.card ≤ (d + 2).choose 2 by
    exact H S.card d S rfl hn
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro d S hcard hn
    rcases two_dist_or_minimal_split S hn with hS | ⟨X, hXS, hX, hY, hCross, hTwo⟩
    · obtain ⟨a, b, ha, hb, h⟩ := hS
      exact IsoscelesTwoDistances.general ha hb h
    let Y := S \ X
    have hYS : Y ⊆ S := Finset.sdiff_subset
    obtain ⟨o, ho⟩ : X.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨q, hq⟩ := hY
    let P := direction X o
    let Q := direction Y q
    let a := finrank ℝ P
    let b := finrank ℝ Q
    have hSum : a + b ≤ d := by
      calc
        a + b ≤ a + finrank ℝ Pᗮ :=
          Nat.add_le_add_left (Submodule.finrank_mono (equidistant_orthogonal ho hq hCross)) a
        _ = d := P.finrank_add_finrank_orthogonal.trans finrank_euclideanSpace_fin
    have hCover := Finset.card_sdiff_add_card_eq_card hXS
    change Y.card + X.card = S.card at hCover
    have hA : X.card + 1 ≤ (a + 2).choose 2 := by
      obtain ⟨c, r, hSphere⟩ := aligned_spherical X o q (fun x hx => hCross q hq x hx o ho)
      have ha : 1 ≤ a := direction_pos hX
      rw [← card_aligned X o]
      obtain ⟨u, v, hu, hv, h⟩ := aligned_twoDistance o hTwo
      exact IsoscelesTwoDistances.sphericalGeneral ha hu hv h c r hSphere
    have hB : Y.card ≤ (b + 2).choose 2 := by
      have hLt : Y.card < k := by omega
      rw [← card_aligned Y q]
      exact ih Y.card hLt b (aligned Y q) (card_aligned Y q) (aligned_noRainbow q (noRainbow_mono hn hYS))
    have hChoose := bound_add a b
    have hMono : (a + b + 2).choose 2 ≤ (d + 2).choose 2 :=
      Nat.choose_le_choose 2 (Nat.add_le_add_right hSum 2)
    omega

end GeneralIsosceles

namespace ThreeDistanceCertificate

private abbrev Coeffs := List ℚ

private def polyEval (t : ℝ) : Coeffs → ℝ
  | [] => 0
  | c :: p => (c : ℝ) + t * polyEval t p

private def polyAdd : Coeffs → Coeffs → Coeffs
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: polyAdd p q

private def polyScale (c : ℚ) (p : Coeffs) : Coeffs := p.map (c * ·)

private def polyShift (n : ℕ) (p : Coeffs) : Coeffs := List.replicate n 0 ++ p

private def polyMul : Coeffs → Coeffs → Coeffs
  | [], _ => []
  | a :: p, q => polyAdd (polyScale a q) (0 :: polyMul p q)

private def polyTrim : Coeffs → Coeffs
  | [] => []
  | c :: p =>
    match polyTrim p with
    | [] => if c = 0 then [] else [c]
    | d :: q => c :: d :: q

private def stripZero : Coeffs → Coeffs
  | [] => []
  | c :: p => if c = 0 then stripZero p else c :: p

private def quotientOne : Coeffs → Coeffs × ℚ
  | [] => ([], 0)
  | c :: p => let (q, r) := quotientOne p; (r :: q, c + r)

private def stripOne : ℕ → Coeffs → Coeffs
  | 0, p => p
  | n + 1, p =>
    if (quotientOne p).2 = 0 then stripOne n (polyTrim (quotientOne p).1) else p

private def monicNormalize (p : Coeffs) : Coeffs :=
  let q := stripOne 5 (stripZero (polyTrim p))
  polyScale (q.getLastD 1)⁻¹ q

private lemma eval_add (t : ℝ) (p q : Coeffs) :
    polyEval t (polyAdd p q) = polyEval t p + polyEval t q := by
  induction p generalizing q with
  | nil => simp [polyAdd, polyEval]
  | cons a p ih =>
    cases q with
    | nil => simp [polyAdd, polyEval]
    | cons b q => simp [polyAdd, polyEval, ih, Rat.cast_add]; ring

private lemma eval_scale (t : ℝ) (c : ℚ) (p : Coeffs) :
    polyEval t (polyScale c p) = (c : ℝ) * polyEval t p := by
  induction p with
  | nil => simp [polyEval, polyScale]
  | cons a p ih =>
    change (↑(c * a) : ℝ) + t * polyEval t (polyScale c p) = _
    rw [Rat.cast_mul, ih, polyEval]
    ring

private lemma eval_shift (t : ℝ) (n : ℕ) (p : Coeffs) :
    polyEval t (polyShift n p) = t ^ n * polyEval t p := by
  induction n with
  | zero => simp [polyShift]
  | succ n ih =>
    change (↑(0 : ℚ) : ℝ) + t * polyEval t (polyShift n p) = _
    rw [Rat.cast_zero, zero_add, ih, pow_succ']
    ring

private lemma eval_mul (t : ℝ) (p q : Coeffs) :
    polyEval t (polyMul p q) = polyEval t p * polyEval t q := by
  induction p with
  | nil => simp [polyEval, polyMul]
  | cons a p ih =>
    rw [polyMul, eval_add, eval_scale, polyEval, ih, polyEval]
    simp only [Rat.cast_zero, zero_add]
    ring

private lemma eval_trim (t : ℝ) (p : Coeffs) :
    polyEval t (polyTrim p) = polyEval t p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    cases he : polyTrim p with
    | nil =>
      have hp : polyEval t p = 0 := by simpa [he, polyEval] using ih.symm
      by_cases ha : a = 0 <;> simp [polyTrim, he, ha, polyEval, hp]
    | cons d q =>
      have hp : polyEval t (d :: q) = polyEval t p := by simpa only [he] using ih
      simp only [polyTrim, he]
      change (a : ℝ) + t * polyEval t (d :: q) = (a : ℝ) + t * polyEval t p
      rw [hp]

private lemma eval_strip_zero {t : ℝ} (ht : t ≠ 0) (p : Coeffs)
    (h : polyEval t p = 0) : polyEval t (stripZero p) = 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [stripZero]
    split
    · rename_i he
      simp only [polyEval, he, Rat.cast_zero, zero_add] at h
      exact ih ((mul_eq_zero.1 h).resolve_left ht)
    · exact h

private lemma eval_quotientOne (t : ℝ) (p : Coeffs) :
    polyEval t p = (t - 1) * polyEval t (quotientOne p).1 + ((quotientOne p).2 : ℝ) := by
  induction p with
  | nil => simp [polyEval, quotientOne]
  | cons a p ih =>
    rw [polyEval, ih]
    change (↑a : ℝ) + t * ((t - 1) * polyEval t (quotientOne p).1 + ((quotientOne p).2 : ℝ)) =
      (t - 1) * ((↑(quotientOne p).2 : ℝ) + t * polyEval t (quotientOne p).1) +
        (↑(a + (quotientOne p).2) : ℝ)
    rw [Rat.cast_add]
    ring

private lemma eval_strip_one {t : ℝ} (ht : t ≠ 1) (n : ℕ) (p : Coeffs)
    (h : polyEval t p = 0) : polyEval t (stripOne n p) = 0 := by
  induction n generalizing p with
  | zero => exact h
  | succ n ih =>
    rw [stripOne]
    split
    · rename_i he
      apply ih
      rw [eval_trim]
      rw [eval_quotientOne, he, Rat.cast_zero, add_zero] at h
      exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 ht)
    · exact h

private lemma eval_normalize {t : ℝ} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (p : Coeffs)
    (h : polyEval t p = 0) : polyEval t (monicNormalize p) = 0 := by
  unfold monicNormalize
  rw [eval_scale, eval_strip_one ht1 5 _ (eval_strip_zero ht0 _ ((eval_trim t p).trans h)),
    mul_zero]

private def polyRemainder (p q : Coeffs) : Coeffs :=
  polyTrim (polyAdd (polyScale (q.getLastD 0) p)
    (polyShift (p.length - q.length) (polyScale (-p.getLastD 0) q)))

private def constantCheck : Coeffs → Bool
  | [a] => a != 0
  | _ => false

private lemma constantCheck_sound {t : ℝ} {p : Coeffs} (h : constantCheck p = true)
    (he : polyEval t p = 0) : False := by
  rcases p with _ | ⟨a, _ | ⟨b, p⟩⟩
  · simp [constantCheck] at h
  · have ha : a = 0 := by exact_mod_cast (show (a : ℝ) = 0 by simpa [polyEval] using he)
    simp [constantCheck, ha] at h
  · simp [constantCheck] at h

private def coprimeCheck : ℕ → Coeffs → Coeffs → Bool
  | 0, _, _ => false
  | n + 1, p, q =>
    if constantCheck p || constantCheck q then true
    else if p.length < q.length then coprimeCheck n q p
    else if q = [] then false
    else coprimeCheck n (polyRemainder p q) q

private lemma eval_remainder {t : ℝ} {p q : Coeffs}
    (hp : polyEval t p = 0) (hq : polyEval t q = 0) :
    polyEval t (polyRemainder p q) = 0 := by
  rw [polyRemainder, eval_trim, eval_add, eval_scale, eval_shift, eval_scale, hp, hq]
  ring

private lemma coprimeCheck_sound {t : ℝ} (n : ℕ) (p q : Coeffs) (h : coprimeCheck n p q = true)
    (hp : polyEval t p = 0) (hq : polyEval t q = 0) : False := by
  induction n generalizing p q with
  | zero => cases h
  | succ n ih =>
    by_cases hp' : constantCheck p = true
    · exact constantCheck_sound hp' hp
    by_cases hq' : constantCheck q = true
    · exact constantCheck_sound hq' hq
    have hpN : constantCheck p = false := Bool.eq_false_iff.2 hp'
    have hqN : constantCheck q = false := Bool.eq_false_iff.2 hq'
    simp only [coprimeCheck, hpN, hqN, Bool.false_or, Bool.false_eq_true, if_false] at h
    split at h
    · exact ih _ _ h hq hp
    · split at h
      · cases h
      · exact ih _ _ h (eval_remainder hp hq) hq


private def polySub (p q : Coeffs) : Coeffs := polyAdd p (polyScale (-1) q)

private lemma eval_sub (t : ℝ) (p q : Coeffs) :
    polyEval t (polySub p q) = polyEval t p - polyEval t q := by
  rw [polySub, eval_add, eval_scale]
  norm_num
  ring

def patternBit (p : Fin 8) (k : Fin 3) : Bool := p.val.testBit k.val

def value (t : ℝ) (b : Bool) : ℝ := if b then t else 1

private def valuePoly (b : Bool) : Coeffs := if b then [0, 1] else [1]

private lemma eval_value (t : ℝ) (b : Bool) : polyEval t (valuePoly b) = value t b := by
  cases b <;> simp [polyEval, valuePoly, value]

def residual (x₀ x₁ y₀ y₁ v : ℝ) : ℝ :=
  3 * v - (2 * x₀ * y₀ - x₀ * y₁ - x₁ * y₀ + 2 * x₁ * y₁)

private def residualPoly (x₀ x₁ y₀ y₁ v : Coeffs) : Coeffs :=
  polySub (polyScale 3 v)
    (polyAdd (polySub (polySub (polyScale 2 (polyMul x₀ y₀)) (polyMul x₀ y₁))
      (polyMul x₁ y₀)) (polyScale 2 (polyMul x₁ y₁)))

private lemma eval_residual (t : ℝ) (x₀ x₁ y₀ y₁ v : Coeffs) :
    polyEval t (residualPoly x₀ x₁ y₀ y₁ v) =
      residual (polyEval t x₀) (polyEval t x₁) (polyEval t y₀) (polyEval t y₁) (polyEval t v) := by
  simp only [residualPoly, eval_sub, eval_scale, eval_add, eval_mul, residual]
  norm_num
  ring

private def rawPolynomial (i j : Fin 8) (b : Bool) : Coeffs :=
  let x := fun k => valuePoly (patternBit i k)
  let y := fun k => valuePoly (patternBit j k)
  let u₀ := polyAdd [1] (polySub (x 0) (x 1))
  let u₁ := polyAdd [1] (polySub (x 0) (x 2))
  let v₀ := polyAdd [1] (polySub (y 0) (y 1))
  let v₁ := polyAdd [1] (polySub (y 0) (y 2))
  let rxx := residualPoly u₀ u₁ u₀ u₁ (polyScale 2 (x 0))
  let ryy := residualPoly v₀ v₁ v₀ v₁ (polyScale 2 (y 0))
  let rxy := residualPoly u₀ u₁ v₀ v₁ (polySub (polyAdd (x 0) (y 0)) (valuePoly b))
  polySub (polyMul rxy rxy) (polyMul rxx ryy)

def schurExpression (x y : Fin 3 → ℝ) (d : ℝ) : ℝ :=
  let u₀ := 1 + (x 0 - x 1)
  let u₁ := 1 + (x 0 - x 2)
  let v₀ := 1 + (y 0 - y 1)
  let v₁ := 1 + (y 0 - y 2)
  let rxx := residual u₀ u₁ u₀ u₁ (2 * x 0)
  let ryy := residual v₀ v₁ v₀ v₁ (2 * y 0)
  let rxy := residual u₀ u₁ v₀ v₁ (x 0 + y 0 - d)
  rxy * rxy - rxx * ryy

private lemma eval_raw (t : ℝ) (i j : Fin 8) (b : Bool) :
    polyEval t (rawPolynomial i j b) =
      schurExpression (fun k => value t (patternBit i k))
        (fun k => value t (patternBit j k)) (value t b) := by
  simp only [rawPolynomial, schurExpression, eval_sub, eval_mul, eval_residual, eval_add, eval_scale,
    eval_value, polyEval, Rat.cast_ofNat, Rat.cast_one, mul_zero, add_zero]

private def knownPolynomial : Fin 19 → Coeffs :=
  ![[1], [-8/3, 1], [-9/4, 1], [-7/12, 1], [-4/9, 1], [-3/8, 1],
    [1/2, -17/8, 1], [3/4, -3, 1], [1, -13/4, 1], [4/3, -4, 1],
    [7/4, -4, 1], [12, -8, 1], [-8, 24, -12, 1], [-4, 16, -8, 1],
    [-1/4, 2, -4, 1], [3/4, -1, -2, 1], [1, -1, -9/4, 1],
    [-3, 6, 7, -6, 1], [1, -10, 23, -10, 1]]

private def edgePolynomialIndex (p q : Fin 8) (b : Bool) : Fin 19 :=
  let rows : Fin 8 → Fin 8 → Fin 19 × Fin 19 :=
    ![![(0,1), (1,7), (1,7), (7,9), (1,7), (7,9), (7,9), (9,5)],
      ![(1,7), (7,2), (11,17), (17,13), (11,17), (17,13), (6,15), (15,8)],
      ![(1,7), (11,17), (7,2), (17,13), (11,17), (6,15), (17,13), (15,8)],
      ![(7,9), (17,13), (17,13), (10,8), (6,15), (12,18), (12,18), (16,14)],
      ![(1,7), (11,17), (11,17), (6,15), (7,2), (17,13), (17,13), (15,8)],
      ![(7,9), (17,13), (6,15), (12,18), (17,13), (10,8), (12,18), (16,14)],
      ![(7,9), (6,15), (17,13), (12,18), (17,13), (12,18), (10,8), (16,14)],
      ![(9,5), (15,8), (15,8), (16,14), (15,8), (16,14), (16,14), (3,4)]]
  if b then (rows p q).2 else (rows p q).1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem polynomial_index_verified :
    ∀ (p q : Fin 8) (b : Bool),
      knownPolynomial (edgePolynomialIndex p q b) = monicNormalize (rawPolynomial p q b) := by
  decide +kernel

private def group (i : Fin 19) : Fin 19 := if i = 12 then 11 else if i = 18 then 17 else i

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem groups_verified : ∀ i j : Fin 19, group i ≠ group j →
    coprimeCheck 14 (knownPolynomial i) (knownPolynomial j) = true := by
  decide +kernel

private abbrev allowed (r : Fin 19) (i j : Fin 8) : Prop :=
  group (edgePolynomialIndex i j false) = r ∨ group (edgePolynomialIndex i j true) = r

abbrev NoTripleRepeat (i j k l : Fin 8) : Prop :=
  ¬(i = j ∧ i = k) ∧ ¬(i = j ∧ i = l) ∧ ¬(i = k ∧ i = l) ∧ ¬(j = k ∧ j = l)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem no_four_verified : ∀ (r : Fin 19) (i j k l : Fin 8), r ≠ 0 →
    NoTripleRepeat i j k l → allowed r i j → allowed r i k → allowed r i l →
    allowed r j k → allowed r j l → allowed r k l → False := by
  decide +kernel

def edgeClass (t : ℝ) (i j : Fin 8) : Prop :=
  ∃ b : Bool, schurExpression (fun k => value t (patternBit i k))
    (fun k => value t (patternBit j k)) (value t b) = 0

theorem no_four {t : ℝ} (ht0 : t ≠ 0) (ht1 : t ≠ 1) {i j k l : Fin 8}
    (hRep : NoTripleRepeat i j k l)
    (hij : edgeClass t i j) (hik : edgeClass t i k) (hil : edgeClass t i l)
    (hjk : edgeClass t j k) (hjl : edgeClass t j l) (hkl : edgeClass t k l) : False := by
  have root {i j : Fin 8} {e : Bool}
      (he : schurExpression (fun k => value t (patternBit i k))
        (fun k => value t (patternBit j k)) (value t e) = 0) :
      polyEval t (knownPolynomial (edgePolynomialIndex i j e)) = 0 := by
    rw [polynomial_index_verified]
    apply eval_normalize ht0 ht1
    rwa [eval_raw]
  obtain ⟨e, he⟩ := hij
  let p := edgePolynomialIndex i j e
  have hp : polyEval t (knownPolynomial p) = 0 := root he
  have hpN : group p ≠ 0 := by
    intro h
    have heq : p = 0 := by
      unfold group at h
      split at h <;> simp_all
      split at h <;> simp_all
    rw [heq] at hp
    norm_num [knownPolynomial, polyEval] at hp
  have sameGroup {u v : Fin 8} (h : edgeClass t u v) : allowed (group p) u v := by
    obtain ⟨e, he⟩ := h
    have hr := root he
    have heq : group p = group (edgePolynomialIndex u v e) := by
      by_contra hne
      exact coprimeCheck_sound 14 _ _ (groups_verified _ _ hne) hp hr
    cases e
    · exact Or.inl heq.symm
    · exact Or.inr heq.symm
  exact no_four_verified _ _ _ _ _ hpN hRep (sameGroup ⟨e, he⟩)
    (sameGroup hik) (sameGroup hil) (sameGroup hjk) (sameGroup hjl) (sameGroup hkl)

end ThreeDistanceCertificate

namespace ThreeDistanceGeometry

open ThreeDistanceCertificate

private def gramForm (a b c d e f g : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![2, 1, a, c; 1, 2, b, d; a, b, e, g; c, d, g, f]

private lemma det_three_literal (a b c d e f g h i : ℝ) :
    Matrix.det !![a,b,c;d,e,f;g,h,i] =
      a*e*i - a*f*h - b*d*i + b*f*g + c*d*h - c*e*g := by
  rw [Matrix.det_fin_three]
  rfl

set_option maxHeartbeats 1500000 in
private lemma det_gramForm (a b c d e f g : ℝ) :
    3 * (gramForm a b c d e f g).det =
      residual a b a b e * residual c d c d f - residual a b c d g ^ 2 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  change 3 * (((-1 : ℝ) ^ (0 : ℕ)) * 2 * Matrix.det !![2,b,d;b,e,g;d,g,f] +
    (((-1 : ℝ) ^ (1 : ℕ)) * 1 * Matrix.det !![1,b,d;a,e,g;c,g,f] +
    (((-1 : ℝ) ^ (2 : ℕ)) * a * Matrix.det !![1,2,d;a,b,g;c,d,f] +
    ((-1 : ℝ) ^ (3 : ℕ)) * c * Matrix.det !![1,2,b;a,b,e;c,d,g]))) = _
  simp only [det_three_literal, ThreeDistanceCertificate.residual]
  ring

private lemma inner_of_dist (o x y : ℝ³) :
    2 * inner ℝ (x - o) (y - o) = dist x o ^ 2 + dist y o ^ 2 - dist x y ^ 2 := by
  have h := norm_sub_sq_real (x - o) (y - o)
  rw [show (x - o) - (y - o) = x - y by abel, ← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm] at h
  linarith only [h]

private noncomputable def normalizedDistance (A : ℝ) (x y : ℝ³) : ℝ := dist x y ^ 2 / A

private lemma normalized_inner (A : ℝ) (o x y : ℝ³) :
    2 / A * inner ℝ (x - o) (y - o) =
      normalizedDistance A x o + normalizedDistance A y o - normalizedDistance A x y := by
  rw [show 2 / A * inner ℝ (x - o) (y - o) = (2 * inner ℝ (x - o) (y - o)) / A by ring,
    inner_of_dist]
  unfold normalizedDistance
  ring

private def anchor (o a b : ℝ³) : Fin 3 → ℝ³ := ![o, a, b]

private lemma pair_schur {o a b : ℝ³} {A : ℝ} (hA : A ≠ 0)
    (ha : dist a o ^ 2 = A) (hb : dist b o ^ 2 = A) (hab : dist a b ^ 2 = A)
    (x y : ℝ³) :
    schurExpression (fun i => normalizedDistance A x (anchor o a b i))
      (fun i => normalizedDistance A y (anchor o a b i)) (normalizedDistance A x y) = 0 := by
  let v : Fin 4 → ℝ³ := ![a - o, b - o, x - o, y - o]
  have hdet : (Matrix.gram ℝ v).det = 0 := by
    by_contra! hn
    have hc := (Matrix.linearIndependent_of_det_gram_ne_zero hn).fintype_card_le_finrank
    rw [Fintype.card_fin, finrank_euclideanSpace_fin] at hc
    omega
  let δ := normalizedDistance A
  have hδa : δ a o = 1 := by simp [δ, normalizedDistance, ha, hA]
  have hδb : δ b o = 1 := by simp [δ, normalizedDistance, hb, hA]
  have hδab : δ a b = 1 := by simp [δ, normalizedDistance, hab, hA]
  have hSym (u w : ℝ³) : δ u w = δ w u := by
    unfold δ normalizedDistance
    rw [dist_comm]
  have hSelf (u : ℝ³) : δ u u = 0 := by simp [δ, normalizedDistance]
  have heq :
      (2 / A) • Matrix.gram ℝ v =
        gramForm (1 + (δ x o - δ x a)) (1 + (δ x o - δ x b))
          (1 + (δ y o - δ y a)) (1 + (δ y o - δ y b)) (2 * δ x o) (2 * δ y o)
          (δ x o + δ y o - δ x y) := by
    have hEntry (u w : ℝ³) :
        (2 / A) * inner ℝ (u - o) (w - o) = δ u o + δ w o - δ u w :=
      normalized_inner A o u w
    ext i j
    fin_cases i <;> fin_cases j
    · change (2 / A) * inner ℝ (a - o) (a - o) = 2
      rw [hEntry, hSelf a, hδa]
      ring
    · change (2 / A) * inner ℝ (a - o) (b - o) = 1
      rw [hEntry, hδab, hδa, hδb]
      ring
    · change (2 / A) * inner ℝ (a - o) (x - o) = 1 + (δ x o - δ x a)
      rw [hEntry, hSym a x, hδa]
      ring
    · change (2 / A) * inner ℝ (a - o) (y - o) = 1 + (δ y o - δ y a)
      rw [hEntry, hSym a y, hδa]
      ring
    · change (2 / A) * inner ℝ (b - o) (a - o) = 1
      rw [hEntry, hSym b a, hδab, hδa, hδb]
      ring
    · change (2 / A) * inner ℝ (b - o) (b - o) = 2
      rw [hEntry, hSelf b, hδb]
      ring
    · change (2 / A) * inner ℝ (b - o) (x - o) = 1 + (δ x o - δ x b)
      rw [hEntry, hSym b x, hδb]
      ring
    · change (2 / A) * inner ℝ (b - o) (y - o) = 1 + (δ y o - δ y b)
      rw [hEntry, hSym b y, hδb]
      ring
    · change (2 / A) * inner ℝ (x - o) (a - o) = 1 + (δ x o - δ x a)
      rw [hEntry, hδa]
      ring
    · change (2 / A) * inner ℝ (x - o) (b - o) = 1 + (δ x o - δ x b)
      rw [hEntry, hδb]
      ring
    · change (2 / A) * inner ℝ (x - o) (x - o) = 2 * δ x o
      rw [hEntry, hSelf x]
      ring
    · change (2 / A) * inner ℝ (x - o) (y - o) = δ x o + δ y o - δ x y
      rw [hEntry]
    · change (2 / A) * inner ℝ (y - o) (a - o) = 1 + (δ y o - δ y a)
      rw [hEntry, hδa]
      ring
    · change (2 / A) * inner ℝ (y - o) (b - o) = 1 + (δ y o - δ y b)
      rw [hEntry, hδb]
      ring
    · change (2 / A) * inner ℝ (y - o) (x - o) = δ x o + δ y o - δ x y
      rw [hEntry, hSym y x]
      ring
    · change (2 / A) * inner ℝ (y - o) (y - o) = 2 * δ y o
      rw [hEntry, hSelf y]
      ring
  have hdet' : ((2 / A) • Matrix.gram ℝ v).det = 0 := by rw [Matrix.det_smul, hdet, mul_zero]
  rw [heq] at hdet'
  have hres := det_gramForm (1 + (δ x o - δ x a)) (1 + (δ x o - δ x b))
    (1 + (δ y o - δ y a)) (1 + (δ y o - δ y b)) (2 * δ x o) (2 * δ y o)
    (δ x o + δ y o - δ x y)
  rw [hdet', mul_zero] at hres
  have h0 : anchor o a b 0 = o := rfl
  have h1 : anchor o a b 1 = a := rfl
  have h2 : anchor o a b 2 = b := rfl
  simp only [schurExpression, h0, h1, h2, ← pow_two]
  change ThreeDistanceCertificate.residual (1 + (δ x o - δ x a)) (1 + (δ x o - δ x b))
      (1 + (δ y o - δ y a)) (1 + (δ y o - δ y b)) (δ x o + δ y o - δ x y) ^ 2 -
    ThreeDistanceCertificate.residual (1 + (δ x o - δ x a)) (1 + (δ x o - δ x b))
      (1 + (δ x o - δ x a)) (1 + (δ x o - δ x b)) (2 * δ x o) *
    ThreeDistanceCertificate.residual (1 + (δ y o - δ y a)) (1 + (δ y o - δ y b))
      (1 + (δ y o - δ y a)) (1 + (δ y o - δ y b)) (2 * δ y o) = 0
  linarith only [hres]

private lemma anchor_independent {o a b : ℝ³} {A : ℝ} (hA : 0 < A)
    (ha : dist a o ^ 2 = A) (hb : dist b o ^ 2 = A) (hab : dist a b ^ 2 = A) :
    LinearIndependent ℝ (![a - o, b - o] : Fin 2 → ℝ³) := by
  have h01 := inner_of_dist o a b
  have h10 := inner_of_dist o b a
  rw [dist_comm b a, ha, hb, hab] at h10
  rw [ha, hb, hab] at h01
  have hEq : Matrix.gram ℝ (![a - o, b - o] : Fin 2 → ℝ³) = !![A, A / 2; A / 2, A] := by
    ext i j
    fin_cases i <;> fin_cases j
    · change inner ℝ (a - o) (a - o) = A
      rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, ha]
    · change inner ℝ (a - o) (b - o) = A / 2
      linarith only [h01]
    · change inner ℝ (b - o) (a - o) = A / 2
      linarith only [h10]
    · change inner ℝ (b - o) (b - o) = A
      rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hb]
  apply Matrix.linearIndependent_of_det_gram_ne_zero
  rw [hEq, Matrix.det_fin_two_of]
  have hs : 0 < A ^ 2 := sq_pos_of_pos hA
  nlinarith only [hs]

end ThreeDistanceGeometry

namespace ThreeDistanceGeometry

open GeneralIsosceles ThreeDistanceCertificate

private lemma triangle_from_neighborhood (S C : Finset ℝ³) {o : ℝ³} (ho : o ∈ S)
    (hC : C ⊆ S.erase o) (hCard : 3 ≤ C.card) {r s : ℝ}
    (hD : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y = r ∨ dist x y = s)
    (hStar : ∀ x ∈ C, dist x o = r) :
    ∃ x y z, x ∈ S ∧ y ∈ S ∧ z ∈ S ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      dist z x = dist y x ∧ dist y z = dist y x := by
  classical
  obtain ⟨U, hUC, hU⟩ := Finset.exists_subset_card_eq hCard
  obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := Finset.card_eq_three.1 hU
  have hu : u ∈ C := hUC (by simp)
  have hv : v ∈ C := hUC (by simp)
  have hw : w ∈ C := hUC (by simp)
  obtain ⟨huo, huS⟩ := Finset.mem_erase.1 (hC hu)
  obtain ⟨hvo, hvS⟩ := Finset.mem_erase.1 (hC hv)
  obtain ⟨hwo, hwS⟩ := Finset.mem_erase.1 (hC hw)
  by_cases h₁ : dist u v = r
  · exact ⟨o, u, v, ho, huS, hvS, Ne.symm huo, Ne.symm hvo, huv,
      (hStar v hv).trans (hStar u hu).symm, h₁.trans (hStar u hu).symm⟩
  by_cases h₂ : dist u w = r
  · exact ⟨o, u, w, ho, huS, hwS, Ne.symm huo, Ne.symm hwo, huw,
      (hStar w hw).trans (hStar u hu).symm, h₂.trans (hStar u hu).symm⟩
  by_cases h₃ : dist v w = r
  · exact ⟨o, v, w, ho, hvS, hwS, Ne.symm hvo, Ne.symm hwo, hvw,
      (hStar w hw).trans (hStar v hv).symm, h₃.trans (hStar v hv).symm⟩
  have h₁' := (hD u huS v hvS huv).resolve_left h₁
  have h₂' := (hD u huS w hwS huw).resolve_left h₂
  have h₃' := (hD v hvS w hwS hvw).resolve_left h₃
  exact ⟨u, v, w, huS, hvS, hwS, huv, huw, hvw,
    (dist_comm w u).trans (h₂'.trans ((dist_comm v u).trans h₁').symm),
    h₃'.trans ((dist_comm v u).trans h₁').symm⟩

private lemma equilateral_triangle (S : Finset ℝ³) (hCard : 7 ≤ S.card) {r s : ℝ}
    (hD : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y = r ∨ dist x y = s) :
    ∃ o a b, o ∈ S ∧ a ∈ S ∧ b ∈ S ∧ o ≠ a ∧ o ≠ b ∧ a ≠ b ∧
      dist b o = dist a o ∧ dist a b = dist a o := by
  classical
  obtain ⟨o, ho⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
  let U := (S.erase o).filter fun x => dist x o = r
  let V := (S.erase o) \ U
  have hU : U ⊆ S.erase o := Finset.filter_subset _ _
  have hV : V ⊆ S.erase o := Finset.sdiff_subset
  have hSum := Finset.card_sdiff_add_card_eq_card hU
  change V.card + U.card = (S.erase o).card at hSum
  have hErase := Finset.card_erase_add_one ho
  by_cases hu : 3 ≤ U.card
  · exact triangle_from_neighborhood S U ho hU hu hD fun x hx => (Finset.mem_filter.1 hx).2
  have hv : 3 ≤ V.card := by omega
  apply triangle_from_neighborhood S V ho hV hv (r := s) (s := r)
  · exact fun x hx y hy hxy => (hD x hx y hy hxy).symm
  · intro x hx
    obtain ⟨hxo, hxS⟩ := Finset.mem_erase.1 (hV hx)
    refine (hD x hxS o ho hxo).resolve_left ?_
    exact fun he => (Finset.mem_sdiff.1 hx).2 (Finset.mem_filter.2 ⟨hV hx, he⟩)

private lemma triangle_direction_rank {o a b : ℝ³} {A : ℝ} (hA : 0 < A)
    (ha : dist a o ^ 2 = A) (hb : dist b o ^ 2 = A) (hab : dist a b ^ 2 = A) :
    2 ≤ finrank ℝ (direction ({o, a, b} : Finset ℝ³) o) := by
  classical
  let v : Fin 2 → ℝ³ := ![a - o, b - o]
  have hV : LinearIndependent ℝ v := anchor_independent hA ha hb hab
  have hle : Submodule.span ℝ (Set.range v) ≤ direction ({o, a, b} : Finset ℝ³) o := by
    apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · change a - o ∈ direction ({o, a, b} : Finset ℝ³) o
      exact sub_mem_direction (by simp)
    · change b - o ∈ direction ({o, a, b} : Finset ℝ³) o
      exact sub_mem_direction (by simp)
  have hr := Submodule.finrank_mono hle
  rwa [finrank_span_eq_card hV, Fintype.card_fin] at hr

private lemma repeated_pattern_card {B P : Finset ℝ³} {o : ℝ³} (ho : o ∈ B)
    (hDim : 2 ≤ finrank ℝ (direction B o)) (hCross : Equidistant P B)
    (hP : TwoDistance P) : P.card ≤ 2 := by
  classical
  rcases P.eq_empty_or_nonempty with rfl | ⟨q, hq⟩
  · simp
  let a := finrank ℝ (direction P q)
  have hOrth := equidistant_orthogonal hq ho hCross
  have hRank := Submodule.finrank_mono hOrth
  have hSum := (direction P q).finrank_add_finrank_orthogonal
  rw [finrank_euclideanSpace_fin] at hSum
  have ha : a ≤ 1 := by dsimp [a]; omega
  obtain ⟨u, v, hu, hv, h⟩ := aligned_twoDistance q hP
  by_cases hZero : a = 0
  · have hC := IsoscelesTwoDistances.general hu hv h
    change (aligned P q).card ≤ (a + 2).choose 2 at hC
    rw [card_aligned, hZero] at hC
    exact hC.trans (by decide)
  have hOne : a = 1 := by omega
  obtain ⟨c, r, hSphere⟩ := aligned_spherical P q o (fun x hx => hCross o ho x hx q hq)
  have hC := IsoscelesTwoDistances.sphericalGeneral (show 1 ≤ a by omega) hu hv h c r hSphere
  change (aligned P q).card + 1 ≤ (a + 2).choose 2 at hC
  rw [card_aligned, hOne] at hC
  change P.card + 1 ≤ 3 at hC
  omega

private def encodePattern (v : Fin 3 → Bool) : Fin 8 :=
  ⟨(if v 0 then 1 else 0) + (if v 1 then 2 else 0) + (if v 2 then 4 else 0), by
    split <;> split <;> split <;> decide⟩

private lemma encodePattern_spec :
    ∀ (v : Fin 3 → Bool) (k : Fin 3), patternBit (encodePattern v) k = v k := by
  decide +kernel

private lemma distinct_two_distance {S : Finset ℝ³} (hS : TwoDistance S) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a ≠ b ∧
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y = a ∨ dist x y = b := by
  obtain ⟨a, b, ha, hb, h⟩ := hS
  by_cases he : a = b
  · refine ⟨a, a + 1, ha, by positivity, by linarith, ?_⟩
    intro x hx y hy hxy
    exact Or.inl ((h x hx y hy hxy).elim id (fun hh => hh.trans he.symm))
  · exact ⟨a, b, ha, hb, he, h⟩

private theorem two_distance_card (S : Finset ℝ³) (hS : TwoDistance S) : S.card ≤ 6 := by
  classical
  by_contra! hCard
  obtain ⟨r₁, r₂, hr₁, hr₂, hDiff, hDist⟩ := distinct_two_distance hS
  obtain ⟨o, a, b, ho, ha, hb, hoa, hob, hab, hEqB, hEqAB⟩ :=
    equilateral_triangle S (by omega) hDist
  let r := dist a o
  obtain ⟨s, hr, hs, hrs, hD⟩ :
      ∃ s : ℝ, 0 < r ∧ 0 < s ∧ r ≠ s ∧
        ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y = r ∨ dist x y = s := by
    rcases hDist a ha o ho (Ne.symm hoa) with h | h
    · change r = r₁ at h
      rw [h]
      exact ⟨r₂, hr₁, hr₂, hDiff, hDist⟩
    · change r = r₂ at h
      rw [h]
      exact ⟨r₁, hr₂, hr₁, Ne.symm hDiff, fun x hx y hy hxy => (hDist x hx y hy hxy).symm⟩
  let A := r ^ 2
  let t := s ^ 2 / A
  have hA : 0 < A := sq_pos_of_pos hr
  have ht₀ : t ≠ 0 := div_ne_zero (pow_ne_zero _ hs.ne') hA.ne'
  have ht₁ : t ≠ 1 := by
    intro h
    have h' : s ^ 2 = r ^ 2 := by
      change s ^ 2 / A = 1 at h
      simpa using (div_eq_iff hA.ne').1 h
    exact hrs ((sq_eq_sq₀ hs.le hr.le).1 h').symm
  let B : Finset ℝ³ := {o, a, b}
  let T := S \ B
  have hBS : B ⊆ S := by simp [B, Finset.insert_subset_iff, ho, ha, hb]
  have hTS : T ⊆ S := Finset.sdiff_subset
  have hBcard : B.card = 3 := Finset.card_eq_three.2 ⟨o, a, b, hoa, hob, hab, rfl⟩
  have hCover := Finset.card_sdiff_add_card_eq_card hBS
  change T.card + B.card = S.card at hCover
  obtain ⟨U, hUT, hUcard⟩ := Finset.exists_subset_card_eq (show 4 ≤ T.card by omega)
  let w (i : Fin 4) : ℝ³ := (U.equivFinOfCardEq hUcard).symm i
  have hw (i : Fin 4) : w i ∈ T := hUT ((U.equivFinOfCardEq hUcard).symm i).property
  have hw_inj : Function.Injective w :=
    Subtype.val_injective.comp (U.equivFinOfCardEq hUcard).symm.injective
  have hAnchor (i : Fin 3) : anchor o a b i ∈ B := by
    fin_cases i
    · change o ∈ B; simp [B]
    · change a ∈ B; simp [B]
    · change b ∈ B; simp [B]
  have hSurj {x : ℝ³} (hx : x ∈ B) : ∃ i : Fin 3, anchor o a b i = x := by
    change x ∈ ({o, a, b} : Finset ℝ³) at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  have hδ {x y : ℝ³} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
      normalizedDistance A x y = 1 ∨ normalizedDistance A x y = t := by
    rcases hD x hx y hy hxy with h | h
    · exact Or.inl (by simp [normalizedDistance, h, ← show A = r ^ 2 from rfl, hA.ne'])
    · exact Or.inr (by simp [normalizedDistance, h, t])
  let p (i : Fin 4) : Fin 8 :=
    encodePattern (fun j => decide (normalizedDistance A (w i) (anchor o a b j) = t))
  have hPat (i : Fin 4) (j : Fin 3) :
      normalizedDistance A (w i) (anchor o a b j) = value t (patternBit (p i) j) := by
    have hne : w i ≠ anchor o a b j :=
      fun he => (Finset.mem_sdiff.1 (hw i)).2 (he.symm ▸ hAnchor j)
    have hn := hδ (hTS (hw i)) (hBS (hAnchor j)) hne
    change _ = value t (patternBit (encodePattern _) j)
    rw [encodePattern_spec]
    rcases hn with h | h
    · simp [value, h, Ne.symm ht₁]
    · simp [value, h]
  have hBsq : dist b o ^ 2 = A := by rw [hEqB]
  have hABsq : dist a b ^ 2 = A := by rw [hEqAB]
  have hDim := triangle_direction_rank hA rfl hBsq hABsq
  have hPairs {i j : Fin 4} (hij : i ≠ j) : edgeClass t (p i) (p j) := by
    have h := pair_schur hA.ne' rfl hBsq hABsq (w i) (w j)
    have h₁ : (fun k => normalizedDistance A (w i) (anchor o a b k)) =
        fun k => value t (patternBit (p i) k) := funext (hPat i)
    have h₂ : (fun k => normalizedDistance A (w j) (anchor o a b k)) =
        fun k => value t (patternBit (p j) k) := funext (hPat j)
    rw [h₁, h₂] at h
    rcases hδ (hTS (hw i)) (hTS (hw j)) (hw_inj.ne hij) with h' | h'
    · exact ⟨false, by rwa [h'] at h⟩
    · exact ⟨true, by rwa [h'] at h⟩
  have hRep {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      ¬(p i = p j ∧ p i = p k) := by
    rintro ⟨hij', hik'⟩
    let P : Finset ℝ³ := {w i, w j, w k}
    have hCardP : P.card = 3 :=
      Finset.card_eq_three.2 ⟨w i, w j, w k, hw_inj.ne hij, hw_inj.ne hik, hw_inj.ne hjk, rfl⟩
    have hPT : P ⊆ T := by simp [P, Finset.insert_subset_iff, hw]
    have hPdist : TwoDistance P := ⟨r, s, hr, hs, fun x hx y hy hxy =>
      hD x (hTS (hPT hx)) y (hTS (hPT hy)) hxy⟩
    have hCross : Equidistant P B := by
      intro y hy x hx z hz
      obtain ⟨l, rfl⟩ := hSurj hy
      rw [dist_comm (anchor o a b l) x, dist_comm (anchor o a b l) z]
      apply (sq_eq_sq₀ dist_nonneg dist_nonneg).1
      apply (div_left_inj' hA.ne').1
      change normalizedDistance A x (anchor o a b l) = normalizedDistance A z (anchor o a b l)
      have same (v : ℝ³) (hv : v ∈ P) :
          normalizedDistance A v (anchor o a b l) = value t (patternBit (p i) l) := by
        change v ∈ ({w i, w j, w k} : Finset ℝ³) at hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl
        · exact hPat i l
        · rw [hPat j l, ← hij']
        · rw [hPat k l, ← hik']
      exact (same x hx).trans (same z hz).symm
    have hcap := repeated_pattern_card (show o ∈ B by simp [B]) hDim hCross hPdist
    omega
  exact no_four ht₀ ht₁
    ⟨hRep (by decide : (0 : Fin 4) ≠ 1) (by decide : (0 : Fin 4) ≠ 2) (by decide),
      hRep (by decide : (0 : Fin 4) ≠ 1) (by decide : (0 : Fin 4) ≠ 3) (by decide),
      hRep (by decide : (0 : Fin 4) ≠ 2) (by decide : (0 : Fin 4) ≠ 3) (by decide),
      hRep (by decide : (1 : Fin 4) ≠ 2) (by decide : (1 : Fin 4) ≠ 3) (by decide)⟩
    (hPairs (by decide)) (hPairs (by decide)) (hPairs (by decide))
    (hPairs (by decide)) (hPairs (by decide)) (hPairs (by decide))


theorem finite_upper (S : Finset ℝ³) (hS : (S : Set ℝ³).IsIsosceles) : S.card ≤ 8 := by
  classical
  have hn := noRainbow_of_isosceles S hS
  rcases two_dist_or_minimal_split S hn with hOne | ⟨X, hXS, hX, hY, hCross, hTwo⟩
  · exact (two_distance_card S hOne).trans (by decide)
  let Y := S \ X
  have hYS : Y ⊆ S := Finset.sdiff_subset
  obtain ⟨o, ho⟩ : X.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨q, hq⟩ := hY
  let P := direction X o
  let Q := direction Y q
  let a := finrank ℝ P
  let b := finrank ℝ Q
  have hSum : a + b ≤ 3 := by
    calc
      a + b ≤ a + finrank ℝ Pᗮ :=
        Nat.add_le_add_left (Submodule.finrank_mono (equidistant_orthogonal ho hq hCross)) a
      _ = 3 := P.finrank_add_finrank_orthogonal.trans finrank_euclideanSpace_fin
  have hCover := Finset.card_sdiff_add_card_eq_card hXS
  change Y.card + X.card = S.card at hCover
  have hA : 1 ≤ a := direction_pos hX
  have hAcard : X.card + 1 ≤ (a + 2).choose 2 := by
    obtain ⟨c, r, hSphere⟩ := aligned_spherical X o q (fun x hx => hCross q hq x hx o ho)
    rw [← card_aligned X o]
    obtain ⟨u, v, hu, hv, h⟩ := aligned_twoDistance o hTwo
    exact IsoscelesTwoDistances.sphericalGeneral hA hu hv h c r hSphere
  have hBcard : Y.card ≤ (b + 2).choose 2 := by
    rw [← card_aligned Y q]
    exact general_card b (aligned Y q) (aligned_noRainbow q (noRainbow_mono hn hYS))
  have hCases : a = 1 ∨ a = 2 ∨ a = 3 := by omega
  rcases hCases with h | h | h
  · rw [h] at hAcard
    have hB' := hBcard.trans (Nat.choose_le_choose 2 (show b + 2 ≤ 4 by omega))
    change X.card + 1 ≤ 3 at hAcard
    change Y.card ≤ 6 at hB'
    omega
  · rw [h] at hAcard
    have hB' := hBcard.trans (Nat.choose_le_choose 2 (show b + 2 ≤ 3 by omega))
    change X.card + 1 ≤ 6 at hAcard
    change Y.card ≤ 3 at hB'
    omega
  · have hX' := two_distance_card X hTwo
    have hB' := hBcard.trans (Nat.choose_le_choose 2 (show b + 2 ≤ 2 by omega))
    change Y.card ≤ 1 at hB'
    omega

end ThreeDistanceGeometry

namespace SpatialIsosceles

private noncomputable def root : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

private lemma root_primitive : IsPrimitiveRoot root 5 :=
  Complex.isPrimitiveRoot_exp 5 (by decide)

private lemma root_norm : ‖root‖ = 1 := by
  have h : ‖root‖ ^ 5 = 1 := by rw [← norm_pow, root_primitive.pow_eq_one, norm_one]
  have hp : 0 ≤ ‖root‖ := norm_nonneg _
  by_contra hn
  rcases lt_or_gt_of_ne hn with hlt | hlt
  · have hh := pow_lt_pow_left₀ hlt hp (by decide : 5 ≠ 0)
    rw [h, one_pow] at hh
    exact (lt_irrefl _) hh
  · have hh := pow_lt_pow_left₀ hlt (by norm_num : (0 : ℝ) ≤ 1) (by decide : 5 ≠ 0)
    rw [h, one_pow] at hh
    exact (lt_irrefl _) hh

private lemma rotate_dist (k : ℕ) (x y : ℂ) :
    dist (root ^ k * x) (root ^ k * y) = dist x y := by
  simp [dist_eq_norm, ← mul_sub, norm_pow, root_norm]

private lemma root_complement (k : ℕ) (hk : k ≤ 5) :
    dist (1 : ℂ) (root ^ (5 - k)) = dist 1 (root ^ k) := by
  rw [← rotate_dist k 1 (root ^ (5 - k)), mul_one, ← pow_add, Nat.add_sub_of_le hk,
    root_primitive.pow_eq_one, dist_comm]

private lemma pair_distance (i j : Fin 5) (hne : i ≠ j) :
    dist (root ^ i.val) (root ^ j.val) = dist (1 : ℂ) root ∨
      dist (root ^ i.val) (root ^ j.val) = dist 1 (root ^ 2) := by
  wlog hle : i.val ≤ j.val generalizing i j
  · rw [dist_comm]
    exact this j i hne.symm (by omega)
  have hlt : i.val < j.val := lt_of_le_of_ne hle fun h => hne (Fin.ext h)
  have hshift : dist (root ^ i.val) (root ^ j.val) = dist 1 (root ^ (j.val - i.val)) := by
    have h := rotate_dist i.val 1 (root ^ (j.val - i.val))
    rwa [mul_one, ← pow_add, Nat.add_sub_of_le hle] at h
  rw [hshift]
  have hj := j.isLt
  have hcases : j.val - i.val = 1 ∨ j.val - i.val = 2 ∨
      j.val - i.val = 3 ∨ j.val - i.val = 4 := by omega
  rcases hcases with h | h | h | h
  · left
    rw [h, pow_one]
  · exact Or.inr (by rw [h])
  · right
    rw [h]
    exact root_complement 2 (by decide)
  · left
    rw [h]
    simpa only [pow_one] using root_complement 1 (by decide)

private noncomputable def pentagon : Option (Fin 5) → ℂ
  | none => 0
  | some i => root ^ i.val

private lemma pentagon_injective : Function.Injective pentagon := by
  have hne (i : Fin 5) : root ^ i.val ≠ 0 := by
    intro h
    have hm := congrArg norm h
    simp [norm_pow, root_norm] at hm
  rintro (i | i) (j | j) h
  · rfl
  · exact ((hne j) h.symm).elim
  · exact ((hne i) h).elim
  · exact congrArg some (Fin.ext (root_primitive.pow_inj i.isLt j.isLt h))

private lemma pentagon_triples (i j k : Option (Fin 5))
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    IsIsosceles (pentagon i) (pentagon j) (pentagon k) := by
  cases i <;> cases j <;> cases k
  · exact (hij rfl).elim
  · exact (hij rfl).elim
  · exact (hik rfl).elim
  · unfold IsIsosceles
    right
    right
    simp [pentagon, dist_zero_left, dist_zero_right, norm_pow, root_norm]
  · exact (hjk rfl).elim
  · unfold IsIsosceles
    left
    simp [pentagon, dist_zero_left, dist_zero_right, norm_pow, root_norm]
  · unfold IsIsosceles
    right
    left
    simp [pentagon, dist_zero_left, dist_zero_right, norm_pow, root_norm]
  · rename_i i j k
    have h1 := pair_distance i j (fun h => hij (congrArg some h))
    have h2 := pair_distance j k (fun h => hjk (congrArg some h))
    have h3 := pair_distance k i (fun h => hik (congrArg some h.symm))
    simp only [IsIsosceles, pentagon]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
      first | exact Or.inl (h1.trans h2.symm) | exact Or.inr (Or.inl (h2.trans h3.symm)) |
        exact Or.inr (Or.inr (h3.trans h1.symm))


private noncomputable def liftComplex (z : ℂ) : ℝ³ :=
  WithLp.toLp 2 ![z.re, z.im, 0]

private noncomputable def pole (s : Bool) : ℝ³ :=
  WithLp.toLp 2 ![0, 0, if s then 1 else -1]

private lemma dist_sq_three (x y : ℝ³) :
    dist x y ^ 2 = (x 0 - y 0)^2 + (x 1 - y 1)^2 + (x 2 - y 2)^2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_succ, Fin.sum_univ_two]
  simp only [Real.dist_eq, sq_abs]
  change (x 0 - y 0)^2 + ((x 1 - y 1)^2 + (x 2 - y 2)^2) = _
  ring

private lemma lift_dist (z w : ℂ) : dist (liftComplex z) (liftComplex w) = dist z w := by
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  rw [dist_sq_three, dist_eq_norm, Complex.sq_norm, Complex.normSq_apply]
  simp [liftComplex, Complex.sub_re, Complex.sub_im, pow_two]

private lemma pole_dist_sq (z : ℂ) (s : Bool) :
    dist (liftComplex z) (pole s) ^ 2 = ‖z‖ ^ 2 + 1 := by
  rw [dist_sq_three, Complex.sq_norm, Complex.normSq_apply]
  change (z.re - 0)^2 + (z.im - 0)^2 + (0 - (if s then 1 else -1))^2 = _
  cases s <;> norm_num <;> ring

private lemma eq_pole_dist (z : ℂ) (a b : Bool) :
    dist (liftComplex z) (pole a) = dist (liftComplex z) (pole b) :=
  (sq_eq_sq₀ dist_nonneg dist_nonneg).mp ((pole_dist_sq z a).trans (pole_dist_sq z b).symm)

private lemma isosceles_swap {x y z : ℝ³} (h : IsIsosceles x y z) : IsIsosceles y x z := by
  unfold IsIsosceles at h ⊢
  rw [dist_comm y x, dist_comm x z, dist_comm z y]
  rcases h with h | h | h
  · exact Or.inr (Or.inr h.symm)
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inl h.symm

private lemma isosceles_rotate {x y z : ℝ³} (h : IsIsosceles x y z) : IsIsosceles y z x := by
  unfold IsIsosceles at h ⊢
  tauto

private noncomputable def equator (i : Option (Fin 5)) : ℝ³ := liftComplex (pentagon i)

private lemma one_pole (i j : Option (Fin 5)) (s : Bool) (hij : i ≠ j) :
    IsIsosceles (equator i) (equator j) (pole s) := by
  cases i <;> cases j
  · exact (hij rfl).elim
  · rename_i j
    refine Or.inr (Or.inr ?_)
    rw [dist_comm (pole s), equator, equator, lift_dist]
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    rw [pole_dist_sq]
    simp [pentagon, dist_zero_left, norm_pow, root_norm]
  · rename_i i
    refine Or.inl ?_
    rw [equator, equator, lift_dist]
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    rw [pole_dist_sq]
    simp [pentagon, dist_zero_right, norm_pow, root_norm]
  · rename_i i j
    refine Or.inr (Or.inl ?_)
    rw [dist_comm (pole s), equator, equator]
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    rw [pole_dist_sq, pole_dist_sq]
    simp [pentagon, norm_pow, root_norm]

private lemma two_poles (i : Option (Fin 5)) (a b : Bool) :
    IsIsosceles (equator i) (pole a) (pole b) := by
  refine Or.inr (Or.inr ?_)
  rw [dist_comm (pole b)]
  exact eq_pole_dist (pentagon i) b a

private noncomputable def point : Option (Fin 5) ⊕ Bool → ℝ³
  | .inl i => equator i
  | .inr s => pole s

private lemma equator_injective : Function.Injective equator := by
  intro i j hh
  apply pentagon_injective
  apply dist_eq_zero.mp
  rw [← lift_dist]
  exact dist_eq_zero.mpr hh

private lemma point_injective : Function.Injective point := by
  intro i j h
  cases i with
  | inl i =>
    cases j with
    | inl j => exact congrArg Sum.inl (equator_injective h)
    | inr s =>
      have hh := congrArg (fun p : ℝ³ => p 2) h
      change (0 : ℝ) = (if s then 1 else -1) at hh
      cases s <;> norm_num at hh
  | inr s =>
    cases j with
    | inl j =>
      have hh := congrArg (fun p : ℝ³ => p 2) h
      change (if s then (1 : ℝ) else -1) = 0 at hh
      cases s <;> norm_num at hh
    | inr t =>
      have hh := congrArg (fun p : ℝ³ => p 2) h
      change (if s then (1 : ℝ) else -1) = (if t then 1 else -1) at hh
      cases s <;> cases t
      · rfl
      · norm_num at hh
      · norm_num at hh
      · rfl

private lemma point_triples (i j k : Option (Fin 5) ⊕ Bool)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    IsIsosceles (point i) (point j) (point k) := by
  cases i <;> cases j <;> cases k
  · rename_i i j k
    simpa only [point, equator, IsIsosceles, lift_dist] using
      pentagon_triples i j k (fun h => hij (congrArg Sum.inl h))
        (fun h => hjk (congrArg Sum.inl h)) (fun h => hik (congrArg Sum.inl h))
  · rename_i i j k
    exact one_pole i j k (fun h => hij (congrArg Sum.inl h))
  · rename_i i j k
    exact isosceles_rotate (isosceles_swap (one_pole i k j (fun h => hik (congrArg Sum.inl h))))
  · rename_i i j k
    exact two_poles i j k
  · rename_i i j k
    exact isosceles_rotate (isosceles_rotate (one_pole j k i (fun h => hjk (congrArg Sum.inl h))))
  · rename_i i j k
    exact isosceles_swap (two_poles j i k)
  · rename_i i j k
    exact isosceles_rotate (two_poles k i j)
  · rename_i i j k
    cases i <;> cases j <;> cases k <;> simp_all

private theorem centered_pentagon_with_poles :
    ∃ A : Set ℝ³, A.ncard = 8 ∧ A.IsIsosceles := by
  refine ⟨Set.range point, ?_, ⟨⟨point (.inl none), ⟨.inl none, rfl⟩⟩, ?_⟩⟩
  · rw [Set.ncard_range_of_injective point_injective, Nat.card_eq_fintype_card]
    simp
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _ ⟨k, rfl⟩ hi hj hk
    exact point_triples i j k (fun h => hi (congrArg point h))
      (fun h => hj (congrArg point h)) (fun h => hk (congrArg point h))

end SpatialIsosceles

theorem OMA.solution : type_of% @Erdos503.erdos_503.variants.R3 := by
  classical
  refine ⟨?_, ?_⟩
  · obtain ⟨A, hcard, hA⟩ := SpatialIsosceles.centered_pentagon_with_poles
    exact ⟨A, hA, hcard⟩
  · rintro k ⟨A, hA, rfl⟩
    by_cases hf : A.Finite
    · rw [Set.ncard_eq_toFinset_card _ hf]
      exact ThreeDistanceGeometry.finite_upper hf.toFinset (by simpa using hA)
    · rw [Set.Infinite.ncard hf]
      exact Nat.zero_le _