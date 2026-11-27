import FormalConjectures.ErdosProblems.«503»
import Mathlib.Data.Sym.Card

/-!
Blokhuis's bound for finite isosceles sets. The equidistant decomposition and
dimension argument follow Yi, Proposition 2.5 and Remark 2.6
(https://arxiv.org/abs/2611.05421).
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

theorem OMA.solution : type_of% @Erdos503.erdos_503.variants.upper_bound := by
  classical
  intro d k hk
  obtain ⟨A, hA, rfl⟩ := hk
  by_cases hf : A.Finite
  · rw [Set.ncard_eq_toFinset_card _ hf]
    exact GeneralIsosceles.general_card d hf.toFinset
      (GeneralIsosceles.noRainbow_of_isosceles _ (by simpa using hA))
  · rw [Set.Infinite.ncard hf]
    exact Nat.zero_le _