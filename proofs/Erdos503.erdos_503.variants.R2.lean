import FormalConjectures.ErdosProblems.«503»
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
Kelly's centered regular pentagon, from his solution of Monthly problem E735
(https://www.jstor.org/stable/2304710). The upper bound uses the decomposition
for finite sets whose distance colorings contain no rainbow triangle, as in
Yi, Lemmas 2.1–2.2 (https://arxiv.org/abs/2611.05421).
-/

open scoped BigOperators EuclideanGeometry

namespace IsoscelesTwoDistances

private abbrev Point := ℝ × ℝ

private def sqdist (p q : Point) : ℝ := (p.1 - q.1)^2 + (p.2 - q.2)^2

private def rad (p : Point) : ℝ := p.1^2 + p.2^2

private def kernel (a b : ℝ) (p q : Point) : ℝ :=
  (sqdist p q - a) * (sqdist p q - b)

private theorem weights_eq_zero {I : Type*} [Fintype I] (p : I → Point)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hd : ∀ i j, i ≠ j → sqdist (p i) (p j) = a ∨ sqdist (p i) (p j) = b)
    (w : I → ℝ) (h0 : ∑ i, w i = 0)
    (hx : ∑ i, w i * (p i).1 = 0) (hy : ∑ i, w i * (p i).2 = 0)
    (hxx : ∑ i, w i * (p i).1^2 = 0) (hyy : ∑ i, w i * (p i).2^2 = 0)
    (hxy : ∑ i, w i * ((p i).1 * (p i).2) = 0) :
    ∀ i, w i = 0 := by
  classical
  have hexpand (q z : Point) (u : ℝ) :
      u * kernel a b q z =
        (rad q - a) * (rad q - b) * u +
        (2 * (a+b) - 4 * rad q) * q.1 * (u * z.1) +
        (2 * (a+b) - 4 * rad q) * q.2 * (u * z.2) +
        (2 * rad q - a - b + 4 * q.1^2) * (u * z.1^2) +
        (2 * rad q - a - b + 4 * q.2^2) * (u * z.2^2) +
        (8 * q.1 * q.2) * (u * (z.1 * z.2)) +
        u * rad z^2 +
        (-4 * q.1) * (u * (rad z * z.1)) +
        (-4 * q.2) * (u * (rad z * z.2)) := by
    unfold kernel sqdist rad
    ring
  let A := ∑ i, w i * rad (p i)^2
  let B := ∑ i, w i * (rad (p i) * (p i).1)
  let C := ∑ i, w i * (rad (p i) * (p i).2)
  have hrow (q : Point) :
      ∑ j, w j * kernel a b q (p j) = A + (-4 * B) * q.1 + (-4 * C) * q.2 := by
    simp_rw [hexpand]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, h0, hx, hy, hxx, hyy, hxy,
      mul_zero, zero_add]
    change A + (-4 * q.1) * B + (-4 * q.2) * C = _
    ring
  have hdiag (i : I) :
      ∑ j, w j * kernel a b (p i) (p j) = w i * (a * b) := by
    rw [Finset.sum_eq_single i]
    · simp [kernel, sqdist]
    · intro j _ hji
      rcases hd i j (Ne.symm hji) with h | h
      · simp [kernel, h]
      · simp [kernel, h]
    · simp
  have hW (i : I) : w i * (w i * (a*b)) =
      A * w i + (-4 * B) * (w i * (p i).1) + (-4 * C) * (w i * (p i).2) := by
    have hr := (hdiag i).symm.trans (hrow (p i))
    rw [hr]
    ring
  have hsum : ∑ i, w i * (w i * (a*b)) = 0 := by
    simp_rw [hW]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, h0, hx, hy, mul_zero, add_zero]
  have hnonneg (i : I) : 0 ≤ w i * (w i * (a*b)) := by
    rw [← mul_assoc]
    exact mul_nonneg (mul_self_nonneg _) (mul_nonneg ha.le hb.le)
  intro i
  have hzero : w i * (w i * (a*b)) = 0 := congrFun ((Fintype.sum_eq_zero_iff_of_nonneg hnonneg).1 hsum) i
  rcases mul_eq_zero.mp hzero with h | h
  · exact h
  · exact (mul_eq_zero.mp h).resolve_right (mul_ne_zero ha.ne' hb.ne')

private theorem planar_card {I : Type*} [Fintype I] (p : I → Point)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hd : ∀ i j, i ≠ j → sqdist (p i) (p j) = a ∨ sqdist (p i) (p j) = b) :
    Fintype.card I ≤ 6 := by
  let v (i : I) : Fin 6 → ℝ :=
    ![1, (p i).1, (p i).2, (p i).1^2, (p i).2^2, (p i).1 * (p i).2]
  have hv : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro w h
    have coord (j : Fin 6) : ∑ i, w i * v i j = 0 := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        using congrFun h j
    apply weights_eq_zero p ha hb hd w
    · simpa [v] using coord 0
    · simpa [v] using coord 1
    · simpa [v] using coord 2
    · simpa [v] using coord 3
    · simpa [v] using coord 4
    · simpa [v] using coord 5
  simpa [Module.finrank_fin_fun] using hv.fintype_card_le_finrank

private theorem circle_card {I : Type*} [Fintype I] (p : I → Point)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hd : ∀ i j, i ≠ j → sqdist (p i) (p j) = a ∨ sqdist (p i) (p j) = b)
    {r : ℝ} (hs : ∀ i, rad (p i) = r) :
    Fintype.card I ≤ 5 := by
  let v (i : I) : Fin 5 → ℝ :=
    ![1, (p i).1, (p i).2, (p i).1^2, (p i).1 * (p i).2]
  have hv : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro w h
    have coord (j : Fin 5) : ∑ i, w i * v i j = 0 := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        using congrFun h j
    have h0 : ∑ i, w i = 0 := by simpa [v] using coord 0
    have hxx : ∑ i, w i * (p i).1^2 = 0 := by simpa [v] using coord 3
    have hyy : ∑ i, w i * (p i).2^2 = 0 := by
      have hy (i : I) : (p i).2^2 = r - (p i).1^2 := by
        have hh := hs i
        unfold rad at hh
        linarith only [hh]
      simp_rw [hy, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h0, hxx, zero_mul, sub_self]
    exact weights_eq_zero p ha hb hd w h0
      (by simpa [v] using coord 1) (by simpa [v] using coord 2)
      hxx hyy (by simpa [v] using coord 4)
  simpa [Module.finrank_fin_fun] using hv.fintype_card_le_finrank

private def centered (c x : ℝ²) : Point := (x 0 - c 0, x 1 - c 1)

private theorem sqdist_centered (c x y : ℝ²) :
    sqdist (centered c x) (centered c y) = dist x y ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp only [sqdist, centered, Real.dist_eq, sq_abs]
  ring

private theorem card_le_of_two_distances_aux (S : Finset ℝ²) (a b : ℝ)
    (h : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y = a ∨ dist x y = b)
    (c : ℝ²) :
    ∀ i j : S, i ≠ j →
      sqdist (centered c i) (centered c j) = a^2 ∨
      sqdist (centered c i) (centered c j) = b^2 := by
  intro i j hij
  rw [sqdist_centered]
  rcases h i i.property j j.property (fun he => hij (Subtype.ext he)) with h | h
  · exact Or.inl (congrArg (·^2) h)
  · exact Or.inr (congrArg (·^2) h)

theorem planar (S : Finset ℝ²) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y = a ∨ dist x y = b) : S.card ≤ 6 := by
  simpa using planar_card (fun i : S => centered 0 i) (sq_pos_of_pos ha) (sq_pos_of_pos hb)
    (card_le_of_two_distances_aux S a b h 0)

theorem spherical (S : Finset ℝ²) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y = a ∨ dist x y = b)
    (c : ℝ²) (r : ℝ) (hSphere : ∀ x ∈ S, dist x c = r) : S.card ≤ 5 := by
  have hrad (i : S) : rad (centered c i) = r^2 := by
    calc
      _ = sqdist (centered c i) (centered c c) := by simp [rad, sqdist, centered]
      _ = dist (i : ℝ²) c ^ 2 := sqdist_centered c i c
      _ = r^2 := by rw [hSphere i i.property]
  simpa using circle_card (fun i : S => centered c i) (sq_pos_of_pos ha) (sq_pos_of_pos hb)
    (card_le_of_two_distances_aux S a b h c) hrad

end IsoscelesTwoDistances

namespace PlanarIsosceles

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

private noncomputable def pentagonPlane (i : Option (Fin 5)) : ℝ² :=
  Complex.orthonormalBasisOneI.repr (pentagon i)

theorem centered_pentagon : ∃ A : Set ℝ², A.ncard = 6 ∧ A.IsIsosceles := by
  let e := Complex.orthonormalBasisOneI.repr
  have hI : Function.Injective pentagonPlane := e.injective.comp pentagon_injective
  have hdist (i j : Option (Fin 5)) : dist (pentagonPlane i) (pentagonPlane j) =
      dist (pentagon i) (pentagon j) := e.isometry.dist_eq _ _
  refine ⟨Set.range pentagonPlane, ?_, ⟨⟨pentagonPlane none, ⟨none, rfl⟩⟩, ?_⟩⟩
  · rw [Set.ncard_range_of_injective hI, Nat.card_eq_fintype_card]
    simp
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _ ⟨k, rfl⟩ hi hj hk
    simpa only [IsIsosceles, hdist] using
      pentagon_triples i j k (fun h => hi (congrArg pentagonPlane h))
        (fun h => hj (congrArg pentagonPlane h)) (fun h => hk (congrArg pentagonPlane h))


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

open Finset

private lemma dist_sq_coord (x y : ℝ²) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs]

private lemma coordinate_ne_of_ne {x y : ℝ²} (hne : x ≠ y) :
    y 0 - x 0 ≠ 0 ∨ y 1 - x 1 ≠ 0 := by
  by_contra! h
  apply hne
  ext i
  fin_cases i
  · exact (sub_eq_zero.1 h.1).symm
  · exact (sub_eq_zero.1 h.2).symm

private structure Line (S : Finset ℝ²) where
  t : ℝ² → ℝ
  u : ℝ² → ℝ
  m : ℝ
  c : ℝ
  eq : ∀ x ∈ S, u x = m * t x + c
  injective : Set.InjOn t (S : Set ℝ²)
  dist_sq : ∀ x y, dist x y ^ 2 = (t x - t y) ^ 2 + (u x - u y) ^ 2

private noncomputable def line_coordinates (S : Finset ℝ²) {a b c : ℝ}
    (hne : a ≠ 0 ∨ b ≠ 0) (hLine : ∀ x ∈ S, a * x 0 + b * x 1 = c) : Line S := by
  classical
  by_cases hb : b = 0
  · have ha : a ≠ 0 := hne.resolve_right (fun h => h hb)
    have hx (x : ℝ²) (hxS : x ∈ S) : x 0 = c / a := by
      apply (eq_div_iff ha).2
      simpa [hb, mul_comm] using hLine x hxS
    refine ⟨fun x => x 1, fun x => x 0, 0, c / a, ?_, ?_, ?_⟩
    · intro x hxS
      simpa using hx x hxS
    · intro x hxS y hyS he
      ext i
      fin_cases i
      · exact (hx x hxS).trans (hx y hyS).symm
      · exact he
    · intro x y
      rw [dist_sq_coord, add_comm]
  · have hx (x : ℝ²) (hxS : x ∈ S) : x 1 = (-a / b) * x 0 + c / b := by
      field_simp [hb]
      linarith only [hLine x hxS]
    refine ⟨fun x => x 0, fun x => x 1, -a / b, c / b, hx, ?_, dist_sq_coord⟩
    intro x hxS y hyS he
    ext i
    fin_cases i
    · exact he
    · change x 1 = y 1
      change x 0 = y 0 at he
      rw [hx x hxS, hx y hyS, he]

private lemma line_isosceles_card {S : Finset ℝ²} (L : Line S) (hn : NoRainbow dist S) :
    S.card ≤ 3 := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨a, ha, ham⟩ := Finset.exists_min_image S L.t hne
  obtain ⟨b, hb, hbm⟩ := Finset.exists_max_image S L.t hne
  by_cases he : a = b
  · have hA (x : ℝ²) (hx : x ∈ S) : x = a :=
      L.injective hx ha (le_antisymm (by simpa [← he] using hbm x hx) (ham x hx))
    have hcard : S.card ≤ 1 := Finset.card_le_one_iff.2 fun {x y} hx hy =>
      (hA x hx).trans (hA y hy).symm
    omega
  have hab : L.t a < L.t b := lt_of_le_of_ne (ham b hb) fun h => he (L.injective ha hb h)
  let C := 1 + L.m ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hSq {x y : ℝ²} (hx : x ∈ S) (hy : y ∈ S) :
      dist x y ^ 2 = C * (L.t x - L.t y) ^ 2 := by
    rw [L.dist_sq, L.eq x hx, L.eq y hy]
    dsimp [C]
    ring
  let T := (S.erase a).erase b
  have hMid {x : ℝ²} (hx : x ∈ T) : 2 * L.t x = L.t a + L.t b := by
    obtain ⟨hxb, hx'⟩ := Finset.mem_erase.1 hx
    obtain ⟨hxa, hxS⟩ := Finset.mem_erase.1 hx'
    have hA : L.t a < L.t x := lt_of_le_of_ne (ham x hxS)
      (fun h => hxa (L.injective ha hxS h).symm)
    have hB : L.t x < L.t b := lt_of_le_of_ne (hbm x hxS)
      (fun h => hxb (L.injective hxS hb h))
    have h1 : dist a x ^ 2 < dist b a ^ 2 := by
      rw [hSq ha hxS, hSq hb ha]
      exact mul_lt_mul_of_pos_left (sq_lt_sq' (by linarith) (by linarith)) hC
    have h2 : dist x b ^ 2 < dist b a ^ 2 := by
      rw [hSq hxS hb, hSq hb ha]
      exact mul_lt_mul_of_pos_left (sq_lt_sq' (by linarith) (by linarith)) hC
    have hh := hn ha hxS hb
    have hd : dist a x = dist x b := hh.resolve_right
      (not_or_intro (fun h => h2.ne (congrArg (fun t : ℝ => t ^ 2) h))
        (fun h => h1.ne (congrArg (fun t : ℝ => t ^ 2) h.symm)))
    have h3 := congrArg (fun t : ℝ => t ^ 2) hd
    rw [hSq ha hxS, hSq hxS hb] at h3
    have h4 := mul_left_cancel₀ hC.ne' h3
    have h5 : (L.t a - L.t b) * (L.t a + L.t b - 2 * L.t x) = 0 := by nlinarith only [h4]
    have h6 := (mul_eq_zero.1 h5).resolve_left (sub_ne_zero.2 hab.ne)
    linarith
  have h1 : T.card ≤ 1 := by
    refine Finset.card_le_one_iff.2 fun {x y} hx hy => L.injective
      (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
      (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)) ?_
    linarith only [hMid hx, hMid hy]
  have h2 := Finset.card_erase_add_one (Finset.mem_erase.2 ⟨Ne.symm he, hb⟩)
  have h3 := Finset.card_erase_add_one ha
  change T.card + 1 = (S.erase a).card at h2
  omega

private lemma line_circle_card {S : Finset ℝ²} (L : Line S) (o : ℝ²) (r : ℝ)
    (hSphere : ∀ x ∈ S, dist x o = r) : S.card ≤ 2 := by
  classical
  by_contra! hs
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq (show 3 ≤ S.card by omega)
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 hT
  have ha : a ∈ S := hTS (by simp)
  have hb : b ∈ S := hTS (by simp)
  have hc : c ∈ S := hTS (by simp)
  let A := 1 + L.m ^ 2
  let B := 2 * (L.m * (L.c - L.u o) - L.t o)
  have hq {x y : ℝ²} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
      A * (L.t x + L.t y) + B = 0 := by
    have hh := congrArg (fun t : ℝ => t ^ 2) ((hSphere x hx).trans (hSphere y hy).symm)
    rw [L.dist_sq x o, L.dist_sq y o, L.eq x hx, L.eq y hy] at hh
    have hprod : (L.t x - L.t y) * (A * (L.t x + L.t y) + B) = 0 := by
      dsimp [A, B]
      nlinarith only [hh]
    exact (mul_eq_zero.1 hprod).resolve_left
      (sub_ne_zero.2 (fun h => hxy (L.injective hx hy h)))
  have hk : A * (L.t b - L.t c) = 0 := by linarith only [hq ha hb hab, hq ha hc hac]
  have hpos : 0 < A := by dsimp [A]; positivity
  exact hbc (L.injective hb hc (sub_eq_zero.1 ((mul_eq_zero.1 hk).resolve_left hpos.ne')))


private lemma noRainbow_mono {D : α → α → β} {S T : Finset α}
    (h : NoRainbow D S) (hT : T ⊆ S) : NoRainbow D T :=
  fun _ _ _ hx hy hz => h (hT hx) (hT hy) (hT hz)

private lemma two_dist_or_split (S : Finset ℝ²) (hn : NoRainbow dist S) :
    (∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y = a ∨ dist x y = b) ∨
    (∃ X ⊆ S, 2 ≤ X.card ∧ (S \ X).Nonempty ∧
      ∀ y ∈ S \ X, ∀ x ∈ X, ∀ x' ∈ X, dist y x = dist y x') := by
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

private noncomputable def common_difference_line (S : Finset ℝ²) (p q : ℝ²)
    (hpq : p ≠ q) (t : ℝ) (h : ∀ x ∈ S, dist x p ^ 2 - dist x q ^ 2 = t) :
    Line S := by
  apply line_coordinates S (c := (t - (p 0) ^ 2 - (p 1) ^ 2 + (q 0) ^ 2 + (q 1) ^ 2) / 2)
    (coordinate_ne_of_ne hpq)
  intro x hx
  have he := h x hx
  rw [dist_sq_coord, dist_sq_coord] at he
  nlinarith only [he]

private lemma spherical_upper (S : Finset ℝ²) (hn : NoRainbow dist S) (o : ℝ²) (r : ℝ)
    (hSphere : ∀ x ∈ S, dist x o = r) : S.card ≤ 5 := by
  classical
  rcases two_dist_or_split S hn with ⟨a, b, ha, hb, h⟩ | ⟨X, hXS, hX, ⟨y, hy⟩, hCross⟩
  · exact IsoscelesTwoDistances.spherical S a b ha hb h o r hSphere
  let Y := S \ X
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < X.card)
  have hYS : Y ⊆ S := Finset.sdiff_subset
  have hyo : y ≠ o := by
    intro he
    have hr : r = 0 := by simpa [he] using (hSphere y (hYS hy)).symm
    have hao := dist_eq_zero.1 ((hSphere a (hXS ha)).trans hr)
    have hbo := dist_eq_zero.1 ((hSphere b (hXS hb)).trans hr)
    exact hab (hao.trans hbo.symm)
  let LY : Line Y := common_difference_line Y a b hab 0 fun z hz => by
    rw [hCross z hz a ha b hb, sub_self]
  let LX : Line X := common_difference_line X o y (Ne.symm hyo) (r ^ 2 - dist y a ^ 2)
    fun x hx => by rw [hSphere x (hXS hx), dist_comm x y, hCross y hy x hx a ha]
  have hxc := line_circle_card LX o r fun x hx => hSphere x (hXS hx)
  have hyc := line_circle_card LY o r fun x hx => hSphere x (hYS hx)
  have hc := Finset.card_sdiff_add_card_eq_card hXS
  change Y.card + X.card = S.card at hc
  omega

private lemma finite_upper (S : Finset ℝ²) (hIso : (S : Set ℝ²).IsIsosceles) :
    S.card ≤ 6 := by
  classical
  have hn : NoRainbow dist S := by
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
  rcases two_dist_or_split S hn with ⟨a, b, ha, hb, h⟩ | ⟨X, hXS, hX, ⟨y, hy⟩, hCross⟩
  · exact IsoscelesTwoDistances.planar S a b ha hb h
  let Y := S \ X
  have hYS : Y ⊆ S := Finset.sdiff_subset
  have hc := Finset.card_sdiff_add_card_eq_card hXS
  change Y.card + X.card = S.card at hc
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < X.card)
  by_cases hY : Y.card ≤ 1
  · have hSphere (x : ℝ²) (hx : x ∈ X) : dist x y = dist y a :=
      (dist_comm x y).trans (hCross y hy x hx a ha)
    have h := spherical_upper X (noRainbow_mono hn hXS) y (dist y a) hSphere
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 (by omega : 1 < Y.card)
  let LY : Line Y := common_difference_line Y a b hab 0 fun z hz => by
    rw [hCross z hz a ha b hb, sub_self]
  let LX : Line X := common_difference_line X u v huv (dist u a ^ 2 - dist v a ^ 2)
    fun x hx => by rw [dist_comm x u, dist_comm x v, hCross u hu x hx a ha, hCross v hv x hx a ha]
  have hxc := line_isosceles_card LX (noRainbow_mono hn hXS)
  have hyc := line_isosceles_card LY (noRainbow_mono hn hYS)
  omega

end PlanarIsosceles

theorem OMA.solution : type_of% @Erdos503.erdos_503.variants.R2 := by
  classical
  refine ⟨?_, ?_⟩
  · obtain ⟨A, hcard, hA⟩ := PlanarIsosceles.centered_pentagon
    exact ⟨A, hA, hcard⟩
  · rintro k ⟨A, hA, rfl⟩
    by_cases hf : A.Finite
    · rw [Set.ncard_eq_toFinset_card _ hf]
      exact PlanarIsosceles.finite_upper hf.toFinset (by simpa using hA)
    · rw [Set.Infinite.ncard hf]
      exact Nat.zero_le _