import FormalConjectures.ErdosProblems.«98»

/-!
Project a large lattice norm shell into the plane, and choose a shear
that avoids every cocircular quadruple. The difference vectors still
come from a bounded integer grid.

Credit: @Genbox.
-/

open Set Finset
open scoped Affine EuclideanGeometry

namespace DistanceShell

private theorem separating_form {d : ℕ} (S : Finset (Fin d → ℝ))
    (hs : ∀ v ∈ S, v ≠ 0) :
    ∃ g : (Fin d → ℝ) →ₗ[ℝ] ℝ, ∀ v ∈ S, g v ≠ 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert w S hw ih =>
    obtain ⟨g, hg⟩ := ih (fun v h => hs v (Finset.mem_insert_of_mem h))
    obtain ⟨i, hi⟩ : ∃ i : Fin d, w i ≠ 0 := by
      by_contra! h
      exact hs w (Finset.mem_insert_self _ _) (funext h)
    let h : (Fin d → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj i
    let roots := (insert w S).image (fun v => -g v / h v)
    obtain ⟨t, ht⟩ := roots.finite_toSet.exists_notMem
    refine ⟨g + t • h, ?_⟩
    intro v hv hz
    change g v + t * h v = 0 at hz
    by_cases hzero : h v = 0
    · have hv' : v ∈ S := by
        rcases Finset.mem_insert.mp hv with rfl | hv'
        · exact (hi hzero).elim
        · exact hv'
      exact hg v hv' (by simpa [hzero] using hz)
    · have he := (eq_div_iff hzero).mpr (show t * h v = -g v by linarith)
      exact ht (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨v, hv, he.symm⟩))

noncomputable def lift (d k : ℕ) (a : Fin d → Fin k) : Fin d → ℝ :=
  fun i => (a i).val

theorem lift_inj (d k : ℕ) : Function.Injective (lift d k) := by
  intro a b h
  funext i
  apply Fin.ext
  have hi : ((a i).val : ℝ) = ((b i).val : ℝ) := congrFun h i
  exact_mod_cast hi

private noncomputable def projection {d : ℕ}
    (f g : (Fin d → ℝ) →ₗ[ℝ] ℝ) : (Fin d → ℝ) →ₗ[ℝ] ℝ² :=
  (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm.toLinearMap ∘ₗ LinearMap.pi ![f, g]

private theorem projection_zero {d : ℕ} (f g : (Fin d → ℝ) →ₗ[ℝ] ℝ) (x : Fin d → ℝ) :
    projection f g x 0 = f x := rfl

private theorem projection_one {d : ℕ} (f g : (Fin d → ℝ) →ₗ[ℝ] ℝ) (x : Fin d → ℝ) :
    projection f g x 1 = g x := rfl

theorem exists_projection (d k : ℕ) :
    ∃ F : (Fin d → ℝ) →ₗ[ℝ] ℝ², Function.Injective (F ∘ lift d k) ∧
      ∀ a b c, a ≠ b → F (lift d k c) ∈ line[ℝ, F (lift d k a), F (lift d k b)] →
        lift d k c ∈ line[ℝ, lift d k a, lift d k b] := by
  classical
  let A := Fin d → Fin k
  let L := lift d k
  let diff (ab : A × A) := L ab.2 - L ab.1
  let S := (Finset.univ.image diff).filter (· ≠ 0)
  obtain ⟨f, hf⟩ := separating_form S (fun v hv => (Finset.mem_filter.mp hv).2)
  have hf' {a b : A} (hne : a ≠ b) : f (L b - L a) ≠ 0 := by
    apply hf
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, rfl⟩, ?_⟩
    exact sub_ne_zero.mpr (fun h => hne ((lift_inj d k h).symm))
  let wedge (abc : A × A × A) :=
    f (L abc.2.1 - L abc.1) • (L abc.2.2 - L abc.1) -
      f (L abc.2.2 - L abc.1) • (L abc.2.1 - L abc.1)
  let T := (Finset.univ.image wedge).filter (· ≠ 0)
  obtain ⟨g, hg⟩ := separating_form T (fun v hv => (Finset.mem_filter.mp hv).2)
  let F := projection f g
  refine ⟨F, ?_, ?_⟩
  · intro a b he
    by_contra hab
    apply hf' hab
    rw [map_sub, sub_eq_zero]
    exact congrArg (fun p : ℝ² => p 0) he.symm
  · intro a b c hab hc
    obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hc
    have hV : F (L c - L a) = r • F (L b - L a) := by
      rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add] at hr
      rw [map_sub, map_sub, ← hr, add_sub_cancel_right]
    have hF : f (L c - L a) = r * f (L b - L a) := by
      simpa [F, projection_zero] using congrArg (fun p : ℝ² => p 0) hV
    have hG : g (L c - L a) = r * g (L b - L a) := by
      simpa [F, projection_one] using congrArg (fun p : ℝ² => p 1) hV
    have hw : wedge (a, b, c) = 0 := by
      by_contra hne
      have hg' := hg (wedge (a, b, c))
        (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(a, b, c), Finset.mem_univ _, rfl⟩, hne⟩)
      apply hg'
      dsimp [wedge]
      rw [map_sub, map_smul, map_smul, hF, hG]
      simp only [smul_eq_mul]
      ring
    have hz : f (L b - L a) • ((L c - L a) - r • (L b - L a)) = 0 := by
      rw [smul_sub, smul_smul, mul_comm (f (L b - L a)), ← hF]
      exact hw
    have hv : L c - L a = r • (L b - L a) :=
      sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (hf' hab))
    refine mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨r, ?_⟩
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, ← hv, sub_add_cancel]

open EuclideanGeometry Polynomial

private noncomputable def squareSum {D : ℕ} (p : Fin D → ℝ) : ℝ :=
  ∑ i, p i ^ 2

private theorem squareSum_pos_sub {D : ℕ} {p q : Fin D → ℝ} (hpq : p ≠ q) :
    0 < squareSum (q - p) := by
  obtain ⟨i, hi⟩ : ∃ i, p i ≠ q i := by
    by_contra! h
    exact hpq (funext h)
  apply lt_of_lt_of_le (sq_pos_of_ne_zero (sub_ne_zero.mpr hi.symm))
  exact Finset.single_le_sum (fun j _ => sq_nonneg ((q - p) j)) (Finset.mem_univ i)

private theorem squareSum_combo {D : ℕ} (p q : Fin D → ℝ) (a : ℝ) :
    squareSum (a • (q - p) + p) =
      (1 - a) * squareSum p + a * squareSum q - a * (1 - a) * squareSum (q - p) := by
  simp only [squareSum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem sphere_line_endpoints {D : ℕ} {p q r : Fin D → ℝ} (hpq : p ≠ q)
    (hq : squareSum q = squareSum p) (hr : squareSum r = squareSum p)
    (hline : r ∈ line[ℝ, p, q]) : r = p ∨ r = q := by
  obtain ⟨a, ha⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hline
  rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add] at ha
  have h := squareSum_combo p q a
  rw [ha, hq, hr] at h
  have hz : a * (1 - a) * squareSum (q - p) = 0 := by nlinarith only [h]
  have hab := (mul_eq_zero.mp hz).resolve_right (squareSum_pos_sub hpq).ne'
  rcases mul_eq_zero.mp hab with ha₀ | ha₁
  · left
    simpa [ha₀] using ha.symm
  · right
    have he : a = 1 := (sub_eq_zero.mp ha₁).symm
    simpa [he] using ha.symm

private theorem largest_fiber {α : Type*} (A : Finset α) (f : α → ℕ) (C : ℕ)
    (hC : 0 < C) (hrange : ∀ a ∈ A, f a < C) :
    ∃ b, A.card ≤ C * (A.filter (fun a => f a = b)).card := by
  classical
  obtain ⟨b, _, hb⟩ := Finset.exists_max_image (Finset.range C)
    (fun b => (A.filter (fun a => f a = b)).card) (Finset.nonempty_range_iff.mpr hC.ne')
  have hA : A.filter (fun a => f a ∈ Finset.range C) = A := by
    apply Finset.filter_true_of_mem
    intro a ha
    exact Finset.mem_range.mpr (hrange a ha)
  refine ⟨b, ?_⟩
  calc
    _ = ∑ j ∈ Finset.range C, (A.filter (fun a => f a = j)).card := by
      rw [Finset.sum_card_fiberwise_eq_card_filter, hA]
    _ ≤ ∑ _j ∈ Finset.range C, (A.filter (fun a => f a = b)).card := Finset.sum_le_sum hb
    _ = _ := by simp

private abbrev Lattice (d M : ℕ) := Fin d → Fin M

private def normNat {d M : ℕ} (x : Lattice d M) : ℕ :=
  ∑ j, (x j).val ^ 2

private noncomputable def shear (t : ℝ) : ℝ² →ₗ[ℝ] ℝ² where
  toFun p := WithLp.toLp 2 ![p 0 + t * p 1, p 1]
  map_add' p q := by
    ext i
    fin_cases i
    · change p 0 + q 0 + t * (p 1 + q 1) = p 0 + t * p 1 + (q 0 + t * q 1)
      ring
    · rfl
  map_smul' r p := by
    ext i
    fin_cases i
    · change r * p 0 + t * (r * p 1) = r * (p 0 + t * p 1)
      ring
    · rfl

private theorem shear_zero (t : ℝ) (p : ℝ²) : shear t p 0 = p 0 + t * p 1 := rfl
private theorem shear_one (t : ℝ) (p : ℝ²) : shear t p 1 = p 1 := rfl

private theorem shear_injective (t : ℝ) : Function.Injective (shear t) := by
  intro p q h
  have h₁ := congrArg (fun x : ℝ² => x 1) h
  change p 1 = q 1 at h₁
  have h₀ : p 0 + t * p 1 = q 0 + t * q 1 := congrArg (fun x : ℝ² => x 0) h
  ext i
  fin_cases i
  · simpa [h₁] using h₀
  · exact h₁

private theorem shear_reflects_line (t : ℝ) {p q r : ℝ²}
    (h : shear t r ∈ line[ℝ, shear t p, shear t q]) : r ∈ line[ℝ, p, q] := by
  obtain ⟨a, ha⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp h
  refine mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨a, shear_injective t ?_⟩
  rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add] at ha ⊢
  simpa only [map_add, map_smul, map_sub] using ha

private noncomputable def cross (p q : ℝ²) : ℝ := p 0 * q 1 - p 1 * q 0

private theorem cross_self (p : ℝ²) : cross p p = 0 := by unfold cross; ring

private theorem cross_swap (p q : ℝ²) : cross p q = -cross q p := by unfold cross; ring

private theorem cross_add_left (p q r : ℝ²) : cross (p + q) r = cross p r + cross q r := by
  unfold cross
  simp only [PiLp.add_apply]
  ring

private theorem proportional {u v : ℝ²} (hu : u ≠ 0) (h : cross u v = 0) :
    ∃ a : ℝ, a • u = v := by
  unfold cross at h
  by_cases h₀ : u 0 = 0
  · have h₁ : u 1 ≠ 0 := by
      intro he
      apply hu
      ext i
      fin_cases i <;> assumption
    have hv : v 0 = 0 := (mul_eq_zero.mp (by rw [h₀, zero_mul] at h; linarith only [h])).resolve_left h₁
    refine ⟨v 1 / u 1, ?_⟩
    ext i
    fin_cases i
    · simp [PiLp.smul_apply, h₀, hv]
    · exact div_mul_cancel₀ _ h₁
  · refine ⟨v 0 / u 0, ?_⟩
    ext i
    fin_cases i
    · exact div_mul_cancel₀ _ h₀
    · change v 0 / u 0 * u 1 = v 1
      field_simp [h₀]
      linarith only [h]

private theorem cross_ne_of_not_mem {p q r : ℝ²} (hpq : p ≠ q)
    (hr : r ∉ line[ℝ, p, q]) : cross (q - p) (r - p) ≠ 0 := by
  intro h
  obtain ⟨a, ha⟩ := proportional (sub_ne_zero.mpr hpq.symm) h
  apply hr
  refine mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨a, ?_⟩
  rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, ha, sub_add_cancel]

private noncomputable def moment (u v w : ℝ²) (f : ℝ² → ℝ) : ℝ :=
  cross u v * f w ^ 2 - cross w v * f u ^ 2 - cross u w * f v ^ 2

private noncomputable def mixedMoment (u v w : ℝ²) : ℝ :=
  cross u v * (w 0 * w 1) - cross w v * (u 0 * u 1) - cross u w * (v 0 * v 1)

private noncomputable def circlePolynomial (u v w : ℝ²) : ℝ[X] :=
  let A := moment u v w (fun p => p 1)
  let B := mixedMoment u v w
  let C₀ := moment u v w (fun p => p 0)
  C A * X^2 + C (2 * B) * X + C (A + C₀)

private theorem moment_cross (u v w g : ℝ²) :
    moment u v w (cross g) =
      (g 0)^2 * moment u v w (fun p => p 1) -
        2 * g 0 * g 1 * mixedMoment u v w + (g 1)^2 * moment u v w (fun p => p 0) := by
  unfold moment mixedMoment cross
  ring

private theorem circlePolynomial_ne_zero {u v w : ℝ²}
    (hD : cross u v ≠ 0) (hE : cross w v ≠ 0) (hF : cross u w ≠ 0) :
    circlePolynomial u v w ≠ 0 := by
  intro h
  let A := moment u v w (fun p => p 1)
  let B := mixedMoment u v w
  let C₀ := moment u v w (fun p => p 0)
  change C A * X^2 + C (2 * B) * X + C (A + C₀) = 0 at h
  have e₀ := congrArg (Polynomial.eval (0 : ℝ)) h
  have ep := congrArg (Polynomial.eval (1 : ℝ)) h
  have em := congrArg (Polynomial.eval (-1 : ℝ)) h
  simp at e₀ ep em
  have ha : A = 0 := by linarith only [e₀, ep, em]
  have hb : B = 0 := by linarith only [ep, em]
  have hc : C₀ = 0 := by linarith only [e₀, ha]
  have hz (g : ℝ²) : moment u v w (cross g) = 0 := by
    rw [moment_cross]
    change (g 0)^2 * A - 2 * g 0 * g 1 * B + (g 1)^2 * C₀ = 0
    simp [ha, hb, hc]
  have hf : cross u w = cross u v := by
    have hd := hz u
    unfold moment at hd
    rw [cross_self] at hd
    have hz' : (cross u v * cross u w) * (cross u w - cross u v) = 0 := by nlinarith only [hd]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz').resolve_left (mul_ne_zero hD hF))
  have he : cross w v = cross u v := by
    have hd := hz v
    unfold moment at hd
    rw [cross_self, cross_swap v w, cross_swap v u] at hd
    have hz' : (cross u v * cross w v) * (cross w v - cross u v) = 0 := by nlinarith only [hd]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz').resolve_left (mul_ne_zero hD hE))
  have hs := hz (u + v)
  unfold moment at hs
  rw [cross_add_left, cross_add_left, cross_add_left, cross_self u, cross_self v,
    cross_swap v u, cross_swap v w, he, hf] at hs
  have hcube : cross u v ^ 3 = 0 := by nlinarith only [hs]
  exact (pow_ne_zero _ hD) hcube

private theorem eval_circlePolynomial (t : ℝ) (u v w : ℝ²) :
    (circlePolynomial u v w).eval t =
      cross u v * ((shear t w 0)^2 + (shear t w 1)^2) -
        cross w v * ((shear t u 0)^2 + (shear t u 1)^2) -
        cross u w * ((shear t v 0)^2 + (shear t v 1)^2) := by
  simp [circlePolynomial, moment, mixedMoment, shear_zero, shear_one]
  ring

private theorem equal_distance_chord (t : ℝ) (p q c : ℝ²)
    (h : dist (shear t q) c = dist (shear t p) c) :
    (shear t (q - p) 0)^2 + (shear t (q - p) 1)^2 =
      2 * ((c 0 - shear t p 0) * shear t (q - p) 0 + (c 1 - shear t p 1) * shear t (q - p) 1) := by
  have hsq := congrArg (fun a : ℝ => a^2) h
  simp only [PiLp.dist_sq_eq_of_L2, Fin.sum_univ_two, Real.dist_eq, sq_abs] at hsq
  simp only [map_sub, PiLp.sub_apply]
  nlinarith only [hsq]

private theorem circle_condition (t : ℝ) (p q r s c : ℝ²)
    (hq : dist (shear t q) c = dist (shear t p) c)
    (hr : dist (shear t r) c = dist (shear t p) c)
    (hs : dist (shear t s) c = dist (shear t p) c) :
    (circlePolynomial (q - p) (r - p) (s - p)).eval t = 0 := by
  let u := q - p
  let v := r - p
  let w := s - p
  have halg : cross u v • w = cross w v • u + cross u w • v := by
    ext i
    fin_cases i
    · change cross u v * w 0 = cross w v * u 0 + cross u w * v 0
      unfold cross
      ring
    · change cross u v * w 1 = cross w v * u 1 + cross u w * v 1
      unfold cross
      ring
  have hlinear := congrArg (shear t) halg
  simp only [map_add, map_smul] at hlinear
  have h₀ : cross u v * shear t w 0 = cross w v * shear t u 0 + cross u w * shear t v 0 :=
    congrArg (fun x : ℝ² => x 0) hlinear
  have h₁ : cross u v * shear t w 1 = cross w v * shear t u 1 + cross u w * shear t v 1 :=
    congrArg (fun x : ℝ² => x 1) hlinear
  change (circlePolynomial u v w).eval t = 0
  rw [eval_circlePolynomial,
    show (shear t w 0)^2 + (shear t w 1)^2 = _ from equal_distance_chord t p s c hs,
    show (shear t u 0)^2 + (shear t u 1)^2 = _ from equal_distance_chord t p q c hq,
    show (shear t v 0)^2 + (shear t v 1)^2 = _ from equal_distance_chord t p r c hr]
  linear_combination 2 * (c 0 - shear t p 0) * h₀ + 2 * (c 1 - shear t p 1) * h₁

private def LineFree (S : Finset ℝ²) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → q ≠ r → p ≠ r → r ∉ line[ℝ, p, q]

private theorem shear_general_position (S : Finset ℝ²) (hS : LineFree S) :
    ∃ t : ℝ, InGeneralPosition (S.image (shear t) : Finset ℝ²) := by
  classical
  let Q := S.product (S.product (S.product S))
  let bad (z : ℝ² × ℝ² × ℝ² × ℝ²) :=
    (circlePolynomial (z.2.1 - z.1) (z.2.2.1 - z.1) (z.2.2.2 - z.1)).roots.toFinset
  let roots := Q.biUnion bad
  obtain ⟨t, ht⟩ := roots.finite_toSet.exists_notMem
  refine ⟨t, ?_, ?_⟩
  · intro p hp q hq r hr hpq hqr hpr hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hr
    apply hS x hx y hy z hz (fun he => hpq (congrArg (shear t) he))
      (fun he => hqr (congrArg (shear t) he)) (fun he => hpr (congrArg (shear t) he))
    apply shear_reflects_line
    exact hc.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hpq
  · intro T hT hcard hc
    obtain ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, rfl⟩ := Set.ncard_eq_four.mp hcard
    have hp := hT (by simp : p ∈ ({p,q,r,s} : Set ℝ²))
    have hq := hT (by simp : q ∈ ({p,q,r,s} : Set ℝ²))
    have hr := hT (by simp : r ∈ ({p,q,r,s} : Set ℝ²))
    have hs := hT (by simp : s ∈ ({p,q,r,s} : Set ℝ²))
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hs
    have hnpq : x ≠ y := fun h => hpq (congrArg (shear t) h)
    have hnpr : x ≠ z := fun h => hpr (congrArg (shear t) h)
    have hnps : x ≠ w := fun h => hps (congrArg (shear t) h)
    have hnqr : y ≠ z := fun h => hqr (congrArg (shear t) h)
    have hnqs : y ≠ w := fun h => hqs (congrArg (shear t) h)
    have hnrs : z ≠ w := fun h => hrs (congrArg (shear t) h)
    have hD := cross_ne_of_not_mem hnpq (hS x hx y hy z hz hnpq hnqr hnpr)
    have hE := cross_ne_of_not_mem hnps (hS x hx w hw z hz hnps hnrs.symm hnpr)
    have hF := cross_ne_of_not_mem hnpq (hS x hx y hy w hw hnpq hnqs hnps)
    obtain ⟨c, a, ha⟩ := hc
    have hcx := ha _ (by simp : shear t x ∈ ({shear t x, shear t y, shear t z, shear t w} : Set ℝ²))
    have hcy := ha _ (by simp : shear t y ∈ ({shear t x, shear t y, shear t z, shear t w} : Set ℝ²))
    have hcz := ha _ (by simp : shear t z ∈ ({shear t x, shear t y, shear t z, shear t w} : Set ℝ²))
    have hcw := ha _ (by simp : shear t w ∈ ({shear t x, shear t y, shear t z, shear t w} : Set ℝ²))
    have he := circle_condition t x y z w c (hcy.trans hcx.symm) (hcz.trans hcx.symm) (hcw.trans hcx.symm)
    apply ht
    refine Finset.mem_biUnion.mpr ⟨(x,y,z,w), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨hx, Finset.mem_product.mpr ⟨hy, Finset.mem_product.mpr ⟨hz, hw⟩⟩⟩
    · exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (circlePolynomial_ne_zero hD hE hF)).mpr he)

private theorem latticeNorm_bound {d M : ℕ} (u : Lattice d M) :
    normNat u ≤ d * M^2 := by
  unfold normNat
  calc
    _ ≤ ∑ _j : Fin d, M^2 := Finset.sum_le_sum fun j _ => Nat.pow_le_pow_left (u j).isLt.le 2
    _ = _ := by simp

private def encodeDifference {d M : ℕ} (u v : Lattice d M) : Lattice d (2 * M) :=
  fun i => ⟨(u i).val + M - (v i).val, by have h := (u i).isLt; omega⟩

private noncomputable def decodeDifference {d M : ℕ} (w : Lattice d (2 * M)) : Fin d → ℝ :=
  fun i => (w i).val - (M : ℝ)

private theorem decode_encode {d M : ℕ} (u v : Lattice d M) :
    decodeDifference (encodeDifference u v) = lift d M u - lift d M v := by
  funext i
  change (((u i).val + M - (v i).val : ℕ) : ℝ) - (M : ℝ) =
    ((u i).val : ℝ) - (v i).val
  rw [Nat.cast_sub (by have h := (v i).isLt; omega), Nat.cast_add]
  ring

private theorem distanceCount_le {d M : ℕ} (A : Finset (Lattice d M))
    (F : (Fin d → ℝ) →ₗ[ℝ] ℝ²) :
    distinctDistances (A.image (F ∘ lift d M)) ≤ (2 * M)^d := by
  classical
  let R := (Finset.univ : Finset (Lattice d (2 * M))).image (fun z => ‖F (decodeDifference z)‖)
  have h : distanceSet (A.image (F ∘ lift d M)) ⊆ R := by
    intro r hr
    obtain ⟨⟨x,y⟩, hxy, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hx, hy, _⟩ := Finset.mem_offDiag.mp hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    refine Finset.mem_image.mpr ⟨encodeDifference a b, Finset.mem_univ _, ?_⟩
    simp only [decode_encode, map_sub, Function.comp_apply, dist_eq_norm]
  exact (Finset.card_le_card h).trans (Finset.card_image_le.trans (by simp [Lattice]))

theorem distance_upper_of_shell (d M n : ℕ)
    (hn : (d * M^2 + 1) * n ≤ M^d) : Erdos98.h n ≤ (2*M)^d := by
  classical
  let C := d * M^2 + 1
  obtain ⟨R, hR⟩ := largest_fiber (Finset.univ : Finset (Lattice d M)) normNat C
    (Nat.succ_pos _) (fun u _ => Nat.lt_succ_of_le (latticeNorm_bound u))
  let S := (Finset.univ : Finset (Lattice d M)).filter (fun u => normNat u = R)
  have hS : M^d ≤ C * S.card := by simpa [S, Lattice] using hR
  have hc : n ≤ S.card := Nat.le_of_mul_le_mul_left (hn.trans hS) (Nat.succ_pos _)
  obtain ⟨A, hAS, hA⟩ := Finset.exists_subset_card_eq hc
  obtain ⟨F, hF, hreflect⟩ := exists_projection d M
  let P := A.image (F ∘ lift d M)
  have hnorm (a : Lattice d M) (ha : a ∈ A) : squareSum (lift d M a) = (R : ℝ) := by
    have h := (Finset.mem_filter.mp (hAS ha)).2
    unfold squareSum lift
    exact_mod_cast h
  have hP : LineFree P := by
    intro p hp q hq r hr hpq hqr hpr hs
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hr
    have hab : a ≠ b := fun h => hpq (congrArg (F ∘ lift d M) h)
    have hne : lift d M a ≠ lift d M b := fun h => hab (lift_inj d M h)
    rcases sphere_line_endpoints hne ((hnorm b hb).trans (hnorm a ha).symm)
      ((hnorm c hc).trans (hnorm a ha).symm) (hreflect a b c hab hs) with he | he
    · exact hpr (congrArg F he.symm)
    · exact hqr (congrArg F he.symm)
  obtain ⟨t, ht⟩ := shear_general_position P hP
  have hcard : (P.image (shear t)).card = n := by
    rw [Finset.card_image_of_injective _ (shear_injective t)]
    unfold P
    rw [Finset.card_image_of_injective _ hF, hA]
  have hd : distinctDistances (P.image (shear t)) ≤ (2*M)^d := by
    change distinctDistances ((A.image (F ∘ lift d M)).image (shear t)) ≤ _
    rw [Finset.image_image]
    exact distanceCount_le A ((shear t).comp F)
  have hle : Erdos98.h n ≤ distinctDistances (P.image (shear t)) := by
    unfold Erdos98.h
    apply Nat.sInf_le
    exact ⟨P.image (shear t), hcard, ht, rfl⟩
  exact hle.trans hd

open Filter Real

theorem eventual_upper :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (Erdos98.h n : ℝ) < (n : ℝ) * exp (c * √(log n)) := by
  refine ⟨13, by norm_num, ?_⟩
  have hT : Tendsto (fun n : ℕ => √(log (n : ℝ))) atTop atTop :=
    tendsto_sqrt_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hT.eventually (eventually_ge_atTop (8 : ℝ)), eventually_ge_atTop (2 : ℕ)]
    with n ht hn
  let t := √(log (n : ℝ))
  change 8 ≤ t at ht
  have ht0 : 0 < t := by linarith
  have hn0 : 0 < (n : ℝ) := by positivity
  have htsq : t^2 = log (n : ℝ) := sq_sqrt (log_natCast_nonneg n)
  let d := ⌊t⌋₊
  let M := ⌈exp (t+10)⌉₊
  have hd : (d : ℝ) ≤ t := Nat.floor_le ht0.le
  have hdLo : t - 1 ≤ (d : ℝ) := by
    have h := Nat.lt_floor_add_one t
    change t < (d : ℝ) + 1 at h
    linarith
  have hMlo : exp (t+10) ≤ (M : ℝ) := Nat.le_ceil _
  have hM0 : 0 < (M : ℝ) := (exp_pos _).trans_le hMlo
  have hM1 : 1 ≤ (M : ℝ) := (one_le_exp (by linarith : (0 : ℝ) ≤ t+10)).trans hMlo
  have hMLo : t+10 ≤ log (M : ℝ) := by
    rw [← log_exp (t+10)]
    exact (log_le_log_iff (exp_pos _) hM0).mpr hMlo
  have hDLog : log ((d : ℝ)+1) ≤ t :=
    (log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have hcap : (d*M^2+1)*n ≤ M^d := by
    have hC : (d : ℝ)*(M : ℝ)^2+1 ≤ ((d : ℝ)+1)*(M : ℝ)^2 := by
      nlinarith only [hM1, sq_nonneg ((M : ℝ)-1)]
    have hCL : log ((d : ℝ)*(M : ℝ)^2+1) ≤ log ((d : ℝ)+1) + 2*log (M : ℝ) := by
      have h := (log_le_log_iff (by positivity) (by positivity)).mpr hC
      rw [log_mul (by positivity) (by positivity), log_pow] at h
      simpa only [Nat.cast_ofNat] using h
    have hML : (t-3)*(t+10) ≤ ((d : ℝ)-2)*log (M : ℝ) :=
      mul_le_mul (by linarith only [hdLo]) hMLo (by linarith only [ht])
        (by linarith only [hdLo, ht])
    have hR : ((d : ℝ) * (M : ℝ)^2+1)*(n : ℝ) ≤ (M : ℝ)^d := by
      apply (log_le_log_iff (by positivity) (by positivity)).mp
      rw [log_mul (by positivity) hn0.ne', log_pow, ← htsq]
      nlinarith only [hCL, hML, hDLog, ht]
    exact_mod_cast hR
  have hbound : (Erdos98.h n : ℝ) ≤ (2 * (M : ℝ))^d := by exact_mod_cast distance_upper_of_shell d M n hcap
  have hExp : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
  have hMup : (M : ℝ) ≤ exp (t+11) := by
    calc
      _ ≤ exp (t+10)+1 := (Nat.ceil_lt_add_one (exp_pos (t+10)).le).le
      _ ≤ 2*exp (t+10) := by
        have h := one_le_exp (by linarith : (0 : ℝ) ≤ t+10)
        linarith
      _ ≤ exp 1 * exp (t+10) := mul_le_mul_of_nonneg_right hExp (exp_pos _).le
      _ = _ := by rw [← exp_add]; congr 1; ring
  have hMLog : log (M : ℝ) ≤ t+11 := by
    rw [← log_exp (t+11)]
    exact (log_le_log_iff hM0 (exp_pos _)).mpr hMup
  have hLog2 : log (2 : ℝ) ≤ 1 := by
    rw [← log_exp 1]
    exact (log_le_log_iff (by norm_num) (exp_pos _)).mpr hExp
  apply hbound.trans_lt
  change (2 * (M : ℝ))^d < (n : ℝ) * exp (13 * t)
  apply (log_lt_log_iff (by positivity) (by positivity)).mp
  rw [log_pow, log_mul (by norm_num) hM0.ne', log_mul hn0.ne' (exp_pos _).ne', log_exp, ← htsq]
  calc
    _ ≤ (d : ℝ)*(t+12) := mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg d)
    _ ≤ t*(t+12) := mul_le_mul_of_nonneg_right hd (by linarith)
    _ < _ := by nlinarith only [ht0]

end DistanceShell

theorem OMA.solution : type_of% @Erdos98.erdos_98.variants.upper_bound :=
  DistanceShell.eventual_upper