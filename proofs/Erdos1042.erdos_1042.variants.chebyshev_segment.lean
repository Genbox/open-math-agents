import FormalConjectures.ErdosProblems.«1042»
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Data.Nat.Choose.Cast

/-!
The Chebyshev example of Ghosh and Ramachandran, Example 2.7 in
“On the number of components of polynomial lemniscates”,
https://arxiv.org/abs/2312.13673.
-/

open Polynomial Set Filter
open scoped BigOperators ENNReal Topology
open Polynomial.Chebyshev (T)

private noncomputable def OMA.cheb (n : ℕ) : ℂ[X] :=
  if n = 0 then 1 else Polynomial.Chebyshev.C ℂ (n : ℤ)

private theorem OMA.cheb_degree_monic (n : ℕ) : (cheb n).natDegree = n ∧ (cheb n).Monic := by
  have hC (m : ℕ) :
      (Polynomial.Chebyshev.C ℂ (m : ℤ)).natDegree = m ∧
      (m ≠ 0 → (Polynomial.Chebyshev.C ℂ (m : ℤ)).Monic) := by
    induction m using Nat.twoStepInduction with
    | zero => simp
    | one => simp
    | more m hm hm₁ =>
      let p := (X : ℂ[X]) * Polynomial.Chebyshev.C ℂ ((m + 1 : ℕ) : ℤ)
      let q := Polynomial.Chebyshev.C ℂ (m : ℤ)
      have hp : p.Monic := monic_X.mul (hm₁.2 (by omega))
      have hpd : p.natDegree = m + 2 := by
        change ((X : ℂ[X]) * Polynomial.Chebyshev.C ℂ ((m + 1 : ℕ) : ℤ)).natDegree = _
        rw [monic_X.natDegree_mul (hm₁.2 (by omega)), natDegree_X, hm₁.1]
        omega
      have hlt : q.natDegree < p.natDegree := by
        change (Polynomial.Chebyshev.C ℂ (m : ℤ)).natDegree < p.natDegree
        rw [hm.1, hpd]
        omega
      have he : Polynomial.Chebyshev.C ℂ ((m + 2 : ℕ) : ℤ) = p - q := by
        dsimp [p, q]
        exact Polynomial.Chebyshev.C_add_two ℂ (m : ℤ)
      rw [he, natDegree_sub_eq_left_of_natDegree_lt hlt, hpd]
      exact ⟨rfl, fun _ => hp.sub_of_left (degree_lt_degree hlt)⟩
  by_cases hn : n = 0
  · simp [hn, cheb]
  · simpa only [cheb, if_neg hn] using ⟨(hC n).1, (hC n).2 hn⟩

private theorem OMA.cheb_eval_real_scaled (n : ℕ) (x : ℝ) (hn : n ≠ 0) :
    (cheb n).eval (((2 * x : ℝ)) : ℂ) = (((2 * (T ℝ (n : ℤ)).eval x : ℝ)) : ℂ) := by
  rw [cheb, if_neg hn, ← Polynomial.Chebyshev.map_C Complex.ofRealHom]
  rw [show ((↑(2 * x) : ℂ)) = Complex.ofRealHom (2 * x) by rfl, eval_map_apply]
  have he := congrArg (eval x) (Polynomial.Chebyshev.C_comp_two_mul_X ℝ (n : ℤ))
  exact congrArg Complex.ofReal (by simpa only [eval_comp, eval_mul, eval_ofNat, eval_X] using he)

private def OMA.chebSegment : Set ℂ := Complex.ofReal '' Icc (-2 : ℝ) 2

private theorem OMA.cheb_eval_le_two (n : ℕ) {z : ℂ} (hz : z ∈ chebSegment) :
    ‖(cheb n).eval z‖ ≤ 2 := by
  by_cases hn : n = 0
  · simp [cheb, hn]
  obtain ⟨x, hx, rfl⟩ := hz
  have he : (cheb n).eval (x : ℂ) = (((2 * (T ℝ (n : ℤ)).eval (x / 2) : ℝ)) : ℂ) := by
    rw [← cheb_eval_real_scaled n (x / 2) hn]
    congr 2
    ring
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hx' : |x / 2| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hh := Polynomial.Chebyshev.abs_eval_T_real_le_one (n : ℤ) hx'
  linarith

private noncomputable def OMA.chebAngle (n i : ℕ) : ℝ :=
  (2 * (i : ℝ) + 1) * Real.pi / (2 * (n : ℝ))

private noncomputable def OMA.chebPoint (n : ℕ) (i : Fin n) : ℂ :=
  ((2 * Real.cos (chebAngle n i) : ℝ) : ℂ)

private theorem OMA.cheb_angle_mem (n : ℕ) (i : Fin n) :
    chebAngle n i ∈ Ioo (0 : ℝ) Real.pi := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n from Nat.zero_lt_of_lt i.isLt)
  have hiR : (i : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
  unfold chebAngle
  refine ⟨by positivity, (div_lt_iff₀ (by positivity)).2 ?_⟩
  have h := mul_lt_mul_of_pos_right (show 2 * (i : ℝ) + 1 < 2 * n by linarith) Real.pi_pos
  linarith

private theorem OMA.cheb_point_mem (n : ℕ) (i : Fin n) : chebPoint n i ∈ chebSegment := by
  refine ⟨2 * Real.cos (chebAngle n i), ?_, rfl⟩
  exact ⟨by linarith [Real.neg_one_le_cos (chebAngle n i)],
    by linarith [Real.cos_le_one (chebAngle n i)]⟩

private theorem OMA.cheb_cos_zero (n : ℕ) (i : Fin n) :
    Real.cos ((n : ℝ) * chebAngle n i) = 0 := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.zero_lt_of_lt i.isLt).ne'
  rw [Real.cos_eq_zero_iff]
  refine ⟨(i : ℕ), ?_⟩
  unfold chebAngle
  push_cast
  field_simp

private theorem OMA.cheb_point_eval_zero (n : ℕ) (i : Fin n) : (cheb n).eval (chebPoint n i) = 0 := by
  have hn : n ≠ 0 := (Nat.zero_lt_of_lt i.isLt).ne'
  rw [chebPoint, cheb_eval_real_scaled n _ hn, Polynomial.Chebyshev.T_real_cos]
  simp [cheb_cos_zero]

private theorem OMA.cheb_eval_mid_node (n : ℕ) (hn : n ≠ 0) (k : ℕ) (hk : k ≤ n) :
    ‖(cheb n).eval ((2 * Polynomial.Chebyshev.node n k : ℝ) : ℂ)‖ = 2 := by
  rw [cheb_eval_real_scaled n _ hn, Polynomial.Chebyshev.eval_T_real_node (Finset.mem_Iic.mpr hk)]
  simp

private theorem OMA.cheb_points_separated {n : ℕ} {i j : Fin n} (hij : i < j) :
    (chebPoint n j).re < 2 * Polynomial.Chebyshev.node n ((i : ℕ) + 1) ∧
      2 * Polynomial.Chebyshev.node n ((i : ℕ) + 1) < (chebPoint n i).re := by
  let k : ℕ := (i : ℕ) + 1
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n from Nat.zero_lt_of_lt i.isLt)
  have hjR : (k : ℝ) ≤ j := by exact_mod_cast (show k ≤ (j : ℕ) from Nat.succ_le_of_lt hij)
  let θ := (k : ℝ) * Real.pi / n
  have hθ : θ = (2 * (k : ℝ)) * Real.pi / (2 * (n : ℝ)) := by dsimp [θ]; ring
  have hlt₁ : chebAngle n i < θ := by
    rw [hθ, chebAngle]
    apply div_lt_div_of_pos_right _ (by positivity)
    have he : (k : ℝ) = (i : ℝ) + 1 := by simp [k]
    exact mul_lt_mul_of_pos_right (by linarith) Real.pi_pos
  have hlt₂ : θ < chebAngle n j := by
    rw [hθ, chebAngle]
    apply div_lt_div_of_pos_right _ (by positivity)
    exact mul_lt_mul_of_pos_right (by linarith) Real.pi_pos
  have hi := cheb_angle_mem n i
  have hj := cheb_angle_mem n j
  have h₁ := Real.cos_lt_cos_of_nonneg_of_le_pi (hi.1.le.trans hlt₁.le) hj.2.le hlt₂
  have h₂ := Real.cos_lt_cos_of_nonneg_of_le_pi hi.1.le (hlt₂.le.trans hj.2.le) hlt₁
  change 2 * Real.cos (chebAngle n j) < 2 * Real.cos θ ∧
    2 * Real.cos θ < 2 * Real.cos (chebAngle n i)
  exact ⟨by linarith, by linarith⟩

private theorem OMA.cheb_point_injective (n : ℕ) : Function.Injective (chebPoint n) := by
  intro i j heq
  rcases lt_trichotomy i j with hij | rfl | hij
  · have hs := cheb_points_separated hij
    rw [heq] at hs
    exact False.elim ((lt_irrefl _) (hs.1.trans hs.2))
  · rfl
  · have hs := cheb_points_separated hij
    rw [heq] at hs
    exact False.elim ((lt_irrefl _) (hs.1.trans hs.2))

private theorem OMA.cheb_roots (n : ℕ) :
    (cheb n).roots = (Finset.univ.image (chebPoint n)).val := by
  classical
  refine roots_eq_of_degree_eq_card (fun z hz => ?_) ?_
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact cheb_point_eval_zero n i
  · rw [Finset.card_image_of_injective _ (cheb_point_injective n), Finset.card_univ,
      Fintype.card_fin, degree_eq_natDegree (cheb_degree_monic n).2.ne_zero,
      (cheb_degree_monic n).1]

private theorem OMA.cheb_factor (n : ℕ) : cheb n = ∏ i, (X - C (chebPoint n i)) := by
  classical
  calc
    cheb n = ((cheb n).roots.map fun z => X - C z).prod :=
      (IsAlgClosed.splits (cheb n)).eq_prod_roots_of_monic (cheb_degree_monic n).2
    _ = ∏ z ∈ Finset.univ.image (chebPoint n), (X - C z) := by rw [cheb_roots]; rfl
    _ = _ := Finset.prod_image (fun x _ y _ h => cheb_point_injective n h)

private theorem OMA.cheb_eval_prod (n : ℕ) (z : ℂ) :
    (cheb n).eval z = ∏ i, (z - chebPoint n i) := by
  rw [cheb_factor]
  simp [eval_prod]

private theorem OMA.cheb_deriv_norm_ge (n : ℕ) (i : Fin n) :
    (n : ℝ) ≤ ‖(cheb n).derivative.eval (chebPoint n i)‖ := by
  have hn : n ≠ 0 := (Nat.zero_lt_of_lt i.isLt).ne'
  let θ := chebAngle n i
  have heq := congrArg derivative (Polynomial.Chebyshev.C_comp_two_mul_X ℂ (n : ℤ))
  have he := congrArg (eval (Real.cos θ : ℂ)) heq
  simp only [derivative_comp, derivative_mul, derivative_ofNat, derivative_X, zero_mul,
    mul_one, zero_add, eval_mul, eval_ofNat, eval_comp, eval_X] at he
  have hder : (cheb n).derivative.eval (chebPoint n i) =
      (T ℂ (n : ℤ)).derivative.eval (Real.cos θ : ℂ) := by
    rw [cheb, if_neg hn, chebPoint]
    rw [Complex.ofReal_mul, Complex.ofReal_ofNat]
    exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) he
  rw [hder, Polynomial.Chebyshev.T_derivative_eq_U, eval_mul, eval_intCast, Int.cast_natCast]
  have hU := Polynomial.Chebyshev.U_complex_cos (θ : ℂ) ((n : ℤ) - 1)
  simp only [Int.cast_sub, Int.cast_one, sub_add_cancel, Int.cast_natCast] at hU
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_natCast,
    ← Complex.ofReal_mul, ← Complex.ofReal_sin] at hU
  have hsin : |Real.sin ((n : ℝ) * θ)| = 1 := by
    have hh := Real.sin_sq_add_cos_sq ((n : ℝ) * θ)
    rw [cheb_cos_zero n i, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] at hh
    nlinarith [abs_nonneg (Real.sin ((n : ℝ) * θ)),
      sq_abs (Real.sin ((n : ℝ) * θ))]
  have huNorm := congrArg norm hU
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, hsin] at huNorm
  have hu : 1 ≤ ‖(Polynomial.Chebyshev.U ℂ ((n : ℤ) - 1)).eval (Real.cos θ : ℂ)‖ := by
    exact huNorm.symm.le.trans (mul_le_of_le_one_right (norm_nonneg _) (Real.abs_sin_le_one _))
  rw [norm_mul, Complex.norm_natCast]
  exact le_mul_of_one_le_right (by positivity) hu

private theorem OMA.cheb_det_upper {n : ℕ} (z : Fin n → ℂ) (hz : ∀ i, z i ∈ chebSegment) :
    ‖(Matrix.vandermonde z).det‖ ≤ (2 * (n : ℝ)) ^ n := by
  classical
  let M := Matrix.of (fun i j : Fin n => (cheb j).eval (z i))
  have hdet : (Matrix.vandermonde z).det = M.det :=
    Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde z (fun j : Fin n => cheb j)
      (fun i => (cheb_degree_monic i).1) (fun i => (cheb_degree_monic i).2)
  rw [hdet]
  have hbound := Matrix.det_le (abv := IsAbsoluteValue.toAbsoluteValue (norm : ℂ → ℝ))
    (A := M) (x := (2 : ℝ)) (fun i j => cheb_eval_le_two j (hz i))
  change ‖M.det‖ ≤ _ at hbound
  have hn : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  calc
    ‖M.det‖ ≤ (n.factorial : ℝ) * (2 : ℝ) ^ n := by
      simpa only [Fintype.card_fin, nsmul_eq_mul] using hbound
    _ ≤ (2 * (n : ℝ)) ^ n := by
      rw [mul_pow, mul_comm (2 ^ n)]
      exact mul_le_mul_of_nonneg_right hn (by positivity)

private theorem OMA.edist_prod_eq_det {n : ℕ} (z : Fin n → ℂ) :
    (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, edist (z i) (z j)) =
      ENNReal.ofReal ‖(Matrix.vandermonde z).det‖ := by
  rw [Matrix.det_vandermonde]
  rw [norm_prod, ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _)]
  apply Finset.prod_congr rfl
  intro i _
  rw [norm_prod, ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _)]
  apply Finset.prod_congr rfl
  intro j _
  rw [edist_dist, dist_eq_norm, norm_sub_rev]

private theorem OMA.cheb_nth_upper (n : ℕ) :
    Erdos1042.nthDiameter chebSegment n ≤
      (ENNReal.ofReal ((2 * (n : ℝ)) ^ n)) ^ (1 / ((n.choose 2 : ℕ) : ℝ)) := by
  unfold Erdos1042.nthDiameter
  refine iSup_le fun z => iSup_le fun hz => ?_
  rw [edist_prod_eq_det]
  exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (cheb_det_upper z hz)) (by positivity)

private theorem OMA.cheb_prod_root_derivative_norm {n : ℕ} (r : Fin n → ℂ) :
    ∏ i, ‖(∏ j, (X - C (r j))).derivative.eval (r i)‖ = ‖(Matrix.vandermonde r).det‖ ^ 2 := by
  classical
  have hderiv (i : Fin n) : ‖(∏ j, (X - C (r j))).derivative.eval (r i)‖ =
      ∏ j ∈ Finset.univ.erase i, ‖r i - r j‖ := by
    rw [← Finset.mul_prod_erase Finset.univ (fun j => X - C (r j)) (Finset.mem_univ i)]
    simp [derivative_mul, eval_prod, norm_prod]
  have hsplit (i : Fin n) : ∏ j ∈ Finset.univ.erase i, ‖r i - r j‖ =
      (∏ j ∈ Finset.Ioi i, ‖r i - r j‖) * ∏ j ∈ Finset.Iio i, ‖r i - r j‖ := by
    rw [← Finset.prod_union (by
      refine Finset.disjoint_left.mpr ?_
      intro j hj hk
      exact (not_lt_of_ge (Finset.mem_Ioi.mp hj).le) (Finset.mem_Iio.mp hk))]
    congr 1
    ext j
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_Ioi,
      Finset.mem_Iio]
    exact ne_iff_lt_or_gt.trans or_comm
  have hswap : (∏ i, ∏ j ∈ Finset.Iio i, ‖r i - r j‖) =
      ∏ i, ∏ j ∈ Finset.Ioi i, ‖r j - r i‖ := by
    apply Finset.prod_comm'
    simp
  rw [Matrix.det_vandermonde, norm_prod, sq]
  simp_rw [norm_prod, hderiv, hsplit, Finset.prod_mul_distrib, hswap]
  congr 1
  exact Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j _ => norm_sub_rev _ _))

private theorem OMA.cheb_nth_lower (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ Erdos1042.nthDiameter chebSegment n := by
  have hder : (∏ i, ‖(cheb n).derivative.eval (chebPoint n i)‖) =
      ‖(Matrix.vandermonde (chebPoint n)).det‖ ^ 2 := by
    convert cheb_prod_root_derivative_norm (chebPoint n) using 1
    exact congrArg (fun p : ℂ[X] => ∏ i, ‖p.derivative.eval (chebPoint n i)‖) (cheb_factor n)
  have hge : 1 ≤ ‖(Matrix.vandermonde (chebPoint n)).det‖ ^ 2 := by
    rw [← hder]
    apply Finset.one_le_prod
    intro i _
    exact (show (1 : ℝ) ≤ n by exact_mod_cast hn).trans (cheb_deriv_norm_ge n i)
  have hdet : 1 ≤ ‖(Matrix.vandermonde (chebPoint n)).det‖ := by
    apply (pow_le_pow_iff_left₀ zero_le_one (norm_nonneg _) (by decide : (2 : ℕ) ≠ 0)).mp
    simpa only [one_pow] using hge
  unfold Erdos1042.nthDiameter
  refine le_iSup_of_le (chebPoint n) (le_iSup_of_le (cheb_point_mem n) ?_)
  rw [edist_prod_eq_det, ← ENNReal.one_rpow (1 / ((n.choose 2 : ℕ) : ℝ))]
  apply ENNReal.rpow_le_rpow _ (by positivity)
  simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hdet

private theorem OMA.cheb_nth_upper_limit :
    Tendsto (fun n : ℕ => (ENNReal.ofReal ((2 * (n : ℝ)) ^ n)) ^
      (1 / ((n.choose 2 : ℕ) : ℝ))) atTop (𝓝 1) := by
  have hscale : Tendsto (fun n : ℕ => 2 * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hlog : Tendsto (fun n : ℕ => Real.log (2 * (n : ℝ)) / ((n : ℝ) - 1)) atTop (𝓝 0) := by
    refine ((Real.tendsto_pow_log_div_mul_add_atTop (1 / 2) (-1) 1 (by norm_num)).comp hscale).congr ?_
    intro n
    simp only [Function.comp_apply, pow_one]
    congr 1
    ring
  have hlim : Tendsto (fun n : ℕ => Real.exp (2 * (Real.log (2 * (n : ℝ)) / ((n : ℝ) - 1))))
      atTop (𝓝 1) := by
    have hsmall : Tendsto (fun n : ℕ => 2 * (Real.log (2 * (n : ℝ)) / ((n : ℝ) - 1)))
        atTop (𝓝 0) := by simpa only [mul_zero] using hlog.const_mul (2 : ℝ)
    simpa only [Function.comp_def, Real.exp_zero] using (Real.continuous_exp.tendsto 0).comp hsmall
  have hlim' : Tendsto (fun n : ℕ => ENNReal.ofReal
      (Real.exp (2 * (Real.log (2 * (n : ℝ)) / ((n : ℝ) - 1))))) atTop (𝓝 1) := by
    simpa only [Function.comp_def, ENNReal.ofReal_one] using
      (ENNReal.continuous_ofReal.tendsto (1 : ℝ)).comp hlim
  refine hlim'.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < (2 * (n : ℝ)) ^ n := by positivity
  rw [ENNReal.ofReal_rpow_of_nonneg hpos.le (by positivity), Real.rpow_def_of_pos hpos,
    Real.log_pow, Nat.cast_choose_two]
  congr 2
  field_simp

private theorem OMA.cheb_transfinite_diameter : Erdos1042.transfiniteDiameter chebSegment = 1 := by
  unfold Erdos1042.transfiniteDiameter
  apply le_antisymm
  · rw [← cheb_nth_upper_limit.limsup_eq]
    exact Filter.limsup_le_limsup (Filter.Eventually.of_forall cheb_nth_upper)
  · rw [← Filter.limsup_const (f := (atTop : Filter ℕ)) (1 : ℝ≥0∞)]
    exact Filter.limsup_le_limsup ((eventually_ge_atTop (1 : ℕ)).mono fun n hn => cheb_nth_lower n hn)

private theorem OMA.cheb_strict_component_root (p : ℂ[X]) (hdeg : 0 < p.natDegree)
    {c : ℝ} (hc : 0 < c) (hbounded : Bornology.IsBounded {z : ℂ | ‖p.eval z‖ < c})
    {z : ℂ} (hz : ‖p.eval z‖ < c) :
    ∃ r ∈ connectedComponentIn {q : ℂ | ‖p.eval q‖ < c} z, p.eval r = 0 := by
  let S := {q : ℂ | ‖p.eval q‖ < c}
  let D := Metric.ball (0 : ℂ) c
  let U := connectedComponentIn S z
  have hzS : z ∈ S := hz
  have hUS : U ⊆ S := connectedComponentIn_subset S z
  have hzU : z ∈ U := mem_connectedComponentIn hzS
  have hU : IsConnected U := isConnected_connectedComponentIn_iff.mpr hzS
  have hD : IsPreconnected D := (convex_ball (0 : ℂ) c).isPreconnected
  have hSopen : IsOpen S := isOpen_lt p.continuous.norm continuous_const
  have hmap : IsOpenMap p.eval := by
    have han : AnalyticOnNhd ℂ p.eval univ := fun v _ => p.differentiable.analyticAt v
    rcases han.is_constant_or_isOpenMap with ⟨w, heq⟩ | hopen
    · have hpconst : p = C w := Polynomial.funext (fun x => by simpa using heq x)
      rw [hpconst, natDegree_C] at hdeg
      omega
    · exact hopen
  have hzD : p.eval z ∈ D := by simpa [D, Metric.mem_ball, dist_zero_right] using hz
  have hpart : closure U ∩ S ⊆ U := by
    have hpre : IsPreconnected (closure U ∩ S) :=
      hU.isPreconnected.subset_closure
        (fun q hq => ⟨subset_closure hq, hUS hq⟩) inter_subset_left
    exact hpre.subset_connectedComponentIn ⟨subset_closure hzU, hzS⟩ inter_subset_right
  have hcl : IsClosed (p.eval '' closure U) :=
    (((hbounded.subset hUS).isCompact_closure).image p.continuous).isClosed
  have hclSub : closure (p.eval '' U) ⊆ p.eval '' closure U :=
    closure_minimal (image_mono subset_closure) hcl
  have hsurj := hD.subset_of_closure_inter_subset (hmap _ hSopen.connectedComponentIn)
    ⟨p.eval z, hzD, ⟨z, hzU, rfl⟩⟩ (by
      intro w hw
      obtain ⟨q, hq, rfl⟩ := hclSub hw.1
      have hqS : q ∈ S := by
        simpa [S, D, Metric.mem_ball, dist_zero_right] using hw.2
      exact ⟨q, hpart ⟨hq, hqS⟩, rfl⟩)
  exact hsurj (Metric.mem_ball_self hc)

private theorem OMA.cheb_comp_count (n : ℕ) (hn : 1 ≤ n) :
    Erdos1042.numComponents (cheb n) = n := by
  classical
  let U := Erdos1047.strictSublevelSet (cheb n) 1
  let F (i : Fin n) := connectedComponentIn U (chebPoint n i)
  have hroot (i : Fin n) : chebPoint n i ∈ U := by
    change ‖(cheb n).eval (chebPoint n i)‖ < 1
    simp [cheb_point_eval_zero]
  have hbound : Bornology.IsBounded U := by
    refine Metric.isBounded_ball.subset (t := Metric.ball (0 : ℂ) 4) ?_
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    by_contra! hlarge
    have hge : 1 ≤ ‖(cheb n).eval z‖ := by
      rw [cheb_eval_prod, norm_prod]
      apply Finset.one_le_prod
      intro i _
      have ha : ‖chebPoint n i‖ ≤ 2 := by
        rw [chebPoint, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        have hc := Real.abs_cos_le_one (chebAngle n i)
        linarith
      have hi := norm_add_le (z - chebPoint n i) (chebPoint n i)
      rw [sub_add_cancel] at hi
      linarith
    exact (not_lt_of_ge hge) hz
  have hcover : Erdos1047.componentsIn U = Set.range F := by
    ext C
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨r, hr, hz0⟩ := cheb_strict_component_root (cheb n)
        (by rw [(cheb_degree_monic n).1]; omega) (c := 1) zero_lt_one hbound hz
      have hmem : r ∈ (cheb n).roots := (mem_roots (cheb_degree_monic n).2.ne_zero).2 hz0
      rw [cheb_roots] at hmem
      change r ∈ Finset.univ.image (chebPoint n) at hmem
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
      refine ⟨i, ?_⟩
      change connectedComponentIn U (chebPoint n i) = _
      rw [hi]
      exact (connectedComponentIn_eq hr).symm
    · rintro ⟨i, rfl⟩
      exact ⟨chebPoint n i, hroot i, rfl⟩
  have hsep {i j : Fin n} (hij : i < j) : F i ≠ F j := by
    intro hEq
    let x : ℝ := 2 * Polynomial.Chebyshev.node n ((i : ℕ) + 1)
    have hmid : (chebPoint n j).re < x ∧ x < (chebPoint n i).re := cheb_points_separated hij
    have hB (z : ℂ) (hz : z ∈ U) : z.re ≠ x := by
      intro hx
      have hp : ‖(cheb n).eval ((z.re : ℝ) : ℂ)‖ ≤ ‖(cheb n).eval z‖ := by
        rw [cheb_eval_prod, cheb_eval_prod, norm_prod, norm_prod]
        apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        intro k _
        simp only [chebPoint, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        simpa only [chebPoint, Complex.sub_re, Complex.ofReal_re] using
          Complex.abs_re_le_norm (z - chebPoint n k)
      have hxv : ‖(cheb n).eval (x : ℂ)‖ = 2 :=
        cheb_eval_mid_node n (by omega) ((i : ℕ) + 1) (by omega)
      rw [hx, hxv] at hp
      change ‖(cheb n).eval z‖ < 1 at hz
      linarith
    have hR : chebPoint n i ∈ F i := mem_connectedComponentIn (hroot i)
    have hL : chebPoint n j ∈ F i := hEq ▸ mem_connectedComponentIn (hroot j)
    have hConn : IsConnected (F i) := isConnected_connectedComponentIn_iff.mpr (hroot i)
    have h := hConn.isPreconnected.lt_of_ne Complex.continuous_re.continuousOn
      (fun z hz => hB z (connectedComponentIn_subset _ _ hz))
      ⟨chebPoint n i, hR, hmid.2⟩ hL
    exact (not_lt_of_ge hmid.1.le) h
  have hinj : Function.Injective F := by
    intro i j h
    rcases lt_trichotomy i j with hij | hij | hij
    · exact (hsep hij h).elim
    · exact hij
    · exact (hsep hij h.symm).elim
  unfold Erdos1042.numComponents
  change (Erdos1047.componentsIn U).ncard = n
  rw [hcover, Set.ncard_range_of_injective hinj]
  simp

theorem OMA.solution : type_of% @Erdos1042.erdos_1042.variants.chebyshev_segment := by
  intro F hF
  subst F
  change IsClosed chebSegment ∧ Erdos1042.transfiniteDiameter chebSegment = 1 ∧
    (∀ c : ℂ, ¬ chebSegment ⊆ Metric.closedBall c 1) ∧ _
  refine ⟨(isCompact_Icc.image Complex.continuous_ofReal).isClosed, cheb_transfinite_diameter, ?_, ?_⟩
  · intro c hc
    have hL := hc (show (((-2 : ℝ) : ℂ)) ∈ chebSegment from ⟨-2, by simp, rfl⟩)
    have hR := hc (show (((2 : ℝ) : ℂ)) ∈ chebSegment from ⟨2, by norm_num, rfl⟩)
    have ht := dist_triangle (((-2 : ℝ) : ℂ)) c (((2 : ℝ) : ℂ))
    have hd : dist (((-2 : ℝ) : ℂ)) (((2 : ℝ) : ℂ)) = 4 := by
      rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      norm_num
    rw [hd, dist_comm c _] at ht
    exact (by linarith [Metric.mem_closedBall.mp hL, Metric.mem_closedBall.mp hR] : False)
  · intro n hn
    refine ⟨cheb n, ⟨(cheb_degree_monic n).2, (cheb_degree_monic n).1, ?_⟩, cheb_comp_count n hn⟩
    intro z hz
    rw [cheb_roots] at hz
    change z ∈ Finset.univ.image (chebPoint n) at hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact cheb_point_mem n i