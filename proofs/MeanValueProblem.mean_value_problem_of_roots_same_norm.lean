import FormalConjectures.Wikipedia.MeanValueProblem

-- Problem: Mean value problem — mean value problem of roots same norm
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/MeanValueProblem.lean:92 (declaration MeanValueProblem.mean_value_problem_of_roots_same_norm)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Polynomial Finset

namespace OMAMV

/-- Hadamard's inequality over `ℂ` (rows). -/
theorem hadamard {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    ‖M.det‖ ≤ ∏ i, ‖(WithLp.toLp 2 (M i) : EuclideanSpace ℂ (Fin n))‖ := by
  classical
  set f : Fin n → EuclideanSpace ℂ (Fin n) := fun i => WithLp.toLp 2 (M i) with hf
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n) := by simp
  set b := InnerProductSpace.gramSchmidtOrthonormalBasis hdim f
  set e := EuclideanSpace.basisFun (Fin n) ℂ
  have h1 : e.toBasis.det f = M.det := by
    rw [Module.Basis.det_apply, ← Matrix.det_transpose]
    congr 1
  have h2 : e.toBasis.det f = e.toBasis.det b * b.toBasis.det f := by
    rw [Module.Basis.det_apply, Module.Basis.det_apply, Module.Basis.det_apply, ← Matrix.det_mul,
      ← OrthonormalBasis.coe_toBasis b, Module.Basis.toMatrix_mul_toMatrix]
  rw [← h1, h2, norm_mul, OrthonormalBasis.det_to_matrix_orthonormalBasis, one_mul,
    InnerProductSpace.gramSchmidtOrthonormalBasis_det, norm_prod]
  gcongr with i
  exact (norm_inner_le_norm _ _).trans (by simp [hf])

theorem vdm {n : ℕ} (u : Fin n → ℂ) (hu : ∀ i, ‖u i‖ = 1) :
    ∏ i, ∏ k ∈ univ.erase i, ‖u i - u k‖ ≤ (n : ℝ) ^ n := by
  have hdet := hadamard (Matrix.vandermonde u)
  have hrow : ∀ i, ‖(WithLp.toLp 2 (Matrix.vandermonde u i) : EuclideanSpace ℂ (Fin n))‖ =
      Real.sqrt n := by
    intro i
    rw [EuclideanSpace.norm_eq]
    congr 1
    simp [Matrix.vandermonde_apply, norm_pow, hu]
  simp only [hrow, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
  rw [Matrix.det_vandermonde, norm_prod] at hdet
  simp_rw [norm_prod] at hdet
  have e : ∀ i : Fin n, univ.erase i = Iio i ∪ Ioi i := by
    intro i
    ext k
    simp only [mem_erase, mem_univ, and_true, mem_union, mem_Iio, mem_Ioi]
    exact ne_iff_lt_or_gt
  have hdisj : ∀ i : Fin n, Disjoint (Iio i) (Ioi i) := by
    intro i
    exact Finset.disjoint_left.mpr fun k h1 h2 => by
      simp at h1 h2
      exact lt_asymm h1 h2
  have hsplit : ∏ i, ∏ k ∈ univ.erase i, ‖u i - u k‖ =
      (∏ i, ∏ j ∈ Ioi i, ‖u j - u i‖) ^ 2 := by
    simp_rw [e]
    rw [Finset.prod_congr rfl (fun i _ => Finset.prod_union (hdisj i)), Finset.prod_mul_distrib,
      sq]
    congr 1
    · rw [Finset.prod_comm' (t' := univ) (s' := fun k => Ioi k)]
      intro x y
      simp
    · refine Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j _ => ?_))
      rw [norm_sub_rev]
  rw [hsplit]
  calc (∏ i, ∏ j ∈ Ioi i, ‖u j - u i‖) ^ 2 ≤ (Real.sqrt n ^ n) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hdet 2
    _ = (n : ℝ) ^ n := by
        rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]

theorem split (q : ℂ[X]) :
    ∃ (n : ℕ) (v : Fin n → ℂ), n = q.natDegree ∧ q = C q.leadingCoeff * ∏ i, (X - C (v i)) := by
  refine ⟨q.roots.toList.length, fun i => q.roots.toList[i.1], ?_, ?_⟩
  · rw [Multiset.length_toList, IsAlgClosed.card_roots_eq_natDegree]
  · conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C
      (IsAlgClosed.card_roots_eq_natDegree (k := ℂ) (p := q))]
    congr 1
    rw [Fin.prod_univ_fun_getElem (f := fun a => X - C a)]
    conv_lhs => rw [← Multiset.coe_toList q.roots]
    simp

theorem deriv_eval {n : ℕ} (a : ℂ) (w : Fin n → ℂ) (j : Fin n) :
    (C a * ∏ i, (X - C (w i))).derivative.eval (w j) = a * ∏ k ∈ univ.erase j, (w j - w k) := by
  classical
  rw [derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C, derivative_prod_finset]
  congr 1
  rw [eval_finsetSum, Finset.sum_eq_single j]
  · simp [eval_prod]
  · intro i _ hij
    simp only [eval_mul, eval_prod, eval_sub, eval_X, eval_C, derivative_sub, derivative_X,
      derivative_C, sub_zero, eval_one, mul_one]
    exact Finset.prod_eq_zero (mem_erase.mpr ⟨Ne.symm hij, mem_univ _⟩) (by simp)
  · simp

end OMAMV

theorem OMA.solution : type_of% @MeanValueProblem.mean_value_problem_of_roots_same_norm := by
  intro p hp z h K
  classical
  set d := p.natDegree with hd
  by_cases hz : p.derivative.eval z = 0
  · exact ⟨z, hz, by simp [hz]⟩
  set P := p - C (p.eval z) with hP
  have hPz : P.IsRoot z := by simp [P]
  set F := P /ₘ (X - C z) with hFdef
  have hPF : P = (X - C z) * F := (mul_divByMonic_eq_iff_isRoot.mpr hPz).symm
  have hder : p.derivative = F + (X - C z) * F.derivative := by
    have : p.derivative = P.derivative := by simp [P]
    rw [this, hPF, derivative_mul]
    simp
  have hFz : F.eval z = p.derivative.eval z := by
    rw [hder]
    simp
  have hF0 : F ≠ 0 := by
    intro h0
    apply hz
    rw [← hFz, h0, eval_zero]
  have hPdeg : P.natDegree = d := natDegree_sub_C
  have hp0 : p ≠ 0 := by rintro h0; simp [h0, d] at hp
  have hPlc : P.leadingCoeff = p.leadingCoeff := by
    refine leadingCoeff_sub_of_degree_lt (lt_of_le_of_lt degree_C_le ?_)
    rw [degree_eq_natDegree hp0]
    exact_mod_cast (by omega : 0 < d)
  have hFdeg : F.natDegree = d - 1 := by
    have := congrArg natDegree hPF
    rw [natDegree_mul (X_sub_C_ne_zero z) hF0, natDegree_X_sub_C, hPdeg] at this
    omega
  have hFlc : F.leadingCoeff = p.leadingCoeff := by
    have := congrArg leadingCoeff hPF
    rw [leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul, hPlc] at this
    exact this.symm
  obtain ⟨n, w, hn, hFw⟩ := OMAMV.split F
  obtain ⟨m, c, hm, hDc⟩ := OMAMV.split p.derivative
  have hn' : n = d - 1 := hn.trans hFdeg
  have hm' : m = d - 1 := hm.trans (natDegree_derivative p)
  have hmn : n = m := by omega
  subst hmn
  set a := p.leadingCoeff with ha_def
  have ha : a ≠ 0 := leadingCoeff_ne_zero.mpr (by rintro h0; simp [h0, d] at hp)
  set b := p.derivative.leadingCoeff with hb_def
  have hb : ‖b‖ = d * ‖a‖ := by
    have hb1 : b = p.coeff (d - 1 + 1) * ((d - 1 : ℕ) + 1 : ℂ) := by
      rw [hb_def, leadingCoeff, natDegree_derivative, coeff_derivative]
    have hd1 : d - 1 + 1 = d := by omega
    rw [hb1, hd1, norm_mul]
    have : ((d - 1 : ℕ) + 1 : ℂ) = (d : ℂ) := by exact_mod_cast hd1
    rw [this, Complex.norm_natCast, mul_comm]
    rfl
  have hFeval : ∀ x, F.eval x = a * ∏ i, (x - w i) := by
    intro x
    conv_lhs => rw [hFw]
    simp [eval_prod, hFlc, a]
  have hDeval : ∀ x, p.derivative.eval x = b * ∏ j, (x - c j) := by
    intro x
    conv_lhs => rw [hDc]
    simp [eval_prod, b]
  have hwroot : ∀ i, F.eval (w i) = 0 := by
    intro i
    rw [hFeval]
    exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _))
  have hwne : ∀ i, w i ≠ z := by
    intro i hi
    apply hz
    rw [← hFz, ← hi, hwroot]
  have hwp : ∀ i, p.eval (w i) = p.eval z := by
    intro i
    have := congrArg (eval (w i)) hPF
    simp only [P, eval_sub, eval_C, eval_mul, hwroot, mul_zero] at this
    exact sub_eq_zero.mp this
  have hnpos : 0 < n := by omega
  set R := ‖w ⟨0, hnpos⟩ - z‖ with hR_def
  have hR : ∀ i, ‖w i - z‖ = R := fun i => h _ _ (hwp i) (hwp _) (hwne i) (hwne _)
  have hRpos : 0 < R := norm_pos_iff.mpr (sub_ne_zero.mpr (hwne _))
  have hDw : ∀ i, p.derivative.eval (w i) = (w i - z) * (a * ∏ k ∈ univ.erase i, (w i - w k)) := by
    intro i
    rw [hder]
    simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, hwroot, zero_add]
    congr 1
    rw [hFw, hFlc]
    exact OMAMV.deriv_eval a w i
  -- discriminant bound
  have hdisc : ∏ i, ∏ k ∈ univ.erase i, ‖w i - w k‖ ≤ R ^ (n * (n - 1)) * (n : ℝ) ^ n := by
    have hv := OMAMV.vdm (fun i => (w i - z) / (R : ℂ)) (by
      intro i
      rw [norm_div, hR, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos, div_self hRpos.ne'])
    have hterm : ∀ i k, ‖w i - w k‖ = R * ‖(w i - z) / (R : ℂ) - (w k - z) / (R : ℂ)‖ := by
      intro i k
      rw [← sub_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos]
      field_simp
      ring_nf
    simp_rw [hterm, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_erase_of_mem
      (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hv ⊢
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm (n - 1) n]
    exact mul_le_mul_of_nonneg_left hv (by positivity)
  have key : ‖b‖ ^ n * ∏ j, ‖F.eval (c j)‖ = ‖a‖ ^ n * ∏ i, ‖p.derivative.eval (w i)‖ := by
    simp only [hFeval, hDeval, norm_mul, norm_prod, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    rw [Finset.prod_comm]
    simp_rw [norm_sub_rev (c _)]
    ring
  have e1 : ∏ i, ‖p.derivative.eval (w i)‖ =
      R ^ n * ‖a‖ ^ n * ∏ i, ∏ k ∈ univ.erase i, ‖w i - w k‖ := by
    simp only [hDw, norm_mul, norm_prod, hR, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    ring
  have hFzn : ‖p.derivative.eval z‖ = ‖a‖ * R ^ n := by
    rw [← hFz, hFeval, norm_mul, norm_prod]
    simp_rw [norm_sub_rev z, hR]
    simp
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hprod : ∏ j, ‖F.eval (c j)‖ ≤ ((n : ℝ) / d * ‖p.derivative.eval z‖) ^ n := by
    have hpos : 0 < ‖b‖ ^ n := by rw [hb]; positivity
    refine le_of_mul_le_mul_left ?_ hpos
    rw [key, e1, hFzn, hb]
    calc ‖a‖ ^ n * (R ^ n * ‖a‖ ^ n * ∏ i, ∏ k ∈ univ.erase i, ‖w i - w k‖)
        ≤ ‖a‖ ^ n * (R ^ n * ‖a‖ ^ n * (R ^ (n * (n - 1)) * (n : ℝ) ^ n)) := by gcongr
      _ = (d * ‖a‖) ^ n * ((n : ℝ) / d * (‖a‖ * R ^ n)) ^ n := by
        have hnn : n * n = n + n * (n - 1) := by
          obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
          simp [Nat.add_sub_cancel]
          ring
        rw [mul_pow, mul_pow, div_pow, mul_pow, ← pow_mul, hnn, pow_add]
        field_simp
  obtain ⟨j, hj⟩ : ∃ j, ‖F.eval (c j)‖ ≤ (n : ℝ) / d * ‖p.derivative.eval z‖ := by
    by_contra hcon
    push Not at hcon
    have hne : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, hnpos⟩, mem_univ _⟩
    have := Finset.prod_lt_prod_of_nonempty (fun j _ => by positivity) (fun j _ => hcon j) hne
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    linarith
  have hcj : p.derivative.eval (c j) = 0 := by
    rw [hDeval]
    exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (mem_univ j) (sub_self _))
  refine ⟨c j, hcj, ?_⟩
  have hcz : c j ≠ z := by
    intro e
    apply hz
    rw [← e, hcj]
  have hPc : p.eval z - p.eval (c j) = (z - c j) * F.eval (c j) := by
    have := congrArg (eval (c j)) hPF
    simp only [P, eval_sub, eval_C, eval_mul, eval_X] at this
    linear_combination -this
  rw [hPc, norm_mul, mul_div_cancel_left₀ _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hcz.symm))]
  have hcast : (n : ℝ) = (d : ℝ) - 1 := by
    rw [hn']
    push_cast [Nat.cast_sub (by omega : 1 ≤ d)]
    ring
  rw [hcast] at hj
  convert hj using 2
