import FormalConjectures.ErdosProblems.«990»
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! Hayman's sector count follows by summing the arguments of the linear factors along
root-free rays. Descartes' rule of signs bounds the argument variation, and a finite
perturbation of the sector endpoints handles roots on the boundary. -/

open Polynomial Filter
open scoped Real Topology BigOperators

namespace HaymanRay

noncomputable def rotation (θ : ℝ) : ℂ :=
  Complex.exp ((θ : ℂ) * Complex.I)

noncomputable def normalized (f : ℂ[X]) (θ : ℝ) : ℂ[X] :=
  f.sum fun n a => monomial n ((f.coeff 0)⁻¹ * (a * rotation θ ^ n))

lemma normalized_coeff (f : ℂ[X]) (θ : ℝ) (n : ℕ) :
    (normalized f θ).coeff n = (f.coeff 0)⁻¹ * (f.coeff n * rotation θ ^ n) := by
  classical
  unfold normalized Polynomial.sum
  rw [finsetSum_coeff]
  simp only [coeff_monomial]
  by_cases hn : n ∈ f.support
  · simp [hn]
  · have hz : f.coeff n = 0 := notMem_support_iff.mp hn
    simp [hn, hz]

lemma normalized_support (f : ℂ[X]) (h0 : f.coeff 0 ≠ 0) (θ : ℝ) :
    (normalized f θ).support = f.support := by
  ext n
  simp [mem_support_iff, normalized_coeff, h0, rotation, Complex.exp_ne_zero]

lemma normalized_constant (f : ℂ[X]) (h0 : f.coeff 0 ≠ 0) (θ : ℝ) :
    (normalized f θ).coeff 0 = 1 := by
  simp [normalized_coeff, h0]

lemma normalized_eval (f : ℂ[X]) (θ : ℝ) (z : ℂ) :
    (normalized f θ).eval z = (f.coeff 0)⁻¹ * f.eval (rotation θ * z) := by
  unfold normalized
  rw [eval_eq_sum (p := f), Polynomial.sum, Polynomial.sum, eval_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  simp only [eval_monomial, mul_pow]
  ring

lemma root_ne_zero {f : ℂ[X]} (h0 : f.coeff 0 ≠ 0) {r : ℂ} (hr : r ∈ f.roots) : r ≠ 0 := by
  intro he
  subst r
  have hf : f ≠ 0 := fun h => h0 (by simp [h])
  have hz := (mem_roots hf).mp hr
  exact h0 (by simpa [IsRoot, coeff_zero_eq_eval_zero] using hz)

lemma normalized_prod (f : ℂ[X]) (h0 : f.coeff 0 ≠ 0) (θ : ℝ) (z : ℂ) :
    (normalized f θ).eval z =
      (f.roots.map (fun r => (z - Complex.exp (-(θ : ℂ) * Complex.I) * r) /
        (-(Complex.exp (-(θ : ℂ) * Complex.I) * r)))).prod := by
  classical
  let q := rotation θ
  let k := Complex.exp (-(θ : ℂ) * Complex.I)
  have hq : q ≠ 0 := Complex.exp_ne_zero _
  have hk : k ≠ 0 := Complex.exp_ne_zero _
  have hqk : q * k = 1 := by
    dsimp [q, k, rotation]
    rw [← Complex.exp_add]
    simp
  have hs := IsAlgClosed.splits (k := ℂ) f
  have hf : f ≠ 0 := fun h => h0 (by simp [h])
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf
  have hEval0 : f.coeff 0 = f.leadingCoeff * (f.roots.map (fun r => -r)).prod := by
    simpa [coeff_zero_eq_eval_zero] using hs.eval_eq_prod_roots 0
  have hRatio (r : ℂ) (hr : r ∈ f.roots) :
      (q * z - r) / (-r) = (z - k * r) / (-(k * r)) := by
    have hr0 := root_ne_zero h0 hr
    apply (div_eq_div_iff (neg_ne_zero.mpr hr0) (neg_ne_zero.mpr (mul_ne_zero hk hr0))).mpr
    linear_combination -(z * r) * hqk
  change (normalized f θ).eval z =
    (f.roots.map fun r => (z - k * r) / (-(k * r))).prod
  rw [normalized_eval, show rotation θ = q by rfl, hs.eval_eq_prod_roots, hEval0]
  rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left₀ hlc, mul_comm, ← div_eq_mul_inv,
    ← Multiset.prod_map_div]
  congr 1
  exact Multiset.map_congr rfl hRatio


private lemma ratio_arg (z w : ℂ) :
    z / w = (↑(‖z‖ / ‖w‖) : ℂ) * Complex.exp ((↑(Complex.arg z - Complex.arg w) : ℂ) * Complex.I) := by
  calc
    z / w = (‖z‖ * Complex.exp ((Complex.arg z : ℂ) * Complex.I)) /
      (‖w‖ * Complex.exp ((Complex.arg w : ℂ) * Complex.I)) := by
        rw [Complex.norm_mul_exp_arg_mul_I, Complex.norm_mul_exp_arg_mul_I]
    _ = _ := by
      rw [Complex.ofReal_div, Complex.ofReal_sub, sub_mul, Complex.exp_sub, div_mul_div_comm]

private lemma product_phases (s : Multiset ℂ) (amp φ : ℂ → ℝ) :
    (s.map (fun r => (amp r : ℂ) * Complex.exp ((φ r : ℂ) * Complex.I))).prod =
      (↑(s.map amp).prod : ℂ) * Complex.exp ((↑(s.map φ).sum : ℂ) * Complex.I) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, ih, Complex.ofReal_mul,
      Complex.ofReal_add, add_mul, Complex.exp_add]
    ring

private lemma pos_prod (s : Multiset ℂ) (amp : ℂ → ℝ) (h : ∀ r ∈ s, 0 < amp r) :
    0 < (s.map amp).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    exact mul_pos (h r (Multiset.mem_cons_self _ _))
      (ih fun q hq => h q (Multiset.mem_cons_of_mem hq))

noncomputable def totalPhase (f : ℂ[X]) (θ t : ℝ) : ℝ :=
  (f.roots.map fun r =>
    Complex.arg ((t : ℂ) - Complex.exp (-(θ : ℂ) * Complex.I) * r) -
    Complex.arg ((0 : ℂ) - Complex.exp (-(θ : ℂ) * Complex.I) * r)).sum

lemma totalPhase_zero (f : ℂ[X]) (θ : ℝ) : totalPhase f θ 0 = 0 := by
  simp [totalPhase]

lemma evalIm_eq_zero_iff (f : ℂ[X]) (h0 : f.coeff 0 ≠ 0) (θ t : ℝ)
    (hshift : ∀ r ∈ f.roots, (t : ℂ) - Complex.exp (-(θ : ℂ) * Complex.I) * r ≠ 0) :
    ((normalized f θ).eval (t : ℂ)).im = 0 ↔ Real.sin (totalPhase f θ t) = 0 := by
  let k := Complex.exp (-(θ : ℂ) * Complex.I)
  let amp (r : ℂ) := ‖(t : ℂ) - k * r‖ / ‖0 - k * r‖
  let φ (r : ℂ) := Complex.arg ((t : ℂ) - k * r) - Complex.arg (0 - k * r)
  have hpos : 0 < (f.roots.map amp).prod := by
    apply pos_prod
    intro r hr
    apply div_pos (norm_pos_iff.mpr (hshift r hr))
    rw [zero_sub]
    exact norm_pos_iff.mpr (neg_ne_zero.mpr (mul_ne_zero (Complex.exp_ne_zero _) (root_ne_zero h0 hr)))
  have he : (normalized f θ).eval (t : ℂ) =
      (↑(f.roots.map amp).prod : ℂ) * Complex.exp ((↑(f.roots.map φ).sum : ℂ) * Complex.I) := by
    rw [normalized_prod f h0]
    rw [← product_phases]
    congr 1
    apply Multiset.map_congr rfl
    intro r _
    simpa only [amp, φ, k, zero_sub] using
      ratio_arg ((t : ℂ) - k * r) (0 - k * r)
  rw [he, Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.exp_ofReal_mul_I_im, mul_eq_zero, hpos.ne', false_or]
  rfl

lemma sum_continuousOn (s : Multiset ℂ) (g : ℂ → ℝ → ℝ)
    (hg : ∀ r ∈ s, ContinuousOn (g r) (Set.Ici 0)) :
    ContinuousOn (fun t => (s.map fun r => g r t).sum) (Set.Ici 0) := by
  induction s using Multiset.induction_on with
  | empty => simpa only [Multiset.map_zero, Multiset.sum_zero] using
      (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Set.Ici 0))
  | cons r s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact (hg r (Multiset.mem_cons_self _ _)).add (ih fun q hq => hg q (Multiset.mem_cons_of_mem hq))

lemma sum_tendsto (s : Multiset ℂ) (g : ℂ → ℝ → ℝ) (l : ℂ → ℝ)
    (hg : ∀ r ∈ s, Tendsto (g r) atTop (𝓝 (l r))) :
    Tendsto (fun t => (s.map fun r => g r t).sum) atTop (𝓝 (s.map l).sum) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact (hg r (Multiset.mem_cons_self _ _)).add (ih fun q hq => hg q (Multiset.mem_cons_of_mem hq))

end HaymanRay

namespace HaymanPhase

noncomputable def angle (z : ℂ) : ℝ :=
  if Complex.arg z < 0 then Complex.arg z + 2 * π else Complex.arg z

noncomputable def phase (θ : ℝ) (r : ℂ) (t : ℝ) : ℝ :=
  Complex.arg ((t : ℂ) - Complex.exp (-(θ : ℂ) * Complex.I) * r)

theorem angle_nonneg (r : ℂ) : 0 ≤ angle r := by
  unfold angle
  split_ifs with h
  · linarith only [Complex.neg_pi_lt_arg r, Real.pi_pos]
  · exact le_of_not_gt h

theorem angle_lt_two_pi (r : ℂ) : angle r < 2 * π := by
  unfold angle
  split_ifs with h
  · linarith
  · linarith only [Complex.arg_le_pi r, Real.pi_pos]

theorem norm_mul_exp_angle (r : ℂ) :
    (‖r‖ : ℂ) * Complex.exp ((angle r : ℂ) * Complex.I) = r := by
  unfold angle
  split_ifs
  · have h : Complex.exp ((((2 * π : ℝ)) : ℂ) * Complex.I) = 1 := by
      push_cast
      exact Complex.exp_two_pi_mul_I
    rw [Complex.ofReal_add, add_mul, Complex.exp_add, h, mul_one,
      Complex.norm_mul_exp_arg_mul_I]
  · exact Complex.norm_mul_exp_arg_mul_I r

private lemma rotate_polar (θ : ℝ) (r : ℂ) :
    Complex.exp (-(θ : ℂ) * Complex.I) * r =
      (‖r‖ : ℂ) * Complex.exp (((angle r - θ : ℝ) : ℂ) * Complex.I) := by
  calc
    _ = Complex.exp (-(θ : ℂ) * Complex.I) *
        ((‖r‖ : ℂ) * Complex.exp ((angle r : ℂ) * Complex.I)) := by
          rw [norm_mul_exp_angle]
    _ = _ := by
      have h : -(θ : ℂ) * Complex.I + (angle r : ℂ) * Complex.I =
          ((angle r - θ : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [mul_left_comm, ← Complex.exp_add, h]

private lemma neg_exp_add_pi (θ : ℝ) :
    -Complex.exp ((θ : ℂ) * Complex.I) = Complex.exp (((θ + π : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]

private lemma neg_exp_sub_pi (θ : ℝ) :
    -Complex.exp ((θ : ℂ) * Complex.I) = Complex.exp (((θ - π : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.ofReal_sub, sub_mul, sub_eq_add_neg, Complex.exp_add, Complex.exp_neg,
    Complex.exp_pi_mul_I, inv_neg, inv_one, mul_neg_one]

private lemma arg_scaled_exp {s t : ℝ} (hs : 0 < s) (ht : t ∈ Set.Ioc (-π) π) :
    Complex.arg ((s : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) = t := by
  rw [Complex.exp_mul_I, Complex.arg_mul_cos_add_sin_mul_I hs ht]

theorem phase_zero {θ : ℝ} {r : ℂ} (hr : r ≠ 0)
    (hlo : -(2 * π) < angle r - θ) (hhi : angle r - θ < 2 * π) (hne : angle r ≠ θ) :
    phase θ r 0 = angle r - θ - π + (if angle r < θ then 2 * π else 0) := by
  unfold phase
  rw [Complex.ofReal_zero, zero_sub, rotate_polar, ← mul_neg]
  have hn : 0 < ‖r‖ := norm_pos_iff.2 hr
  by_cases hlt : angle r < θ
  · have ht : angle r - θ + π ∈ Set.Ioc (-π) π :=
      ⟨by linarith only [hlo], by linarith only [hlt]⟩
    rw [neg_exp_add_pi, arg_scaled_exp hn ht, if_pos hlt]
    ring
  · have hgt : θ < angle r := lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
    have ht : angle r - θ - π ∈ Set.Ioc (-π) π :=
      ⟨by linarith only [hgt], by linarith only [hhi]⟩
    rw [neg_exp_sub_pi, arg_scaled_exp hn ht, if_neg hlt, add_zero]

private lemma shifted_mem_slitPlane {θ t : ℝ} {r : ℂ} (hr : r ≠ 0)
    (hlo : -(2 * π) < angle r - θ) (hhi : angle r - θ < 2 * π) (hne : angle r ≠ θ) (ht : 0 ≤ t) :
    (t : ℂ) - Complex.exp (-(θ : ℂ) * Complex.I) * r ∈ Complex.slitPlane := by
  let z := Complex.exp (-(θ : ℂ) * Complex.I) * r
  have hz : z ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) hr
  have harg : Complex.arg (-z) < π := by
    have h := phase_zero hr hlo hhi hne
    change Complex.arg ((0 : ℂ) - z) = _ at h
    rw [zero_sub] at h
    rw [h]
    split_ifs with hlt
    · linarith only [hlt]
    · linarith only [hhi]
  have h0 : -z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff_arg.2 ⟨harg.ne, neg_ne_zero.2 hz⟩
  change (t : ℂ) - z ∈ Complex.slitPlane
  rw [Complex.mem_slitPlane_iff] at h0 ⊢
  rcases h0 with h | h
  · left
    simp only [Complex.neg_re] at h
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  · right
    simpa only [Complex.neg_im, Complex.sub_im, Complex.ofReal_im, zero_sub] using h

theorem shifted_ne_zero {θ t : ℝ} {r : ℂ} (hr : r ≠ 0)
    (hlo : -(2 * π) < angle r - θ) (hhi : angle r - θ < 2 * π) (hne : angle r ≠ θ) (ht : 0 ≤ t) :
    (t : ℂ) - Complex.exp (-(θ : ℂ) * Complex.I) * r ≠ 0 :=
  Complex.slitPlane_ne_zero (shifted_mem_slitPlane hr hlo hhi hne ht)

theorem phase_continuousOn {θ : ℝ} {r : ℂ} (hr : r ≠ 0)
    (hlo : -(2 * π) < angle r - θ) (hhi : angle r - θ < 2 * π) (hne : angle r ≠ θ) :
    ContinuousOn (phase θ r) (Set.Ici 0) := by
  exact Complex.continuousOn_arg.comp (Complex.continuous_ofReal.sub continuous_const).continuousOn
    (fun _ ht => shifted_mem_slitPlane hr hlo hhi hne ht)

theorem phase_tendsto (θ : ℝ) (r : ℂ) : Tendsto (phase θ r) atTop (𝓝 0) := by
  let z := Complex.exp (-(θ : ℂ) * Complex.I) * r
  have hinv : Tendsto (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).ofReal
  have hsmall : Tendsto (fun t : ℝ => (1 : ℂ) - ((t⁻¹ : ℝ) : ℂ) * z) atTop (𝓝 1) := by
    simpa only [zero_mul, sub_zero] using tendsto_const_nhds.sub (hinv.mul_const z)
  have harg1 : ContinuousAt Complex.arg 1 :=
    Complex.continuousAt_arg (Complex.mem_slitPlane_iff.2 (Or.inl (by simp)))
  have harg : Tendsto (fun t : ℝ => Complex.arg ((1 : ℂ) - ((t⁻¹ : ℝ) : ℂ) * z)) atTop (𝓝 0) := by
    simpa only [Complex.arg_one, Function.comp_def] using harg1.tendsto.comp hsmall
  refine harg.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hscale : (t : ℂ) * (1 - ((t⁻¹ : ℝ) : ℂ) * z) = (t : ℂ) - z := by
    rw [mul_sub, mul_one, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ ht.ne',
      Complex.ofReal_one, one_mul]
  calc
    _ = Complex.arg ((t : ℂ) * (1 - ((t⁻¹ : ℝ) : ℂ) * z)) := (Complex.arg_real_mul _ ht).symm
    _ = phase θ r t := by rw [hscale]; rfl

end HaymanPhase

open Filter Polynomial Set
open scoped Topology

namespace HaymanVariation

private noncomputable def imPolynomial (P : ℂ[X]) : ℝ[X] :=
  ∑ k ∈ P.support, monomial k (P.coeff k).im

private lemma coeff_imPolynomial (P : ℂ[X]) (k : ℕ) :
    (imPolynomial P).coeff k = (P.coeff k).im := by
  rw [imPolynomial, finsetSum_coeff, Finset.sum_eq_single k]
  · exact coeff_monomial_same _ _
  · intro j _ hj
    exact coeff_monomial_of_ne _ hj.symm
  · intro hk
    rw [notMem_support_iff.mp hk]
    simp

private lemma eval_imPolynomial (P : ℂ[X]) (t : ℝ) :
    (imPolynomial P).eval t = (P.eval (t : ℂ)).im := by
  simp only [imPolynomial, eval_finsetSum, eval_monomial, P.eval_eq_sum, Polynomial.sum_def,
    Complex.im_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Complex.ofReal_pow]
  simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add]

private lemma sign_variations_lt_card_support (Q : ℝ[X]) (hQ : Q ≠ 0) :
    Q.signVariations < Q.support.card := by
  generalize he : Q.support.card = n
  induction n using Nat.strong_induction_on generalizing Q with
  | h n ih =>
    have hc := Q.card_support_eraseLead_add_one hQ
    by_cases hE : Q.eraseLead = 0
    · have hm := Q.eraseLead_add_monomial_natDegree_leadingCoeff
      rw [hE, zero_add] at hm
      rw [← hm, signVariations_monomial]
      have hn : n = 1 := by simpa [hE, he] using hc.symm
      omega
    · have hL : Q.eraseLead.support.card < n := by omega
      have hV := ih _ hL Q.eraseLead hE rfl
      have hS := Q.signVariations_le_eraseLead_succ
      omega

private lemma exists_pos_eq_of_lt_limit {B : ℝ → ℝ} {b y : ℝ}
    (hB : ContinuousOn B (Ici 0)) (hB0 : B 0 = 0)
    (hBt : Tendsto B atTop (𝓝 b)) (hy0 : 0 < y) (hy : y < b) :
    ∃ t > 0, B t = y := by
  obtain ⟨T, hT, hyT⟩ :=
    ((eventually_gt_atTop (0 : ℝ)).and (hBt.eventually (Ioi_mem_nhds hy))).exists
  have hmem : y ∈ Icc (B 0) (B T) := ⟨hB0.symm ▸ hy0.le, hyT.le⟩
  obtain ⟨t, ht, hty⟩ := intermediate_value_Icc hT.le
    (hB.mono (fun _ hx => hx.1)) hmem
  have ht0 : t ≠ 0 := by
    intro he
    rw [he, hB0] at hty
    exact hy0.ne' hty.symm
  exact ⟨t, lt_of_le_of_ne ht.1 (Ne.symm ht0), hty⟩

/-- A real constant term consumes one support index, so the nonzero imaginary
coefficients allow at most two fewer positive roots than the size of the support. -/
theorem bound (P : ℂ[X]) (h0 : (P.coeff 0).im = 0) (hcoeff : P.coeff 0 ≠ 0)
    (A : ℝ → ℝ) (a : ℝ) (hA : ContinuousOn A (Ici 0)) (hA0 : A 0 = 0)
    (hAt : Tendsto A atTop (𝓝 a))
    (hIm : ∀ (t : ℝ), 0 ≤ t → ((P.eval (t : ℂ)).im = 0 ↔ Real.sin (A t) = 0)) :
    |a| ≤ ((P.support.card : ℝ) - 1) * Real.pi := by
  classical
  let Q := imPolynomial P
  have hmem0 : 0 ∈ P.support := mem_support_iff.mpr hcoeff
  have hPpos : 0 < P.support.card := Finset.card_pos.mpr ⟨0, hmem0⟩
  let n := P.support.card - 1
  have hnR : (n : ℝ) = (P.support.card : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ P.support.card), Nat.cast_one]
  have hsubset : Q.support ⊆ P.support.erase 0 := by
    intro k hk
    have hkn : (P.coeff k).im ≠ 0 := by
      simpa only [Q, mem_support_iff, coeff_imPolynomial] using hk
    have hk0 : k ≠ 0 := by
      intro he
      exact hkn (he.symm ▸ h0)
    exact Finset.mem_erase.mpr ⟨hk0, mem_support_iff.mpr (by
      intro he
      exact hkn (by simp [he]))⟩
  have hQcard : Q.support.card ≤ n := by
    simpa only [n, Finset.card_erase_of_mem hmem0] using Finset.card_le_card hsubset
  let B (t : ℝ) := |A t|
  have hB : ContinuousOn B (Ici 0) := hA.abs
  have hB0 : B 0 = 0 := by simp [B, hA0]
  have hBt : Tendsto B atTop (𝓝 |a|) := hAt.abs
  have hSin (t : ℝ) : Real.sin (B t) = 0 ↔ Real.sin (A t) = 0 := by
    change Real.sin |A t| = 0 ↔ Real.sin (A t) = 0
    by_cases ht : 0 ≤ A t
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg (lt_of_not_ge ht), Real.sin_neg, neg_eq_zero]
  have hZeros (t : ℝ) (ht : 0 ≤ t) : Q.eval t = 0 ↔ Real.sin (B t) = 0 := by
    change (imPolynomial P).eval t = 0 ↔ Real.sin (B t) = 0
    rw [eval_imPolynomial, hIm t ht, hSin]
  rw [← hnR]
  by_contra! hbad
  have habs0 : 0 < |a| := (mul_nonneg (Nat.cast_nonneg n) Real.pi_pos.le).trans_lt hbad
  by_cases hQ : Q = 0
  · let y := min (|a| / 2) (Real.pi / 2)
    have hy0 : 0 < y := lt_min (by linarith) (by linarith [Real.pi_pos])
    have hy : y < |a| := (min_le_left _ _).trans_lt (by linarith)
    have hypi : y < Real.pi := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
    obtain ⟨t, ht, hty⟩ := exists_pos_eq_of_lt_limit hB hB0 hBt hy0 hy
    have hsz := (hZeros t ht.le).mp (by simp [hQ])
    rw [hty] at hsz
    exact (Real.sin_pos_of_pos_of_lt_pi hy0 hypi).ne' hsz
  have hlevels (i : Fin n) : ∃ t > 0, B t = ((i.val + 1 : ℕ) : ℝ) * Real.pi := by
    have hi : ((i.val + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt i.isLt
    refine exists_pos_eq_of_lt_limit hB hB0 hBt (by positivity) ?_
    exact (mul_le_mul_of_nonneg_right hi Real.pi_pos.le).trans_lt hbad
  choose f hfpos hfB using hlevels
  have hfi : Function.Injective f := by
    intro i j he
    have hEq : ((i.val + 1 : ℕ) : ℝ) * Real.pi = ((j.val + 1 : ℕ) : ℝ) * Real.pi :=
      (hfB i).symm.trans ((congrArg B he).trans (hfB j))
    have hCast := mul_right_cancel₀ Real.pi_pos.ne' hEq
    have hNat : i.val + 1 = j.val + 1 := by exact_mod_cast hCast
    exact Fin.ext (by omega)
  let s := (Q.roots.filter (0 < ·)).toFinset
  have hsub : Finset.univ.image f ⊆ s := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    apply Multiset.mem_toFinset.mpr
    apply Multiset.mem_filter.mpr
    refine ⟨(Polynomial.mem_roots hQ).mpr ?_, hfpos i⟩
    apply (hZeros (f i) (hfpos i).le).mpr
    rw [hfB i]
    exact Real.sin_nat_mul_pi (i.val + 1)
  have hcard : n ≤ Q.roots.countP (0 < ·) := by
    rw [Multiset.countP_eq_card_filter]
    have hh := (Finset.card_le_card hsub).trans (Multiset.toFinset_card_le _)
    simpa only [Finset.card_image_of_injective _ hfi, Finset.card_univ, Fintype.card_fin] using hh
  exact (not_lt_of_ge (hcard.trans Q.roots_countP_pos_le_signVariations))
    ((sign_variations_lt_card_support Q hQ).trans_le hQcard)

end HaymanVariation

namespace HaymanRay

open HaymanPhase

def regular (f : ℂ[X]) (a : ℝ) : Prop :=
  ∀ z ∈ f.roots, angle z ≠ a ∧ -(2 * Real.pi) < angle z - a ∧ angle z - a < 2 * Real.pi

noncomputable def rayLimit (s : Multiset ℂ) (θ : ℝ) : ℝ :=
  (s.map fun r => -phase θ r 0).sum

lemma limit_bound (f : ℂ[X]) (h0 : f.coeff 0 ≠ 0) (θ : ℝ) (hθ : regular f θ) :
    |rayLimit f.roots θ| ≤ ((f.support.card : ℝ) - 1) * Real.pi := by
  have hC := normalized_constant f h0 θ
  have hCont : ContinuousOn (totalPhase f θ) (Set.Ici 0) := by
    change ContinuousOn (fun t => (f.roots.map fun r => phase θ r t - phase θ r 0).sum) (Set.Ici 0)
    apply sum_continuousOn
    intro r hr
    obtain ⟨hne, hlo, hhi⟩ := hθ r hr
    exact (phase_continuousOn (root_ne_zero h0 hr) hlo hhi hne).sub continuousOn_const
  have hlim : Tendsto (totalPhase f θ) atTop (𝓝 (rayLimit f.roots θ)) := by
    change Tendsto (fun t => (f.roots.map fun r => phase θ r t - phase θ r 0).sum) atTop
      (𝓝 (rayLimit f.roots θ))
    apply sum_tendsto
    intro r _
    simpa only [zero_sub] using (phase_tendsto θ r).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => phase θ r 0) atTop (𝓝 (phase θ r 0)))
  have hh := HaymanVariation.bound (normalized f θ) (by simp [hC]) (by simp [hC])
    (totalPhase f θ) (rayLimit f.roots θ) hCont (totalPhase_zero f θ) hlim (fun t ht =>
      evalIm_eq_zero_iff f h0 θ t fun r hr => by
        obtain ⟨hne, hlo, hhi⟩ := hθ r hr
        exact shifted_ne_zero (root_ne_zero h0 hr) hlo hhi hne ht)
  rwa [normalized_support f h0] at hh

private lemma one_root {a b : ℝ} {r : ℂ} (hr : r ≠ 0) (hab : a < b)
    (ha : angle r ≠ a ∧ -(2 * Real.pi) < angle r - a ∧ angle r - a < 2 * Real.pi)
    (hb : angle r ≠ b ∧ -(2 * Real.pi) < angle r - b ∧ angle r - b < 2 * Real.pi) :
    -phase b r 0 - (-phase a r 0) = b - a -
      (if a < angle r ∧ angle r < b then 2 * Real.pi else 0) := by
  rw [phase_zero hr ha.2.1 ha.2.2 ha.1, phase_zero hr hb.2.1 hb.2.2 hb.1]
  rcases (lt_or_gt_of_ne ha.1) with h | h
  · simp [h, h.trans hab, not_lt.mpr h.le]
  · rcases (lt_or_gt_of_ne hb.1) with h' | h'
    · simp [h, h', not_lt.mpr h.le]
      ring
    · simp [h, not_lt.mpr h.le, not_lt.mpr h'.le]

noncomputable def openCount (s : Multiset ℂ) (a b : ℝ) : ℕ :=
  s.countP (fun r => a < angle r ∧ angle r < b)

private lemma difference (s : Multiset ℂ) {a b : ℝ} (hab : a < b)
    (h0 : ∀ z ∈ s, z ≠ 0)
    (ha : ∀ z ∈ s, angle z ≠ a ∧ -(2 * Real.pi) < angle z - a ∧ angle z - a < 2 * Real.pi)
    (hb : ∀ z ∈ s, angle z ≠ b ∧ -(2 * Real.pi) < angle z - b ∧ angle z - b < 2 * Real.pi) :
    rayLimit s b - rayLimit s a =
      (b - a) * (s.card : ℝ) - 2 * Real.pi * (openCount s a b : ℝ) := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp [rayLimit, openCount]
  | cons r s ih =>
    have hmem := Multiset.mem_cons_self r s
    have hd := one_root (h0 r hmem) hab (ha r hmem) (hb r hmem)
    have htail := ih (fun z hz => h0 z (Multiset.mem_cons_of_mem hz))
      (fun z hz => ha z (Multiset.mem_cons_of_mem hz)) (fun z hz => hb z (Multiset.mem_cons_of_mem hz))
    simp only [rayLimit, Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, openCount,
      Multiset.countP_cons, Nat.cast_add, Nat.cast_one] at *
    split_ifs at * with hx <;> norm_num at * <;> linarith

lemma open_bound (f : ℂ[X]) (h0 : f.coeff 0 ≠ 0)
    (a b : ℝ) (hab : a < b) (ha : regular f a) (hb : regular f b) :
    |(openCount f.roots a b : ℝ) - (b - a) / (2 * Real.pi) * (f.natDegree : ℝ)| ≤
      (f.support.card : ℝ) - 1 := by
  have hd := difference f.roots hab (fun z hz => root_ne_zero h0 hz) ha hb
  rw [← (IsAlgClosed.splits (k := ℂ) f).natDegree_eq_card_roots] at hd
  have hπ : 0 < 2 * Real.pi := by positivity
  have hnorm :
      ((openCount f.roots a b : ℝ) - (b - a) / (2 * Real.pi) * (f.natDegree : ℝ)) *
        (2 * Real.pi) = rayLimit f.roots a - rayLimit f.roots b := by
    calc
      _ = 2 * Real.pi * (openCount f.roots a b : ℝ) - (b - a) * (f.natDegree : ℝ) := by
        field_simp
      _ = _ := by linarith only [hd]
  have hnorm' := congrArg abs hnorm
  rw [abs_mul, abs_of_pos hπ] at hnorm'
  apply (mul_le_mul_iff_of_pos_right hπ).mp
  rw [hnorm']
  calc
    _ ≤ |rayLimit f.roots a| + |rayLimit f.roots b| := abs_sub _ _
    _ ≤ ((f.support.card : ℝ) - 1) * Real.pi + ((f.support.card : ℝ) - 1) * Real.pi :=
      add_le_add (limit_bound f h0 a ha) (limit_bound f h0 b hb)
    _ = _ := by ring

end HaymanRay

namespace HaymanBoundary

open Filter Polynomial
open scoped Topology

noncomputable def angle (z : ℂ) : ℝ :=
  if Complex.arg z < 0 then Complex.arg z + 2 * Real.pi else Complex.arg z

lemma angle_range (z : ℂ) : 0 ≤ angle z ∧ angle z < 2 * Real.pi := by
  unfold angle
  split_ifs with h
  · constructor <;> linarith [Complex.neg_pi_lt_arg z, Real.pi_pos]
  · exact ⟨le_of_not_gt h, by linarith [Complex.arg_le_pi z, Real.pi_pos]⟩

/-- Every root avoids this endpoint, and its angle difference from it lies in (-2π,2π). -/
def RegularEndpoint (f : ℂ[X]) (x : ℝ) : Prop :=
  ∀ z ∈ f.roots, angle z ≠ x ∧
    -(2 * Real.pi) < angle z - x ∧ angle z - x < 2 * Real.pi

private lemma eventually_small {d : ℝ} (hd : 0 < d) :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < d :=
  nhdsWithin_le_nhds (Iio_mem_nhds hd)

private lemma eventually_small_when {P : Prop} {d : ℝ} (hd : P → 0 < d) :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), P → t < d := by
  classical
  by_cases hp : P
  · filter_upwards [eventually_small (hd hp)] with t ht using fun _ => ht
  · exact Eventually.of_forall fun _ h => (hp h).elim

private noncomputable def rightEnd (β t : ℝ) : ℝ :=
  β + (if β = 2 * Real.pi then -1 else 1) * t

private lemma eventual_endpoints (f : ℂ[X]) {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β)
    (hβ : β ≤ 2 * Real.pi) (hαlt : α < 2 * Real.pi) :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), α - t < rightEnd β t ∧
      RegularEndpoint f (α - t) ∧ RegularEndpoint f (rightEnd β t) ∧
      Erdos990.rootArgCount f (Set.Ioo (α - t) (rightEnd β t)) =
        Erdos990.rootArgCount f (Set.Icc α β) := by
  classical
  have hAll : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ∀ z ∈ f.roots,
      t < 2 * Real.pi - angle z ∧
      (angle z < α → t < α - angle z) ∧ (β < angle z → t < angle z - β) := by
    simp_rw [← Multiset.mem_toFinset]
    apply (eventually_all_finset f.roots.toFinset).mpr
    intro z _
    exact (eventually_small (sub_pos.mpr (angle_range z).2)).and
      ((eventually_small_when sub_pos.mpr).and (eventually_small_when sub_pos.mpr))
  have hPos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hShort : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), β < 2 * Real.pi → t < 2 * Real.pi - β :=
    eventually_small_when sub_pos.mpr
  filter_upwards [hAll, hPos, hShort, eventually_small (by positivity : 0 < 2 * Real.pi)]
    with t hGap ht hShort htPi
  have hRight : α - t < rightEnd β t ∧ 0 ≤ rightEnd β t ∧ rightEnd β t < 2 * Real.pi := by
    by_cases h : β = 2 * Real.pi
    · simp only [rightEnd, if_pos h, neg_mul, one_mul]
      exact ⟨by linarith, by linarith, by linarith⟩
    · have ht' := hShort (lt_of_le_of_ne hβ h)
      simp only [rightEnd, if_neg h, one_mul]
      exact ⟨by linarith, by linarith, by linarith⟩
  have leftSide (z : ℂ) (hz : z ∈ f.roots) :
      (angle z < α ∧ angle z < α - t) ∨ (α ≤ angle z ∧ α - t < angle z) := by
    by_cases h : angle z < α
    · exact Or.inl ⟨h, by linarith [(hGap z hz).2.1 h]⟩
    · exact Or.inr ⟨le_of_not_gt h, by linarith [le_of_not_gt h]⟩
  have rightSide (z : ℂ) (hz : z ∈ f.roots) :
      (β < angle z ∧ rightEnd β t < angle z) ∨ (angle z ≤ β ∧ angle z < rightEnd β t) := by
    by_cases h : β = 2 * Real.pi
    · right
      simp only [rightEnd, if_pos h, neg_mul, one_mul]
      exact ⟨by linarith [(angle_range z).2], by linarith [(hGap z hz).1]⟩
    · simp only [rightEnd, if_neg h, one_mul]
      by_cases hz' : β < angle z
      · exact Or.inl ⟨hz', by linarith [(hGap z hz).2.2 hz']⟩
      · exact Or.inr ⟨le_of_not_gt hz', by linarith [le_of_not_gt hz']⟩
  refine ⟨hRight.1, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨h0,_⟩ := angle_range z
    refine ⟨?_, by linarith, by linarith [(hGap z hz).1]⟩
    rcases leftSide z hz with ⟨_,h⟩ | ⟨_,h⟩
    · exact ne_of_lt h
    · exact ne_of_gt h
  · intro z hz
    obtain ⟨h0,hT⟩ := angle_range z
    obtain ⟨_,hb0,hbT⟩ := hRight
    refine ⟨?_, by linarith, by linarith⟩
    rcases rightSide z hz with ⟨_,h⟩ | ⟨_,h⟩
    · exact ne_of_gt h
    · exact ne_of_lt h
  · unfold Erdos990.rootArgCount
    refine @Multiset.countP_congr ℂ f.roots f.roots rfl _ _
      (fun _ => Classical.propDecidable _) (fun _ => Classical.propDecidable _) ?_
    intro z hz
    apply propext
    change angle z ∈ Set.Ioo (α - t) (rightEnd β t) ↔ angle z ∈ Set.Icc α β
    simp only [Set.mem_Ioo, Set.mem_Icc]
    rcases leftSide z hz with ⟨hL,hLt⟩ | ⟨hL,hLt⟩
    · simp [not_le.mpr hL, not_lt.mpr hLt.le]
    · rcases rightSide z hz with ⟨hR,hRt⟩ | ⟨hR,hRt⟩
      · simp [not_le.mpr hR, not_lt.mpr hRt.le]
      · simp [hL,hLt,hR,hRt]

/-- Extend an open-interval estimate with regular endpoints to all closed intervals in [0,2π]. -/
theorem closed_of_open (f : ℂ[X]) {C : ℝ} (hC : 0 ≤ C)
    (hOpen : ∀ a b : ℝ, a < b → RegularEndpoint f a → RegularEndpoint f b →
      |(Erdos990.rootArgCount f (Set.Ioo a b) : ℝ) -
        (b - a) / (2 * Real.pi) * (f.natDegree : ℝ)| ≤ C)
    (α β : ℝ) (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ 2 * Real.pi) :
    |(Erdos990.rootArgCount f (Set.Icc α β) : ℝ) -
      (β - α) / (2 * Real.pi) * (f.natDegree : ℝ)| ≤ C := by
  by_cases hαT : α = 2 * Real.pi
  · have hβT : β = 2 * Real.pi := le_antisymm hβ (hαT ▸ hαβ)
    have hzero : Erdos990.rootArgCount f (Set.Icc (2 * Real.pi) (2 * Real.pi)) = 0 := by
      unfold Erdos990.rootArgCount
      refine (@Multiset.countP_eq_zero ℂ _ (fun _ => Classical.propDecidable _) f.roots).mpr ?_
      intro z _ hz
      change 2 * Real.pi ≤ angle z ∧ angle z ≤ 2 * Real.pi at hz
      exact (not_le.mpr (angle_range z).2) hz.1
    rw [hαT, hβT, hzero]
    simpa using hC
  · let D (t : ℝ) :=
      |(Erdos990.rootArgCount f (Set.Icc α β) : ℝ) -
        (rightEnd β t - (α - t)) / (2 * Real.pi) * (f.natDegree : ℝ)|
    have hcont : Continuous D := by
      unfold D rightEnd
      fun_prop
    have hlim : Tendsto D (𝓝[>] (0 : ℝ)) (𝓝 (D 0)) :=
      hcont.continuousAt.mono_left nhdsWithin_le_nhds
    have hBound : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), D t ≤ C := by
      filter_upwards [eventual_endpoints f hα hαβ hβ (lt_of_le_of_ne (hαβ.trans hβ) hαT)]
        with t ht
      obtain ⟨hab,ha,hb,he⟩ := ht
      simpa only [D, he] using hOpen (α - t) (rightEnd β t) hab ha hb
    simpa [D, rightEnd] using le_of_tendsto hlim hBound

end HaymanBoundary

theorem OMA.solution : type_of% @Erdos990.erdos_990.variants.hayman := by
  intro f h0 α β hα hαβ hβ
  have hmem : 0 ∈ f.support := Polynomial.mem_support_iff.mpr h0
  have hcard : 1 ≤ f.support.card := Finset.card_pos.mpr ⟨0, hmem⟩
  have hC : 0 ≤ (f.support.card : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hcard)
  apply HaymanBoundary.closed_of_open f hC _ α β hα hαβ hβ
  intro a b hab ha hb
  have hcount : Erdos990.rootArgCount f (Set.Ioo a b) = HaymanRay.openCount f.roots a b := by
    unfold Erdos990.rootArgCount HaymanRay.openCount
    exact @Multiset.countP_congr ℂ f.roots f.roots rfl
      (fun z => (if Complex.arg z < 0 then Complex.arg z + 2 * Real.pi else Complex.arg z) ∈
        Set.Ioo a b)
      (fun z => a < HaymanPhase.angle z ∧ HaymanPhase.angle z < b)
      (fun _ => Classical.propDecidable _) (fun z =>
        inferInstanceAs (Decidable (a < HaymanPhase.angle z ∧ HaymanPhase.angle z < b)))
      (fun _ _ => rfl)
  rw [hcount]
  exact HaymanRay.open_bound f h0 a b hab ha hb