import FormalConjectures.ErdosProblems.«1048»
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.MeanInequalities

/-!
Pommerenke's bound on a component of the strict sublevel set.
https://doi.org/10.1307/mmj/1028998561
-/

open scoped BigOperators ComplexConjugate ENNReal

namespace PommerenkeCentroid

private theorem sum_sqdist_of_sum_zero {n : ℕ} (a : Fin n → ℂ)
    (ha : ∑ i, a i = 0) (z : ℂ) :
    ∑ i, Complex.normSq (z - a i) =
      (n : ℝ) * Complex.normSq z + ∑ i, Complex.normSq (a i) := by
  have hc : ∑ i, conj (a i) = 0 := by
    rw [← map_sum (starRingEnd ℂ), ha, map_zero]
  have hre : ∑ i, (z * conj (a i)).re = 0 := by
    change ∑ i, Complex.reLm (z * conj (a i)) = 0
    rw [← map_sum Complex.reLm, ← Finset.mul_sum, hc, mul_zero, map_zero]
  simp only [Complex.normSq_sub z, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hre, mul_zero, sub_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

private theorem prod_normSq_le_one {n : ℕ} (hn : 0 < n) (p : Fin n → ℂ)
    (hp : ∑ i, Complex.normSq (p i) ≤ n) : ‖∏ i, p i‖ ≤ 1 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let w : Fin n → ℝ := fun _ => (n : ℝ)⁻¹
  let v (i : Fin n) : ℝ := Complex.normSq (p i)
  have hw : ∑ i, w i = 1 := by
    simp [w, nsmul_eq_mul, hnR.ne']
  have hv : ∀ i, 0 ≤ v i := fun i => Complex.normSq_nonneg _
  have ham := Real.geom_mean_le_arith_mean_weighted Finset.univ w v
    (fun i _ => inv_nonneg.2 hnR.le) hw (fun i _ => hv i)
  have hmean : ∑ i, w i * v i ≤ 1 := by
    change (∑ i, (n : ℝ)⁻¹ * v i) ≤ 1
    rw [← Finset.mul_sum, inv_mul_eq_div]
    exact (div_le_iff₀ hnR).2 (by simpa using hp)
  have hgm : (∏ i, v i) ^ (n : ℝ)⁻¹ ≤ 1 := by
    rw [← Real.finsetProd_rpow Finset.univ v (fun i _ => hv i)]
    exact ham.trans hmean
  have hp' : ∏ i, v i ≤ 1 := by
    by_contra! hh
    have hh' := Real.rpow_lt_rpow zero_le_one hh (inv_pos.2 hnR)
    rw [Real.one_rpow] at hh'
    exact (not_lt_of_ge hgm) hh'
  change ∏ i, Complex.normSq (p i) ≤ 1 at hp'
  rw [← map_prod Complex.normSq, Complex.normSq_eq_norm_sq] at hp'
  exact (sq_le_sq₀ (norm_nonneg _) zero_le_one).1 (by simpa using hp')

theorem disk {n : ℕ} (hn : 0 < n) (a : Fin n → ℂ) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : ∀ i, ‖a i‖ ≤ r) :
    ∃ c : ℂ, ‖c‖ ≤ r ∧
      Metric.closedBall c (Real.sqrt (1 - r^2 + ‖c‖^2)) ⊆
        {z | ‖∏ i, (z - a i)‖ ≤ 1} := by
  let c := (∑ i, a i) / (n : ℂ)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hc : ‖c‖ ≤ r := by
    dsimp [c]
    rw [norm_div, Complex.norm_natCast]
    apply (div_le_iff₀ hnR).2
    calc
      ‖∑ i, a i‖ ≤ ∑ i, ‖a i‖ := norm_sum_le _ _
      _ ≤ ∑ _ : Fin n, r := Finset.sum_le_sum (fun i _ => ha i)
      _ = r * n := by simp [nsmul_eq_mul, mul_comm]
  refine ⟨c, hc, ?_⟩
  let b (i : Fin n) := a i - c
  have hb : ∑ i, b i = 0 := by
    simp only [b, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    dsimp [c]
    field_simp [hnC]
    ring
  have hvar : ∑ i, Complex.normSq (b i) ≤ (n : ℝ) * (r^2 - ‖c‖^2) := by
    have h := sum_sqdist_of_sum_zero b hb (-c)
    have hid (i : Fin n) : -c - b i = -a i := by dsimp [b]; abel
    simp only [hid, Complex.normSq_eq_norm_sq, norm_neg] at h
    have hsum : ∑ i, ‖a i‖^2 ≤ (n : ℝ) * r^2 := by
      calc
        _ ≤ ∑ _ : Fin n, r^2 := Finset.sum_le_sum
          (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (ha i) 2)
        _ = _ := by simp [nsmul_eq_mul]
    simp only [Complex.normSq_eq_norm_sq]
    nlinarith only [h, hsum]
  intro z hz
  change dist z c ≤ _ at hz
  rw [dist_eq_norm] at hz
  have hrad : 0 ≤ 1 - r^2 + ‖c‖^2 := by nlinarith [sq_nonneg ‖c‖]
  have hzc : ‖z - c‖^2 ≤ 1 - r^2 + ‖c‖^2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hz 2
    rwa [Real.sq_sqrt hrad] at h
  have hnorm := sum_sqdist_of_sum_zero b hb (z-c)
  have hid (i : Fin n) : z-c-b i = z-a i := by dsimp [b]; abel
  simp only [hid, Complex.normSq_eq_norm_sq] at hnorm
  change ‖∏ i, (z - a i)‖ ≤ 1
  apply prod_normSq_le_one hn
  simp only [Complex.normSq_eq_norm_sq] at hvar ⊢
  rw [hnorm]
  nlinarith only [hvar, mul_le_mul_of_nonneg_left hzc hnR.le]

private theorem far_side (c w : ℂ) (h : w ≠ c) (R : ℝ) (hR : 0 ≤ R) :
    ∃ u ∈ Metric.closedBall c R, dist w u = ‖w-c‖ + R := by
  have hd : 0 < ‖w-c‖ := norm_pos_iff.2 (sub_ne_zero.2 h)
  let t := R / ‖w-c‖
  have ht : 0 ≤ t := div_nonneg hR hd.le
  let u := c - t • (w-c)
  have hnorm : ‖t • (w-c)‖ = R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    exact div_mul_cancel₀ _ hd.ne'
  refine ⟨u, ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_eq_norm]
    have he : u-c = -(t • (w-c)) := by dsimp [u]; abel
    rw [he, norm_neg, hnorm]
  · rw [dist_eq_norm]
    have he : w-u = (1+t) • (w-c) := by
      change w - (c - t • (w-c)) = (1+t) • (w-c)
      rw [add_smul, one_smul]
      abel
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1+t),
      add_mul, one_mul]
    congr 1
    exact div_mul_cancel₀ _ hd.ne'

theorem diameter_witness {r : ℝ} (hr1 : r ≤ 1) {c w : ℂ} (hc : ‖c‖ ≤ r)
    (hw : 1 < ‖w‖) :
    ∃ u ∈ Metric.closedBall c (Real.sqrt (1 - r^2 + ‖c‖^2)), 2 - r < dist w u := by
  let R := Real.sqrt (1 - r^2 + ‖c‖^2)
  have hr : 0 ≤ r := (norm_nonneg c).trans hc
  have hr2 : r^2 ≤ 1 := by simpa using pow_le_pow_left₀ hr hr1 2
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R^2 = 1 - r^2 + ‖c‖^2 := Real.sq_sqrt (by linarith [sq_nonneg ‖c‖])
  have hbase : 0 ≤ 1 - r + ‖c‖ := by linarith [norm_nonneg c]
  have hprod := mul_nonneg (sub_nonneg.mpr hr1) (sub_nonneg.mpr hc)
  have hR : 1 - r + ‖c‖ ≤ R := (sq_le_sq₀ hbase hR0).1 (by nlinarith only [hR2, hprod])
  have hwc : w ≠ c := by
    rintro rfl
    exact (not_lt_of_ge (hc.trans hr1)) hw
  obtain ⟨u, hu, hdu⟩ := far_side c w hwc R hR0
  have ht : ‖w‖ ≤ ‖w-c‖ + ‖c‖ := by
    simpa only [sub_add_cancel] using norm_add_le (w-c) c
  exact ⟨u, hu, by rw [hdu]; linarith only [hw, ht, hR]⟩

end PommerenkeCentroid

open Set Polynomial
open scoped BigOperators ComplexConjugate ENNReal

private theorem OMA.escape_prod_index {R M : Type*} [CommMonoid M] (s : Multiset R)
    (g : R → M) : (s.map g).prod = ∏ i : Fin s.toList.length, g (s.toList.get i) := by
  rw [← List.prod_ofFn]
  change _ = (List.ofFn (g ∘ s.toList.get)).prod
  rw [← List.map_ofFn, List.ofFn_get]
  simp

private theorem OMA.reciprocal_factor_norm (a z : ℂ) (ha : ‖a‖ ≤ 1) (hz : ‖z‖ ≤ 1) :
    ‖z - a‖ ≤ ‖1 - conj a * z‖ := by
  have hEq : ‖1 - conj a * z‖ ^ 2 - ‖z - a‖ ^ 2 =
      (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re,
      Complex.one_im]
    ring
  have ha₂ : ‖a‖ ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg a) ha 2
  have hz₂ : ‖z‖ ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg z) hz 2
  have hsq : ‖z - a‖ ^ 2 ≤ ‖1 - conj a * z‖ ^ 2 := by
    linarith [mul_nonneg (sub_nonneg.mpr ha₂) (sub_nonneg.mpr hz₂)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by decide : (2 : ℕ) ≠ 0)).mp hsq

private theorem OMA.positive_degree_eval_open (f : ℂ[X]) (hn : 0 < f.natDegree) :
    IsOpenMap f.eval := by
  have ha : AnalyticOnNhd ℂ f.eval univ := fun z _ => f.differentiable.analyticAt z
  rcases ha.is_constant_or_isOpenMap with ⟨c, hc⟩ | ho
  · have heq : f = C c := Polynomial.funext (fun z => by simpa using hc z)
    rw [heq, natDegree_C] at hn
    omega
  · exact ho

private theorem OMA.strict_component0_escapes_unit (f : ℂ[X]) (hf : f.Monic)
    (hr : ∀ z ∈ f.roots, ‖z‖ ≤ 1) (hne : f ≠ X ^ f.natDegree)
    (h0 : (0 : ℂ) ∈ Erdos1048.openLevelSet f) :
    ∃ w ∈ connectedComponentIn (Erdos1048.openLevelSet f) 0, 1 < ‖w‖ := by
  classical
  let S := Erdos1048.openLevelSet f
  let K := connectedComponentIn S (0 : ℂ)
  let L := f.roots.toList
  let a : Fin L.length → ℂ := L.get
  have hL : L.length = f.natDegree := by
    simpa [L] using (IsAlgClosed.splits f).natDegree_eq_card_roots.symm
  have hrootNorm (i : Fin L.length) : ‖a i‖ ≤ 1 :=
    hr (a i) (Multiset.mem_toList.mp (List.get_mem L i))
  have hfFact : f = ∏ i, (X - C (a i)) :=
    ((IsAlgClosed.splits f).eq_prod_roots_of_monic hf).trans (OMA.escape_prod_index _ _)
  have hfEval (z : ℂ) : f.eval z = ∏ i, (z - a i) := by
    conv_lhs => rw [hfFact]
    simp [eval_prod]
  have hSopen : IsOpen S := isOpen_lt f.continuous.norm continuous_const
  have hKopen : IsOpen K := hSopen.connectedComponentIn
  have h0K : (0 : ℂ) ∈ K := mem_connectedComponentIn h0
  have hKS : K ⊆ S := connectedComponentIn_subset S _
  have hpart : closure K ∩ S ⊆ K := by
    have hconn : IsPreconnected K := (isConnected_connectedComponentIn_iff.mpr h0).isPreconnected
    have hpre : IsPreconnected (closure K ∩ S) :=
      hconn.subset_closure (fun z hz => ⟨subset_closure hz, hKS hz⟩) inter_subset_left
    exact hpre.subset_connectedComponentIn ⟨subset_closure h0K, h0⟩ inter_subset_right
  by_contra! hKnorm
  have hKunit : K ⊆ Metric.closedBall (0 : ℂ) 1 := by
    intro z hz
    simpa only [Metric.mem_closedBall, dist_zero_right] using hKnorm z hz
  have hClunit : closure K ⊆ Metric.closedBall (0 : ℂ) 1 :=
    closure_minimal hKunit Metric.isClosed_closedBall
  have hKstrict (z : ℂ) (hz : z ∈ K) : ‖z‖ < 1 := by
    have hi : z ∈ interior K := by rw [hKopen.interior_eq]; exact hz
    have hb := interior_mono hKunit hi
    rw [interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)] at hb
    simpa only [Metric.mem_ball, dist_zero_right] using hb
  let g : ℂ[X] := ∏ i, (1 - C (conj (a i)) * X)
  have hgEval (z : ℂ) : g.eval z = ∏ i, (1 - conj (a i) * z) := by
    simp [g, eval_prod]
  have hg0 : g.eval 0 = 1 := by simp [hgEval]
  have hnorm_ge (z : ℂ) (hz : z ∈ closure K) : ‖f.eval z‖ ≤ ‖g.eval z‖ := by
    rw [hfEval, hgEval, norm_prod, norm_prod]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ =>
      OMA.reciprocal_factor_norm (a i) z (hrootNorm i) (by simpa using hClunit hz))
  have hgNz (z : ℂ) (hz : z ∈ closure K) : g.eval z ≠ 0 := by
    intro hgEq
    have hfEq : f.eval z = 0 := by simpa [hgEq] using hnorm_ge z hz
    have hzS : z ∈ S := by
      change ‖f.eval z‖ < 1
      simp [hfEq]
    have hlt := hKstrict z (hpart ⟨hz, hzS⟩)
    rw [hgEval, Finset.prod_eq_zero_iff] at hgEq
    obtain ⟨i, _, hi⟩ := hgEq
    have heq : conj (a i) * z = 1 := (sub_eq_zero.mp hi).symm
    have hnprod := congrArg norm heq
    rw [norm_mul, Complex.norm_conj, norm_one] at hnprod
    have hh := mul_le_mul_of_nonneg_right (hrootNorm i) (norm_nonneg z)
    linarith
  have hboundary (z : ℂ) (hz : z ∈ frontier K) : 1 ≤ ‖g.eval z‖ := by
    have hfGe : 1 ≤ ‖f.eval z‖ := by
      by_contra! hlt
      apply hz.2
      rw [hKopen.interior_eq]
      exact hpart ⟨hz.1, hlt⟩
    exact hfGe.trans (hnorm_ge z hz.1)
  have hdiff : DiffContOnCl ℂ (fun z : ℂ => (g.eval z)⁻¹) K :=
    (g.differentiable.differentiableOn.inv hgNz).diffContOnCl
  have hgBig (z : ℂ) (hz : z ∈ K) : 1 ≤ ‖g.eval z‖ := by
    have hle := Complex.norm_le_of_forall_mem_frontier_norm_le
      (Metric.isBounded_closedBall.subset hKunit) hdiff
      (C := 1) (fun w hw => by rw [norm_inv]; exact inv_le_one_of_one_le₀ (hboundary w hw))
      (subset_closure hz)
    rw [norm_inv] at hle
    exact (inv_le_one₀ (norm_pos_iff.mpr (hgNz z (subset_closure hz)))).mp hle
  have haNe : ∃ i, a i ≠ 0 := by
    by_contra! hall
    apply hne
    rw [hfFact]
    simp [hall, hL]
  obtain ⟨j, hj⟩ := haNe
  have hconj : conj (a j) ≠ 0 := by simpa using hj
  have hgZero : g.eval (conj (a j))⁻¹ = 0 := by
    rw [hgEval]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [hconj]
  have han : AnalyticOnNhd ℂ g.eval univ := fun z _ => g.differentiable.analyticAt z
  rcases han.is_constant_or_isOpenMap with ⟨c, hconst⟩ | hmap
  · exact one_ne_zero (hg0.symm.trans ((hconst 0).trans
      ((hconst ((conj (a j))⁻¹)).symm.trans hgZero)))
  · have hclosure : (1 : ℂ) ∈ closure (Metric.ball 0 1) := by
      rw [closure_ball _ (by norm_num : (1 : ℝ) ≠ 0), Metric.mem_closedBall,
        dist_zero_right, norm_one]
    obtain ⟨w, hw, hwball⟩ := mem_closure_iff.mp hclosure (g.eval '' K)
      (hmap _ hKopen) ⟨0, h0K, hg0⟩
    obtain ⟨z, hz, rfl⟩ := hw
    exact (not_lt_of_ge (hgBig z hz)) (by simpa [Metric.mem_ball, dist_zero_right] using hwball)

private theorem OMA.strict_component0_diameter (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (f : ℂ[X]) (hf : f.Monic) (hn : 0 < f.natDegree)
    (hroots : ∀ z ∈ f.roots, ‖z‖ ≤ r) (h0 : (0 : ℂ) ∈ Erdos1048.openLevelSet f) :
    ENNReal.ofReal (2 - r) < Metric.ediam (connectedComponentIn (Erdos1048.openLevelSet f) 0) := by
  let S := Erdos1048.openLevelSet f
  let K := connectedComponentIn S (0 : ℂ)
  change ENNReal.ofReal (2 - r) < Metric.ediam K
  have finish {x y : ℂ} (hx : x ∈ closure K) (hy : y ∈ closure K)
      (hxy : 2 - r < dist x y) : ENNReal.ofReal (2 - r) < Metric.ediam K := by
    rw [← Metric.ediam_closure]
    refine lt_of_lt_of_le ?_ (Metric.edist_le_ediam_of_mem hx hy)
    rw [edist_dist]
    exact ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hxy, by linarith only [hr1, hxy]⟩
  by_cases heq : f = X ^ f.natDegree
  · have hB : Metric.ball (0 : ℂ) 1 ⊆ S := by
      intro z hz
      change ‖f.eval z‖ < 1
      rw [heq, eval_pow, eval_X, norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) (by simpa [Metric.mem_ball, dist_zero_right] using hz) hn.ne'
    have hK : Metric.ball (0 : ℂ) 1 ⊆ K :=
      (convex_ball 0 1).isPreconnected.subset_connectedComponentIn
        (Metric.mem_ball_self zero_lt_one) hB
    have hC : Metric.closedBall (0 : ℂ) 1 ⊆ closure K := by
      rw [← closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
      exact closure_mono hK
    have hx : (1 : ℂ) ∈ closure K := hC (by simp [Metric.mem_closedBall, dist_zero_right])
    have hy : (-1 : ℂ) ∈ closure K := hC (by simp [Metric.mem_closedBall, dist_zero_right])
    have hdist : dist (1 : ℂ) (-1) = 2 := by
      rw [dist_eq_norm, show (1 : ℂ) - (-1) = ((2:ℝ):ℂ) by push_cast; ring]
      norm_num
    exact finish hx hy (by rw [hdist]; linarith only [hr])
  · obtain ⟨w, hw, hw1⟩ := OMA.strict_component0_escapes_unit f hf
      (fun z hz => (hroots z hz).trans hr1) heq h0
    rcases hr1.eq_or_lt with hr_eq | hr_lt
    · apply finish (subset_closure hw) (subset_closure (mem_connectedComponentIn h0))
      norm_num [hr_eq, dist_zero_right]
      exact hw1
    · let L := f.roots.toList
      let a : Fin L.length → ℂ := L.get
      have hL : L.length = f.natDegree := by
        simpa [L] using (IsAlgClosed.splits f).natDegree_eq_card_roots.symm
      have ha (i : Fin L.length) : ‖a i‖ ≤ r :=
        hroots (a i) (Multiset.mem_toList.mp (List.get_mem L i))
      have hfFact : f = ∏ i, (X - C (a i)) :=
        ((IsAlgClosed.splits f).eq_prod_roots_of_monic hf).trans (OMA.escape_prod_index _ _)
      have hfEval (z : ℂ) : f.eval z = ∏ i, (z - a i) := by
        conv_lhs => rw [hfFact]
        simp [eval_prod]
      obtain ⟨c, hc, hdisk⟩ := PommerenkeCentroid.disk (hL.symm ▸ hn) a hr.le hr1 ha
      let R := Real.sqrt (1 - r^2 + ‖c‖^2)
      have hr2 : r^2 < 1 := by
        simpa only [one_pow] using pow_lt_pow_left₀ hr_lt hr.le (by decide : 2 ≠ 0)
      have hsq : R^2 = 1 - r^2 + ‖c‖^2 := Real.sq_sqrt (by linarith [sq_nonneg ‖c‖])
      have hrc : ‖c‖ < R :=
        (sq_lt_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1 (by linarith only [hsq, hr2])
      have hpos : 0 < R := (norm_nonneg c).trans_lt hrc
      have hzero : (0 : ℂ) ∈ Metric.ball c R := by
        simpa only [Metric.mem_ball, dist_zero_left] using hrc
      have hB : Metric.ball c R ⊆ S := by
        intro z hz
        change ‖f.eval z‖ < 1
        by_contra! hlarge
        let T := f.eval '' Metric.ball c R
        have hTo : IsOpen T := (OMA.positive_degree_eval_open f hn) _ Metric.isOpen_ball
        have hTout : T ⊆ Metric.closedBall (0 : ℂ) 1 := by
          rintro _ ⟨u, hu, rfl⟩
          rw [Metric.mem_closedBall, dist_zero_right]
          change ‖f.eval u‖ ≤ 1
          rw [hfEval]
          exact hdisk (Metric.ball_subset_closedBall hu)
        have hins : f.eval z ∈ interior T := by
          rw [hTo.interior_eq]
          exact ⟨z, hz, rfl⟩
        have hsmall := interior_mono hTout hins
        rw [interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)] at hsmall
        exact hlarge.not_gt (by simpa [Metric.mem_ball, dist_zero_right] using hsmall)
      have hBK : Metric.ball c R ⊆ K :=
        (convex_ball c R).isPreconnected.subset_connectedComponentIn hzero hB
      have hCK : Metric.closedBall c R ⊆ closure K := by
        rw [← closure_ball _ hpos.ne']
        exact closure_mono hBK
      obtain ⟨u, hu, hwu⟩ := PommerenkeCentroid.diameter_witness hr1 hc hw1
      exact finish (subset_closure hw) (hCK hu) hwu

private theorem OMA.unit_root_strict_component_root (p : ℂ[X]) (hmap : IsOpenMap p.eval)
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

private theorem OMA.lemniscate_unit_roots_diam_gt_one (f : ℂ[X]) (hf : f.Monic)
    (hn : 0 < f.natDegree) (hr : ∀ z ∈ f.roots, ‖z‖ = 1) :
    ∃ z ∈ Erdos1048.openLevelSet f, (1 : ℝ≥0∞) <
      Metric.ediam (connectedComponentIn (Erdos1048.openLevelSet f) z) := by
  classical
  let U := Erdos1048.openLevelSet f
  let L := f.roots.toList
  let a : Fin L.length → ℂ := L.get
  have ha (i : Fin L.length) : ‖a i‖ = 1 :=
    hr (a i) (Multiset.mem_toList.mp (List.get_mem L i))
  have hEval (z : ℂ) : f.eval z = ∏ i, (z - a i) :=
    ((IsAlgClosed.splits f).eval_eq_prod_roots_of_monic hf z).trans (OMA.escape_prod_index _ _)
  have h0norm : ‖f.eval 0‖ = 1 := by simp [hEval, norm_prod, ha]
  have hOpen : IsOpen U := isOpen_lt f.continuous.norm continuous_const
  have hBounded : Bornology.IsBounded U := by
    refine Metric.isBounded_ball.subset (t := Metric.ball (0 : ℂ) 2) ?_
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    by_contra! hZ
    have hge : 1 ≤ ‖f.eval z‖ := by
      rw [hEval, norm_prod]
      apply Finset.one_le_prod
      intro i _
      have hi := norm_add_le (z - a i) (a i)
      rw [sub_add_cancel, ha] at hi
      linarith
    exact (not_lt_of_ge hge) hz
  have hmap : IsOpenMap f.eval := by
    have han : AnalyticOnNhd ℂ f.eval univ := fun v _ => f.differentiable.analyticAt v
    rcases han.is_constant_or_isOpenMap with ⟨w, heq⟩ | hopen
    · have hfc : f = C w := Polynomial.funext (fun v => by simpa using heq v)
      rw [hfc, natDegree_C] at hn
      omega
    · exact hopen
  have h0 : (0 : ℂ) ∈ closure U := by
    have hb : f.eval 0 ∈ closure (Metric.ball (0 : ℂ) 1) := by
      rw [closure_ball _ (by norm_num : (1 : ℝ) ≠ 0), Metric.mem_closedBall, dist_zero_right, h0norm]
    apply mem_closure_iff.mpr
    intro V hV h0V
    obtain ⟨w, ⟨v, hv, rfl⟩, hw⟩ := mem_closure_iff.mp hb (f.eval '' V)
      (hmap _ hV) ⟨0, h0V, rfl⟩
    exact ⟨v, hv, by simpa [U, Erdos1048.openLevelSet, Metric.mem_ball, dist_zero_right] using hw⟩
  let R := f.roots.toFinset
  let K (r : R) := connectedComponentIn U r.1
  have hRootsU (r : R) : r.1 ∈ U := by
    have hr0 : f.eval r.1 = 0 := (mem_roots hf.ne_zero).1 (Multiset.mem_toFinset.mp r.2)
    change ‖f.eval r.1‖ < 1
    simp [hr0]
  have hcover : U = ⋃ r : R, K r := by
    apply Subset.antisymm
    · intro z hz
      obtain ⟨r, hrK, hr0⟩ := unit_root_strict_component_root f hmap zero_lt_one hBounded hz
      have hrR : r ∈ R := Multiset.mem_toFinset.mpr ((mem_roots hf.ne_zero).2 hr0)
      let i : R := ⟨r, hrR⟩
      apply mem_iUnion.mpr
      refine ⟨i, ?_⟩
      change z ∈ connectedComponentIn U r
      change r ∈ connectedComponentIn U z at hrK
      rw [← connectedComponentIn_eq hrK]
      exact mem_connectedComponentIn hz
    · exact iUnion_subset fun r => connectedComponentIn_subset _ _
  rw [hcover, closure_iUnion_of_finite, mem_iUnion] at h0
  obtain ⟨r, h0K⟩ := h0
  have hrK : r.1 ∈ K r := mem_connectedComponentIn (hRootsU r)
  have hw : ∃ w ∈ K r, 1 < ‖w‖ := by
    by_contra! h
    have hsub : K r ⊆ Metric.closedBall (0 : ℂ) 1 := by
      intro w hw
      simpa [Metric.mem_closedBall, dist_zero_right] using h w hw
    have hOpenK : IsOpen (K r) := hOpen.connectedComponentIn
    have hri : r.1 ∈ interior (K r) := by rw [hOpenK.interior_eq]; exact hrK
    have hBall := interior_mono hsub hri
    rw [interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)] at hBall
    have hnlt : ‖r.1‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hBall
    exact (not_lt_of_ge (hr r.1 (Multiset.mem_toFinset.mp r.2)).ge) hnlt
  obtain ⟨w, hwK, hw⟩ := hw
  refine ⟨r.1, hRootsU r, ?_⟩
  have hwdist : (1 : ℝ≥0∞) < edist w 0 := by
    rw [edist_dist, dist_zero_right, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg zero_le_one).2 hw
  have hle := Metric.edist_le_ediam_of_mem (subset_closure hwK) h0K
  rw [Metric.ediam_closure] at hle
  exact hwdist.trans_le hle

theorem OMA.solution : type_of% @Erdos1048.erdos_1048.variants.r_le_one := by
  intro r hr hr1 f hf hd hroots
  classical
  have hn : 0 < f.natDegree := by
    rw [degree_eq_natDegree hf.ne_zero] at hd
    exact Nat.succ_le_iff.mp (by exact_mod_cast hd : 1 ≤ f.natDegree)
  by_cases h0 : (0 : ℂ) ∈ Erdos1048.openLevelSet f
  · refine ⟨0, h0, OMA.strict_component0_diameter r hr hr1 f hf hn hroots h0⟩
  · have hunit (z : ℂ) (hz : z ∈ f.roots) : ‖z‖ = 1 := by
      apply le_antisymm ((hroots z hz).trans hr1)
      by_contra! hlt
      apply h0
      let L := f.roots.toList
      let a : Fin L.length → ℂ := L.get
      have ha (i : Fin L.length) : ‖a i‖ ≤ 1 :=
        (hroots (a i) (Multiset.mem_toList.mp (List.get_mem L i))).trans hr1
      have hfFact : f = ∏ i, (X - C (a i)) :=
        ((IsAlgClosed.splits f).eq_prod_roots_of_monic hf).trans (OMA.escape_prod_index _ _)
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp (Multiset.mem_toList.mpr hz)
      have hfEval (w : ℂ) : f.eval w = ∏ i, (w - a i) := by
        conv_lhs => rw [hfFact]
        simp [eval_prod]
      change ‖f.eval 0‖ < 1
      simp only [hfEval, norm_prod, zero_sub, norm_neg]
      rw [← Finset.mul_prod_erase Finset.univ (fun i => ‖a i‖) (Finset.mem_univ j)]
      have hrest : ∏ i ∈ Finset.univ.erase j, ‖a i‖ ≤ 1 :=
        Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => ha i)
      apply (mul_le_of_le_one_right (norm_nonneg _) hrest).trans_lt
      have hget : L.get j = z := hj
      simpa only [a, hget] using hlt
    have hcard : 0 < f.roots.card := (IsAlgClosed.splits f).natDegree_eq_card_roots ▸ hn
    obtain ⟨z, hz⟩ := Multiset.card_pos_iff_exists_mem.mp hcard
    have hr_eq : r = 1 := le_antisymm hr1 (by simpa only [hunit z hz] using hroots z hz)
    norm_num [hr_eq]
    exact OMA.lemniscate_unit_roots_diam_gt_one f hf hn hunit