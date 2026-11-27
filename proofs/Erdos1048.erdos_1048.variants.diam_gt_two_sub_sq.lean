import FormalConjectures.ErdosProblems.«1048»
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.MeanInequalities

/-!
Pommerenke's component diameter bound. The centroid disk and the reciprocal polynomial
are the two ingredients of Theorem 3.
https://doi.org/10.1307/mmj/1028998561
-/

open scoped BigOperators ComplexConjugate

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

theorem diameter_witness {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) {c : ℂ} (hc : ‖c‖ ≤ r)
    {T : Set ℂ}
    (hball : Metric.closedBall c (Real.sqrt (1 - r^2 + ‖c‖^2)) ⊆ T)
    {w : ℂ} (hw : w ∈ T) (hw1 : 1 < ‖w‖) :
    ∃ x ∈ T, ∃ y ∈ T, 2 - r^2 < dist x y := by
  let R := Real.sqrt (1 - r^2 + ‖c‖^2)
  have hr2 : r^2 ≤ 1 := by simpa using pow_le_pow_left₀ hr hr1 2
  have h0 : 0 ≤ 1 - r^2 + ‖c‖^2 := by nlinarith [sq_nonneg ‖c‖]
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R^2 = 1 - r^2 + ‖c‖^2 := Real.sq_sqrt h0
  by_cases hsmall : 2 * ‖c‖ ≤ r^2
  · have hA : 0 ≤ 1 + ‖c‖ - r^2 := by linarith [norm_nonneg c]
    have hprod := mul_nonneg (sub_nonneg.2 hr2) (sub_nonneg.2 hsmall)
    have hSq : (1 + ‖c‖ - r^2)^2 ≤ R^2 := by nlinarith only [hprod, hR2]
    have hR : 1 + ‖c‖ - r^2 ≤ R := (sq_le_sq₀ hA hR0).1 hSq
    have hwc : w ≠ c := by
      intro he
      subst w
      exact (not_lt_of_ge (hc.trans hr1)) hw1
    obtain ⟨u, hu, hdu⟩ := far_side c w hwc R hR0
    have ht : ‖w‖ ≤ ‖w-c‖ + ‖c‖ := by
      simpa only [sub_add_cancel] using norm_add_le (w-c) c
    refine ⟨w, hw, u, hball hu, ?_⟩
    rw [hdu]
    linarith only [hw1, ht, hR]
  · have hlarge : r^2 / 2 < ‖c‖ := by linarith
    have hbase : 0 ≤ 1 - r^2 / 2 := by linarith
    have hpos := pow_lt_pow_left₀ hlarge (by positivity : 0 ≤ r^2 / 2) (show (2:ℕ) ≠ 0 by decide)
    have hSq : (1-r^2/2)^2 < R^2 := by nlinarith only [hpos, hR2]
    have hR : 1 - r^2 / 2 < R := (sq_lt_sq₀ hbase hR0).1 hSq
    have hposR : 0 < R := hbase.trans_lt hR
    let z := c + (R : ℂ)
    have hz : ‖z-c‖ = R := by
      have he : z-c = (R : ℂ) := by dsimp [z]; abel
      rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR0]
    have hzc : z ≠ c := by
      intro he
      have hzero : ‖z-c‖ = 0 := by simp [he]
      exact hposR.ne' (hz.symm.trans hzero)
    obtain ⟨u, hu, hdu⟩ := far_side c z hzc R hR0
    have hzball : z ∈ Metric.closedBall c R := by
      rw [Metric.mem_closedBall, dist_eq_norm, hz]
    refine ⟨z, hball hzball, u, hball hu, ?_⟩
    rw [hdu, hz]
    linarith only [hR]

end PommerenkeCentroid

open Set Polynomial
open scoped BigOperators ComplexConjugate

private theorem OMA.escape_prod_index {R M : Type*} [CommMonoid M] (s : Multiset R)
    (g : R → M) : (s.map g).prod = ∏ i : Fin s.toList.length, g (s.toList.get i) := by
  rw [← List.prod_ofFn]
  change _ = (List.ofFn (g ∘ s.toList.get)).prod
  rw [← List.map_ofFn, List.ofFn_get]
  simp

private theorem OMA.escape_sublevel_compact (p : ℂ[X]) (hp : p.Monic)
    (hdeg : 0 < p.natDegree) (c : ℝ) (hc : 0 ≤ c) :
    IsCompact {z : ℂ | ‖p.eval z‖ ≤ c} := by
  classical
  have hclosed : IsClosed {z : ℂ | ‖p.eval z‖ ≤ c} := isClosed_le p.continuous.norm continuous_const
  have hfin : (p.rootSet ℂ).Finite := p.rootSet_finite _
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (0 : ℂ)).mp hfin.isBounded
  have hroot (r : ℂ) (hr : r ∈ p.roots) : ‖r‖ < R := by
    have he : p.eval r = 0 := (mem_roots hp.ne_zero).1 hr
    have hrC : r ∈ p.rootSet ℂ := hp.mem_rootSet.mpr (by simpa using he)
    simpa [Metric.mem_ball, dist_zero_right] using hR hrC
  refine Metric.isCompact_of_isClosed_isBounded hclosed
    (Metric.isBounded_ball.subset (t := Metric.ball (0 : ℂ) (R + c + 1)) ?_)
  intro z hz
  rw [Metric.mem_ball, dist_zero_right]
  by_contra! h
  have hbound (i : Fin p.roots.toList.length) : c + 1 ≤ ‖z - p.roots.toList.get i‖ := by
    have hr := hroot (p.roots.toList.get i) (Multiset.mem_toList.mp (List.get_mem _ i))
    have ht := norm_add_le (z - p.roots.toList.get i) (p.roots.toList.get i)
    rw [sub_add_cancel] at ht
    linarith
  have hL : p.roots.toList.length = p.natDegree := by
    simpa using (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
  have hprod : (c + 1) ^ p.natDegree ≤ ‖p.eval z‖ := by
    rw [(IsAlgClosed.splits p).eval_eq_prod_roots_of_monic hp, escape_prod_index, norm_prod]
    have hprod : (∏ _ : Fin p.roots.toList.length, (c + 1)) ≤
        ∏ i, ‖z - p.roots.toList.get i‖ :=
      Finset.prod_le_prod (s := Finset.univ) (fun _ _ => by positivity) (fun i _ => hbound i)
    simpa [hL] using hprod
  have hpow : c + 1 ≤ (c + 1) ^ p.natDegree := by
    simpa only [pow_one] using pow_le_pow_right₀ (show 1 ≤ c + 1 by linarith) (by omega : 1 ≤ p.natDegree)
  change ‖p.eval z‖ ≤ c at hz
  linarith [hpow.trans hprod]

private theorem OMA.escape_component_has_root (p : ℂ[X]) (hdeg : 0 < p.natDegree)
    (c : ℝ) {S : Set ℂ} (hS : S = {z : ℂ | ‖p.eval z‖ ≤ c}) (hcompact : IsCompact S)
    {z : ℂ} (hz : z ∈ S) : ∃ r ∈ connectedComponentIn S z, p.eval r = 0 := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hcompact
  let x : S := ⟨z, hz⟩
  let F : S → ℂ := fun y => p.eval y.1
  let Z := F ⁻¹' {0}
  have hF : Continuous F := p.continuous.comp continuous_subtype_val
  have hmap : IsOpenMap p.eval := by
    have han : AnalyticOnNhd ℂ p.eval univ := fun w _ => p.differentiable.analyticAt w
    rcases han.is_constant_or_isOpenMap with ⟨w, heq⟩ | hopen
    · have hpconst : p = C w := Polynomial.funext (fun v => by simpa using heq v)
      rw [hpconst, natDegree_C] at hdeg
      omega
    · exact hopen
  -- Every clopen neighborhood in the compact sublevel set has a point of minimum modulus.
  -- Open mapping forces that minimum to be zero.
  have hclopen (U : Set S) (hU : IsClopen U) (hxU : x ∈ U) : (Z ∩ U).Nonempty := by
    obtain ⟨m, hm, hmin⟩ := hU.1.isCompact.exists_isMinOn ⟨x, hxU⟩ hF.norm.continuousOn
    by_cases hm0 : F m = 0
    · exact ⟨m, hm0, hm⟩
    obtain ⟨V, hV, hEq⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hU.2
    have hmV : m.val ∈ V := by rw [← hEq] at hm; exact hm
    have hmNorm : 0 < ‖F m‖ := norm_pos_iff.mpr hm0
    have hclosure : F m ∈ closure (Metric.ball (0 : ℂ) ‖F m‖) := by
      rw [closure_ball _ hmNorm.ne', Metric.mem_closedBall, dist_zero_right]
    obtain ⟨w, hw, hwi⟩ := mem_closure_iff.mp hclosure (p.eval '' V) (hmap V hV)
      ⟨m.val, hmV, rfl⟩
    obtain ⟨v, hvV, rfl⟩ := hw
    have hvlt : ‖p.eval v‖ < ‖F m‖ := by simpa [Metric.mem_ball, dist_zero_right] using hwi
    have hmle : ‖F m‖ ≤ c := by simpa [hS, F] using m.2
    have hvS : v ∈ S := by rw [hS]; exact hvlt.le.trans hmle
    let y : S := ⟨v, hvS⟩
    have hyU : y ∈ U := by rw [← hEq]; exact hvV
    exact ((not_lt_of_ge (hmin hyU)) hvlt).elim
  let ι := {U : Set S // IsClopen U ∧ x ∈ U}
  have hZ : IsCompact Z := (isClosed_singleton.preimage hF).isCompact
  have hinter := hZ.inter_iInter_nonempty (fun i : ι => i.1) (fun i => i.2.1.1) (by
    intro t
    exact hclopen _ (isClopen_biInter_finset fun i _ => i.2.1)
      (mem_iInter₂.2 fun i _ => i.2.2))
  obtain ⟨r, hrZ, hrC⟩ := hinter
  rw [← connectedComponent_eq_iInter_isClopen] at hrC
  exact ⟨r.1, connectedComponentIn_eq_image hz ▸ ⟨r, hrC, rfl⟩, hrZ⟩

private theorem OMA.strict_mem_interior_level_component (f : ℂ[X]) {x z : ℂ}
    (hz : z ∈ connectedComponentIn (Erdos1043.levelSet f) x)
    (h : ‖f.eval z‖ < 1) :
    z ∈ interior (connectedComponentIn (Erdos1043.levelSet f) x) := by
  let S := Erdos1043.levelSet f
  let U := {w : ℂ | ‖f.eval w‖ < 1}
  have hU : IsOpen U := isOpen_lt f.continuous.norm continuous_const
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z h
  have hballS : Metric.ball z ε ⊆ S := fun w hw => (show ‖f.eval w‖ < 1 from hball hw).le
  have hcenter : z ∈ Metric.ball z ε := Metric.mem_ball_self hε
  have hballC : Metric.ball z ε ⊆ connectedComponentIn S z :=
    (convex_ball z ε).isPreconnected.subset_connectedComponentIn hcenter hballS
  have hEq : connectedComponentIn S x = connectedComponentIn S z := connectedComponentIn_eq hz
  rw [hEq]
  exact mem_interior.mpr ⟨Metric.ball z ε, hballC, Metric.isOpen_ball, hcenter⟩

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

private theorem OMA.lemniscate_component0_escapes_unit (f : ℂ[X]) (hf : f.Monic)
    (hn : 0 < f.natDegree) (hr : ∀ z ∈ f.roots, ‖z‖ ≤ 1) (hne : f ≠ X ^ f.natDegree) :
    ∃ w ∈ connectedComponentIn (Erdos1043.levelSet f) 0, 1 < ‖w‖ := by
  classical
  let S := Erdos1043.levelSet f
  let K := connectedComponentIn S (0 : ℂ)
  let L := f.roots.toList
  let a : Fin L.length → ℂ := L.get
  have hL : L.length = f.natDegree := by
    simpa [L] using (IsAlgClosed.splits f).natDegree_eq_card_roots.symm
  have hrootNorm (i : Fin L.length) : ‖a i‖ ≤ 1 :=
    hr (a i) (Multiset.mem_toList.mp (List.get_mem L i))
  have hfFact : f = ∏ i, (X - C (a i)) :=
    ((IsAlgClosed.splits f).eq_prod_roots_of_monic hf).trans (escape_prod_index _ _)
  have hfEval (z : ℂ) : f.eval z = ∏ i, (z - a i) := by
    conv_lhs => rw [hfFact]
    simp [eval_prod]
  have hnorm₀ : ‖f.eval 0‖ = ∏ i, ‖a i‖ := by simp [hfEval, norm_prod]
  have h0 : (0 : ℂ) ∈ S := by
    change ‖f.eval 0‖ ≤ 1
    rw [hnorm₀]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => hrootNorm i)
  have h0K : (0 : ℂ) ∈ K := mem_connectedComponentIn h0
  have hKS : K ⊆ S := connectedComponentIn_subset S _
  have hKcon : IsConnected K := isConnected_connectedComponentIn_iff.mpr h0
  have hSc : IsClosed S := isClosed_le f.continuous.norm continuous_const
  have hKcl : IsClosed K := by
    refine closure_subset_iff_isClosed.mp ?_
    exact hKcon.isPreconnected.closure.subset_connectedComponentIn
      (subset_closure h0K) (closure_minimal hKS hSc)
  by_contra! hKnorm
  have hKunit : K ⊆ Metric.closedBall (0 : ℂ) 1 := by
    intro z hz
    simpa [Metric.mem_closedBall, dist_zero_right] using hKnorm z hz
  have hstrictRoot {z : ℂ} (hz : z ∈ K) (hf0 : f.eval z = 0) : ‖z‖ < 1 := by
    have hi : z ∈ interior K := strict_mem_interior_level_component f hz (by simp [hf0])
    have hb := interior_mono hKunit hi
    rw [interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)] at hb
    simpa [Metric.mem_ball, dist_zero_right] using hb
  have hScompact : IsCompact S := escape_sublevel_compact f hf hn 1 zero_le_one
  obtain ⟨r, hrK, hr0⟩ := escape_component_has_root f hn 1 rfl hScompact h0
  have hri : r ∈ L := Multiset.mem_toList.mpr (mem_roots hf.ne_zero |>.mpr hr0)
  obtain ⟨i₀, hi₀⟩ := List.mem_iff_get.mp hri
  have hltᵢ : ‖a i₀‖ < 1 := by
    change ‖L.get i₀‖ < 1
    rw [hi₀]
    exact hstrictRoot hrK hr0
  have h0int : (0 : ℂ) ∈ interior K := by
    apply strict_mem_interior_level_component f h0K
    rw [hnorm₀, ← Finset.mul_prod_erase Finset.univ (fun i => ‖a i‖) (Finset.mem_univ i₀)]
    have hrest : ∏ i ∈ Finset.univ.erase i₀, ‖a i‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => hrootNorm i)
    exact (mul_le_of_le_one_right (norm_nonneg _) hrest).trans_lt hltᵢ
  let g : ℂ[X] := ∏ i, (1 - C (conj (a i)) * X)
  have hgEval (z : ℂ) : g.eval z = ∏ i, (1 - conj (a i) * z) := by simp [g, eval_prod]
  have hg0 : g.eval 0 = 1 := by simp [hgEval]
  have hnorm_ge (z : ℂ) (hz : z ∈ K) : ‖f.eval z‖ ≤ ‖g.eval z‖ := by
    rw [hfEval, hgEval, norm_prod, norm_prod]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      (fun i _ => reciprocal_factor_norm (a i) z (hrootNorm i) (hKnorm z hz))
  have hgNz (z : ℂ) (hz : z ∈ K) : g.eval z ≠ 0 := by
    intro hgEq
    have hfEq : f.eval z = 0 := by simpa [hgEq] using hnorm_ge z hz
    have hlt := hstrictRoot hz hfEq
    rw [hgEval, Finset.prod_eq_zero_iff] at hgEq
    obtain ⟨i, _, hi⟩ := hgEq
    have heq : conj (a i) * z = 1 := (sub_eq_zero.mp hi).symm
    have hnprod := congrArg norm heq
    rw [norm_mul, Complex.norm_conj, norm_one] at hnprod
    have hh := mul_le_mul_of_nonneg_right (hrootNorm i) (norm_nonneg z)
    linarith
  have hboundary (z : ℂ) (hz : z ∈ frontier K) : 1 ≤ ‖g.eval z‖ := by
    have hzK : z ∈ K := hKcl.closure_eq ▸ frontier_subset_closure hz
    have hfGe : 1 ≤ ‖f.eval z‖ := by
      by_contra! hlt
      have hi := strict_mem_interior_level_component f hzK hlt
      exact hz.2 hi
    exact hfGe.trans (hnorm_ge z hzK)
  have hdiff : DiffContOnCl ℂ (fun z : ℂ => (g.eval z)⁻¹) K := by
    apply DifferentiableOn.diffContOnCl
    rw [hKcl.closure_eq]
    exact g.differentiable.differentiableOn.inv hgNz
  have hgBig (z : ℂ) (hz : z ∈ K) : 1 ≤ ‖g.eval z‖ := by
    have hle := Complex.norm_le_of_forall_mem_frontier_norm_le
      (Metric.isBounded_closedBall.subset hKunit) hdiff
      (C := 1) (fun w hw => by rw [norm_inv]; exact inv_le_one_of_one_le₀ (hboundary w hw))
      (subset_closure hz)
    rw [norm_inv] at hle
    exact (inv_le_one₀ (norm_pos_iff.mpr (hgNz z hz))).mp hle
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
      rw [closure_ball _ (by norm_num : (1 : ℝ) ≠ 0), Metric.mem_closedBall, dist_zero_right, norm_one]
    obtain ⟨w, hw, hwball⟩ := mem_closure_iff.mp hclosure (g.eval '' interior K)
      (hmap _ isOpen_interior) ⟨0, h0int, hg0⟩
    obtain ⟨z, hz, rfl⟩ := hw
    have hlt : ‖g.eval z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hwball
    exact (not_lt_of_ge (hgBig z (interior_subset hz))) hlt


theorem OMA.solution : type_of% @Erdos1048.erdos_1048.variants.diam_gt_two_sub_sq := by
  intro r hr₀ hr₁ f hf hd hroots
  have hs : 1 < Real.sqrt 5 := (Real.lt_sqrt (by norm_num : 0 ≤ (1 : ℝ))).2 (by norm_num)
  have hr : 0 < r := by linarith only [hr₀, hs]
  have hr2 : r^2 ≤ 1 := by simpa using pow_le_pow_left₀ hr.le hr₁ 2
  have hn : 0 < f.natDegree := by
    rw [degree_eq_natDegree hf.ne_zero] at hd
    exact Nat.succ_le_iff.mp (by exact_mod_cast hd : 1 ≤ f.natDegree)
  let S := Erdos1043.levelSet f
  let K := connectedComponentIn S (0 : ℂ)
  change ENNReal.ofReal (2 - r^2) < Metric.ediam K
  have finish {x y : ℂ} (hx : x ∈ K) (hy : y ∈ K) (hxy : 2 - r^2 < dist x y) :
      ENNReal.ofReal (2-r^2) < Metric.ediam K := by
    refine lt_of_lt_of_le ?_ (Metric.edist_le_ediam_of_mem hx hy)
    rw [edist_dist]
    exact ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hxy, by linarith only [hr2, hxy]⟩
  by_cases heq : f = X ^ f.natDegree
  · have hB : Metric.closedBall (0 : ℂ) 1 ⊆ S := by
      intro z hz
      change ‖f.eval z‖ ≤ 1
      rw [heq, eval_pow, eval_X, norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (by simpa [Metric.mem_closedBall, dist_zero_right] using hz)
    have hC : Metric.closedBall (0 : ℂ) 1 ⊆ K :=
      Metric.isPreconnected_closedBall.subset_connectedComponentIn
        (Metric.mem_closedBall_self zero_le_one) hB
    have hx : (1 : ℂ) ∈ K := hC (by simp [Metric.mem_closedBall, dist_zero_right])
    have hy : (-1 : ℂ) ∈ K := hC (by simp [Metric.mem_closedBall, dist_zero_right])
    have hdist : dist (1 : ℂ) (-1) = 2 := by
      rw [dist_eq_norm, show (1 : ℂ) - (-1) = ((2:ℝ):ℂ) by push_cast; ring]
      norm_num
    apply finish hx hy
    rw [hdist]
    linarith [sq_pos_of_pos hr]
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
    obtain ⟨c, hc, hdisk⟩ := PommerenkeCentroid.disk (hL.symm ▸ hn) a hr.le hr₁ ha
    let R := Real.sqrt (1 - r^2 + ‖c‖^2)
    have hsq : R^2 = 1 - r^2 + ‖c‖^2 :=
      Real.sq_sqrt (by nlinarith [sq_nonneg ‖c‖])
    have hrc : ‖c‖ ≤ R :=
      (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1 (by linarith only [hsq, hr2])
    have hzero : (0 : ℂ) ∈ Metric.closedBall c R := by
      simpa only [Metric.mem_closedBall, dist_zero_left] using hrc
    have hB : Metric.closedBall c R ⊆ S := by
      intro z hz
      change ‖f.eval z‖ ≤ 1
      rw [hfEval]
      exact hdisk hz
    have hBK : Metric.closedBall c R ⊆ K :=
      Metric.isPreconnected_closedBall.subset_connectedComponentIn hzero hB
    obtain ⟨w, hw, hw1⟩ := OMA.lemniscate_component0_escapes_unit f hf hn
      (fun z hz => (hroots z hz).trans hr₁) heq
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      PommerenkeCentroid.diameter_witness hr.le hr₁ hc hBK hw hw1
    exact finish hx hy hxy