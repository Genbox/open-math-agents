import FormalConjectures.Wikipedia.MoserWorm
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Combination
import Mathlib.MeasureTheory.Group.Action

/-! Translate each cover to contain a fixed ball obtained from an L-shaped worm. An area
cap then bounds its radius. Blaschke selection and lower semicontinuity of area give a
minimizer among those normalized compact convex covers. -/

open EuclideanGeometry MeasureTheory TopologicalSpace Set Filter
open scoped Topology Pointwise ENNReal BigOperators EuclideanGeometry

namespace WormCompact

abbrev Plane := ℝ²
abbrev Bodies := NonemptyCompacts Plane

lemma closed_membership : IsClosed {p : Plane × Bodies | p.1 ∈ (p.2 : Set Plane)} := by
  have h : {p : Plane × Bodies | p.1 ∈ (p.2 : Set Plane)} =
      (fun p : Plane × Bodies => Metric.infDist p.1 (p.2 : Set Plane)) ⁻¹' {0} := by
    ext p
    exact p.2.isCompact.isClosed.mem_iff_infDist_zero p.2.nonempty
  rw [h]
  exact isClosed_singleton.preimage Metric.lipschitz_infDist.continuous

lemma closed_supersets (S : Set Plane) : IsClosed {K : Bodies | S ⊆ (K : Set Plane)} := by
  have h : {K : Bodies | S ⊆ (K : Set Plane)} =
      ⋂ x : S, {K : Bodies | (x : Plane) ∈ (K : Set Plane)} := by
    ext K
    simp only [mem_ofPred_eq, mem_iInter]
    exact ⟨fun h x => h x.property, fun h x hx => h ⟨x, hx⟩⟩
  rw [h]
  apply isClosed_iInter
  intro x
  exact closed_membership.preimage
    (continuous_const.prodMk continuous_id : Continuous (fun K : Bodies => ((x : Plane), K)))

private lemma finiteHausdorff (K L : Bodies) :
    Metric.hausdorffEDist (K : Set Plane) (L : Set Plane) ≠ ⊤ :=
  Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded K.nonempty L.nonempty
    K.isCompact.isBounded L.isCompact.isBounded

private lemma approximate {K L : Bodies} {δ : ℝ} {x : Plane} (hx : x ∈ (K : Set Plane))
    (hKL : dist K L < δ) : ∃ y ∈ (L : Set Plane), dist x y < δ :=
  Metric.exists_dist_lt_of_hausdorffDist_lt (s := (K : Set Plane)) (t := (L : Set Plane))
    hx hKL (finiteHausdorff K L)

private lemma tendsto_points {Ks : ℕ → Bodies} {K : Bodies}
    (hKs : Tendsto Ks atTop (𝓝 K)) {x : Plane} (hx : x ∈ (K : Set Plane)) :
    ∃ xs : ℕ → Plane, (∀ n, xs n ∈ (Ks n : Set Plane)) ∧ Tendsto xs atTop (𝓝 x) := by
  have hh (n : ℕ) : ∃ y ∈ (Ks n : Set Plane),
      Metric.infDist x (Ks n : Set Plane) = dist x y :=
    (Ks n).isCompact.exists_infDist_eq_dist (Ks n).nonempty x
  choose xs hmem hdist using hh
  refine ⟨xs, hmem, tendsto_iff_dist_tendsto_zero.mpr ?_⟩
  have hN : Tendsto (fun n => dist K (Ks n)) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => K) atTop (𝓝 K) := tendsto_const_nhds
    simpa using hc.dist hKs
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) hN
  rw [dist_comm (xs n), ← hdist n, Metric.NonemptyCompacts.dist_eq]
  exact Metric.infDist_le_hausdorffDist_of_mem hx (finiteHausdorff K (Ks n))

lemma closed_convex : IsClosed {K : Bodies | Convex ℝ (K : Set Plane)} := by
  apply IsSeqClosed.isClosed
  intro Ks K hconv hK
  change Convex ℝ (K : Set Plane)
  intro x hx y hy a b ha hb hab
  obtain ⟨xs, hxs, hxt⟩ := tendsto_points hK hx
  obtain ⟨ys, hys, hyt⟩ := tendsto_points hK hy
  let zs (n : ℕ) := a • xs n + b • ys n
  have hzt : Tendsto zs atTop (𝓝 (a • x + b • y)) :=
    (tendsto_const_nhds.smul hxt).add (tendsto_const_nhds.smul hyt)
  exact closed_membership.mem_of_tendsto (hzt.prodMk_nhds hK)
    (Eventually.of_forall fun n => hconv n (hxs n) (hys n) ha hb hab)

private lemma smul_subset {K L : Bodies} {t r : ℝ} (ht : 0 ≤ t) (ht1 : t < 1)
    (hr : 0 < r) (hconv : Convex ℝ (L : Set Plane))
    (hball : Metric.closedBall (0 : Plane) r ⊆ (L : Set Plane))
    (hclose : dist K L < (1 - t) * r) :
    t • (K : Set Plane) ⊆ (L : Set Plane) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hxy⟩ := approximate hx hclose
  have ht' : 0 < 1 - t := sub_pos.mpr ht1
  let z := (t / (1 - t)) • (x - y)
  have hz : z ∈ (L : Set Plane) := by
    apply hball
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖(t / (1 - t)) • (x - y)‖ ≤ r
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg ht ht'.le), ← dist_eq_norm]
    calc
      _ ≤ (t / (1 - t)) * ((1 - t) * r) :=
        mul_le_mul_of_nonneg_left hxy.le (div_nonneg ht ht'.le)
      _ = t * r := by field_simp
      _ ≤ r := by nlinarith only [mul_le_mul_of_nonneg_right ht1.le hr.le]
  have hscalar : (1 - t) * (t / (1 - t)) = t := by field_simp
  have hzEq : t • x = t • y + (1 - t) • z := by
    dsimp [z]
    rw [smul_smul, hscalar, smul_sub]
    abel
  change t • x ∈ (L : Set Plane)
  rw [hzEq]
  exact hconv hy hz ht ht'.le (by ring)

lemma volume_lowerSemicontinuous {r : ℝ} (hr : 0 < r) {S : Set Bodies}
    (hS : ∀ K ∈ S, Convex ℝ (K : Set Plane) ∧ Metric.closedBall (0 : Plane) r ⊆ (K : Set Plane)) :
    LowerSemicontinuousOn (fun K : Bodies => volume (K : Set Plane)) S := by
  intro K hK v hv
  let d := Module.finrank ℝ Plane
  have hfinite : volume (K : Set Plane) ≠ ⊤ := K.isCompact.measure_lt_top.ne
  let scale (t : ℝ) := ENNReal.ofReal (t ^ d) * volume (K : Set Plane)
  have hscale : Continuous scale :=
    (ENNReal.continuous_mul_const hfinite).comp (ENNReal.continuous_ofReal.comp (continuous_pow d))
  have hside : Tendsto scale (𝓝[<] (1 : ℝ)) (𝓝 (volume (K : Set Plane))) := by
    have h : scale 1 = volume (K : Set Plane) := by simp [scale]
    rw [← h]
    exact hscale.continuousAt.continuousWithinAt
  have hm : ∀ᶠ t in 𝓝[<] (1 : ℝ), v < scale t := hside.eventually (Ioi_mem_nhds hv)
  have hpos : ∀ᶠ t in 𝓝[<] (1 : ℝ), 0 < t := nhdsWithin_le_nhds (Ioi_mem_nhds zero_lt_one)
  have hone : ∀ᶠ t in 𝓝[<] (1 : ℝ), t < 1 := self_mem_nhdsWithin
  obtain ⟨t, hvt, ht, ht1⟩ := (hm.and (hpos.and hone)).exists
  have hδ : 0 < (1 - t) * r := mul_pos (sub_pos.mpr ht1) hr
  have hadj : ∀ᶠ L in 𝓝[S] K, L ∈ Metric.ball K ((1 - t) * r) :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds _ hδ)
  filter_upwards [self_mem_nhdsWithin, hadj] with L hL hclose
  have hsub := smul_subset ht.le ht1 hr (hS L hL).1 (hS L hL).2
    (by simpa only [Metric.mem_ball, dist_comm] using hclose : dist K L < (1 - t) * r)
  have hvol : scale t ≤ volume (L : Set Plane) := by
    change ENNReal.ofReal (t ^ Module.finrank ℝ Plane) * volume (K : Set Plane) ≤ volume (L : Set Plane)
    rw [← Measure.addHaar_smul_of_nonneg volume ht.le (K : Set Plane)]
    exact measure_mono hsub
  exact hvt.trans_le hvol


def family (r R : ℝ) : Set Bodies :=
  {K | ((K : Set Plane) ⊆ Metric.closedBall 0 R ∧ (K : Set Plane) ∈ MoserWorm.WormCovers) ∧
    Convex ℝ (K : Set Plane) ∧ Metric.closedBall 0 r ⊆ (K : Set Plane)}

lemma minimizes {r R : ℝ} (hr : 0 < r)
    (hc : IsClosed {K : Bodies | (K : Set Plane) ⊆ Metric.closedBall 0 R ∧
      (K : Set Plane) ∈ MoserWorm.WormCovers})
    (hne : (family r R).Nonempty) :
    ∃ K ∈ family r R, IsMinOn (fun L : Bodies => volume (L : Set Plane)) (family r R) K := by
  have hClosed : IsClosed (family r R) := hc.inter (closed_convex.inter (closed_supersets _))
  have hCompact : IsCompact (family r R) := by
    have hb := NonemptyCompacts.isCompact_subsets_of_isCompact (isCompact_closedBall (0 : Plane) R)
    exact hb.of_isClosed_subset hClosed (fun K hK => hK.1.1)
  exact LowerSemicontinuousOn.exists_isMinOn hne hCompact
    (volume_lowerSemicontinuous hr fun K hK => hK.2)

end WormCompact

namespace WormInball

private abbrev Time := Set.Icc (0 : ℝ) 1

private def point (x y : ℝ) : ℝ² := WithLp.toLp 2 ![x,y]

private lemma point_zero (x y : ℝ) : point x y 0 = x := rfl

private lemma point_one (x y : ℝ) : point x y 1 = y := rfl

private noncomputable def worm (t : Time) : ℝ² :=
  point (min t.val (1/2)) (max (t.val - 1/2) 0)

private lemma sum_coords (t : ℝ) : min t (1/2) + max (t - 1/2) 0 = t := by
  by_cases ht : t ≤ 1/2
  · rw [min_eq_left ht, max_eq_right (sub_nonpos.2 ht), add_zero]
  · rw [min_eq_right (le_of_not_ge ht), max_eq_left (sub_nonneg.2 (le_of_not_ge ht))]
    ring

private lemma worm_lipschitz : LipschitzWith 1 worm := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [NNReal.coe_one, one_mul]
  wlog hst : s.val ≤ t.val generalizing s t
  · rw [dist_comm (worm s),dist_comm s t]
    exact this t s (le_of_not_ge hst)
  have hm : min s.val (1/2) ≤ min t.val (1/2) := min_le_min_right _ hst
  have hM : max (s.val - 1/2) 0 ≤ max (t.val - 1/2) 0 :=
    max_le_max_right _ (sub_le_sub_right hst _)
  apply (sq_le_sq₀ dist_nonneg dist_nonneg).1
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Subtype.dist_eq]
  simp only [worm, point_zero, point_one, Real.dist_eq, sq_abs]
  have hsum : min t.val (1/2) - min s.val (1/2) +
       (max (t.val - 1/2) 0 - max (s.val - 1/2) 0) = t.val - s.val := by
    linarith only [sum_coords s.val,sum_coords t.val]
  calc
    _ ≤ (min t.val (1/2) - min s.val (1/2) +
        (max (t.val - 1/2) 0 - max (s.val - 1/2) 0)) ^ 2 := by
      nlinarith only [mul_nonneg (sub_nonneg.2 hm) (sub_nonneg.2 hM)]
    _ = _ := by rw [hsum, ← neg_sub, neg_sq]

private noncomputable def vertices : Fin 3 → ℝ² := ![point 0 0,point (1/2) 0,point (1/2) (1/2)]

private lemma vertices_in_worm (i : Fin 3) : vertices i ∈ Set.range worm := by
  fin_cases i
  · refine ⟨⟨0,by constructor <;> norm_num⟩,?_⟩
    change point (min 0 (1/2)) (max (0-1/2) 0) = point 0 0
    norm_num [min_def,max_def]
  · refine ⟨⟨1/2,by constructor <;> norm_num⟩,?_⟩
    change point (min (1/2) (1/2)) (max ((1/2)-(1/2)) 0) = point (1/2) 0
    norm_num
  · refine ⟨⟨1,by constructor <;> norm_num⟩,?_⟩
    change point (min 1 (1/2)) (max (1-1/2) 0) = point (1/2) (1/2)
    norm_num [min_def,max_def]

private noncomputable def center : ℝ² := point (3/8) (1/8)

private lemma ball_in_convexHull : Metric.closedBall center (1/16) ⊆ convexHull ℝ (Set.range worm) := by
  intro z hz
  have hd : dist z center ≤ 1/16 := Metric.mem_closedBall.1 hz
  have hs : dist z center ^ 2 ≤ (1/16 : ℝ) ^ 2 :=
    (sq_le_sq₀ dist_nonneg (by norm_num)).2 hd
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two] at hs
  simp only [center, point_zero, point_one, Real.dist_eq, sq_abs] at hs
  have hxAbs : |z 0 - 3/8| ≤ 1/16 := by
    apply (sq_le_sq₀ (abs_nonneg _) (by norm_num)).1
    rw [sq_abs]
    nlinarith only [hs,sq_nonneg (z 1 - 1/8)]
  have hyAbs : |z 1 - 1/8| ≤ 1/16 := by
    apply (sq_le_sq₀ (abs_nonneg _) (by norm_num)).1
    rw [sq_abs]
    nlinarith only [hs,sq_nonneg (z 0 - 3/8)]
  rw [abs_le] at hxAbs hyAbs
  have hx : z 0 ≤ 1/2 := by linarith only [hxAbs.2]
  have hy : 0 ≤ z 1 := by linarith only [hyAbs.1]
  have hxy : z 1 ≤ z 0 := by linarith only [hyAbs.2,hxAbs.1]
  let w : Fin 3 → ℝ := ![1-2*z 0,2*(z 0-z 1),2*z 1]
  have hw (i : Fin 3) : 0 ≤ w i := by
    fin_cases i
    · change 0 ≤ 1-2*z 0
      linarith
    · exact mul_nonneg (by norm_num) (sub_nonneg.2 hxy)
    · exact mul_nonneg (by norm_num) hy
  have hwSum : ∑ i : Fin 3, w i = 1 := by
    rw [Fin.sum_univ_three]
    change 1-2*z 0 + 2*(z 0-z 1) + 2*z 1 = 1
    ring
  have hsum : (∑ i : Fin 3, w i • vertices i) = z := by
    rw [Fin.sum_univ_three]
    ext i
    fin_cases i
    · change (1-2*z 0)*0 + (2*(z 0-z 1))*(1/2) + (2*z 1)*(1/2) = z 0
      ring
    · change (1-2*z 0)*0 + (2*(z 0-z 1))*0 + (2*z 1)*(1/2) = z 1
      ring
  rw [← hsum]
  exact (convex_convexHull ℝ (Set.range worm)).sum_mem (fun i _ => hw i) hwSum
    (fun i _ => subset_convexHull ℝ _ (vertices_in_worm i))

private lemma translated_worm_cover {X : Set ℝ²} (hX : X ∈ MoserWorm.WormCovers) (p : ℝ²) :
    ((p + ·) ⁻¹' X) ∈ MoserWorm.WormCovers := by
  refine ⟨hX.1.preimage (continuous_const.add continuous_id).measurable, ?_⟩
  intro W hW
  obtain ⟨e,v,hdet,hSub⟩ := hX.2 W hW
  refine ⟨e,e p + v,hdet,?_⟩
  intro z hz
  obtain ⟨x,hx,rfl⟩ := hSub hz
  refine ⟨x-p,?_,?_⟩
  · change p + (x-p) ∈ X
    rwa [show p + (x-p) = x by abel]
  · change e (x-p) + (e p + v) = e x + v
    rw [map_sub]
    abel

theorem normalize :
    ∃ r : ℝ, 0 < r ∧ ∀ X : Set ℝ², X ∈ MoserWorm.WormCovers → Convex ℝ X →
      ∃ Y : Set ℝ², Y ∈ MoserWorm.WormCovers ∧ Convex ℝ Y ∧
        Metric.closedBall 0 r ⊆ Y ∧ volume Y = volume X := by
  refine ⟨1/16,by norm_num,?_⟩
  intro X hX hConv
  obtain ⟨e,v,_,hW⟩ := hX.2 (Set.range worm) ⟨worm,worm_lipschitz,rfl⟩
  have hConvImage : Convex ℝ ((fun x => e x + v) '' X) := by
    let L := e.toLinearEquiv.toLinearMap
    have h := (hConv.linear_image L).translate v
    rw [Set.image_image] at h
    have he : (fun x => v + L x) = (fun x => e x + v) := by
      ext x
      exact add_comm _ _
    rw [he] at h
    exact h
  have hC : Metric.closedBall center (1/16) ⊆ (fun x => e x + v) '' X :=
    ball_in_convexHull.trans (convexHull_min hW hConvImage)
  let p := e.symm (center-v)
  have hp : e p + v = center := by simp [p]
  have hBall : Metric.closedBall p (1/16) ⊆ X := by
    intro x hx
    have hDist : dist (e x + v) center = dist x p := by
      rw [← hp, dist_eq_norm, show e x + v - (e p + v) = e x - e p by abel, ← dist_eq_norm,
        e.isometry.dist_eq]
    obtain ⟨y,hy,heq⟩ := hC (Metric.mem_closedBall.2 (hDist.trans_le (Metric.mem_closedBall.1 hx)))
    have hEq : y = x := e.injective (add_right_cancel heq)
    exact hEq ▸ hy
  let Y : Set ℝ² := (p + ·) ⁻¹' X
  refine ⟨Y, translated_worm_cover hX p, hConv.translate_preimage_right p, ?_, ?_⟩
  · intro x hx
    apply hBall
    have hdist : dist (p+x) p = dist x 0 := by
      rw [dist_eq_norm,dist_zero_right,show p+x-p=x by abel]
    exact Metric.mem_closedBall.2 (hdist.trans_le (Metric.mem_closedBall.1 hx))
  · exact measure_preimage_vadd (volume : Measure ℝ²) p X

end WormInball

namespace WormBound

open EuclideanGeometry MeasureTheory
open scoped ENNReal

private lemma one_le_abs_cast_sub {i j : ℕ} (h : i ≠ j) :
    1 ≤ |(i : ℝ) - (j : ℝ)| := by
  rcases lt_or_gt_of_ne h with hij | hji
  · have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hij
    exact (show 1 ≤ -((i : ℝ) - j) by linarith).trans (neg_le_abs _)
  · have hcast : (j : ℝ) + 1 ≤ (i : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hji
    exact (show 1 ≤ (i : ℝ) - j by linarith).trans (le_abs_self _)

/-- Convex sets containing an origin-centered ball and with bounded area have a common radius. -/
theorem exists_radius (r : ℝ) (hr : 0 < r) (M : ℝ≥0∞) (hM : M < ⊤) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ Y : Set ℝ², Convex ℝ Y → Metric.closedBall 0 r ⊆ Y →
      volume Y ≤ M → Y ⊆ Metric.closedBall 0 R := by
  let v : ℝ≥0∞ := volume (Metric.ball (0 : ℝ²) (r / 2))
  have hv : 0 < v := Metric.measure_ball_pos volume _ (half_pos hr)
  obtain ⟨N, hNpos, hN⟩ := ENNReal.exists_nat_pos_mul_gt hv.ne' hM.ne
  have hNreal : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  let D : ℝ := 2 * N
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D * r, mul_nonneg hD.le hr.le, ?_⟩
  intro Y hY hball hvol y hy
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! hFar
  let t (i : Fin N) : ℝ := (i.val : ℝ) / D
  let center (i : Fin N) : ℝ² := t i • y
  have ht0 (i : Fin N) : 0 ≤ t i := div_nonneg (Nat.cast_nonneg _) hD.le
  have htHalf (i : Fin N) : t i ≤ 1 / 2 := by
    change (i.val : ℝ) / D ≤ 1 / 2
    apply (div_le_iff₀ hD).2
    have h : (i.val : ℝ) ≤ N := by exact_mod_cast i.isLt.le
    dsimp [D]
    linarith
  have hContained (i : Fin N) : Metric.ball (center i) (r / 2) ⊆ Y := by
    intro z hz
    let d := 1 - t i
    have hHalf : (1 / 2 : ℝ) ≤ d := by dsimp [d]; linarith [htHalf i]
    have hd : 0 < d := by linarith
    let w := d⁻¹ • (z - center i)
    have hw : w ∈ Metric.closedBall (0 : ℝ²) r := by
      have hz' : ‖z - center i‖ < r / 2 := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
      rw [Metric.mem_closedBall, dist_zero_right]
      change ‖d⁻¹ • (z - center i)‖ ≤ r
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
      apply (inv_mul_le_iff₀ hd).2
      have hle := mul_le_mul_of_nonneg_right hHalf hr.le
      exact hz'.le.trans (by linarith)
    have hsum : d + t i = 1 := sub_add_cancel _ _
    have hmem := hY (hball hw) hy hd.le (ht0 i) hsum
    have hwc : d • w = z - center i := by
      dsimp only [w]
      rw [smul_smul, mul_inv_cancel₀ hd.ne', one_smul]
    change d • w + center i ∈ Y at hmem
    rwa [hwc, sub_add_cancel] at hmem
  have hDisjoint : Pairwise (fun i j : Fin N =>
      Disjoint (Metric.ball (center i) (r / 2)) (Metric.ball (center j) (r / 2))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    rw [add_halves]
    have hi : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hgap := one_le_abs_cast_sub hi
    change r ≤ dist (t i • y) (t j • y)
    rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs]
    dsimp [t]
    rw [← sub_div, abs_div, abs_of_pos hD, div_mul_eq_mul_div]
    apply (le_div_iff₀ hD).2
    calc
      r * D ≤ ‖y‖ := by simpa only [mul_comm] using hFar.le
      _ ≤ |(i.val : ℝ) - (j.val : ℝ)| * ‖y‖ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hgap (norm_nonneg y)
  have hSameVolume (i : Fin N) : volume (Metric.ball (center i) (r / 2)) = v := by
    simp [v, EuclideanSpace.volume_ball]
  have hVolume : volume (⋃ i : Fin N, Metric.ball (center i) (r / 2)) =
      (N : ℝ≥0∞) * v := by
    rw [measure_iUnion hDisjoint (fun _ => measurableSet_ball)]
    simp only [hSameVolume, tsum_fintype, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hUpper := (measure_mono (Set.iUnion_subset hContained)).trans hvol
  rw [hVolume] at hUpper
  exact (not_lt_of_ge hUpper) hN

/-- The closure of a convex set has the same area. -/
theorem volume_closure {Y : Set ℝ²} (hY : Convex ℝ Y) :
    volume (closure Y) = volume Y := by
  apply le_antisymm _ (measure_mono subset_closure)
  have hsub : closure Y ⊆ Y ∪ frontier Y := by
    intro x hx
    by_cases hy : x ∈ Y
    · exact Or.inl hy
    · exact Or.inr ⟨hx, fun hi => hy (interior_subset hi)⟩
  calc
    volume (closure Y) ≤ volume (Y ∪ frontier Y) := measure_mono hsub
    _ ≤ volume Y + volume (frontier Y) := measure_union_le _ _
    _ = volume Y := by rw [hY.addHaar_frontier volume, add_zero]

/-- Closing a worm cover preserves its covering property. -/
theorem closure_cover {Y : Set ℝ²} (hY : Y ∈ MoserWorm.WormCovers) :
    closure Y ∈ MoserWorm.WormCovers := by
  refine ⟨isClosed_closure.measurableSet, ?_⟩
  intro w hw
  obtain ⟨e, v, he, hwY⟩ := hY.2 w hw
  exact ⟨e, v, he, hwY.trans (Set.image_mono subset_closure)⟩

end WormBound

namespace WormCompact

lemma attains
    (hclosed : ∀ R : ℝ, IsClosed {K : Bodies | (K : Set Plane) ⊆ Metric.closedBall 0 R ∧
      (K : Set Plane) ∈ MoserWorm.WormCovers}) :
    ∃ X ∈ MoserWorm.WormCovers, Convex ℝ X ∧ volume X = MoserWorm.convexWormCoverConstant := by
  obtain ⟨r, hr, hInball⟩ := WormInball.normalize
  let D : Set Plane := Metric.closedBall 0 0.5
  let M : ℝ≥0∞ := volume D
  have hD : D ∈ MoserWorm.WormCovers := MoserWorm.disc_mem_worm_covers
  have hDconv : Convex ℝ D := convex_closedBall _ _
  have hDcompact : IsCompact D := isCompact_closedBall _ _
  obtain ⟨R, _, hBound⟩ := WormBound.exists_radius r hr M hDcompact.measure_lt_top
  have represent (X : Set Plane) (hX : X ∈ MoserWorm.WormCovers) (hConv : Convex ℝ X)
      (hVol : volume X ≤ M) :
      ∃ K ∈ family r R, volume (K : Set Plane) = volume X := by
    obtain ⟨Y, hY, hYconv, hrY, hYvol⟩ := hInball X hX hConv
    have hYR : Y ⊆ Metric.closedBall 0 R := hBound Y hYconv hrY (hYvol ▸ hVol)
    have hCR : closure Y ⊆ Metric.closedBall 0 R := closure_minimal hYR Metric.isClosed_closedBall
    have hC : IsCompact (closure Y) :=
      Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, Metric.isBounded_closedBall.subset hCR⟩
    have hne : (closure Y).Nonempty := ⟨0, subset_closure (hrY (Metric.mem_closedBall_self hr.le))⟩
    let K : Bodies := ⟨⟨closure Y, hC⟩, hne⟩
    exact ⟨K, ⟨⟨hCR, WormBound.closure_cover hY⟩, hYconv.closure, hrY.trans subset_closure⟩,
      (WormBound.volume_closure hYconv).trans hYvol⟩
  obtain ⟨L, hL, hLv⟩ := represent D hD hDconv le_rfl
  obtain ⟨K, hK, hmin⟩ := minimizes hr (hclosed R) ⟨L, hL⟩
  have hKM : volume (K : Set Plane) ≤ M := ((isMinOn_iff.mp hmin) L hL).trans_eq hLv
  refine ⟨(K : Set Plane), hK.1.2, hK.2.1, le_antisymm ?_ ?_⟩
  · unfold MoserWorm.convexWormCoverConstant
    apply le_sInf
    rintro _ ⟨X, hX, hConv, rfl⟩
    by_cases hV : volume X ≤ M
    · obtain ⟨K', hK', hKv⟩ := represent X hX hConv hV
      exact ((isMinOn_iff.mp hmin) K' hK').trans_eq hKv
    · exact hKM.trans (le_of_not_ge hV)
  · exact sInf_le ⟨(K : Set Plane), hK.1.2, hK.2.1, rfl⟩

end WormCompact

namespace WormCoverLimit

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

private lemma mem_limit {E : Type*} [MetricSpace E]
    {K : ℕ → NonemptyCompacts E} {Klim : NonemptyCompacts E} {x : ℕ → E} {xlim : E}
    (hK : Tendsto K atTop (𝓝 Klim)) (hx : Tendsto x atTop (𝓝 xlim))
    (hmem : ∀ n, x n ∈ (K n : Set E)) : xlim ∈ (Klim : Set E) := by
  have hc : Continuous (fun p : E × NonemptyCompacts E => Metric.infDist p.1 p.2) :=
    Metric.lipschitz_infDist.continuous
  have hc0 : IsClosed {p : E × NonemptyCompacts E | Metric.infDist p.1 p.2 = 0} :=
    isClosed_eq hc continuous_const
  have hprod : Tendsto (fun n => (x n, K n)) atTop (𝓝 (xlim, Klim)) :=
    hx.prodMk_nhds hK
  have hz : (xlim, Klim) ∈ {p : E × NonemptyCompacts E | Metric.infDist p.1 p.2 = 0} :=
    hc0.mem_of_tendsto hprod (Eventually.of_forall (fun n => Metric.infDist_zero_of_mem (hmem n)))
  exact (Klim.isCompact.isClosed.mem_iff_infDist_zero Klim.nonempty).mpr hz

private lemma det_symm_eq_one {e : Plane ≃ₗᵢ[ℝ] Plane} (h : e.toLinearEquiv.det = 1) :
    e.symm.toLinearEquiv.det = 1 := by
  have hR : LinearMap.det (e.toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1 := by
    simpa only [LinearEquiv.coe_det, Units.val_one] using
      congrArg (fun u : ℝˣ => (u : ℝ)) h
  have hh := LinearEquiv.det_mul_det_symm e.toLinearEquiv
  rw [hR, one_mul] at hh
  rw [LinearIsometryEquiv.toLinearEquiv_symm]
  apply Units.ext
  rw [LinearEquiv.coe_det]
  exact hh

set_option maxHeartbeats 800000 in
/-- A Hausdorff limit of worm covers lying in a fixed closed ball is a worm cover
in the same closed ball. -/
theorem isClosed_covers (R : ℝ) :
    IsClosed {K : NonemptyCompacts Plane |
      (K : Set Plane) ⊆ Metric.closedBall 0 R ∧
        (K : Set Plane) ∈ MoserWorm.WormCovers} := by
  classical
  apply isSeqClosed_iff_isClosed.mp
  intro K Klim hKs hKt
  have hball (n : ℕ) : (K n : Set Plane) ⊆ Metric.closedBall 0 R := (hKs n).1
  have hclosed := NonemptyCompacts.isClosed_subsets_of_isClosed
    (F := Metric.closedBall (0 : Plane) R) Metric.isClosed_closedBall
  refine ⟨hclosed.mem_of_tendsto hKt (Eventually.of_forall hball),
    Klim.isCompact.measurableSet, ?_⟩
  intro w hw
  have hW : w.Nonempty := by
    obtain ⟨f, _, rfl⟩ := hw
    exact ⟨f ⟨0, by norm_num⟩, _, rfl⟩
  obtain ⟨w0, hw0⟩ := hW
  have hM (n : ℕ) : ∃ (e : Plane ≃ₗᵢ[ℝ] Plane) (v : Plane),
      e.toLinearEquiv.det = 1 ∧ w ⊆ (fun x => e x + v) '' (K n : Set Plane) :=
    (hKs n).2.2 w hw
  choose e v hDet hCover using hM
  let F (n : ℕ) : Plane →L[ℝ] Plane := (e n).symm.toContinuousLinearMap
  let p (n : ℕ) : Plane := (e n).symm (w0 - v n)
  have hBack (n : ℕ) {x : Plane} (hx : x ∈ w) :
      F n (x - w0) + p n ∈ (K n : Set Plane) := by
    obtain ⟨y, hy, he⟩ := hCover n hx
    have hEq : (e n).symm (x - v n) = y := by
      rw [← he, add_sub_cancel_right, LinearIsometryEquiv.symm_apply_apply]
    have hEq' : F n (x - w0) + p n = (e n).symm (x - v n) := by
      change (e n).symm (x - w0) + (e n).symm (w0 - v n) = (e n).symm (x - v n)
      rw [← map_add]
      congr 1
      abel
    rwa [hEq', hEq]
  have hp (n : ℕ) : p n ∈ (K n : Set Plane) := by simpa using hBack n hw0
  let _ : FiniteDimensional ℝ (Plane →L[ℝ] Plane) := ContinuousLinearMap.finiteDimensional
  let S := Metric.closedBall (0 : Plane →L[ℝ] Plane) 1 ×ˢ Metric.closedBall (0 : Plane) R
  have hS : IsCompact S := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hSeq (n : ℕ) : (F n, p n) ∈ S := by
    refine ⟨Metric.mem_closedBall.mpr ?_, hball n (hp n)⟩
    rw [dist_zero_right]
    exact (LinearIsometryEquiv.norm_toContinuousLinearMap (e n).symm).le
  obtain ⟨⟨Flim, plim⟩, _, φ, hφ, hLim⟩ := hS.tendsto_subseq hSeq
  have hF : Tendsto (F ∘ φ) atTop (𝓝 Flim) := hLim.fst_nhds
  have hpLim : Tendsto (p ∘ φ) atTop (𝓝 plim) := hLim.snd_nhds
  have hEval (x : Plane) : Tendsto (fun n => F (φ n) x) atTop (𝓝 (Flim x)) :=
    (ContinuousLinearMap.apply ℝ Plane x).continuous.continuousAt.tendsto.comp hF
  have hNorm (x : Plane) : ‖Flim x‖ = ‖x‖ := by
    apply tendsto_nhds_unique (hEval x).norm
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall (fun n => ((e (φ n)).symm.norm_map x).symm)
  have hDetF (n : ℕ) : (F n).det = 1 := by
    have h := congrArg (fun u : ℝˣ => (u : ℝ)) (det_symm_eq_one (hDet n))
    rw [LinearEquiv.coe_det] at h
    exact h
  have hdLim : Tendsto (fun n => (F (φ n)).det) atTop (𝓝 Flim.det) :=
    ContinuousLinearMap.continuous_det.continuousAt.tendsto.comp hF
  have hd : Flim.det = 1 := by
    apply tendsto_nhds_unique hdLim
    exact tendsto_const_nhds.congr' (Eventually.of_forall (fun n => (hDetF (φ n)).symm))
  let L : Plane →ₗᵢ[ℝ] Plane := ⟨Flim.toLinearMap, hNorm⟩
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective (f := L.toLinearMap)).mp L.injective
  let f := LinearIsometryEquiv.ofSurjective L hsurj
  have hfdet : f.toLinearEquiv.det = 1 := by
    apply Units.ext
    rw [LinearEquiv.coe_det]
    exact hd
  refine ⟨f.symm, w0 - f.symm plim, det_symm_eq_one hfdet, ?_⟩
  intro x hx
  have hxLim : Tendsto (fun n => F (φ n) (x - w0) + p (φ n)) atTop
      (𝓝 (Flim (x - w0) + plim)) := (hEval (x - w0)).add hpLim
  have hxMem : Flim (x - w0) + plim ∈ (Klim : Set Plane) :=
    mem_limit (hKt.comp hφ.tendsto_atTop) hxLim (fun n => hBack (φ n) hx)
  refine ⟨f (x - w0) + plim, hxMem, ?_⟩
  change f.symm (f (x - w0) + plim) + (w0 - f.symm plim) = x
  rw [map_add, LinearIsometryEquiv.symm_apply_apply]
  abel

end WormCoverLimit

theorem OMA.solution : type_of% @MoserWorm.convex_mosers_worm_problem_bound_attained :=
  WormCompact.attains WormCoverLimit.isClosed_covers