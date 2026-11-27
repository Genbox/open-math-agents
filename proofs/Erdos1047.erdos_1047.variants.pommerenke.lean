import FormalConjectures.ErdosProblems.«1047»
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
This proves Pommerenke's result using the exponential limit of the rescaled lemniscates.
See Christian Pommerenke, “On metric properties of complex polynomials” (1961),
https://doi.org/10.1307/mmj/1028998561.
-/

open Polynomial Set Filter
open scoped BigOperators Topology

private noncomputable def OMA.pommerenkeRatio (k : ℕ) (s y : ℝ) : ℝ :=
  ((((k : ℝ) - s) ^ 2 + y ^ 2) / (k : ℝ) ^ 2) ^ k * ((1 + s) ^ 2 + y ^ 2)

private theorem OMA.tendsto_pommerenkeRatio (s y : ℝ) :
    Tendsto (fun k => pommerenkeRatio k s y) atTop
      (𝓝 (Real.exp (-2 * s) * ((1 + s) ^ 2 + y ^ 2))) := by
  let g (k : ℕ) : ℝ := (-2 * s + (s ^ 2 + y ^ 2) / (k : ℝ)) / (k : ℝ)
  have ht : Tendsto (fun k : ℕ => -2 * s + (s ^ 2 + y ^ 2) / (k : ℝ)) atTop (𝓝 (-2 * s)) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (s ^ 2 + y ^ 2))
  have hg : Tendsto (fun k : ℕ => (k : ℝ) * g k) atTop (𝓝 (-2 * s)) := by
    refine ht.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with k hk
    have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    dsimp [g]
    field_simp
  have hmain := (Real.tendsto_one_add_pow_exp_of_tendsto hg).mul_const ((1 + s) ^ 2 + y ^ 2)
  refine hmain.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with k hk
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  dsimp [pommerenkeRatio, g]
  congr 2
  field_simp
  ring

private theorem OMA.pommerenke_ratio_signs :
    ∀ᶠ k : ℕ in atTop,
      pommerenkeRatio k 1 0 < 1 ∧ pommerenkeRatio k 3 16 < 1 ∧ 1 < pommerenkeRatio k 2 8 := by
  have hlim (s : ℕ) (y : ℝ) :
      Real.exp (-2 * (s : ℝ)) * ((1 + (s : ℝ)) ^ 2 + y ^ 2) =
        ((1 + (s : ℝ)) ^ 2 + y ^ 2) / Real.exp 1 ^ (2 * s) := by
    have he : 2 * (s : ℝ) = ((2 * s : ℕ) : ℝ) * 1 := by push_cast; ring
    rw [neg_mul, he, Real.exp_neg, inv_mul_eq_div, Real.exp_nat_mul]
  have h₁ : Real.exp (-2 * (1 : ℝ)) * ((1 + 1) ^ 2 + 0 ^ 2) < 1 := by
    have he := hlim 1 0
    simp only [Nat.cast_one] at he
    rw [he, div_lt_one (by positivity)]
    have h := pow_lt_pow_left₀ Real.exp_one_gt_two (by norm_num : (0 : ℝ) ≤ 2) (by decide : 2 ≠ 0)
    convert h using 1
    norm_num
  have h₂ : Real.exp (-2 * (3 : ℝ)) * ((1 + 3) ^ 2 + 16 ^ 2) < 1 := by
    change Real.exp (-2 * ↑(3 : ℕ)) * ((1 + ↑(3 : ℕ)) ^ 2 + 16 ^ 2) < 1
    rw [hlim 3 16, div_lt_one (by positivity)]
    have hlow : (8 / 3 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h := pow_lt_pow_left₀ hlow (by norm_num : (0 : ℝ) ≤ 8 / 3) (by decide : 6 ≠ 0)
    exact (show (1 + (3 : ℝ)) ^ 2 + 16 ^ 2 < (8 / 3 : ℝ) ^ 6 by norm_num).trans h
  have h₃ : 1 < Real.exp (-2 * (2 : ℝ)) * ((1 + 2) ^ 2 + 8 ^ 2) := by
    change 1 < Real.exp (-2 * ↑(2 : ℕ)) * ((1 + ↑(2 : ℕ)) ^ 2 + 8 ^ 2)
    rw [hlim 2 8, one_lt_div (by positivity)]
    have hupp : Real.exp 1 < (11 / 4 : ℝ) := by linarith [Real.exp_one_lt_d9]
    have h := pow_lt_pow_left₀ hupp (Real.exp_pos _).le (by decide : 4 ≠ 0)
    exact h.trans (show (11 / 4 : ℝ) ^ 4 < (1 + (2 : ℝ)) ^ 2 + 8 ^ 2 by norm_num)
  filter_upwards [(tendsto_pommerenkeRatio 1 0).eventually_lt_const h₁,
    (tendsto_pommerenkeRatio 3 16).eventually_lt_const h₂,
    (tendsto_pommerenkeRatio 2 8).eventually_const_lt h₃] with k h₁ h₂ h₃
  exact ⟨h₁, h₂, h₃⟩

private noncomputable def OMA.pommerenkePoly (k : ℕ) (a : ℝ) : ℂ[X] :=
  X ^ k * (X - C (a : ℂ))

private noncomputable def OMA.pommerenkeCritical (k : ℕ) : ℝ :=
  (1 + 1 / (k : ℝ)) * (k : ℝ) ^ ((1 : ℝ) / ((k : ℝ) + 1))

private noncomputable def OMA.pommerenkeScale (k : ℕ) (a : ℝ) : ℝ :=
  a / ((k : ℝ) + 1)

private noncomputable def OMA.pommerenkeHeight (k : ℕ) (a : ℝ) : ℝ :=
  ((pommerenkeScale k a) ^ (k + 1) * (k : ℝ) ^ k) ^ 2

private noncomputable def OMA.pommerenkePoint (k : ℕ) (a s y : ℝ) : ℂ :=
  ⟨pommerenkeScale k a * ((k : ℝ) - s), pommerenkeScale k a * y⟩

private theorem OMA.pommerenke_critical_pos (k : ℕ) (hk : 0 < k) : 0 < pommerenkeCritical k := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  unfold pommerenkeCritical
  positivity

private theorem OMA.pommerenke_height_critical (k : ℕ) (hk : 0 < k) :
    pommerenkeHeight k (pommerenkeCritical k) = 1 := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkp : 0 < (k : ℝ) + 1 := by positivity
  have hscale : pommerenkeScale k (pommerenkeCritical k) =
      (k : ℝ) ^ ((1 : ℝ) / ((k : ℝ) + 1)) / (k : ℝ) := by
    unfold pommerenkeScale pommerenkeCritical
    field_simp
  have hr : ((k : ℝ) ^ ((1 : ℝ) / ((k : ℝ) + 1))) ^ (k + 1) = k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hkR.le]
    push_cast
    rw [div_mul_cancel₀ _ hkp.ne', Real.rpow_one]
  unfold pommerenkeHeight
  rw [hscale, div_pow, hr, pow_succ]
  field_simp
  rw [pow_succ (k : ℝ) k]
  ring

private theorem OMA.pommerenke_height_gt (k : ℕ) (hk : 0 < k) {a : ℝ}
    (ha : pommerenkeCritical k < a) : 1 < pommerenkeHeight k a := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have ht : 0 < pommerenkeScale k (pommerenkeCritical k) :=
    div_pos (pommerenke_critical_pos k hk) (by positivity)
  have hs : pommerenkeScale k (pommerenkeCritical k) < pommerenkeScale k a :=
    div_lt_div_of_pos_right ha (by positivity)
  rw [← pommerenke_height_critical k hk]
  unfold pommerenkeHeight
  apply pow_lt_pow_left₀ _ (by positivity) (by decide)
  exact mul_lt_mul_of_pos_right (pow_lt_pow_left₀ hs ht.le (by omega)) (by positivity)

private theorem OMA.pommerenke_eval_sq (k : ℕ) (a : ℝ) (z : ℂ) :
    ‖(pommerenkePoly k a).eval z‖ ^ 2 =
      (z.re ^ 2 + z.im ^ 2) ^ k * ((z.re - a) ^ 2 + z.im ^ 2) := by
  simp only [pommerenkePoly, eval_mul, eval_pow, eval_X, eval_sub, eval_C, norm_mul, norm_pow]
  rw [mul_pow, pow_right_comm ‖z‖ k 2, Complex.sq_norm, Complex.sq_norm]
  simp [Complex.normSq_apply, pow_two]

private theorem OMA.pommerenke_scaled_eval_sq (k : ℕ) (hk : 0 < k) (a s y : ℝ) :
    ‖(pommerenkePoly k a).eval (pommerenkePoint k a s y)‖ ^ 2 =
      pommerenkeHeight k a * pommerenkeRatio k s y := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  let t := pommerenkeScale k a
  have ha : a = t * ((k : ℝ) + 1) := by
    dsimp [t, pommerenkeScale]
    field_simp
  rw [pommerenke_eval_sq]
  change ((t * ((k : ℝ) - s)) ^ 2 + (t * y) ^ 2) ^ k *
      ((t * ((k : ℝ) - s) - a) ^ 2 + (t * y) ^ 2) = _
  rw [show (t * ((k : ℝ) - s)) ^ 2 + (t * y) ^ 2 =
      t ^ 2 * (((k : ℝ) - s) ^ 2 + y ^ 2) by ring,
    show (t * ((k : ℝ) - s) - a) ^ 2 + (t * y) ^ 2 = t ^ 2 * ((1 + s) ^ 2 + y ^ 2) by
      rw [ha]
      ring]
  unfold pommerenkeRatio pommerenkeHeight
  change _ = (t ^ (k + 1) * (k : ℝ) ^ k) ^ 2 * _
  rw [mul_pow _ _ 2, pow_right_comm t (k + 1) 2, pow_right_comm (k : ℝ) k 2,
    pow_succ (t ^ 2) k, div_pow, mul_pow]
  field_simp

private theorem OMA.pommerenke_component_has_root (p : ℂ[X]) (hdeg : 0 < p.natDegree)
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

private def OMA.pommerenkeSet (k : ℕ) (a : ℝ) : Set ℂ :=
  Erdos1047.sublevelSet (pommerenkePoly k a) 1

private theorem OMA.pommerenke_mem_sq (k : ℕ) (a : ℝ) (z : ℂ) :
    z ∈ pommerenkeSet k a ↔ ‖(pommerenkePoly k a).eval z‖ ^ 2 ≤ 1 := by
  change ‖(pommerenkePoly k a).eval z‖ ≤ 1 ↔ _
  have h := pow_le_pow_iff_left₀ (norm_nonneg ((pommerenkePoly k a).eval z))
    (by norm_num : (0 : ℝ) ≤ 1) (by decide : (2 : ℕ) ≠ 0)
  simpa only [one_pow] using h.symm

private theorem OMA.pommerenke_compact (k : ℕ) {a : ℝ} (ha : 0 < a) :
    IsCompact (pommerenkeSet k a) := by
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_le (pommerenkePoly k a).continuous.norm continuous_const)
    (Metric.isBounded_ball.subset (t := Metric.ball (0 : ℂ) (a + 2)) ?_)
  intro z hz
  rw [Metric.mem_ball, dist_zero_right]
  by_contra! hn
  have hdist := norm_add_le (z - (a : ℂ)) (a : ℂ)
  rw [sub_add_cancel, Complex.norm_real, Real.norm_of_nonneg ha.le] at hdist
  have hn₁ : 1 ≤ ‖z‖ := by linarith
  have hn₂ : 2 ≤ ‖z - (a : ℂ)‖ := by linarith
  have hp : 2 ≤ ‖(pommerenkePoly k a).eval z‖ := by
    simp only [pommerenkePoly, eval_mul, eval_pow, eval_X, eval_sub, eval_C, norm_mul, norm_pow]
    exact hn₂.trans (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hn₁))
  change ‖(pommerenkePoly k a).eval z‖ ≤ 1 at hz
  linarith

private theorem OMA.pommerenke_barrier (k : ℕ) (hk : 0 < k) {a : ℝ}
    (ha : pommerenkeCritical k < a) (z : ℂ) (hz : z ∈ pommerenkeSet k a) :
    z.re ≠ pommerenkeScale k a * (k : ℝ) := by
  intro he
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have ha₀ := (pommerenke_critical_pos k hk).trans ha
  let t := pommerenkeScale k a
  have ht : 0 < t := div_pos ha₀ (by positivity)
  let y := z.im / t
  have hzEq : z = pommerenkePoint k a 0 y := by
    apply Complex.ext
    · change z.re = t * ((k : ℝ) - 0)
      simpa only [sub_zero] using he
    · change z.im = t * (z.im / t)
      field_simp
  have hRatio : 1 ≤ pommerenkeRatio k 0 y := by
    unfold pommerenkeRatio
    simp only [sub_zero, add_zero, one_pow]
    have hbase : 1 ≤ ((k : ℝ) ^ 2 + y ^ 2) / (k : ℝ) ^ 2 := by
      exact (le_div_iff₀ (by positivity)).2 (by nlinarith [sq_nonneg y])
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hbase) (by nlinarith [sq_nonneg y])
  have hs := (pommerenke_mem_sq k a z).1 hz
  rw [hzEq, pommerenke_scaled_eval_sq k hk] at hs
  have hHeight := pommerenke_height_gt k hk ha
  exact (not_lt_of_ge hs)
    (hHeight.trans_le (le_mul_of_one_le_right (by positivity) hRatio))

private theorem OMA.pommerenke_two_components (k : ℕ) (hk : 0 < k) {a : ℝ}
    (ha : pommerenkeCritical k < a) :
    (Erdos1047.componentsIn (pommerenkeSet k a)).ncard = 2 ∧
    ∀ z ∈ pommerenkeSet k a, z.re < pommerenkeScale k a * (k : ℝ) →
      z ∈ connectedComponentIn (pommerenkeSet k a) 0 := by
  classical
  let p := pommerenkePoly k a
  let S := pommerenkeSet k a
  let U := connectedComponentIn S 0
  let V := connectedComponentIn S (a : ℂ)
  let t := pommerenkeScale k a
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have ha₀ := (pommerenke_critical_pos k hk).trans ha
  have ht : 0 < t := div_pos ha₀ (by positivity)
  have hare : t * (k : ℝ) < (a : ℂ).re := by
    have hta : t * ((k : ℝ) + 1) = a := div_mul_cancel₀ _ (by positivity)
    rw [Complex.ofReal_re]
    linarith
  have h0re : (0 : ℂ).re < t * (k : ℝ) := by simpa using mul_pos ht hkR
  have hdegEq : p.natDegree = k + 1 := by
    unfold p pommerenkePoly
    rw [(monic_X_pow k).natDegree_mul (monic_X_sub_C _), natDegree_X_pow, natDegree_X_sub_C]
  have h0 : (0 : ℂ) ∈ S := by
    change ‖p.eval 0‖ ≤ 1
    simp [p, pommerenkePoly, zero_pow hk.ne']
  have hA : (a : ℂ) ∈ S := by
    change ‖p.eval (a : ℂ)‖ ≤ 1
    simp [p, pommerenkePoly]
  have hV : IsConnected V := isConnected_connectedComponentIn_iff.mpr hA
  have hVright (z : ℂ) (hz : z ∈ V) : t * (k : ℝ) < z.re :=
    hV.isPreconnected.lt_of_ne Complex.continuous_re.continuousOn
      (fun v hv => pommerenke_barrier k hk ha v (connectedComponentIn_subset _ _ hv))
      ⟨(a : ℂ), mem_connectedComponentIn hA, hare⟩ hz
  have hdiff : U ≠ V := by
    intro hEq
    have h0V : (0 : ℂ) ∈ V := hEq ▸ mem_connectedComponentIn h0
    exact (not_lt_of_ge h0re.le) (hVright 0 h0V)
  have hScompact : IsCompact S := pommerenke_compact k ha₀
  have hcomponents : Erdos1047.componentsIn S = {U, V} := by
    ext C
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨r, hr, hr0⟩ := pommerenke_component_has_root p (by omega) 1 rfl hScompact hz
      have hor : r = 0 ∨ r = (a : ℂ) := by
        simp only [p, pommerenkePoly, eval_mul, eval_pow, eval_X, eval_sub, eval_C,
          mul_eq_zero] at hr0
        rcases hr0 with hr0 | hr0
        · exact Or.inl (by by_contra! hn; exact (pow_ne_zero k hn) hr0)
        · exact Or.inr (sub_eq_zero.mp hr0)
      rcases hor with rfl | rfl
      · exact Set.mem_insert_iff.mpr (Or.inl (connectedComponentIn_eq hr))
      · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr (connectedComponentIn_eq hr)))
    · intro hC
      rcases Set.mem_insert_iff.mp hC with hC | hC
      · exact ⟨0, h0, hC⟩
      · exact ⟨(a : ℂ), hA, Set.mem_singleton_iff.mp hC⟩
  refine ⟨by rw [hcomponents, Set.ncard_pair hdiff], ?_⟩
  intro z hz hleft
  have hC : connectedComponentIn S z ∈ ({U, V} : Set (Set ℂ)) := by
    rw [← hcomponents]
    exact ⟨z, hz, rfl⟩
  rcases Set.mem_insert_iff.mp hC with hC | hC
  · change z ∈ U
    rw [← hC]
    exact mem_connectedComponentIn hz
  · have hEq : connectedComponentIn S z = V := Set.mem_singleton_iff.mp hC
    exact ((not_lt_of_ge hleft.le) (hVright z (hEq ▸ mem_connectedComponentIn hz))).elim

theorem OMA.solution : type_of% @Erdos1047.erdos_1047.variants.pommerenke := by
  change ∀ᶠ k : ℕ in atTop, ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ,
    pommerenkeCritical k < a → a < pommerenkeCritical k + δ →
    (Erdos1047.componentsIn (pommerenkeSet k a)).ncard = 2 ∧
    ¬ Convex ℝ (connectedComponentIn (pommerenkeSet k a) 0)
  filter_upwards [eventually_gt_atTop (0 : ℕ), pommerenke_ratio_signs] with k hk hs
  let a₀ := pommerenkeCritical k
  let U : Set ℝ := {a : ℝ | pommerenkeHeight k a * pommerenkeRatio k 1 0 < 1}
  let V : Set ℝ := {a : ℝ | pommerenkeHeight k a * pommerenkeRatio k 3 16 < 1}
  have hH : Continuous (pommerenkeHeight k) := by
    unfold pommerenkeHeight pommerenkeScale
    fun_prop
  have hOpen : IsOpen (U ∩ V) :=
    (isOpen_lt (hH.mul continuous_const) continuous_const).inter
      (isOpen_lt (hH.mul continuous_const) continuous_const)
  have hMem : a₀ ∈ U ∩ V := by
    constructor
    · change pommerenkeHeight k a₀ * pommerenkeRatio k 1 0 < 1
      rw [pommerenke_height_critical k hk, one_mul]
      exact hs.1
    · change pommerenkeHeight k a₀ * pommerenkeRatio k 3 16 < 1
      rw [pommerenke_height_critical k hk, one_mul]
      exact hs.2.1
  obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hOpen.mem_nhds hMem)
  refine ⟨u - a₀, sub_pos.mpr hu, ?_⟩
  intro a ha hb
  have hcut : a ∈ U ∩ V := hsub ⟨hl.trans ha, by linarith⟩
  obtain ⟨hcard, hleft⟩ := pommerenke_two_components k hk ha
  refine ⟨hcard, ?_⟩
  intro hConvex
  have ha₀ := (pommerenke_critical_pos k hk).trans ha
  let t := pommerenkeScale k a
  have ht : 0 < t := div_pos ha₀ (by positivity)
  let p₁ := pommerenkePoint k a 1 0
  let p₂ := pommerenkePoint k a 3 16
  have h₁ : p₁ ∈ pommerenkeSet k a := by
    rw [pommerenke_mem_sq, pommerenke_scaled_eval_sq k hk]
    exact (show pommerenkeHeight k a * pommerenkeRatio k 1 0 < 1 from hcut.1).le
  have h₂ : p₂ ∈ pommerenkeSet k a := by
    rw [pommerenke_mem_sq, pommerenke_scaled_eval_sq k hk]
    exact (show pommerenkeHeight k a * pommerenkeRatio k 3 16 < 1 from hcut.2).le
  have h₁re : p₁.re < t * (k : ℝ) := by dsimp [p₁, pommerenkePoint]; linarith
  have h₂re : p₂.re < t * (k : ℝ) := by dsimp [p₂, pommerenkePoint]; linarith
  have hmid := hConvex (hleft _ h₁ h₁re) (hleft _ h₂ h₂re)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (by norm_num) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hmidS := connectedComponentIn_subset (pommerenkeSet k a) 0 hmid
  have hEq : (1 / 2 : ℝ) • p₁ + (1 / 2 : ℝ) • p₂ = pommerenkePoint k a 2 8 := by
    apply Complex.ext <;> simp [p₁, p₂, pommerenkePoint, Complex.add_re, Complex.add_im] <;> ring
  rw [hEq, pommerenke_mem_sq, pommerenke_scaled_eval_sq k hk] at hmidS
  have hgt := pommerenke_height_gt k hk ha
  exact (not_lt_of_ge hmidS)
    (hgt.trans_le (le_mul_of_one_le_right (by positivity) hs.2.2.le))