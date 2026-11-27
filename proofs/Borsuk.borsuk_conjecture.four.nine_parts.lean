import FormalConjectures.Wikipedia.BorsukConjecture

/-! A nine-part diameter cover using a smallest enclosing ball and a contact point. -/

open Metric Bornology
open scoped EuclideanGeometry InnerProductSpace

namespace BorsukNine

section EnclosingBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

private theorem enclosing (K : Set E) (hc : IsCompact K) (hK : K.Nontrivial) :
    ∃ c a : E, ∃ r : ℝ, a ∈ K ∧ dist a c = r ∧
      (∀ x ∈ K, dist x c ≤ r) ∧ 0 < r ∧ 2 * r^2 < (diam K)^2 := by
  classical
  let D := diam K
  have hd : 0 < D := diam_pos hK hc.isBounded
  let R (c : E) : ℝ := sSup ((fun x => dist x c) '' K)
  have hex (c : E) : ∃ x ∈ K, dist x c = R c := by
    obtain ⟨x, hx, hm⟩ := hc.exists_isMaxOn hK.nonempty (continuous_id.dist continuous_const).continuousOn
    refine ⟨x, hx, le_antisymm (le_csSup ?_ ⟨x, hx, rfl⟩) ?_⟩
    · exact ⟨dist x c, by rintro _ ⟨y, hy, rfl⟩; exact hm hy⟩
    · exact csSup_le (hK.nonempty.image _) (by rintro _ ⟨y, hy, rfl⟩; exact hm hy)
  have habove (c x : E) (hx : x ∈ K) : dist x c ≤ R c := by
    change dist x c ≤ sSup ((fun y => dist y c) '' K)
    exact le_csSup (hc.image (continuous_id.dist continuous_const)).bddAbove
      (Set.mem_image_of_mem _ hx)
  have hLip (c d : E) : R c ≤ R d + dist c d := by
    obtain ⟨x, hx, hxr⟩ := hex c
    rw [← hxr]
    exact (dist_triangle x d c).trans (by rw [dist_comm d c]; gcongr; exact habove d x hx)
  have hR : Continuous R := by
    apply LipschitzWith.continuous (K := 1)
    apply LipschitzWith.of_dist_le_mul
    intro c d
    rw [NNReal.coe_one, one_mul, Real.dist_eq, abs_le]
    constructor
    · linarith [hLip d c, dist_comm d c]
    · linarith [hLip c d]
  obtain ⟨a₀, ha₀⟩ := hK.nonempty
  obtain ⟨c, _, hmin⟩ := (isCompact_closedBall a₀ D).exists_isMinOn
    ⟨a₀, mem_closedBall_self hd.le⟩ hR.continuousOn
  have hmic (d : E) : R c ≤ R d := by
    by_cases H : d ∈ closedBall a₀ D
    · exact hmin H
    · have h0 : R a₀ ≤ D := by
        obtain ⟨x, hx, hr⟩ := hex a₀
        rw [← hr]
        exact dist_le_diam_of_mem hc.isBounded hx ha₀
      have h1 : D < dist d a₀ := lt_of_not_ge H
      rw [dist_comm] at h1
      exact (hmin (mem_closedBall_self hd.le)).trans (h0.trans (h1.le.trans (habove d a₀ ha₀)))
  let r := R c
  obtain ⟨a, ha, har⟩ := hex c
  have hr : 0 < r := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hK
    linarith [dist_pos.mpr hxy, dist_triangle x c y, habove c x hx,
      habove c y hy, dist_comm c y]
  refine ⟨c, a, r, ha, har, habove c, hr, ?_⟩
  change 2 * r^2 < D^2
  by_contra! H
  let A : Set E := K ∩ {x | dist x c = r}
  have hA : IsCompact A := hc.inter_right (isClosed_eq (continuous_id.dist continuous_const) continuous_const)
  have haA : a ∈ A := ⟨ha, har⟩
  have hinner (x y : E) (hx : x ∈ A) (hy : y ∈ A) : 0 ≤ ⟪x-c,y-c⟫_ℝ := by
    have hxy := dist_le_diam_of_mem hc.isBounded hx.1 hy.1
    have hs : dist x y ^ 2 ≤ D^2 :=
      pow_le_pow_left₀ dist_nonneg hxy 2
    rw [dist_eq_norm] at hs
    rw [← sub_sub_sub_cancel_right x y c, norm_sub_sq_real] at hs
    have hx' := hx.2
    have hy' := hy.2
    change dist x c = r at hx'
    change dist y c = r at hy'
    rw [dist_eq_norm] at hx' hy'
    rw [hx', hy'] at hs
    linarith only [hs, H]
  let U (y : A) : Set E := {x | 0 < ⟪x-c, y.val-c⟫_ℝ}
  have hu (y : A) : IsOpen (U y) := isOpen_lt continuous_const
    ((continuous_id.sub continuous_const).inner continuous_const)
  have hsub : A ⊆ ⋃ y : A, U y := by
    intro x hx
    have hxc := hx.2
    change dist x c = r at hxc
    rw [dist_eq_norm] at hxc
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    change 0 < ⟪x-c,x-c⟫_ℝ
    rw [real_inner_self_eq_norm_sq, hxc]
    positivity
  obtain ⟨T, hT⟩ := hA.elim_finite_subcover U hu hsub
  let v : E := ∑ y ∈ T, (y.val - c)
  have hpos (x : E) (hx : x ∈ A) : 0 < ⟪x-c,v⟫_ℝ := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hT hx)
    obtain ⟨hiT, hUi⟩ := Set.mem_iUnion.mp hi
    dsimp [v]
    rw [inner_sum]
    exact Finset.sum_pos' (fun y _ => hinner x y.val hx y.property) ⟨i, hiT, hUi⟩
  let g (x : E) : ℝ := ⟪x-c,v⟫_ℝ
  have hg : Continuous g := (continuous_id.sub continuous_const).inner continuous_const
  obtain ⟨z, hz, hzn⟩ := hA.exists_isMinOn ⟨a, haA⟩ hg.continuousOn
  let μ := g z / 2
  have hμ : 0 < μ := by dsimp [μ, g]; linarith [hpos z hz]
  let L := K ∩ {x | g x ≤ μ}
  have hL : IsCompact L := hc.inter_right (isClosed_le hg continuous_const)
  have hless (x : E) (hx : x ∈ L) : dist x c < r := by
    refine (habove c x hx.1).lt_of_ne fun he => ?_
    have hz' := hzn (show x ∈ A from ⟨hx.1, he⟩)
    have hm : g x ≤ μ := hx.2
    change g z ≤ g x at hz'
    dsimp [μ] at hm hμ
    linarith only [hm, hμ, hz']
  have hsmall : ∃ r' : ℝ, r' < r ∧ ∀ x ∈ L, dist x c ≤ r' := by
    by_cases hne : L.Nonempty
    · obtain ⟨w, hw, hwmax⟩ := hL.exists_isMaxOn hne
        (continuous_id.dist continuous_const).continuousOn
      exact ⟨dist w c, hless w hw, fun _ hx => hwmax hx⟩
    · exact ⟨0, hr, fun x hx => (hne ⟨x, hx⟩).elim⟩
  obtain ⟨r', hr', hlow⟩ := hsmall
  let ε := min ((r - r') / (‖v‖ + 1)) (μ / (‖v‖^2 + 1)) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    apply div_pos _ (by norm_num)
    exact lt_min (by positivity) (by positivity)
  have hε₁ : ε * (‖v‖ + 1) < r - r' := by
    rw [← lt_div_iff₀ (by positivity)]
    have hh := min_le_left ((r - r') / (‖v‖ + 1)) (μ / (‖v‖^2 + 1))
    dsimp [ε] at *
    linarith
  have hε₂ : ε * (‖v‖^2 + 1) < μ := by
    rw [← lt_div_iff₀ (by positivity)]
    have hh := min_le_right ((r - r') / (‖v‖ + 1)) (μ / (‖v‖^2 + 1))
    dsimp [ε] at *
    linarith
  let d : E := c + ε • v
  have hstrict (x : E) (hx : x ∈ K) : dist x d < r := by
    by_cases hlo : g x ≤ μ
    · have hnorm : dist c d = ε * ‖v‖ := by
        rw [dist_comm, dist_eq_norm]
        dsimp [d]
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
      linarith only [dist_triangle x c d, hlow x ⟨hx, hlo⟩, hnorm, hε₁, hε]
    · have hx2 := pow_le_pow_left₀ dist_nonneg (habove c x hx) 2
      have hgx : μ < g x := lt_of_not_ge hlo
      rw [dist_eq_norm] at hx2
      have hsq : dist x d ^ 2 = dist x c ^ 2 - 2 * ε * g x + ε^2 * ‖v‖^2 := by
        simp only [dist_eq_norm, d, sub_add_eq_sub_sub, norm_sub_sq_real (x - c),
          inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
        dsimp [g]
        ring
      rw [← dist_eq_norm] at hx2
      have hh : dist x d ^ 2 < r^2 := by
        nlinarith only [hsq, hx2, mul_lt_mul_of_pos_left hgx hε,
          mul_lt_mul_of_pos_left hε₂ hε, mul_pos hε hμ, sq_nonneg ε]
      exact lt_of_pow_lt_pow_left₀ 2 hr.le hh
  obtain ⟨w, hw, hw'⟩ := hex d
  exact (not_lt_of_ge (hmic d)) (hw' ▸ hstrict w hw)

end EnclosingBall

private theorem compact_diam_lt {E : Type*} [MetricSpace E] {S K : Set E}
    (hc : IsCompact S) (hK : IsBounded K) (hnt : K.Nontrivial)
    (hsmall : ∀ x ∈ S, ∀ y ∈ S, dist x y < diam K) :
    ediam S < ediam K := by
  rcases S.eq_empty_or_nonempty with h | hn
  · simpa [h] using ediam_pos_iff.mpr hnt
  obtain ⟨p, hp, hm⟩ := (hc.prod hc).exists_isMaxOn (hn.prod hn)
    (continuous_fst.dist continuous_snd).continuousOn
  have hdiam : ediam S ≤ ENNReal.ofReal (dist p.1 p.2) := by
    apply ediam_le
    intro x hx y hy
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (hm (show (x, y) ∈ S ×ˢ S from ⟨hx, hy⟩))
  apply hdiam.trans_lt
  have he : ENNReal.ofReal (diam K) = ediam K :=
    ENNReal.ofReal_toReal hK.ediam_ne_top
  rw [← he]
  exact (ENNReal.ofReal_lt_ofReal_iff (diam_pos hnt hK)).mpr (hsmall _ hp.1 _ hp.2)

private theorem nine_cover (K : Set (ℝ^4)) (hc : IsCompact K) (hK : K.Nontrivial) :
    Borsuk.HasBorsukCover 9 K := by
  classical
  obtain ⟨c, a, r, ha, har, hball, hr, hsmall⟩ := enclosing K hc hK
  let D := diam K
  let E := ℝ^4
  let u : E := r⁻¹ • (a - c)
  let n := Fin.last 3
  have hunit : ‖u‖ = 1 := by
    have har' : ‖a-c‖ = r := by simpa only [dist_eq_norm] using har
    simp [u, norm_smul, Real.norm_eq_abs, abs_of_pos hr, har', hr.ne']
  let v : Fin 4 → E := fun _ => u
  have horth : Orthonormal ℝ (({n} : Set (Fin 4)).domRestrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    have he : i = j := Subtype.ext (i.property.trans j.property.symm)
    simp [he, v, Set.domRestrict, hunit]
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq
    (show Module.finrank ℝ E = Fintype.card (Fin 4) by simp [E])
  have hcontact : a - c = r • b n := by
    rw [hb n (Set.mem_singleton _)]
    change a - c = r • (r⁻¹ • (a-c))
    simp [smul_smul, hr.ne']
  let f (i : Fin 4) (x : E) : ℝ := b.repr (x-c) i
  let t := f n
  have hcont (i : Fin 4) : Continuous (f i) :=
    (PiLp.continuous_apply 2 _ i).comp
      (b.repr.continuous.comp (continuous_id.sub continuous_const))
  have hnorm (x : E) (hx : x ∈ K) : ‖x-c‖^2 ≤ r^2 := by
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    simpa only [dist_eq_norm] using hball x hx
  have hinnera (x : E) : ⟪x-c,a-c⟫_ℝ = r * t x := by
    rw [hcontact, inner_smul_right, real_inner_comm (b n) (x-c), ← b.repr_apply_apply]
  have hda (x : E) : dist x a ^ 2 = ‖x-c‖^2 - 2 * r * t x + r^2 := by
    have ha' : ‖a-c‖ = r := by simpa only [dist_eq_norm] using har
    rw [dist_eq_norm, ← sub_sub_sub_cancel_right x a c, norm_sub_sq_real, hinnera, ha']
    ring
  have hpair (x y : E) (hx : x ∈ K) (hy : y ∈ K)
      (htx : t x ≤ 3 * r / 4) (hty : t y ≤ 3 * r / 4)
      (hsign : ∀ i : Fin 3, 0 ≤ f i.castSucc x * f i.castSucc y) : dist x y < D := by
    have hinner : t x * t y ≤ ⟪x-c,y-c⟫_ℝ := by
      have hi (i : Fin 4) : ⟪x-c,b i⟫_ℝ * ⟪b i,y-c⟫_ℝ = f i x * f i y := by
        simp only [f, b.repr_apply_apply, real_inner_comm (b i) (x-c)]
      have hsum : (∑ i : Fin 4, f i x * f i y) = ⟪x-c,y-c⟫_ℝ := by
        simpa only [hi] using b.sum_inner_mul_inner (x-c) (y-c)
      rw [Fin.sum_univ_castSucc] at hsum
      rw [← hsum]
      exact le_add_of_nonneg_left (Finset.sum_nonneg (fun i _ => hsign i))
    have hxy :
        dist x y ^ 2 ≤ ‖x-c‖^2 + ‖y-c‖^2 - 2 * t x * t y := by
      rw [dist_eq_norm, ← sub_sub_sub_cancel_right x y c, norm_sub_sq_real]
      nlinarith only [hinner]
    apply lt_of_pow_lt_pow_left₀ 2 (diam_nonneg (s := K))
    by_cases h : 0 ≤ t x * t y
    · nlinarith only [hxy, hsmall, hnorm x hx, hnorm y hy, h]
    · by_cases hxneg : t x < 0
      · have hbound := pow_le_pow_left₀ dist_nonneg (dist_le_diam_of_mem hc.isBounded hx ha) 2
        rw [hda] at hbound
        nlinarith only [hxy, hbound, hnorm y hy,
          mul_neg_of_neg_of_pos hxneg (show 0 < r - t y by linarith)]
      · have hyneg : t y < 0 := by
          by_contra! hn
          exact h (mul_nonneg (le_of_not_gt hxneg) hn)
        have hbound := pow_le_pow_left₀ dist_nonneg (dist_le_diam_of_mem hc.isBounded hy ha) 2
        rw [hda] at hbound
        nlinarith only [hxy, hbound, hnorm x hx,
          mul_neg_of_neg_of_pos hyneg (show 0 < r - t x by linarith)]
  let U : Option (Fin 3 → Bool) → Set E
    | none => K ∩ {x | 3 * r / 4 ≤ t x}
    | some σ => K ∩ ({x | t x ≤ 3 * r / 4} ∩
      ⋂ i : Fin 3, {x | if σ i then 0 ≤ f i.castSucc x else f i.castSucc x ≤ 0})
  let e : Option (Fin 3 → Bool) ≃ Fin 9 := Fintype.equivFinOfCardEq (by simp)
  refine ⟨fun i => U (e.symm i), ?_, ?_⟩
  · intro x hx
    by_cases ht : 3 * r / 4 ≤ t x
    · exact Set.mem_iUnion.mpr ⟨e none, by simpa only [e.symm_apply_apply] using
        (show x ∈ U none from ⟨hx, ht⟩)⟩
    · let σ (i : Fin 3) : Bool := decide (0 ≤ f i.castSucc x)
      refine Set.mem_iUnion.mpr ⟨e (some σ), ?_⟩
      rw [e.symm_apply_apply]
      refine ⟨hx, (le_of_not_ge ht), Set.mem_iInter.mpr (fun i => ?_)⟩
      change if σ i then 0 ≤ f i.castSucc x else f i.castSucc x ≤ 0
      dsimp [σ]
      by_cases hi : 0 ≤ f i.castSucc x
      · simp [hi]
      · simp [hi, le_of_not_ge hi]
  · have hU (o : Option (Fin 3 → Bool)) : ediam (U o) < ediam K := by
      refine compact_diam_lt ?_ hc.isBounded hK ?_
      · rcases o with _ | σ
        · exact hc.inter_right (isClosed_le continuous_const (hcont n))
        · apply hc.inter_right
          apply (isClosed_le (hcont n) continuous_const).inter
          apply isClosed_iInter
          intro j
          cases h : σ j
          · simpa only [h, Bool.false_eq_true, ↓reduceIte] using
              isClosed_le (hcont j.castSucc) (continuous_const (y := (0 : ℝ)))
          · simpa only [h, ↓reduceIte] using
              isClosed_le (continuous_const (y := (0 : ℝ))) (hcont j.castSucc)
      · rcases o with _ | σ
        · intro x hx y hy
          have hxa : dist x a ^ 2 ≤ r ^ 2 / 2 := by
            rw [hda]
            nlinarith only [hnorm x hx.1, mul_le_mul_of_nonneg_left hx.2 hr.le]
          have hya : dist y a ^ 2 ≤ r ^ 2 / 2 := by
            rw [hda]
            nlinarith only [hnorm y hy.1, mul_le_mul_of_nonneg_left hy.2 hr.le]
          have hsum : (dist x a + dist y a)^2 < D^2 := by
            nlinarith only [hxa, hya, sq_nonneg (dist x a - dist y a), hsmall]
          exact (dist_triangle_right x y a).trans_lt
            (lt_of_pow_lt_pow_left₀ 2 diam_nonneg hsum)
        · intro x hx y hy
          apply hpair x y hx.1 hy.1 hx.2.1 hy.2.1
          intro j
          have hxj := Set.mem_iInter.mp hx.2.2 j
          have hyj := Set.mem_iInter.mp hy.2.2 j
          change (if σ j then 0 ≤ f j.castSucc x else f j.castSucc x ≤ 0) at hxj
          change (if σ j then 0 ≤ f j.castSucc y else f j.castSucc y ≤ 0) at hyj
          cases h : σ j
          · exact mul_nonneg_of_nonpos_of_nonpos (by simpa [h] using hxj) (by simpa [h] using hyj)
          · exact mul_nonneg (by simpa [h] using hxj) (by simpa [h] using hyj)
    exact fun i => hU (e.symm i)

end BorsukNine

theorem OMA.solution : type_of% @Borsuk.borsuk_conjecture.four.nine_parts := by
  intro s hs hnt
  obtain ⟨c, hcover, hlt⟩ := BorsukNine.nine_cover (closure s)
    (isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, hs.closure⟩)
    (hnt.mono subset_closure)
  exact ⟨c, subset_closure.trans hcover, by simpa only [ediam_closure] using hlt⟩