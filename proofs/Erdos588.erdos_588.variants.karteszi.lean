import FormalConjectures.ErdosProblems.«588»

/-!
Kárteszi's grid construction. Project a finite digit grid into the plane by
choosing two linear forms that preserve distinct points and reflect collinear
triples. The coordinate lines of a face give the lower bound, and extra
points from the larger grid permit every intermediate cardinality.

Credit: @Genbox.
-/

open Set Finset
open scoped Affine EuclideanGeometry

namespace Karteszi

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

private theorem grid_line_bound {d k : ℕ} (F : (Fin d → ℝ) →ₗ[ℝ] ℝ²)
    (hinj : Function.Injective (F ∘ lift d k))
    (hreflect : ∀ a b c, a ≠ b → F (lift d k c) ∈ line[ℝ, F (lift d k a), F (lift d k b)] →
      lift d k c ∈ line[ℝ, lift d k a, lift d k b])
    {a b : Fin d → Fin k} (hab : a ≠ b) (S : Set ℝ²)
    (hS : S ⊆ Set.range (F ∘ lift d k)) :
    ((line[ℝ, F (lift d k a), F (lift d k b)] : Set ℝ²) ∩ S).ncard ≤ k := by
  classical
  let φ := F ∘ lift d k
  let L := ((line[ℝ, φ a, φ b] : AffineSubspace ℝ ℝ²) : Set ℝ²) ∩ S
  let U := φ ⁻¹' L
  obtain ⟨i, hi⟩ : ∃ i : Fin d, a i ≠ b i := by
    by_contra! h
    exact hab (funext h)
  have hL : φ '' U = L := by
    apply Set.Subset.antisymm (Set.image_preimage_subset _ _)
    intro x hx
    obtain ⟨u, rfl⟩ := hS hx.2
    exact ⟨u, hx, rfl⟩
  have hU : Set.InjOn (fun x => x i) U := by
    intro x hx y hy hxy
    obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp (hreflect a b x hab hx.1)
    obtain ⟨s, hs⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp (hreflect a b y hab hy.1)
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add] at hr hs
    have hr' := congrFun hr i
    have hs' := congrFun hs i
    change r * (((b i).val : ℝ) - (a i).val) + (a i).val = (x i).val at hr'
    change s * (((b i).val : ℝ) - (a i).val) + (a i).val = (y i).val at hs'
    have hxy' : ((x i).val : ℝ) = (y i).val := congrArg (fun j : Fin k => (j.val : ℝ)) hxy
    have hn : (((b i).val : ℝ) - (a i).val) ≠ 0 := by
      intro hz
      apply hi
      apply Fin.ext
      have hv : ((a i).val : ℝ) = (b i).val := (sub_eq_zero.mp hz).symm
      exact_mod_cast hv
    have hrs : r = s := mul_right_cancel₀ hn (by linarith only [hr', hs', hxy'])
    apply lift_inj d k
    rw [← hr, ← hs, hrs]
  change L.ncard ≤ k
  rw [← hL, Set.ncard_image_of_injective _ hinj]
  calc
    U.ncard ≤ (Set.univ : Set (Fin k)).ncard :=
      Set.ncard_le_ncard_of_injOn (fun x => x i) (fun _ _ => Set.mem_univ _) hU
    _ = k := by simp

private theorem grid_noncollinear {d k : ℕ} (hk : 1 ≤ k) (F : (Fin d → ℝ) →ₗ[ℝ] ℝ²)
    (hinj : Function.Injective (F ∘ lift d k))
    (hreflect : ∀ a b c, a ≠ b → F (lift d k c) ∈ line[ℝ, F (lift d k a), F (lift d k b)] →
      lift d k c ∈ line[ℝ, lift d k a, lift d k b])
    {S : Set ℝ²} (hS : S ⊆ Set.range (F ∘ lift d k)) :
    EuclideanGeometry.NonCollinearFor (k + 1) S := by
  intro T hTS hT hcard hcol
  let : Finite T := hT.to_subtype
  have hn : T.Nontrivial := Set.one_lt_ncard_iff_nontrivial.mp (by omega)
  obtain ⟨x, hx, y, hy, hxy⟩ := hn
  obtain ⟨a, rfl⟩ := hS (hTS hx)
  obtain ⟨b, rfl⟩ := hS (hTS hy)
  have hab : a ≠ b := fun h => hxy (congrArg (F ∘ lift d k) h)
  have hsub : T ⊆ (line[ℝ, F (lift d k a), F (lift d k b)] : Set ℝ²) ∩ T :=
    fun z hz => ⟨hcol.mem_affineSpan_of_mem_of_ne hx hy hz hxy, hz⟩
  have hc := Set.ncard_le_ncard hsub (hT.subset Set.inter_subset_right)
  have hbound := grid_line_bound F hinj hreflect hab T (hTS.trans hS)
  omega

private abbrev Axis (b k : ℕ) := Fin (b + 1) × (Fin b → Fin k)

private def axisPoint {b k : ℕ} [NeZero k] (I : Axis b k) (t : Fin k) :
    Fin (b + 2) → Fin k :=
  Fin.snoc (Fin.insertNth I.1 t I.2) 0

private theorem axisPoint_coord {b k : ℕ} [NeZero k] (I : Axis b k) (t : Fin k) :
    axisPoint I t I.1.castSucc = t := by
  simp [axisPoint, Fin.insertNth_apply_same]

private theorem axisPoint_other {b k : ℕ} [NeZero k] (I : Axis b k) (t : Fin k) (j : Fin b) :
    axisPoint I t (I.1.succAbove j).castSucc = I.2 j := by
  simp [axisPoint, Fin.insertNth_apply_succAbove]

private theorem axisPoint_injective {b k : ℕ} [NeZero k] (I : Axis b k) :
    Function.Injective (axisPoint I) := by
  intro t s h
  simpa only [axisPoint_coord] using congrFun h I.1.castSucc

private def digitOne (k : ℕ) (hk : 1 < k) : Fin k := ⟨1, hk⟩

private theorem digitOne_ne_zero {k : ℕ} [NeZero k] (hk : 1 < k) : digitOne k hk ≠ 0 := by
  intro h
  have h' := congrArg Fin.val h
  norm_num [digitOne] at h'

private theorem axisPoint_combo {b k : ℕ} [NeZero k] (hk : 1 < k)
    (I : Axis b k) (t : Fin k) :
    lift (b + 2) k (axisPoint I t) =
      (t.val : ℝ) • (lift (b + 2) k (axisPoint I (digitOne k hk)) -
        lift (b + 2) k (axisPoint I 0)) + lift (b + 2) k (axisPoint I 0) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [lift, axisPoint]
  · by_cases hi : i = I.1
    · subst i
      simp [lift, axisPoint_coord, digitOne]
    · obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hi
      rw [← hl]
      simp [lift, axisPoint_other]

private theorem axisPoint_image_mem {b k : ℕ} [NeZero k] (hk : 1 < k)
    (F : (Fin (b + 2) → ℝ) →ₗ[ℝ] ℝ²) (I : Axis b k) (t : Fin k) :
    F (lift (b + 2) k (axisPoint I t)) ∈
      line[ℝ, F (lift (b + 2) k (axisPoint I 0)), F (lift (b + 2) k (axisPoint I (digitOne k hk)))] := by
  apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
  refine ⟨(t.val : ℝ), ?_⟩
  rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  rw [axisPoint_combo hk I t]
  rw [map_add, map_smul, map_sub]

private theorem axis_coord_on_line {b k : ℕ} [NeZero k] (hk : 1 < k)
    (I : Axis b k) {a : Fin (b + 2) → Fin k}
    (ha : lift (b + 2) k a ∈ line[ℝ, lift (b + 2) k (axisPoint I 0),
      lift (b + 2) k (axisPoint I (digitOne k hk))]) (j : Fin b) :
    a (I.1.succAbove j).castSucc = I.2 j := by
  obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp ha
  rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add] at hr
  have h := congrFun hr (I.1.succAbove j).castSucc
  have h' : ((I.2 j).val : ℝ) = (a (I.1.succAbove j).castSucc).val := by
    simpa [lift, axisPoint_other] using h
  apply Fin.ext
  exact_mod_cast h'.symm

private theorem axis_subsets {b k : ℕ} [NeZero k] (F : (Fin (b + 2) → ℝ) →ₗ[ℝ] ℝ²)
    (I : Axis b k) (t : Fin k) :
    F (lift (b + 2) k (axisPoint I t)) ∈
      Set.range (fun a : Fin (b + 1) → Fin k => F (lift (b + 2) k (Fin.snoc a 0))) :=
  ⟨Fin.insertNth I.1 t I.2, rfl⟩

private noncomputable def axisLine {b k : ℕ} [NeZero k] (hk : 1 < k)
    (F : (Fin (b + 2) → ℝ) →ₗ[ℝ] ℝ²) (I : Axis b k) : AffineSubspace ℝ ℝ² :=
  line[ℝ, F (lift (b + 2) k (axisPoint I 0)), F (lift (b + 2) k (axisPoint I (digitOne k hk)))]

private theorem axis_ne {b k : ℕ} [NeZero k] (hk : 1 < k) (I : Axis b k) :
    axisPoint I 0 ≠ axisPoint I (digitOne k hk) :=
  fun h => digitOne_ne_zero hk ((axisPoint_injective I h).symm)

private theorem axisLine_injective {b k : ℕ} [NeZero k] (hk : 1 < k)
    (F : (Fin (b + 2) → ℝ) →ₗ[ℝ] ℝ²)
    (hreflect : ∀ x y z, x ≠ y →
      F (lift (b + 2) k z) ∈ line[ℝ, F (lift (b + 2) k x), F (lift (b + 2) k y)] →
      lift (b + 2) k z ∈ line[ℝ, lift (b + 2) k x, lift (b + 2) k y]) :
    Function.Injective (axisLine hk F) := by
  intro I J h
  have hcoords (t : Fin k) (j : Fin b) : axisPoint I t (J.1.succAbove j).castSucc = J.2 j := by
    apply axis_coord_on_line hk J _ j
    apply hreflect _ _ _ (axis_ne hk J)
    change F (lift (b + 2) k (axisPoint I t)) ∈ axisLine hk F J
    rw [← h]
    exact axisPoint_image_mem hk F I t
  have hdir : I.1 = J.1 := by
    by_contra hne
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hne
    have h0 := hcoords 0 j
    have h1 := hcoords (digitOne k hk) j
    rw [hj, axisPoint_coord] at h0 h1
    exact digitOne_ne_zero hk (h1.trans h0.symm)
  apply Prod.ext hdir
  funext j
  have hval := hcoords 0 j
  rw [← hdir, axisPoint_other] at hval
  exact hval

open EuclideanGeometry

private theorem finite_lines (k : ℕ) {S : Set ℝ²} (hf : S.Finite) :
    (linesWithPointsFor k S).Finite := by
  apply ((hf.prod hf).image (fun pq : ℝ² × ℝ² => affineSpan ℝ {pq.1, pq.2})).subset
  rintro L ⟨⟨p, hp, q, hq, -, rfl⟩, -⟩
  exact ⟨(p, q), ⟨hp, hq⟩, rfl⟩

private theorem max_lower {k n : ℕ} {S : Set ℝ²} (hf : S.Finite) (hc : S.ncard = n)
    (hnc : NonCollinearFor (k + 1) S) :
    (linesWithPointsFor k S).ncard ≤ Erdos588.numLinesWithPointsMax k n := by
  apply le_csSup
  · refine ⟨n ^ 2, ?_⟩
    rintro _ ⟨T, hTc, hTf, -, rfl⟩
    let p := fun pq : ℝ² × ℝ² => affineSpan ℝ {pq.1, pq.2}
    have hsub : linesWithPointsFor k T ⊆ p '' (T ×ˢ T) := by
      rintro L ⟨⟨x, hx, y, hy, -, rfl⟩, -⟩
      exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
    have hp := hTf.prod hTf
    calc
      _ ≤ (p '' (T ×ˢ T)).ncard := Set.ncard_le_ncard hsub (hp.image p)
      _ ≤ (T ×ˢ T).ncard := Set.ncard_image_le hp
      _ = n ^ 2 := by simp [Set.ncard_prod, hTc, pow_two]
  · exact ⟨S, hc, hf, hnc, rfl⟩

/-- The zero-coordinate face provides the lines, and the larger grid supplies spare points. -/
theorem grid_lower (b k n : ℕ) (hk : 1 < k)
    (hn₁ : k ^ (b + 1) ≤ n) (hn₂ : n ≤ k ^ (b + 2)) :
    (b + 1) * k ^ b ≤ Erdos588.numLinesWithPointsMax k n := by
  classical
  let : NeZero k := ⟨by omega⟩
  obtain ⟨F, hinj, hreflect⟩ := exists_projection (b + 2) k
  let φ := F ∘ lift (b + 2) k
  let face (a : Fin (b + 1) → Fin k) := φ (Fin.snoc a 0)
  have hface : Function.Injective face := by
    intro a c h
    funext i
    simpa only [Fin.snoc_castSucc] using congrFun (hinj h) i.castSucc
  have hsub : Set.range face ⊆ Set.range φ := by
    rintro _ ⟨a, rfl⟩
    exact ⟨Fin.snoc a 0, rfl⟩
  have hCard₁ : (Set.range face).ncard = k ^ (b + 1) := by
    rw [Set.ncard_range_of_injective hface]
    simp [Nat.card_eq_fintype_card]
  have hCard₂ : (Set.range φ).ncard = k ^ (b + 2) := by
    rw [Set.ncard_range_of_injective hinj]
    simp [Nat.card_eq_fintype_card]
  obtain ⟨S, h₁, h₂, hcard⟩ := Set.exists_subsuperset_card_eq hsub (hCard₁.symm ▸ hn₁) (hCard₂.symm ▸ hn₂)
  have hs : S.Finite := (Set.finite_range φ).subset h₂
  have hAxis (I : Axis b k) : axisLine hk F I ∈ linesWithPointsFor k S := by
    have hm (t : Fin k) : F (lift (b + 2) k (axisPoint I t)) ∈ S :=
      h₁ (axis_subsets F I t)
    have hx : F (lift (b + 2) k (axisPoint I 0)) ≠
        F (lift (b + 2) k (axisPoint I (digitOne k hk))) :=
      fun h => axis_ne hk I (hinj h)
    refine ⟨⟨_, hm 0, _, hm (digitOne k hk), hx, rfl⟩, ?_⟩
    apply le_antisymm (grid_line_bound F hinj hreflect (axis_ne hk I) S h₂)
    let P := fun t : Fin k => φ (axisPoint I t)
    have hPinj : Function.Injective P := hinj.comp (axisPoint_injective I)
    have hP : (Set.range P).ncard = k := by
      rw [Set.ncard_range_of_injective hPinj]
      simp
    have hPS : Set.range P ⊆ (axisLine hk F I : Set ℝ²) ∩ S := by
      rintro _ ⟨t, rfl⟩
      exact ⟨axisPoint_image_mem hk F I t, hm t⟩
    exact hP.symm.le.trans (Set.ncard_le_ncard hPS (hs.subset Set.inter_subset_right))
  have haxes : (Set.range (axisLine hk F)).ncard = (b + 1) * k ^ b := by
    rw [Set.ncard_range_of_injective (axisLine_injective hk F hreflect)]
    simp [Axis, Nat.card_eq_fintype_card]
  rw [← haxes]
  exact (Set.ncard_le_ncard (Set.range_subset_iff.mpr hAxis) (finite_lines k hs)).trans
    (max_lower hs hcard (grid_noncollinear (by omega) F hinj hreflect h₂))

end Karteszi
open Filter Karteszi

theorem OMA.solution : type_of% @Erdos588.erdos_588.variants.karteszi := by
  intro k hk
  have hk' : 1 < k := by omega
  have hkR : (1 : ℝ) < k := by exact_mod_cast hk'
  have hlog : 0 < Real.log (k : ℝ) := Real.log_pos hkR
  let c : ℝ := 1 / (2 * (k : ℝ) ^ 2 * Real.log k)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  filter_upwards [eventually_ge_atTop k] with n hn
  have hn0 : n ≠ 0 := by omega
  have hd : 1 ≤ Nat.log k n := (Nat.le_log_iff_pow_le hk' hn0).mpr (by simpa)
  obtain ⟨b, hb⟩ := Nat.exists_eq_succ_of_ne_zero (show Nat.log k n ≠ 0 by omega)
  have h₁ : k ^ (b + 1) ≤ n := by
    simpa only [hb] using Nat.pow_log_le_self k hn0
  have h₂ : n < k ^ (b + 2) := by
    simpa only [hb] using Nat.lt_pow_succ_log_self hk' n
  have hNR : (n : ℝ) ≤ (k : ℝ) ^ (b + 2) := by exact_mod_cast h₂.le
  have hN : (n : ℝ) ≤ (k : ℝ) ^ 2 * (k : ℝ) ^ b := by
    rw [← pow_add, add_comm 2 b]
    exact hNR
  have hD : Real.log (n : ℝ) ≤ 2 * ((b : ℝ) + 1) * Real.log k := by
    have np : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
    have kp : 0 < (k : ℝ) ^ (b + 2) := by positivity
    calc
      _ ≤ Real.log ((k : ℝ) ^ (b + 2)) := (Real.log_le_log_iff np kp).mpr hNR
      _ = ((b : ℝ) + 2) * Real.log k := by simp [Real.log_pow]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) b]) hlog.le
  have hprod := mul_le_mul hN hD (Real.log_natCast_nonneg n)
    (by positivity : 0 ≤ (k : ℝ) ^ 2 * (k : ℝ) ^ b)
  calc
    c * (n : ℝ) * Real.log n = c * ((n : ℝ) * Real.log n) := mul_assoc _ _ _
    _ ≤ c * (((k : ℝ) ^ 2 * (k : ℝ) ^ b) * (2 * ((b : ℝ) + 1) * Real.log k)) :=
      mul_le_mul_of_nonneg_left hprod hc.le
    _ = ((b : ℝ) + 1) * (k : ℝ) ^ b := by
      dsimp [c]
      field_simp [show (k : ℝ) ≠ 0 by positivity, hlog.ne']
    _ ≤ (Erdos588.numLinesWithPointsMax k n : ℝ) := by
      exact_mod_cast grid_lower b k n hk' h₁ h₂.le