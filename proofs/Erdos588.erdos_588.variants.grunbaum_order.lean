import FormalConjectures.ErdosProblems.«588»

/-!
A family of progressions in parallel layers supplies many rich lines.
The points of each layer lie on a sphere.
The construction uses the lattice-sphere idea of Solymosi and Stojaković (arXiv:1107.0327).

Credit: @Genbox.
-/

open Set Finset
open scoped Affine EuclideanGeometry

namespace LayeredGrid

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

private theorem line_constant {D : ℕ} {p q r : Fin D → ℝ} (i : Fin D) (hpq : p i = q i)
    (hr : r ∈ line[ℝ, p, q]) : r i = p i := by
  obtain ⟨a, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hr
  rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add] at hr
  simpa [← hpq] using (congrFun hr i).symm

private theorem line_coord_inj {D : ℕ} {p q : Fin D → ℝ} (i : Fin D) (hpq : p i ≠ q i) :
    Set.InjOn (fun r => r i) (line[ℝ, p, q] : Set (Fin D → ℝ)) := by
  intro r hr s hs heq
  obtain ⟨a, hra⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hr
  obtain ⟨b, hsb⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hs
  rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add] at hra hsb
  have h₁ : a * (q i - p i) + p i = r i := congrFun hra i
  have h₂ : b * (q i - p i) + p i = s i := congrFun hsb i
  have hab : a = b := mul_right_cancel₀ (sub_ne_zero.mpr hpq.symm) (by linarith only [h₁, h₂, heq])
  rw [← hra, ← hsb, hab]

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

private theorem fresh_point (S : Set ℝ²) (hS : S.Finite) :
    ∃ p : ℝ², p ∉ S ∧ ∀ u ∈ S, ∀ v ∈ S, p ∉ line[ℝ, u, v] := by
  obtain ⟨x, hx⟩ := (hS.image (fun p : ℝ² => p 0)).exists_notMem
  let atX (uv : ℝ² × ℝ²) :=
    uv.1 1 + (x - uv.1 0) / (uv.2 0 - uv.1 0) * (uv.2 1 - uv.1 1)
  obtain ⟨y, hy⟩ := ((hS.prod hS).image atX).exists_notMem
  let p : ℝ² := WithLp.toLp 2 ![x,y]
  have p0 : p 0 = x := rfl
  have p1 : p 1 = y := rfl
  refine ⟨p, fun hp => hx ⟨p, hp, p0⟩, ?_⟩
  intro u hu v hv hline
  obtain ⟨a, ha⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hline
  rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add] at ha
  have h₀ : a * (v 0 - u 0) + u 0 = x := p0 ▸ congrArg (fun p : ℝ² => p 0) ha
  have h₁ : a * (v 1 - u 1) + u 1 = y := p1 ▸ congrArg (fun p : ℝ² => p 1) ha
  have hne : v 0 - u 0 ≠ 0 := by
    intro he
    apply hx
    refine ⟨u, hu, ?_⟩
    simpa [he] using h₀
  have halpha : a = (x - u 0) / (v 0 - u 0) :=
    (eq_div_iff hne).mpr (by linarith only [h₀])
  apply hy
  refine ⟨(u,v), ⟨hu,hv⟩, ?_⟩
  change u 1 + (x - u 0) / (v 0 - u 0) * (v 1 - u 1) = y
  rw [← halpha, add_comm, h₁]

private theorem extend_one {k : ℕ} (hk : 2 ≤ k) {S : Set ℝ²}
    (hS : S.Finite) (hnc : NonCollinearFor (k + 1) S) :
    ∃ T : Set ℝ², T.Finite ∧ T.ncard = S.ncard + 1 ∧ NonCollinearFor (k + 1) T ∧
      linesWithPointsFor k S ⊆ linesWithPointsFor k T := by
  obtain ⟨p, hp, hoff⟩ := fresh_point S hS
  refine ⟨insert p S, hS.insert p, ncard_insert_of_notMem hp hS, ?_, ?_⟩
  · intro A hA hAf hAc hcol
    by_cases hpa : p ∈ A
    · let B := A \ {p}
      have hBf : B.Finite := hAf.subset Set.sdiff_subset
      let : Finite B := hBf.to_subtype
      have hcard : B.ncard = k := by
        change (A \ {p}).ncard = k
        rw [ncard_sdiff_singleton_of_mem hpa, hAc]
        omega
      have hbt : B.Nontrivial := one_lt_ncard_iff_nontrivial.mp (by omega)
      obtain ⟨u, hu, v, hv, huv⟩ := hbt
      have hBS : B ⊆ S := by
        intro q hq
        rcases Set.mem_insert_iff.mp (hA hq.1) with he | he
        · exact (hq.2 he).elim
        · exact he
      exact hoff u (hBS hu) v (hBS hv) (hcol.mem_affineSpan_of_mem_of_ne hu.1 hv.1 hpa huv)
    · apply hnc A _ hAf hAc hcol
      intro q hq
      rcases Set.mem_insert_iff.mp (hA hq) with rfl | hq'
      · exact (hpa hq).elim
      · exact hq'
  · rintro L ⟨⟨u, hu, v, hv, huv, rfl⟩, hcard⟩
    refine ⟨⟨u, Set.mem_insert_of_mem _ hu, v, Set.mem_insert_of_mem _ hv, huv, rfl⟩, ?_⟩
    have he : ((line[ℝ, u, v] : AffineSubspace ℝ ℝ²) : Set ℝ²) ∩ insert p S =
        ((line[ℝ, u, v] : AffineSubspace ℝ ℝ²) : Set ℝ²) ∩ S := by
      ext q
      simp only [Set.mem_inter_iff, Set.mem_insert_iff]
      exact ⟨fun ⟨hq, h⟩ => ⟨hq, h.resolve_left (fun h => hoff u hu v hv (h ▸ hq))⟩,
        fun ⟨hq, h⟩ => ⟨hq, Or.inr h⟩⟩
    rw [he]
    exact hcard

private theorem extend_many {k : ℕ} (hk : 2 ≤ k) (e : ℕ) (S : Set ℝ²)
    (hS : S.Finite) (hnc : NonCollinearFor (k + 1) S) :
    ∃ T : Set ℝ², T.Finite ∧ T.ncard = S.ncard + e ∧ NonCollinearFor (k + 1) T ∧
      linesWithPointsFor k S ⊆ linesWithPointsFor k T := by
  induction e generalizing S with
  | zero => exact ⟨S, hS, by simp, hnc, Set.Subset.rfl⟩
  | succ e ih =>
    obtain ⟨T, hT, hTc, hTnc, hST⟩ := extend_one hk hS hnc
    obtain ⟨U, hU, hUc, hUnc, hTU⟩ := ih T hT hTnc
    exact ⟨U, hU, by omega, hUnc, hST.trans hTU⟩

private def layerIndex {d B : ℕ} (x : Fin (d + 1) → Fin B) : ℕ := (x 0).val

private theorem layer_eq_iff {d B : ℕ} {x y : Fin (d + 1) → Fin B} :
    lift (d + 1) B x 0 = lift (d + 1) B y 0 ↔ layerIndex x = layerIndex y := by
  unfold lift layerIndex
  exact_mod_cast (Iff.rfl : (x 0).val = (y 0).val ↔ (x 0).val = (y 0).val)

private theorem projected_layer_bound {d B k : ℕ} (hk : 2 ≤ k)
    (S : Finset (Fin (d + 1) → Fin B))
    (hsmall : ∀ x ∈ S, layerIndex x < k)
    (hsphere : ∀ x ∈ S, ∀ y ∈ S, layerIndex x = layerIndex y →
      squareSum (lift (d + 1) B x) = squareSum (lift (d + 1) B y))
    (F : (Fin (d + 1) → ℝ) →ₗ[ℝ] ℝ²)
    (hinj : Function.Injective (F ∘ lift (d + 1) B))
    (hreflect : ∀ a b c, a ≠ b →
      F (lift (d + 1) B c) ∈ line[ℝ, F (lift (d + 1) B a), F (lift (d + 1) B b)] →
      lift (d + 1) B c ∈ line[ℝ, lift (d + 1) B a, lift (d + 1) B b])
    {a b : Fin (d + 1) → Fin B} (ha : a ∈ S) (hb : b ∈ S) (hne : a ≠ b) :
    (((line[ℝ, F (lift (d + 1) B a), F (lift (d + 1) B b)] : AffineSubspace ℝ ℝ²) : Set ℝ²) ∩
      ((F ∘ lift (d + 1) B) '' (S : Set (Fin (d + 1) → Fin B)))).ncard ≤ k := by
  let φ := F ∘ lift (d + 1) B
  let L := ((line[ℝ, φ a, φ b] : AffineSubspace ℝ ℝ²) : Set ℝ²)
  let U : Set (Fin (d + 1) → Fin B) := {x | x ∈ S ∧ φ x ∈ L}
  have hr (x : Fin (d + 1) → Fin B) (hx : x ∈ U) :
      lift (d + 1) B x ∈ line[ℝ, lift (d + 1) B a, lift (d + 1) B b] :=
    hreflect a b x hne hx.2
  have hUL : φ '' U = L ∩ (φ '' (S : Set (Fin (d + 1) → Fin B))) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx.2, ⟨x, hx.1, rfl⟩⟩
    · rintro ⟨hz, x, hx, rfl⟩
      exact ⟨x, ⟨hx, hz⟩, rfl⟩
  change (L ∩ (φ '' _)).ncard ≤ k
  rw [← hUL, Set.ncard_image_of_injective U hinj]
  by_cases h : layerIndex a = layerIndex b
  · have hsub : U ⊆ {a, b} := by
      intro x hx
      have ht := line_constant 0 (layer_eq_iff.mpr h) (hr x hx)
      have hQx := hsphere x hx.1 a ha (layer_eq_iff.mp ht)
      have hQb := hsphere b hb a ha h.symm
      have hab : lift (d + 1) B a ≠ lift (d + 1) B b := fun ht => hne (lift_inj _ _ ht)
      rcases sphere_line_endpoints hab hQb hQx (hr x hx) with hx' | hx'
      · exact Set.mem_insert_iff.mpr (Or.inl (lift_inj _ _ hx'))
      · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr (lift_inj _ _ hx')))
    have hb := Set.ncard_le_ncard hsub ((Set.finite_singleton b).insert a)
    rw [Set.ncard_pair hne] at hb
    omega
  · have hin : Set.InjOn layerIndex U := by
      intro x hx y hy hxy
      apply lift_inj (d + 1) B
      have hh : lift (d + 1) B a 0 ≠ lift (d + 1) B b 0 := fun he => h (layer_eq_iff.mp he)
      exact line_coord_inj 0 hh (hr x hx) (hr y hy) (layer_eq_iff.mpr hxy)
    calc
      _ ≤ (Set.Iio k).ncard := Set.ncard_le_ncard_of_injOn layerIndex
        (fun x hx => hsmall x hx.1) hin (Set.finite_Iio k)
      _ = k := by simp

private theorem line_bound_noncollinear {k : ℕ} (hk : 1 ≤ k) {S : Set ℝ²}
    (hbound : ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
      (((line[ℝ, u, v] : AffineSubspace ℝ ℝ²) : Set ℝ²) ∩ S).ncard ≤ k)
    (hS : S.Finite) : NonCollinearFor (k + 1) S := by
  intro A hAS hA hcard hcol
  let : Finite A := hA.to_subtype
  have hnt : A.Nontrivial := one_lt_ncard_iff_nontrivial.mp (by omega)
  obtain ⟨x, hx, y, hy, hxy⟩ := hnt
  have hs : A ⊆ ((line[ℝ, x, y] : AffineSubspace ℝ ℝ²) : Set ℝ²) ∩ S :=
    fun a ha => ⟨hcol.mem_affineSpan_of_mem_of_ne hx hy ha hxy, hAS ha⟩
  have hc := Set.ncard_le_ncard hs (hS.subset Set.inter_subset_right)
  have hb := hbound x (hAS hx) y (hAS hy) hxy
  omega

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

private def dotNat {d M : ℕ} (p : Lattice d M × Lattice d M) : ℕ :=
  ∑ j, (p.1 j).val * (p.2 j).val

private theorem dot_bound {d M : ℕ} (p : Lattice d M × Lattice d M) :
    dotNat p ≤ d * M ^ 2 := by
  unfold dotNat
  calc
    _ ≤ ∑ _j : Fin d, M ^ 2 :=
      Finset.sum_le_sum fun j _ => by
        simpa only [pow_two] using Nat.mul_le_mul (p.1 j).isLt.le (p.2 j).isLt.le
    _ = _ := by simp

private theorem rich_pairs (d M : ℕ) :
    ∃ (R D : ℕ) (P : Finset (Lattice d M × Lattice d M)),
      (∀ p ∈ P, normNat p.1 = R ∧ normNat p.2 = R ∧ dotNat p = D) ∧
      M ^ (2 * d) ≤ (d * M ^ 2 + 1) ^ 3 * P.card := by
  classical
  let C := d * M ^ 2 + 1
  have hc : 0 < C := Nat.succ_pos _
  obtain ⟨R, hR⟩ := largest_fiber (Finset.univ : Finset (Lattice d M)) normNat C hc
    (fun x _ => Nat.lt_succ_of_le (by simpa only [normNat, dotNat, pow_two] using dot_bound (x,x)))
  let S := (Finset.univ : Finset (Lattice d M)).filter (fun x => normNat x = R)
  have hS : M ^ d ≤ C * S.card := by
    simpa [S, Lattice] using hR
  obtain ⟨D, hD⟩ := largest_fiber (S.product S) dotNat C hc
    (fun p _ => Nat.lt_succ_of_le (dot_bound p))
  let P := (S.product S).filter (fun p => dotNat p = D)
  have hP : S.card ^ 2 ≤ C * P.card := by simpa [P, pow_two] using hD
  refine ⟨R, D, P, ?_, ?_⟩
  · intro p hp
    obtain ⟨hprod, hd⟩ := Finset.mem_filter.mp hp
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hprod
    exact ⟨(Finset.mem_filter.mp h₁).2, (Finset.mem_filter.mp h₂).2, hd⟩
  · calc
      _ = (M ^ d) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
      _ ≤ (C * S.card) ^ 2 := Nat.pow_le_pow_left hS 2
      _ = C ^ 2 * S.card ^ 2 := mul_pow _ _ _
      _ ≤ C ^ 2 * (C * P.card) := Nat.mul_le_mul_left _ hP
      _ = _ := by change _ = C ^ 3 * P.card; ring

private def latticePoint {d M k : ℕ} (hM : 0 < M) (i : Fin k)
    (p : Lattice d M × Lattice d M) : Fin (d + 1) → Fin (k * M) :=
  Fin.cons ⟨i.val, i.isLt.trans_le (by simpa using Nat.mul_le_mul_left k hM)⟩
    (fun j => ⟨(k - 1 - i.val) * (p.1 j).val + i.val * (p.2 j).val, by
      have hi : i.val ≤ k - 1 := by omega
      calc
        _ ≤ (k - 1 - i.val) * M + i.val * M :=
          Nat.add_le_add (Nat.mul_le_mul_left _ (p.1 j).isLt.le)
            (Nat.mul_le_mul_left _ (p.2 j).isLt.le)
        _ = (k - 1) * M := by rw [← Nat.add_mul, Nat.sub_add_cancel hi]
        _ < k * M := Nat.mul_lt_mul_of_pos_right (by omega) hM⟩)

private theorem latticePoint_layer {d M k : ℕ} (hM : 0 < M) (i : Fin k)
    (p : Lattice d M × Lattice d M) : layerIndex (latticePoint hM i p) = i.val := by
  simp [layerIndex, latticePoint]

private theorem latticePoint_zero {d M k : ℕ} (hM : 0 < M) (i : Fin k)
    (p : Lattice d M × Lattice d M) :
    lift (d + 1) (k * M) (latticePoint hM i p) 0 = i.val := by
  simp [lift, latticePoint]

private theorem latticePoint_succ {d M k : ℕ} (hM : 0 < M) (i : Fin k)
    (p : Lattice d M × Lattice d M) (j : Fin d) :
    lift (d + 1) (k * M) (latticePoint hM i p) j.succ =
      (((k - 1 : ℕ) : ℝ) - i.val) * (p.1 j).val + (i.val : ℝ) * (p.2 j).val := by
  simp [lift, latticePoint, Nat.cast_sub (show i.val ≤ k - 1 by omega)]

private theorem latticePoint_norm {d M k R D : ℕ} (hM : 0 < M) (i : Fin k)
    (p : Lattice d M × Lattice d M) (h₁ : normNat p.1 = R) (h₂ : normNat p.2 = R)
    (h₃ : dotNat p = D) :
    squareSum (lift (d + 1) (k * M) (latticePoint hM i p)) =
      (i.val : ℝ)^2 + (((k - 1 : ℕ) : ℝ) - i.val)^2 * R + (i.val : ℝ)^2 * R +
        2 * (((k - 1 : ℕ) : ℝ) - i.val) * i.val * D := by
  have e₁ : ∑ j, ((p.1 j).val : ℝ)^2 = (R : ℝ) := by exact_mod_cast h₁
  have e₂ : ∑ j, ((p.2 j).val : ℝ)^2 = (R : ℝ) := by exact_mod_cast h₂
  have e₃ : ∑ j, ((p.1 j).val : ℝ) * (p.2 j).val = (D : ℝ) := by exact_mod_cast h₃
  rw [squareSum, Fin.sum_univ_succ]
  simp only [latticePoint_zero, latticePoint_succ]
  let a := ((k - 1 : ℕ) : ℝ) - i.val
  let b := (i.val : ℝ)
  change b^2 + (∑ j, (a * (p.1 j).val + b * (p.2 j).val)^2) =
    b^2 + a^2 * R + b^2 * R + 2 * a * b * D
  have he : ∑ j, (a * (p.1 j).val + b * (p.2 j).val)^2 =
      a^2 * R + b^2 * R + 2 * a * b * D := by
    calc
      _ = a^2 * (∑ j, ((p.1 j).val : ℝ)^2) + b^2 * (∑ j, ((p.2 j).val : ℝ)^2) +
          2 * a * b * (∑ j, ((p.1 j).val : ℝ) * (p.2 j).val) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [e₁, e₂, e₃]
  rw [he]
  ring


private def firstLayer (k : ℕ) (hk : 2 ≤ k) : Fin k := ⟨0, by omega⟩
private def lastLayer (k : ℕ) (hk : 2 ≤ k) : Fin k := ⟨k - 1, by omega⟩

private theorem latticePoint_first_succ {d M k : ℕ} (hM : 0 < M) (hk : 2 ≤ k)
    (p : Lattice d M × Lattice d M) (j : Fin d) :
    lift (d + 1) (k * M) (latticePoint hM (firstLayer k hk) p) j.succ =
      ((k - 1 : ℕ) : ℝ) * (p.1 j).val := by
  rw [latticePoint_succ]
  simp [firstLayer]

private theorem latticePoint_last_succ {d M k : ℕ} (hM : 0 < M) (hk : 2 ≤ k)
    (p : Lattice d M × Lattice d M) (j : Fin d) :
    lift (d + 1) (k * M) (latticePoint hM (lastLayer k hk) p) j.succ =
      ((k - 1 : ℕ) : ℝ) * (p.2 j).val := by
  rw [latticePoint_succ]
  simp [lastLayer]

private theorem endpoint_distinct {d M k : ℕ} (hM : 0 < M) (hk : 2 ≤ k)
    (p : Lattice d M × Lattice d M) :
    latticePoint hM (firstLayer k hk) p ≠ latticePoint hM (lastLayer k hk) p := by
  intro h
  have he := congrArg layerIndex h
  simp only [latticePoint_layer, firstLayer, lastLayer] at he
  omega

private theorem latticePoint_combo {d M k : ℕ} (hM : 0 < M) (hk : 2 ≤ k)
    (p : Lattice d M × Lattice d M) (i : Fin k) :
    lift (d + 1) (k * M) (latticePoint hM i p) =
      ((i.val : ℝ) / ((k - 1 : ℕ) : ℝ)) •
        (lift (d + 1) (k * M) (latticePoint hM (lastLayer k hk) p) -
          lift (d + 1) (k * M) (latticePoint hM (firstLayer k hk) p)) +
        lift (d + 1) (k * M) (latticePoint hM (firstLayer k hk) p) := by
  have hn : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < k - 1 by omega)
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, latticePoint_zero,
      firstLayer, lastLayer, Nat.cast_zero, sub_zero, add_zero]
    field_simp [hn.ne']
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      latticePoint_succ, firstLayer, lastLayer, Nat.cast_zero, sub_zero, zero_mul, add_zero, sub_self, zero_add]
    field_simp [hn.ne']
    ring

private noncomputable def projectedLine {d M k : ℕ} (hM : 0 < M) (hk : 2 ≤ k)
    (F : (Fin (d + 1) → ℝ) →ₗ[ℝ] ℝ²) (p : Lattice d M × Lattice d M) : AffineSubspace ℝ ℝ² :=
  line[ℝ, F (lift (d + 1) (k * M) (latticePoint hM (firstLayer k hk) p)),
    F (lift (d + 1) (k * M) (latticePoint hM (lastLayer k hk) p))]

private theorem image_on_line {d M k : ℕ} (hM : 0 < M) (hk : 2 ≤ k)
    (F : (Fin (d + 1) → ℝ) →ₗ[ℝ] ℝ²) (p : Lattice d M × Lattice d M) (i : Fin k) :
    F (lift (d + 1) (k * M) (latticePoint hM i p)) ∈ projectedLine hM hk F p := by
  apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
  refine ⟨(i.val : ℝ) / ((k - 1 : ℕ) : ℝ), ?_⟩
  rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, latticePoint_combo hM hk p i]
  rw [map_add, map_smul, map_sub]

private theorem projectedLine_injective {d M k : ℕ} (hM : 0 < M) (hk : 2 ≤ k)
    (F : (Fin (d + 1) → ℝ) →ₗ[ℝ] ℝ²)
    (hreflect : ∀ a b c, a ≠ b →
      F (lift (d + 1) (k * M) c) ∈ line[ℝ, F (lift (d + 1) (k * M) a), F (lift (d + 1) (k * M) b)] →
      lift (d + 1) (k * M) c ∈ line[ℝ, lift (d + 1) (k * M) a, lift (d + 1) (k * M) b]) :
    Function.Injective (projectedLine hM hk F) := by
  intro p q h
  let L := lift (d + 1) (k * M)
  let a := latticePoint hM (firstLayer k hk) p
  let b := latticePoint hM (lastLayer k hk) p
  have hab : L a 0 ≠ L b 0 := by
    dsimp only [L, a, b]
    rw [latticePoint_zero, latticePoint_zero]
    have hn : 0 < k - 1 := by omega
    exact_mod_cast (show (firstLayer k hk).val ≠ (lastLayer k hk).val from hn.ne)
  have he (i : Fin k) : L (latticePoint hM i p) = L (latticePoint hM i q) := by
    have hp : L (latticePoint hM i p) ∈ line[ℝ, L a, L b] :=
      hreflect a b _ (endpoint_distinct hM hk p) (image_on_line hM hk F p i)
    have hq : L (latticePoint hM i q) ∈ line[ℝ, L a, L b] := by
      apply hreflect a b _ (endpoint_distinct hM hk p)
      change F (L (latticePoint hM i q)) ∈ projectedLine hM hk F p
      rw [h]
      exact image_on_line hM hk F q i
    apply line_coord_inj 0 hab hp hq
    simp only [L, latticePoint_zero]
  have hn : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < k - 1 by omega)
  apply Prod.ext
  · funext j
    apply Fin.ext
    have hj := congrFun (he (firstLayer k hk)) j.succ
    change lift (d + 1) (k * M) (latticePoint hM (firstLayer k hk) p) j.succ =
      lift (d + 1) (k * M) (latticePoint hM (firstLayer k hk) q) j.succ at hj
    rw [latticePoint_first_succ, latticePoint_first_succ] at hj
    exact_mod_cast mul_left_cancel₀ hn.ne' hj
  · funext j
    apply Fin.ext
    have hj := congrFun (he (lastLayer k hk)) j.succ
    change lift (d + 1) (k * M) (latticePoint hM (lastLayer k hk) p) j.succ =
      lift (d + 1) (k * M) (latticePoint hM (lastLayer k hk) q) j.succ at hj
    rw [latticePoint_last_succ, latticePoint_last_succ] at hj
    exact_mod_cast mul_left_cancel₀ hn.ne' hj

theorem high_dimensional_lower (d M k n : ℕ) (hM : 0 < M) (hk : 2 ≤ k)
    (hN : (k * M) ^ (d + 1) ≤ n) :
    M ^ (2 * d) ≤ (d * M ^ 2 + 1) ^ 3 * Erdos588.numLinesWithPointsMax k n := by
  classical
  obtain ⟨R, D, P, hP, hcount⟩ := rich_pairs d M
  obtain ⟨F, hF, hreflect⟩ := exists_projection (d + 1) (k * M)
  let T := ((Finset.univ : Finset (Fin k)).product P).image (fun ip => latticePoint hM ip.1 ip.2)
  let φ := F ∘ lift (d + 1) (k * M)
  let S := φ '' (T : Set (Fin (d + 1) → Fin (k * M)))
  have hS : S.Finite := T.finite_toSet.image φ
  have ht (i : Fin k) (p : Lattice d M × Lattice d M) (hp : p ∈ P) : latticePoint hM i p ∈ T :=
    Finset.mem_image.mpr ⟨(i,p), Finset.mem_product.mpr ⟨Finset.mem_univ _, hp⟩, rfl⟩
  have hsmall (x : Fin (d + 1) → Fin (k * M)) (hx : x ∈ T) : layerIndex x < k := by
    obtain ⟨⟨i,p⟩, _, rfl⟩ := Finset.mem_image.mp hx
    simpa only [latticePoint_layer] using i.isLt
  have hnorm (x : Fin (d + 1) → Fin (k * M)) (hx : x ∈ T)
      (y : Fin (d + 1) → Fin (k * M)) (hy : y ∈ T) (he : layerIndex x = layerIndex y) :
      squareSum (lift _ _ x) = squareSum (lift _ _ y) := by
    obtain ⟨⟨i,p⟩, hp, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨⟨j,q⟩, hq, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hp₁, hp₂, hp₃⟩ := hP p (Finset.mem_product.mp hp).2
    obtain ⟨hq₁, hq₂, hq₃⟩ := hP q (Finset.mem_product.mp hq).2
    simp only [latticePoint_layer] at he
    rw [latticePoint_norm hM i p hp₁ hp₂ hp₃, latticePoint_norm hM j q hq₁ hq₂ hq₃, he]
  have hsBound (u : ℝ²) (hu : u ∈ S) (v : ℝ²) (hv : v ∈ S) (hne : u ≠ v) :
      (((line[ℝ, u, v] : AffineSubspace ℝ ℝ²) : Set ℝ²) ∩ S).ncard ≤ k := by
    obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨b, hb, rfl⟩ := hv
    exact projected_layer_bound hk T hsmall hnorm F hF hreflect ha hb (fun h => hne (congrArg φ h))
  have hnc := line_bound_noncollinear (by omega : 1 ≤ k) hsBound hS
  have hlines (p : Lattice d M × Lattice d M) (hp : p ∈ P) :
      projectedLine hM hk F p ∈ linesWithPointsFor k S := by
    have hs (i : Fin k) : φ (latticePoint hM i p) ∈ S := Set.mem_image_of_mem _ (ht i p hp)
    have hne : φ (latticePoint hM (firstLayer k hk) p) ≠ φ (latticePoint hM (lastLayer k hk) p) :=
      fun h => endpoint_distinct hM hk p (hF h)
    refine ⟨⟨_, hs (firstLayer k hk), _, hs (lastLayer k hk), hne, rfl⟩, ?_⟩
    apply le_antisymm (hsBound _ (hs (firstLayer k hk)) _ (hs (lastLayer k hk)) hne)
    let points (i : Fin k) := φ (latticePoint hM i p)
    have hpoints : Function.Injective points := by
      intro i j h
      apply Fin.ext
      have he := congrArg layerIndex (hF h)
      simpa only [latticePoint_layer] using he
    have hc : (Set.range points).ncard = k := by rw [Set.ncard_range_of_injective hpoints]; simp
    have hsub : Set.range points ⊆ ((projectedLine hM hk F p : AffineSubspace ℝ ℝ²) : Set ℝ²) ∩ S := by
      rintro _ ⟨i, rfl⟩
      exact ⟨image_on_line hM hk F p i, hs i⟩
    exact hc.symm.le.trans (Set.ncard_le_ncard hsub (hS.subset Set.inter_subset_right))
  have hsCard : S.ncard ≤ n := by
    change (φ '' (T : Set (Fin (d + 1) → Fin (k * M)))).ncard ≤ n
    rw [Set.ncard_image_of_injective _ hF, Set.ncard_coe_finset]
    exact (T.card_le_univ.trans (by simpa using hN))
  obtain ⟨U, hU, hUc, hUnc, hSU⟩ := extend_many hk (n - S.ncard) S hS hnc
  have hPad : U.ncard = n := by omega
  have hLineCard : P.card ≤ (linesWithPointsFor k S).ncard := by
    have hsub : projectedLine hM hk F '' (P : Set (Lattice d M × Lattice d M)) ⊆ linesWithPointsFor k S := by
      rintro _ ⟨p, hp, rfl⟩
      exact hlines p hp
    have hcount := Set.ncard_le_ncard hsub (finite_lines k hS)
    rw [Set.ncard_image_of_injective _ (projectedLine_injective hM hk F hreflect), Set.ncard_coe_finset] at hcount
    exact hcount
  have hMax := hLineCard.trans ((Set.ncard_le_ncard hSU (finite_lines k hU)).trans (max_lower hU hPad hUnc))
  exact hcount.trans (Nat.mul_le_mul_left _ hMax)

open Real Filter

/-- A square-root logarithmic side scale balances lattice size and the pigeonhole loss. -/
theorem strong_lower (k : ℕ) (hk : 2 ≤ k) :
    ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (2 - C / √(log n)) ≤ (Erdos588.numLinesWithPointsMax k n : ℝ) := by
  have hk0 : 0 < (k : ℝ) := by positivity
  let A := log (2 * (k : ℝ))
  have hA : 0 < A := log_pos (by linarith [show (2 : ℝ) ≤ k by exact_mod_cast hk])
  refine ⟨13 + 2 * A, by positivity, ?_⟩
  have htend : Tendsto (fun n : ℕ => √(log (n : ℝ))) atTop atTop :=
    tendsto_sqrt_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [htend.eventually (eventually_ge_atTop (max 8 A)), eventually_ge_atTop (2 : ℕ)]
    with n ht hn
  let t := √(log (n : ℝ))
  change max 8 A ≤ t at ht
  have ht8 : 8 ≤ t := le_max_left _ _ |>.trans ht
  have htA : A ≤ t := le_max_right _ _ |>.trans ht
  have ht0 : 0 < t := by linarith
  have hn0 : 0 < (n : ℝ) := by positivity
  have htsq : t^2 = log (n : ℝ) := sq_sqrt (log_natCast_nonneg n)
  let d := ⌊t⌋₊ - 1
  have hdEq : d + 1 = ⌊t⌋₊ := Nat.sub_add_cancel (Nat.le_floor (by norm_num; linarith))
  have hDUp : (d : ℝ) + 1 ≤ t := by
    have h := Nat.floor_le ht0.le
    rw [← hdEq, Nat.cast_add, Nat.cast_one] at h
    exact h
  have hDLo : t - 2 ≤ (d : ℝ) := by
    have h := Nat.lt_floor_add_one t
    rw [← hdEq, Nat.cast_add, Nat.cast_one] at h
    linarith
  let y := exp t / (k : ℝ)
  let M := ⌊y⌋₊
  have hy : 2 ≤ y := by
    apply (le_div_iff₀ hk0).mpr
    exact (exp_log (show 0 < 2 * (k : ℝ) by positivity)).symm.le.trans (exp_le_exp.mpr htA)
  have hM : 0 < M := Nat.le_floor (by norm_num; linarith)
  have hM0 : 0 < (M : ℝ) := by exact_mod_cast hM
  have hMy : (M : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hMlo : y / 2 ≤ (M : ℝ) := by
    have hf := Nat.lt_floor_add_one y
    change y < (M : ℝ) + 1 at hf
    linarith
  have hkm : (k : ℝ) * M ≤ exp t := by
    rw [mul_comm]
    exact (le_div_iff₀ hk0).mp hMy
  have hN : (k * M) ^ (d + 1) ≤ n := by
    have hP : ((k : ℝ) * M) ^ (d + 1) ≤ (n : ℝ) := by
      apply (log_le_log_iff (by positivity) hn0).mp
      rw [log_pow, Nat.cast_add, Nat.cast_one, ← htsq, pow_two]
      have hkmlog : log ((k : ℝ) * M) ≤ t := by
        rw [← log_exp t]
        exact (log_le_log_iff (by positivity) (exp_pos _)).mpr hkm
      exact (mul_le_mul_of_nonneg_left hkmlog (by positivity)).trans
        (mul_le_mul_of_nonneg_right hDUp ht0.le)
    exact_mod_cast hP
  let f := Erdos588.numLinesWithPointsMax k n
  have hraw : M ^ (2 * d) ≤ (d * M ^ 2 + 1) ^ 3 * f := high_dimensional_lower d M k n hM hk hN
  have hf : 0 < f := by
    by_contra! h
    have he : f = 0 := Nat.le_zero.mp h
    rw [he, mul_zero] at hraw
    exact (pow_pos hM _).not_ge hraw
  have hf0 : 0 < (f : ℝ) := by exact_mod_cast hf
  have hterm : (d : ℝ) * (M : ℝ)^2 + 1 ≤ ((d : ℝ) + 1) * (M : ℝ)^2 := by
    have h1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    nlinarith only [h1, sq_nonneg ((M : ℝ) - 1)]
  have hpow : (M : ℝ) ^ (2 * d) ≤ (((d : ℝ) + 1) * (M : ℝ)^2)^3 * (f : ℝ) := by
    have h := pow_le_pow_left₀ (by positivity) hterm 3
    exact (by exact_mod_cast hraw : (M : ℝ) ^ (2 * d) ≤ ((d : ℝ) * (M : ℝ)^2 + 1)^3 * (f : ℝ)).trans
      (mul_le_mul_of_nonneg_right h hf0.le)
  have hlog : (2 * (d : ℝ)) * log (M : ℝ) ≤ 3 * (log ((d : ℝ) + 1) + 2 * log (M : ℝ)) +
      log (f : ℝ) := by
    have h := (log_le_log_iff (by positivity) (by positivity)).mpr hpow
    rw [log_mul (by positivity) hf0.ne', log_pow (M : ℝ) (2*d), log_pow _ 3,
      log_mul (by positivity) (by positivity), log_pow (M : ℝ) 2] at h
    push_cast at h
    simpa only [Nat.cast_ofNat] using h
  have hlogM : t - A ≤ log (M : ℝ) := by
    have hle : exp t / (2 * (k : ℝ)) ≤ (M : ℝ) := by
      convert hMlo using 1
      dsimp [y]
      ring
    have h := (log_le_log_iff (by positivity) hM0).mpr hle
    simpa [log_div (exp_pos _).ne' (show 2 * (k : ℝ) ≠ 0 by positivity), A] using h
  have hmul : (2*t - 10) * (t-A) ≤ (2*(d : ℝ) - 6) * log (M : ℝ) :=
    mul_le_mul (by linarith only [hDLo]) hlogM (sub_nonneg.mpr htA) (by linarith only [ht8, hDLo])
  have hlogD : log ((d : ℝ) + 1) ≤ t :=
    (log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have hfinal : 2*t^2 - (13 + 2*A)*t ≤ log (f : ℝ) :=
    by nlinarith only [hmul, hlog, hlogD, hA.le]
  change (n : ℝ) ^ (2 - (13 + 2*A) / t) ≤ (f : ℝ)
  rw [rpow_def_of_pos hn0, ← exp_log hf0, exp_le_exp, ← htsq]
  calc
    _ = 2*t^2 - (13 + 2*A)*t := by
      field_simp [ht0.ne']
    _ ≤ _ := hfinal

theorem any_power_lower (k : ℕ) (hk : 2 ≤ k) (a : ℝ) (ha : a < 2) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ a ≤ (Erdos588.numLinesWithPointsMax k n : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := strong_lower k hk
  have htend : Tendsto (fun n : ℕ => √(log (n : ℝ))) atTop atTop :=
    tendsto_sqrt_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hbound, htend.eventually (eventually_ge_atTop (max 1 (C / (2 - a)))),
    eventually_ge_atTop (1 : ℕ)] with n hbn htn hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have htt : 0 < √(log (n : ℝ)) := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans htn)
  have hc : C / √(log (n : ℝ)) ≤ 2 - a := by
    apply (div_le_iff₀ htt).mpr
    have h := (div_le_iff₀ (sub_pos.mpr ha)).mp ((le_max_right _ _).trans htn)
    linarith only [h]
  exact (rpow_le_rpow_of_exponent_le hn1 (by linarith)).trans hbn

end LayeredGrid

open LayeredGrid Filter Real
open scoped Asymptotics

theorem OMA.solution : type_of% @Erdos588.erdos_588.variants.grunbaum_order := by
  intro k hk hO
  let a : ℝ := 1 + 1 / ((k : ℝ) - 2)
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : (0 : ℝ) < (k : ℝ) - 2 := by linarith
  have hdiv : (1 : ℝ) / ((k : ℝ) - 2) ≤ 1 / 2 := (div_le_iff₀ hp).mpr (by linarith)
  have ha : a ≤ 3 / 2 := by dsimp [a]; linarith
  obtain ⟨C, hC, hUpper⟩ := hO.exists_pos
  have hpow := any_power_lower k (by omega) (7 / 4) (by norm_num)
  have hdiverge : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop
  have hbad : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hUpper.bound, hpow, hdiverge.eventually (eventually_gt_atTop C),
      eventually_ge_atTop (1 : ℕ)] with n hu hl hbig hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hU : (Erdos588.numLinesWithPointsMax k n : ℝ) ≤ C * (n : ℝ)^a := by
      simpa [a, Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg (Nat.cast_nonneg n) _)] using hu
    have hlt : C * (n : ℝ)^a < (n : ℝ) ^ (7 / 4 : ℝ) := by
      calc
        _ ≤ C * (n : ℝ) ^ (3 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le hn1 ha) hC.le
        _ < (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) :=
          mul_lt_mul_of_pos_right hbig (rpow_pos_of_pos hn0 _)
        _ = _ := by rw [← rpow_add hn0]; norm_num
    exact hlt.not_ge (hl.trans hU)
  exact hbad.exists.choose_spec