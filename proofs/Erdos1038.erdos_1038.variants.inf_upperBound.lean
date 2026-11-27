import FormalConjectures.ErdosProblems.«1038»
import Mathlib.Analysis.MeanInequalities

/-!
A degree-3180 monic polynomial with rational roots in the unit interval.
The short root intervals have total length 1.834998376308. Weighted AM-GM
controls the product in the gaps, using integer endpoint certificates.
The rational roots discretize the positive-platform distribution in
https://github.com/ShouqiaoW/erdos/blob/main/1038/paper.tex
-/

open scoped BigOperators ENNReal
open Set Polynomial MeasureTheory

namespace SublevelCertificate

private def value {ι : Type*} [Fintype ι] (roots : ι → ℝ) (mult : ι → ℕ) (x : ℝ) : ℝ :=
  ∏ i, |x - roots i| ^ mult i

private theorem gap_bound {ι : Type*} [Fintype ι] (roots : ι → ℝ) (mult : ι → ℕ)
    {a b x : ℝ} (hax : a ≤ x) (hxb : x ≤ b)
    (hgap : ∀ i, roots i < a ∨ b < roots i)
    (ha : 1 ≤ value roots mult a) (hb : 1 ≤ value roots mult b) :
    1 ≤ value roots mult x := by
  rcases (hax.trans hxb).eq_or_lt with he | hab
  · have hx : x = a := le_antisymm (hxb.trans_eq he.symm) hax
    simpa only [hx] using ha
  let u := (b-x)/(b-a)
  let v := (x-a)/(b-a)
  have hba : 0 < b-a := sub_pos.2 hab
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.2 hxb) hba.le
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.2 hax) hba.le
  have huv : u + v = 1 := by
    dsimp [u, v]
    rw [← add_div, show b-x+(x-a) = b-a by ring, div_self hba.ne']
  have hx : u*a + v*b = x := by
    dsimp [u, v]
    field_simp
    ring
  have hlinear (i : ι) : u * (a-roots i) + v * (b-roots i) = x-roots i := by
    calc
      _ = u*a + v*b - (u+v)*roots i := by ring
      _ = _ := by rw [hx, huv, one_mul]
  have hmix (i : ι) : u * |a-roots i| + v * |b-roots i| = |x-roots i| := by
    rcases hgap i with hi | hi
    · rw [abs_of_nonneg (sub_nonneg.2 hi.le), abs_of_nonneg (sub_nonneg.2 (hi.le.trans (hax.trans hxb))),
        abs_of_nonneg (sub_nonneg.2 (hi.le.trans hax))]
      exact hlinear i
    · rw [abs_of_nonpos (sub_nonpos.2 ((hax.trans hxb).trans hi.le)),
        abs_of_nonpos (sub_nonpos.2 hi.le), abs_of_nonpos (sub_nonpos.2 (hxb.trans hi.le))]
      linarith only [hlinear i]
  have hterm (i : ι) :
      (|a-roots i| ^ mult i) ^ u * (|b-roots i| ^ mult i) ^ v ≤ |x-roots i| ^ mult i := by
    have hm := Real.geom_mean_le_arith_mean2_weighted hu hv
      (abs_nonneg (a-roots i)) (abs_nonneg (b-roots i)) huv
    rw [hmix i] at hm
    have hp := pow_le_pow_left₀ (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
      (Real.rpow_nonneg (abs_nonneg _) _)) hm (mult i)
    rw [mul_pow, ← Real.rpow_mul_natCast (abs_nonneg _), ← Real.rpow_mul_natCast (abs_nonneg _),
      mul_comm u, mul_comm v, Real.rpow_natCast_mul (abs_nonneg _),
      Real.rpow_natCast_mul (abs_nonneg _)] at hp
    exact hp
  have hprod :
      value roots mult a ^ u * value roots mult b ^ v ≤ value roots mult x := by
    unfold value
    rw [← Real.finsetProd_rpow _ _ (fun _ _ => pow_nonneg (abs_nonneg _) _) u,
      ← Real.finsetProd_rpow _ _ (fun _ _ => pow_nonneg (abs_nonneg _) _) v, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun _ _ => mul_nonneg (Real.rpow_nonneg (pow_nonneg (abs_nonneg _) _) _)
      (Real.rpow_nonneg (pow_nonneg (abs_nonneg _) _) _)) (fun i _ => hterm i)
  apply le_trans _ hprod
  simpa only [Real.one_rpow, one_mul] using
    mul_le_mul (Real.rpow_le_rpow zero_le_one ha hu) (Real.rpow_le_rpow zero_le_one hb hv)
      (Real.rpow_nonneg zero_le_one _) (Real.rpow_nonneg (zero_le_one.trans ha) _)

end SublevelCertificate

namespace SublevelCertificate

private theorem outside_windows_ge_one {ι : Type*} [Fintype ι] [Nonempty ι]
    (roots lower upper : ι → ℝ) (mult : ι → ℕ)
    (hroot : ∀ i, lower i < roots i ∧ roots i < upper i)
    (hlo : ∀ i, 1 ≤ value roots mult (lower i))
    (hhi : ∀ i, 1 ≤ value roots mult (upper i)) {x : ℝ}
    (hx : x ∉ ⋃ i, Ioo (lower i) (upper i)) :
    1 ≤ value roots mult x := by
  classical
  have hside (i : ι) : upper i ≤ x ∨ x ≤ lower i := by
    by_contra! hh
    exact hx (mem_iUnion.2 ⟨i, hh.2, hh.1⟩)
  let A := (Finset.univ.filter (fun i : ι => upper i ≤ x)).image upper
  let B := (Finset.univ.filter (fun i : ι => x ≤ lower i)).image lower
  have hAmem {i : ι} (hi : upper i ≤ x) : upper i ∈ A :=
    Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
  have hBmem {i : ι} (hi : x ≤ lower i) : lower i ∈ B :=
    Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
  by_cases hA : A.Nonempty
  · let a := A.max' hA
    obtain ⟨j, hj, hj_eq⟩ := Finset.mem_image.mp (Finset.max'_mem A hA)
    have hax : a ≤ x := by
      rw [show a = upper j from hj_eq.symm]
      exact (Finset.mem_filter.mp hj).2
    have hha : 1 ≤ value roots mult a := by
      rw [show a = upper j from hj_eq.symm]
      exact hhi j
    have hleft (i : ι) (hi : upper i ≤ x) : roots i < a :=
      (hroot i).2.trans_le (Finset.le_max' A _ (hAmem hi))
    by_cases hB : B.Nonempty
    · let b := B.min' hB
      obtain ⟨k, hk, hk_eq⟩ := Finset.mem_image.mp (Finset.min'_mem B hB)
      have hxb : x ≤ b := by
        rw [show b = lower k from hk_eq.symm]
        exact (Finset.mem_filter.mp hk).2
      have hhb : 1 ≤ value roots mult b := by
        rw [show b = lower k from hk_eq.symm]
        exact hlo k
      have hright (i : ι) (hi : x ≤ lower i) : b < roots i :=
        (Finset.min'_le B _ (hBmem hi)).trans_lt (hroot i).1
      exact gap_bound roots mult hax hxb
        (fun i => (hside i).imp (hleft i) (hright i)) hha hhb
    · apply hha.trans
      unfold value
      refine Finset.prod_le_prod (fun _ _ => pow_nonneg (abs_nonneg _) _) (fun i _ => ?_)
      have hi := (hside i).resolve_right (fun hr => hB ⟨_, hBmem hr⟩)
      have hr := hleft i hi
      rw [abs_of_nonneg (sub_nonneg.2 hr.le),
        abs_of_nonneg (sub_nonneg.2 (hr.le.trans hax))]
      exact pow_le_pow_left₀ (sub_nonneg.2 hr.le) (sub_le_sub_right hax _) _
  · have hright (i : ι) : x ≤ lower i :=
      (hside i).resolve_left (fun hl => hA ⟨_, hAmem hl⟩)
    let i₀ : ι := Classical.choice inferInstance
    have hB : B.Nonempty := ⟨_, hBmem (hright i₀)⟩
    let b := B.min' hB
    obtain ⟨k, hk, hk_eq⟩ := Finset.mem_image.mp (Finset.min'_mem B hB)
    have hxb : x ≤ b := by
      rw [show b = lower k from hk_eq.symm]
      exact (Finset.mem_filter.mp hk).2
    have hhb : 1 ≤ value roots mult b := by
      rw [show b = lower k from hk_eq.symm]
      exact hlo k
    apply hhb.trans
    unfold value
    refine Finset.prod_le_prod (fun _ _ => pow_nonneg (abs_nonneg _) _) (fun i _ => ?_)
    have hr : b < roots i := (Finset.min'_le B _ (hBmem (hright i))).trans_lt (hroot i).1
    rw [abs_of_nonpos (sub_nonpos.2 hr.le),
      abs_of_nonpos (sub_nonpos.2 (hxb.trans hr.le))]
    exact pow_le_pow_left₀ (neg_nonneg.2 (sub_nonpos.2 hr.le))
      (neg_le_neg (sub_le_sub_right hxb _)) _

private theorem sublevel_volume_lt {ι : Type*} [Fintype ι] [Nonempty ι]
    (roots lower upper : ι → ℝ) (mult : ι → ℕ)
    (hroot : ∀ i, lower i < roots i ∧ roots i < upper i)
    (hlo : ∀ i, 1 ≤ value roots mult (lower i))
    (hhi : ∀ i, 1 ≤ value roots mult (upper i)) {E : ℝ} (hE : 0 < E)
    (hwidth : ∑ i, (upper i - lower i) < E) :
    volume {x | value roots mult x < 1} < ENNReal.ofReal E := by
  have hsub : {x | value roots mult x < 1} ⊆ ⋃ i, Ioo (lower i) (upper i) := by
    intro x hx
    by_contra hn
    exact (not_lt_of_ge (outside_windows_ge_one roots lower upper mult hroot hlo hhi hn)) hx
  refine (measure_mono hsub).trans_lt ((measure_iUnion_le _).trans_lt ?_)
  rw [tsum_fintype]
  simp only [Real.volume_Ioo]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => sub_nonneg.2 ((hroot i).1.trans (hroot i).2).le)]
  exact ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hwidth, hE⟩

end SublevelCertificate

namespace SublevelCertificate

private theorem polynomial_witness_of_windows {ι : Type*} [Fintype ι] [Nonempty ι]
    (roots lower upper : ι → ℝ) (mult : ι → ℕ)
    (hroots : ∀ i, roots i ∈ Icc (-1 : ℝ) 1) (hdegree : ∃ i, 0 < mult i)
    (hwindow : ∀ i, lower i < roots i ∧ roots i < upper i)
    (hlo : ∀ i, 1 ≤ value roots mult (lower i))
    (hhi : ∀ i, 1 ≤ value roots mult (upper i)) {E : ℝ} (hE : 0 < E)
    (hwidth : ∑ i, (upper i - lower i) < E) :
    ∃ f : {f : Polynomial ℝ // f.Monic ∧ f ≠ 1 ∧
        (f.roots.filter fun x => x ∈ Icc (-1 : ℝ) 1).card = f.natDegree},
      volume {x | |f.1.eval x| < 1} < ENNReal.ofReal E := by
  classical
  let fac (i : ι) : ℝ[X] := (X - C (roots i)) ^ mult i
  let f := ∏ i, fac i
  have hm (i) : (fac i).Monic := (monic_X_sub_C (roots i)).pow _
  have hf : f.Monic := monic_prod_of_monic _ _ (fun i _ => hm i)
  have hs : f.Splits := Polynomial.Splits.prod (fun i _ => (Splits.X_sub_C (roots i)).pow _)
  have hd : f.natDegree = ∑ i, mult i := by
    rw [show f = ∏ i, fac i from rfl, natDegree_prod_of_monic _ _ (fun i _ => hm i)]
    simp only [fac, natDegree_pow, natDegree_X_sub_C, mul_one]
  have hfne : f ≠ 1 := by
    obtain ⟨i, hi⟩ := hdegree
    have hl : mult i ≤ ∑ j, mult j := Finset.single_le_sum (fun j _ => Nat.zero_le (mult j))
      (Finset.mem_univ i)
    have hpos : 0 < f.natDegree := by rw [hd]; exact hi.trans_le hl
    intro he
    simp [he] at hpos
  have heval (z : ℝ) : f.eval z = ∏ i, (z-roots i) ^ mult i := by
    simp [f, fac, eval_prod, eval_pow, eval_sub, eval_X, eval_C]
  have hfilter : (f.roots.filter fun x => x ∈ Icc (-1 : ℝ) 1) = f.roots := by
    apply Multiset.filter_eq_self.2
    intro z hz
    have he := (mem_roots hf.ne_zero).1 hz
    change f.eval z = 0 at he
    rw [heval] at he
    obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.1 he
    have hz' : z = roots i := sub_eq_zero.1 (eq_zero_of_pow_eq_zero hi)
    rw [hz']
    exact hroots i
  refine ⟨⟨f, hf, hfne, by rw [hfilter, hs.natDegree_eq_card_roots]⟩, ?_⟩
  change volume {z | |f.eval z| < 1} < _
  have habs (z : ℝ) : |f.eval z| = value roots mult z := by
    rw [heval, Finset.abs_prod, value]
    simp only [abs_pow]
  simp_rw [habs]
  exact sublevel_volume_lt roots lower upper mult hwindow hlo hhi hE hwidth

end SublevelCertificate

private noncomputable def OMA.witnessRoot (D : ℕ) (W : List (ℕ × ℕ × ℕ)) :
    Option (Fin W.length) → ℝ
  | none => -1
  | some i => ((W.get i).2.1 : ℝ) / D

private def OMA.witnessMultiplicity (k : ℕ) (W : List (ℕ × ℕ × ℕ)) :
    Option (Fin W.length) → ℕ
  | none => k
  | some _ => 1

private noncomputable def OMA.witnessLower (D : ℕ) (p : ℤ) (W : List (ℕ × ℕ × ℕ)) :
    Option (Fin W.length) → ℝ
  | none => (p : ℝ) / D
  | some i => ((W.get i).1 : ℝ) / D

private noncomputable def OMA.witnessUpper (D : ℕ) (q : ℤ) (W : List (ℕ × ℕ × ℕ)) :
    Option (Fin W.length) → ℝ
  | none => (q : ℝ) / D
  | some i => ((W.get i).2.2 : ℝ) / D

private theorem OMA.witness_list_prod {α M : Type*} [CommMonoid M] (L : List α) (g : α → M) :
    (L.map g).prod = ∏ i : Fin L.length, g (L.get i) := by
  rw [← List.prod_ofFn]
  change _ = (List.ofFn (g ∘ L.get)).prod
  rw [← List.map_ofFn, List.ofFn_get]

private theorem OMA.witness_list_sum {α M : Type*} [AddCommMonoid M] (L : List α) (g : α → M) :
    (L.map g).sum = ∑ i : Fin L.length, g (L.get i) := by
  rw [← List.sum_ofFn]
  change _ = (List.ofFn (g ∘ L.get)).sum
  rw [← List.map_ofFn, List.ofFn_get]

private theorem OMA.scaled_abs_prod_ge_one {D : ℕ} (hD : 0 < D) (k : ℕ)
    (W : List (ℕ × ℕ × ℕ)) (x : ℤ)
    (hx : D ^ (k + W.length) ≤
      (x + (D : ℤ)).natAbs ^ k * (W.map fun w => (x - (w.2.1 : ℤ)).natAbs).prod) :
    1 ≤ ∏ i : Option (Fin W.length), |(x : ℝ) / D - witnessRoot D W i| ^
      witnessMultiplicity k W i := by
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  have habs (u v : ℤ) : |(u : ℝ) / D - (v : ℝ) / D| =
      ((u - v).natAbs : ℝ) / D := by
    rw [← sub_div, abs_div, ← Int.cast_sub, Nat.cast_natAbs, Int.cast_abs, abs_of_pos hDR]
  have hnone : |(x : ℝ) / D - witnessRoot D W none| = ((x + (D : ℤ)).natAbs : ℝ) / D := by
    change |(x : ℝ) / D - (-1)| = _
    have hneg : ((-(D : ℤ) : ℤ) : ℝ) / D = -1 := by simp [hDR.ne']
    simpa only [hneg, sub_neg_eq_add] using habs x (-(D : ℤ))
  have hsome (i : Fin W.length) : |(x : ℝ) / D - witnessRoot D W (some i)| =
      ((x - ((W.get i).2.1 : ℤ)).natAbs : ℝ) / D := by
    simpa only [witnessRoot, Int.cast_natCast] using habs x ((W.get i).2.1 : ℤ)
  rw [Fintype.prod_option, hnone]
  simp_rw [witnessMultiplicity, pow_one, hsome]
  rw [div_pow, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    div_mul_div_comm, ← pow_add]
  apply (le_div_iff₀ (pow_pos hDR _)).2
  rw [one_mul]
  have hp := (witness_list_prod W (fun w => (x - (w.2.1 : ℤ)).natAbs))
  rw [hp] at hx
  exact_mod_cast hx

private theorem OMA.scaled_window_width_lt {D : ℕ} (hD : 0 < D) (p q : ℤ)
    (W : List (ℕ × ℕ × ℕ))
    (hwidth : (1000 : ℤ) * (q - p + (W.map fun w => w.2.2 - w.1).sum) <
      1835 * (D : ℤ))
    (horder : ∀ i, witnessLower D p W i ≤ witnessUpper D q W i) :
    (∑ i : Option (Fin W.length), (witnessUpper D q W i - witnessLower D p W i)) <
      (1835 : ℝ) / 1000 := by
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  have hmain : witnessUpper D q W none - witnessLower D p W none =
      ((q - p : ℤ) : ℝ) / D := by simp only [witnessUpper, witnessLower, Int.cast_sub, sub_div]
  have hsome (i : Fin W.length) : witnessUpper D q W (some i) - witnessLower D p W (some i) =
      (((W.get i).2.2 - (W.get i).1 : ℕ) : ℝ) / D := by
    have hi : (((W.get i).1 : ℝ) / D) ≤ ((W.get i).2.2 : ℝ) / D := horder (some i)
    have hiN : (W.get i).1 ≤ (W.get i).2.2 := by
      exact_mod_cast (div_le_div_iff_of_pos_right hDR).mp hi
    simp only [witnessUpper, witnessLower, Nat.cast_sub hiN, sub_div]
  rw [Fintype.sum_option, hmain]
  simp_rw [hsome]
  rw [← Finset.sum_div, ← add_div]
  have hscale :
      (1000 : ℝ) * ((q : ℝ) - p + (((W.map fun w => w.2.2 - w.1).sum : ℕ) : ℝ)) <
        1835 * (D : ℝ) := by
    simpa only [Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_natCast, Int.cast_ofNat] using
      (Int.cast_lt (R := ℝ)).2 hwidth
  rw [witness_list_sum] at hscale
  push_cast at hscale
  rw [Int.cast_sub]
  exact (div_lt_iff₀ hDR).2 (by linarith)

namespace SublevelCertificate

private theorem proof_from_integer_windows (D k : ℕ) (p q : ℤ) (W : List (ℕ × ℕ × ℕ))
    (hD : 0 < D) (hk : 0 < k) (hmain : p < -(D : ℤ) ∧ -(D : ℤ) < q)
    (hgeometry : ∀ w ∈ W, w.1 < w.2.1 ∧ w.2.1 < w.2.2 ∧ w.2.1 ≤ D)
    (hends : ∀ x : ℤ, (x = p ∨ x = q ∨ ∃ w ∈ W, x = (w.1 : ℤ) ∨ x = (w.2.2 : ℤ)) →
      D ^ (k + W.length) ≤
        (x + (D : ℤ)).natAbs ^ k * (W.map fun w => (x - (w.2.1 : ℤ)).natAbs).prod)
    (hwidth : (1000 : ℤ) * (q-p + (W.map fun w => w.2.2-w.1).sum) < 1835 * (D : ℤ)) :
    type_of% @Erdos1038.erdos_1038.variants.inf_upperBound := by
  classical
  let r := OMA.witnessRoot D W
  let m := OMA.witnessMultiplicity k W
  let a := OMA.witnessLower D p W
  let b := OMA.witnessUpper D q W
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  have hgeo (i : Fin W.length) := hgeometry (W.get i) (List.get_mem W i)
  have hroot (i : Option (Fin W.length)) : r i ∈ Icc (-1 : ℝ) 1 := by
    cases i with
    | none =>
      change (-1 : ℝ) ∈ Icc (-1 : ℝ) 1
      simp
    | some j =>
      change (-1 : ℝ) ≤ ((W.get j).2.1 : ℝ)/D ∧ ((W.get j).2.1 : ℝ)/D ≤ 1
      refine ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans (by positivity), (div_le_one₀ hDR).2 ?_⟩
      exact_mod_cast (hgeo j).2.2
  have hwindow (i : Option (Fin W.length)) : a i < r i ∧ r i < b i := by
    cases i with
    | none =>
      change (p : ℝ)/D < -1 ∧ -1 < (q : ℝ)/D
      have hneg : ((-(D : ℤ) : ℤ) : ℝ)/D = -1 := by simp [hDR.ne']
      rw [← hneg]
      exact ⟨(div_lt_div_iff_of_pos_right hDR).2 (by exact_mod_cast hmain.1),
        (div_lt_div_iff_of_pos_right hDR).2 (by exact_mod_cast hmain.2)⟩
    | some j =>
      change ((W.get j).1 : ℝ)/D < ((W.get j).2.1 : ℝ)/D ∧
        ((W.get j).2.1 : ℝ)/D < ((W.get j).2.2 : ℝ)/D
      exact ⟨(div_lt_div_iff_of_pos_right hDR).2 (by exact_mod_cast (hgeo j).1),
        (div_lt_div_iff_of_pos_right hDR).2 (by exact_mod_cast (hgeo j).2.1)⟩
  have hval (x : ℤ) (hx : x = p ∨ x = q ∨ ∃ w ∈ W, x = (w.1 : ℤ) ∨ x = (w.2.2 : ℤ)) :
      1 ≤ value r m ((x : ℝ)/D) := OMA.scaled_abs_prod_ge_one hD k W x (hends x hx)
  have hlo (i : Option (Fin W.length)) : 1 ≤ value r m (a i) := by
    cases i with
    | none => exact hval p (Or.inl rfl)
    | some j =>
      simpa only [a, OMA.witnessLower, Int.cast_natCast] using
        hval ((W.get j).1 : ℤ) (Or.inr (Or.inr ⟨W.get j, List.get_mem W j, Or.inl rfl⟩))
  have hhi (i : Option (Fin W.length)) : 1 ≤ value r m (b i) := by
    cases i with
    | none => exact hval q (Or.inr (Or.inl rfl))
    | some j =>
      simpa only [b, OMA.witnessUpper, Int.cast_natCast] using
        hval ((W.get j).2.2 : ℤ) (Or.inr (Or.inr ⟨W.get j, List.get_mem W j, Or.inr rfl⟩))
  have hw : ∑ i, (b i-a i) < (1835 : ℝ)/1000 :=
    OMA.scaled_window_width_lt hD p q W hwidth (fun i => ((hwindow i).1.trans (hwindow i).2).le)
  obtain ⟨f, hf⟩ := polynomial_witness_of_windows r a b m hroot ⟨none, hk⟩ hwindow hlo hhi
    (by norm_num) hw
  have heq : ENNReal.ofReal ((1835 : ℝ)/1000) = (1.835 : ℝ≥0∞) := by
    have hd : ((1.835 : NNReal) : ℝ) = (1835 : ℝ)/1000 := by
      rw [NNReal.coe_ofScientific]
      norm_num
    rw [← hd, ENNReal.ofReal_coe_nnreal]
    rfl
  rw [heq] at hf
  exact (iInf_le _ f).trans_lt hf

end SublevelCertificate

namespace SublevelWitness

private def denominator : ℕ := 1000000000000
private def mainMultiplicity : ℕ := 2625
private def mainLeft : ℤ := -1809120433668
private def mainRight : ℤ := 25803935340

private def windowBatch0 : List (ℕ × ℕ × ℕ) :=
  [(806460682888, 806460683411, 806460683934), (806466148992, 806466150560, 806466152128),
   (806477081499, 806477084112, 806477086725), (806493478916, 806493482574, 806493486232),
   (806515339008, 806515343710, 806515348412), (806542658792, 806542664538, 806542670284),
   (806575434546, 806575441334, 806575448122), (806613661803, 806613669633, 806613677463),
   (806657335360, 806657344231, 806657353102), (806706449276, 806706459187, 806706469098),
   (806760996877, 806761007826, 806761018775), (806820970758, 806820982743, 806820994728)]

private def windowBatch1 : List (ℕ × ℕ × ℕ) :=
  [(806886362784, 806886375805, 806886388826), (806957164100, 806957178154, 806957192208),
   (807033365130, 807033380215, 807033395300), (807114955579, 807114971694, 807114987809),
   (807201924448, 807201941590, 807201958732), (807294260026, 807294278193, 807294296360),
   (807391949904, 807391969093, 807391988282), (807494980977, 807495001186, 807495021395),
   (807603339453, 807603360679, 807603381905), (807717010853, 807717033094, 807717055335),
   (807835980025, 807836003277, 807836026529), (807960231145, 807960255405, 807960279665)]

private def windowBatch2 : List (ℕ × ℕ × ℕ) :=
  [(808089747724, 808089772990, 808089798256), (808224512623, 808224538890, 808224565157),
   (808364508047, 808364535313, 808364562579), (808509715567, 808509743827, 808509772087),
   (808660116115, 808660145366, 808660174617), (808815690003, 808815720241, 808815750479),
   (808976416923, 808976448145, 808976479367), (809142275963, 809142308164, 809142340365),
   (809313245609, 809313278785, 809313311961), (809489303756, 809489337903, 809489372050),
   (809670427723, 809670462836, 809670497949), (809856594252, 809856630327, 809856666402)]

private def windowBatch3 : List (ℕ × ℕ × ℕ) :=
  [(810047779527, 810047816559, 810047853591), (810243959177, 810243997162, 810244035147),
   (810445108290, 810445147222, 810445186154), (810651201421, 810651241296, 810651281171),
   (810862212603, 810862253416, 810862294229), (811078115358, 811078157103, 811078198848),
   (811298882702, 811298925375, 811298968048), (811524487165, 811524530760, 811524574355),
   (811754900794, 811754945306, 811754989818), (811990095167, 811990140590, 811990186013),
   (812230041400, 812230087729, 812230134058), (812474710164, 812474757393, 812474804622)]

private def windowBatch4 : List (ℕ × ℕ × ℕ) :=
  [(812724071692, 812724119815, 812724167938), (812978095788, 812978144800, 812978193812),
   (813236751845, 813236801739, 813236851633), (813500008847, 813500059618, 813500110389),
   (813767835387, 813767887029, 813767938671), (814040199678, 814040252184, 814040304690),
   (814317069556, 814317122921, 814317176286), (814598412506, 814598466723, 814598520940),
   (814884195656, 814884250718, 814884305780), (815174385801, 815174441703, 815174497605),
   (815468949409, 815469006144, 815469062879), (815767852633, 815767910194, 815767967755)]

private def windowBatch5 : List (ℕ × ℕ × ℕ) :=
  [(816071061320, 816071119701, 816071178082), (816378541028, 816378600222, 816378659416),
   (816690257028, 816690317029, 816690377030), (817006174324, 817006235125, 817006295926),
   (817326257661, 817326319255, 817326380849), (817650471530, 817650533910, 817650596290),
   (817978780186, 817978843346, 817978906506), (818311147660, 818311211592, 818311275524),
   (818647537761, 818647602459, 818647667157), (818987914095, 818987979552, 818988045009),
   (819332240071, 819332306279, 819332372487), (819680478912, 819680545865, 819680612818)]

private def windowBatch6 : List (ℕ × ℕ × ℕ) :=
  [(820032593669, 820032661359, 820032729049), (820388547224, 820388615645, 820388684066),
   (820748302308, 820748371452, 820748440596), (821111821507, 821111891367, 821111961227),
   (821479067270, 821479137839, 821479208408), (821850001923, 821850073194, 821850144465),
   (822224587677, 822224659642, 822224731607), (822602786637, 822602859289, 822602931941),
   (822984560809, 822984634141, 822984707473), (823369872117, 823369946122, 823370020127),
   (823758682403, 823758757073, 823758831743), (824150953443, 824151028771, 824151104099)]

private def windowBatch7 : List (ℕ × ℕ × ℕ) :=
  [(824546646951, 824546722930, 824546798909), (824945724592, 824945801214, 824945877836),
   (825348147985, 825348225243, 825348302501), (825753878719, 825753956606, 825754034493),
   (826162878355, 826162956863, 826163035371), (826575108435, 826575187557, 826575266679),
   (826990530494, 826990610223, 826990689952), (827409106064, 827409186392, 827409266720),
   (827830796684, 827830877604, 827830958524), (828255563905, 828255645409, 828255726913),
   (828683369297, 828683451379, 828683533461), (829114174466, 829114257117, 829114339768)]

private def windowBatch8 : List (ℕ × ℕ × ℕ) :=
  [(829547941043, 829548024257, 829548107471), (829984630708, 829984714477, 829984798246),
   (830424205189, 830424289506, 830424373823), (830866626267, 830866711125, 830866795983),
   (831311855789, 831311941180, 831312026571), (831759855667, 831759941584, 831760027501),
   (832210587890, 832210674326, 832210760762), (832664014526, 832664101473, 832664188420),
   (833120097729, 833120185181, 833120272633), (833578799749, 833578887698, 833578975647),
   (834040082931, 834040171370, 834040259809), (834503909723, 834503998644, 834504087565)]

private def windowBatch9 : List (ℕ × ℕ × ℕ) :=
  [(834970242680, 834970332077, 834970421474), (835439044476, 835439134341, 835439224206),
   (835910277898, 835910368225, 835910458552), (836383905860, 836383996641, 836384087422),
   (836859891403, 836859982631, 836860073859), (837338197699, 837338289367, 837338381035),
   (837818788058, 837818880160, 837818972262), (838301625934, 838301718462, 838301810990),
   (838786674923, 838786767870, 838786860817), (839273898770, 839273992130, 839274085490),
   (839763261378, 839763355143, 839763448908), (840254726799, 840254820963, 840254915127)]

private def windowBatch10 : List (ℕ × ℕ × ℕ) :=
  [(840748259255, 840748353810, 840748448365), (841243823123, 841243918063, 841244013003),
   (841741382951, 841741478270, 841741573589), (842240903461, 842240999151, 842241094841),
   (842742349541, 842742445596, 842742541651), (843245686262, 843245782675, 843245879088),
   (843750878870, 843750975635, 843751072400), (844257892796, 844257989906, 844258087016),
   (844766693653, 844766791101, 844766888549), (845277247241, 845277345021, 845277442801),
   (845789519552, 845789617657, 845789715762), (846303476766, 846303575190, 846303673614)]

private def windowBatch11 : List (ℕ × ℕ × ℕ) :=
  [(846819085258, 846819183995, 846819282732), (847336311601, 847336410644, 847336509687),
   (847855122563, 847855221905, 847855321247), (848375485109, 848375584745, 848375684381),
   (848897366411, 848897466334, 848897566257), (849420733839, 849420834043, 849420934247),
   (849945554970, 849945655449, 849945755928), (850471797584, 850471898332, 850471999080),
   (850999429672, 850999530682, 850999631692), (851528419427, 851528520694, 851528621961),
   (852058735256, 852058836774, 852058938292), (852590345778, 852590447540, 852590549302)]

private def windowBatch12 : List (ℕ × ℕ × ℕ) :=
  [(853123219816, 853123321817, 853123423818), (853657326414, 853657428647, 853657530880),
   (854192634822, 854192737282, 854192839742), (854729114507, 854729217188, 854729319869),
   (855266735150, 855266838047, 855266940944), (855805466648, 855805569754, 855805672860),
   (856345279112, 856345382422, 856345485732), (856886142869, 856886246377, 856886349885),
   (857428028462, 857428132163, 857428235864), (857970906653, 857971010541, 857971114429),
   (858514748419, 858514852488, 858514956557), (859059524952, 859059629197, 859059733442)]

private def windowBatch13 : List (ℕ × ℕ × ℕ) :=
  [(859605207664, 859605312080, 859605416496), (860151768185, 860151872766, 860151977347),
   (860699178359, 860699283099, 860699387839), (861247410247, 861247515142, 861247620037),
   (861796436131, 861796541175, 861796646219), (862346228505, 862346333693, 862346438881),
   (862896760082, 862896865409, 862896970736), (863448003793, 863448109253, 863448214713),
   (863999932779, 864000038368, 864000143957), (864552520403, 864552626115, 864552731827),
   (865105740238, 865105846069, 865105951900), (865659566077, 865659672021, 865659777965)]

private def windowBatch14 : List (ℕ × ℕ × ℕ) :=
  [(866213971922, 866214077974, 866214184026), (866768931990, 866769038146, 866769144302),
   (867324420714, 867324526968, 867324633222), (867880412734, 867880519082, 867880625430),
   (868436882906, 868436989343, 868437095780), (868993806296, 868993912818, 868994019340),
   (869551158180, 869551264781, 869551371382), (870108914042, 870109020718, 870109127394),
   (870667049578, 870667156324, 870667263070), (871225540687, 871225647499, 871225754311),
   (871784363481, 871784470354, 871784577227), (872343494273, 872343601203, 872343708133)]

private def windowBatch15 : List (ℕ × ℕ × ℕ) :=
  [(872902909585, 872903016567, 872903123549), (873462586140, 873462693170, 873462800200),
   (874022500866, 874022607939, 874022715012), (874582630894, 874582738006, 874582845118),
   (875142953554, 875143060701, 875143167848), (875703446380, 875703553557, 875703660734),
   (876264087101, 876264194304, 876264301507), (876824853646, 876824960871, 876825068096),
   (877385724142, 877385831385, 877385938628), (877946676911, 877946784168, 877946891425),
   (878507690471, 878507797737, 878507905003), (879068743531, 879068850803, 879068958075)]

private def windowBatch16 : List (ℕ × ℕ × ℕ) :=
  [(879629814996, 879629922269, 879630029542), (880190883959, 880190991230, 880191098501),
   (880751929707, 880752036971, 880752144235), (881312931712, 881313038966, 881313146220),
   (881873869637, 881873976877, 881874084117), (882434723330, 882434830552, 882434937774),
   (882995472826, 882995580026, 882995687226), (883556098340, 883556205515, 883556312690),
   (884116580277, 884116687422, 884116794567), (884676899216, 884677006328, 884677113440),
   (885237035921, 885237142997, 885237250073), (885796971336, 885797078371, 885797185406)]

private def windowBatch17 : List (ℕ × ℕ × ℕ) :=
  [(886356686579, 886356793570, 886356900561), (886916162947, 886916269891, 886916376835),
   (887475381912, 887475488805, 887475595698), (888034325120, 888034431958, 888034538796),
   (888592974389, 888593081170, 888593187951), (889151311712, 889151418431, 889151525150),
   (889709319246, 889709425900, 889709532554), (890266979322, 890267085908, 890267192494),
   (890824274436, 890824380951, 890824487466), (891381187252, 891381293692, 891381400132),
   (891937700598, 891937806960, 891937913322), (892493797464, 892493903745, 892494010026)]

private def windowBatch18 : List (ℕ × ℕ × ℕ) :=
  [(893049461007, 893049567203, 893049673399), (893604674539, 893604780648, 893604886757),
   (894159421538, 894159527556, 894159633574), (894713685635, 894713791559, 894713897483),
   (895267450622, 895267556449, 895267662276), (895820700445, 895820806172, 895820911899),
   (896373419204, 896373524828, 896373630452), (896925591156, 896925696674, 896925802192),
   (897477200705, 897477306114, 897477411523), (898028232409, 898028337706, 898028443003),
   (898578670975, 898578776157, 898578881339), (899128501256, 899128606321, 899128711386)]

private def windowBatch19 : List (ℕ × ℕ × ℕ) :=
  [(899677708256, 899677813200, 899677918144), (900226277119, 900226381940, 900226486761),
   (900774193141, 900774297835, 900774402529), (901321441753, 901321546318, 901321650883),
   (901868008532, 901868112966, 901868217400), (902413879196, 902413983495, 902414087794),
   (902959039602, 902959143764, 902959247926), (903503475743, 903503579765, 903503683787),
   (904047173750, 904047277630, 904047381510), (904590119892, 904590223627, 904590327362),
   (905132300569, 905132404156, 905132507743), (905673702316, 905673805753, 905673909190)]

private def windowBatch20 : List (ℕ × ℕ × ℕ) :=
  [(906214311800, 906214415084, 906214518368), (906754115818, 906754218947, 906754322076),
   (907293101296, 907293204267, 907293307238), (907831255291, 907831358102, 907831460913),
   (908368564986, 908368667634, 908368770282), (908905017687, 908905120170, 908905222653),
   (909440600829, 909440703145, 909440805461), (909975301970, 909975404116, 909975506262),
   (910509108788, 910509210762, 910509312736), (911042009086, 911042110885, 911042212684),
   (911573990783, 911574092406, 911574194029), (912105041921, 912105143365, 912105244809)]

private def windowBatch21 : List (ℕ × ℕ × ℕ) :=
  [(912635150660, 912635251922, 912635353184), (913164305272, 913164406351, 913164507430),
   (913692494151, 913692595044, 913692695937), (914219705802, 914219806507, 914219907212),
   (914745928844, 914746029359, 914746129874), (915271152008, 915271252331, 915271352654),
   (915795364141, 915795464269, 915795564397), (916318554192, 916318654124, 916318754056),
   (916840711227, 916840810960, 916840910693), (917361824415, 917361923948, 917362023481),
   (917881883037, 917881982367, 917882081697), (918400876476, 918400975601, 918401074726)]

private def windowBatch22 : List (ℕ × ℕ × ℕ) :=
  [(918918794220, 918918893139, 918918992058), (919435625867, 919435724577, 919435823287),
   (919951361110, 919951459609, 919951558108), (920465989749, 920466088036, 920466186323),
   (920979501685, 920979599757, 920979697829), (921491886916, 921491984772, 921492082628),
   (922003135543, 922003233181, 922003330819), (922513237763, 922513335181, 922513432599),
   (923022183870, 923022281066, 923022378262), (923529964255, 923530061227, 923530158199),
   (924036569404, 924036666150, 924036762896), (924541989897, 924542086416, 924542182935)]

private def windowBatch23 : List (ℕ × ℕ × ℕ) :=
  [(925046216408, 925046312698, 925046408988), (925549239703, 925549335762, 925549431821),
   (926051050640, 926051146466, 926051242292), (926551640167, 926551735759, 926551831351),
   (927050999322, 927051094678, 927051190034), (927549119234, 927549214352, 927549309470),
   (928045991116, 928046085995, 928046180874), (928541606271, 928541700908, 928541795545),
   (929035956087, 929036050482, 929036144877), (929529032039, 929529126189, 929529220339),
   (930020825684, 930020919588, 930021013492), (930511328664, 930511422321, 930511515978)]

private def windowBatch24 : List (ℕ × ℕ × ℕ) :=
  [(931000532704, 931000626112, 931000719520), (931488429613, 931488522770, 931488615927),
   (931975011277, 931975104182, 931975197087), (932460269665, 932460362316, 932460454967),
   (932944196826, 932944289222, 932944381618), (933426784887, 933426877026, 933426969165),
   (933908026051, 933908117932, 933908209813), (934387912604, 934388004225, 934388095846),
   (934866436901, 934866528261, 934866619621), (935343591379, 935343682476, 935343773573),
   (935819368547, 935819459380, 935819550213), (936293760987, 936293851555, 936293942123)]

private def windowBatch25 : List (ℕ × ℕ × ℕ) :=
  [(936766761359, 936766851660, 936766941961), (937238362390, 937238452423, 937238542456),
   (937708556884, 937708646647, 937708736410), (938177337713, 938177427205, 938177516697),
   (938644697820, 938644787040, 938644876260), (939110630221, 939110719167, 939110808113),
   (939575127996, 939575216667, 939575305338), (940038184297, 940038272692, 940038361087),
   (940499792344, 940499880461, 940499968578), (940959945421, 940960033260, 940960121099),
   (941418636884, 941418724442, 941418812000), (941875860147, 941875947424, 941876034701)]

private def windowBatch26 : List (ℕ × ℕ × ℕ) :=
  [(942331608695, 942331695690, 942331782685), (942785876077, 942785962788, 942786049499),
   (943238655904, 943238742330, 943238828756), (943689941850, 943690027990, 943690114130),
   (944139727653, 944139813505, 944139899357), (944588007112, 944588092676, 944588178240),
   (945034774088, 945034859362, 945034944636), (945480022502, 945480107485, 945480192468),
   (945923746336, 945923831027, 945923915718), (946365939629, 946366024027, 946366108425),
   (946806596484, 946806680587, 946806764690), (947245711056, 947245794864, 947245878672)]

private def windowBatch27 : List (ℕ × ℕ × ℕ) :=
  [(947683277563, 947683361074, 947683444585), (948119290275, 948119373489, 948119456703),
   (948553743525, 948553826440, 948553909355), (948986631698, 948986714313, 948986796928),
   (949417949233, 949418031547, 949418113861), (949847690627, 949847772640, 949847854653),
   (950275850432, 950275932142, 950276013852), (950702423251, 950702504657, 950702586063),
   (951127403742, 951127484843, 951127565944), (951550786614, 951550867409, 951550948204),
   (951972566631, 951972647119, 951972727607), (952392738608, 952392818788, 952392898968)]

private def windowBatch28 : List (ℕ × ℕ × ℕ) :=
  [(952811297409, 952811377280, 952811457151), (953228237951, 953228317512, 953228397073),
   (953643555201, 953643634451, 953643713701), (954057244174, 954057323113, 954057402052),
   (954469299938, 954469378564, 954469457190), (954879717607, 954879795919, 954879874231),
   (955288492341, 955288570339, 955288648337), (955695619354, 955695697036, 955695774718),
   (956101093901, 956101171267, 956101248633), (956504911290, 956504988338, 956505065386),
   (956907066869, 956907143599, 956907220329), (957307556038, 957307632449, 957307708860)]

private def windowBatch29 : List (ℕ × ℕ × ℕ) :=
  [(957706374238, 957706450329, 957706526420), (958103516957, 958103592728, 958103668499),
   (958498979729, 958499055178, 958499130627), (958892758130, 958892833256, 958892908382),
   (959284847780, 959284922583, 959284997386), (959675244343, 959675318822, 959675393301),
   (960063943528, 960064017682, 960064091836), (960450941083, 960451014911, 960451088739),
   (960836232799, 960836306301, 960836379803), (961219814512, 961219887686, 961219960860),
   (961601682094, 961601754940, 961601827786), (961981831462, 961981903979, 961981976496)]

private def windowBatch30 : List (ℕ × ℕ × ℕ) :=
  [(962360258572, 962360330760, 962360402948), (962736959422, 962737031279, 962737103136),
   (963111930046, 963112001572, 963112073098), (963485166522, 963485237716, 963485308910),
   (963856664962, 963856735824, 963856806686), (964226421522, 964226492050, 964226562578),
   (964594432392, 964594502586, 964594572780), (964960693803, 964960763662, 964960833521),
   (965325202020, 965325271544, 965325341068), (965687953351, 965688022538, 965688091725),
   (966048944135, 966049012985, 966049081835), (966408170750, 966408239263, 966408307776)]

private def windowBatch31 : List (ℕ × ℕ × ℕ) :=
  [(966765629610, 966765697785, 966765765960), (967121317167, 967121385003, 967121452839),
   (967475229904, 967475297400, 967475364896), (967827364343, 967827431499, 967827498655),
   (968177717040, 968177783855, 968177850670), (968526284585, 968526351058, 968526417531),
   (968873063601, 968873129732, 968873195863), (969218050748, 969218116536, 969218182324),
   (969561242717, 969561308161, 969561373605), (969902636234, 969902701334, 969902766434),
   (970242228056, 970242292811, 970242357566), (970580014975, 970580079385, 970580143795)]

private def windowBatch32 : List (ℕ × ℕ × ℕ) :=
  [(970915993814, 970916057878, 970916121942), (971250161429, 971250225146, 971250288863),
   (971582514707, 971582578077, 971582641447), (971913050566, 971913113588, 971913176610),
   (972241765957, 972241828631, 972241891305), (972568657860, 972568720185, 972568782510),
   (972893723288, 972893785264, 972893847240), (973216959282, 973217020908, 973217082534),
   (973538362916, 973538424191, 973538485466), (973857931290, 973857992214, 973858053138),
   (974175661537, 974175722109, 974175782681), (974491550818, 974491611038, 974491671258)]

private def windowBatch33 : List (ℕ × ℕ × ℕ) :=
  [(974805596323, 974805656190, 974805716057), (975117795271, 975117854785, 975117914299),
   (975428144910, 975428204070, 975428263230), (975736642515, 975736701321, 975736760127),
   (976043285392, 976043343843, 976043402294), (976348070871, 976348128966, 976348187061),
   (976650996313, 976651054052, 976651111791), (976952059103, 976952116486, 976952173869),
   (977251256657, 977251313683, 977251370709), (977548586414, 977548643083, 977548699752),
   (977844045843, 977844102154, 977844158465), (978137632438, 978137688391, 978137744344)]

private def windowBatch34 : List (ℕ × ℕ × ℕ) :=
  [(978429343719, 978429399313, 978429454907), (978719177233, 978719232468, 978719287703),
   (979007130550, 979007185425, 979007240300), (979293201270, 979293255785, 979293310300),
   (979577387014, 979577441168, 979577495322), (979859685432, 979859739225, 979859793018),
   (980140094194, 980140147626, 980140201058), (980418611001, 980418664071, 980418717141),
   (980695233575, 980695286282, 980695338989), (980969959661, 980970012005, 980970064349),
   (981242787030, 981242839011, 981242890992), (981513713476, 981513765094, 981513816712)]

private def windowBatch35 : List (ℕ × ℕ × ℕ) :=
  [(981782736821, 981782788074, 981782839327), (982049854902, 982049905791, 982049956680),
   (982315065587, 982315116111, 982315166635), (982578366765, 982578416924, 982578467083),
   (982839756346, 982839806139, 982839855932), (983099232264, 983099281691, 983099331118),
   (983356792477, 983356841538, 983356890599), (983612434964, 983612483658, 983612532352),
   (983866157726, 983866206053, 983866254380), (984117958787, 984118006746, 984118054705),
   (984367836193, 984367883784, 984367931375), (984615788010, 984615835233, 984615882456)]

private def windowBatch36 : List (ℕ × ℕ × ℕ) :=
  [(984861812329, 984861859183, 984861906037), (985105907258, 985105953743, 985106000228),
   (985348070931, 985348117046, 985348163161), (985588301497, 985588347243, 985588392989),
   (985826597133, 985826642509, 985826687885), (986062956033, 986063001038, 986063046043),
   (986297376411, 986297421045, 986297465679), (986529856502, 986529900765, 986529945028),
   (986760394562, 986760438454, 986760482346), (986988988868, 986989032388, 986989075908),
   (987215637716, 987215680864, 987215724012), (987440339421, 987440382196, 987440424971)]

private def windowBatch37 : List (ℕ × ℕ × ℕ) :=
  [(987663092318, 987663134721, 987663177124), (987883894764, 987883936794, 987883978824),
   (988102745133, 988102786789, 988102828445), (988319641819, 988319683101, 988319724383),
   (988534583234, 988534624143, 988534665052), (988747567812, 988747608346, 988747648880),
   (988958594002, 988958634162, 988958674322), (989167660276, 989167700061, 989167739846),
   (989374765122, 989374804532, 989374843942), (989579907047, 989579946081, 989579985115),
   (989783084576, 989783123234, 989783161892), (989984296253, 989984334535, 989984372817)]

private def windowBatch38 : List (ℕ × ℕ × ℕ) :=
  [(990183540640, 990183578546, 990183616452), (990380816317, 990380853847, 990380891377),
   (990576121882, 990576159035, 990576196188), (990769455950, 990769492726, 990769529502),
   (990960817156, 990960853554, 990960889952), (991150204149, 991150240170, 991150276191),
   (991337615599, 991337651242, 991337686885), (991523050191, 991523085456, 991523120721),
   (991706506628, 991706541515, 991706576402), (991887983631, 991888018139, 991888052647),
   (992067479936, 992067514065, 992067548194), (992244994297, 992245028047, 992245061797)]

private def windowBatch39 : List (ℕ × ℕ × ℕ) :=
  [(992420525486, 992420558857, 992420592228), (992594072290, 992594105281, 992594138272),
   (992765633513, 992765666125, 992765698737), (992935207977, 992935240209, 992935272441),
   (993102794517, 993102826369, 993102858221), (993268391990, 993268423461, 993268454932),
   (993431999261, 993432030352, 993432061443), (993593615220, 993593645930, 993593676640),
   (993753238768, 993753269097, 993753299426), (993910868822, 993910898769, 993910928716),
   (994066504315, 994066533881, 994066563447), (994220144199, 994220173383, 994220202567)]

private def windowBatch40 : List (ℕ × ℕ × ℕ) :=
  [(994371787438, 994371816240, 994371845042), (994521433013, 994521461433, 994521489853),
   (994669079919, 994669107957, 994669135995), (994814727170, 994814754826, 994814782482),
   (994958373793, 994958401066, 994958428339), (995100018829, 995100045719, 995100072609),
   (995239661337, 995239687844, 995239714351), (995377300390, 995377326514, 995377352638),
   (995512935075, 995512960816, 995512986557), (995646564495, 995646589853, 995646615211),
   (995778187769, 995778212743, 995778237717), (995907804029, 995907828619, 995907853209)]

private def windowBatch41 : List (ℕ × ℕ × ℕ) :=
  [(996035412422, 996035436628, 996035460834), (996161012110, 996161035932, 996161059754),
   (996284602271, 996284625709, 996284649147), (996406182097, 996406205150, 996406228203),
   (996525750791, 996525773460, 996525796129), (996643307576, 996643329860, 996643352144),
   (996758851685, 996758873584, 996758895483), (996872382368, 996872403882, 996872425396),
   (996983898888, 996983920017, 996983941146), (997093400522, 997093421266, 997093442010),
   (997200886563, 997200906921, 997200927279), (997306356315, 997306376288, 997306396261)]

private def windowBatch42 : List (ℕ × ℕ × ℕ) :=
  [(997409809100, 997409828687, 997409848274), (997511244249, 997511263450, 997511282651),
   (997610661112, 997610679927, 997610698742), (997708059049, 997708077478, 997708095907),
   (997803437435, 997803455478, 997803473521), (997896795661, 997896813318, 997896830975),
   (997988133129, 997988150399, 997988167669), (998077449254, 998077466138, 998077483022),
   (998164743469, 998164759966, 998164776463), (998250015216, 998250031326, 998250047436),
   (998333263952, 998333279675, 998333295398), (998414489147, 998414504484, 998414519821)]

private def windowBatch43 : List (ℕ × ℕ × ℕ) :=
  [(998493690287, 998493705237, 998493720187), (998570866870, 998570881432, 998570895994),
   (998646018405, 998646032580, 998646046755), (998719144417, 998719158205, 998719171993),
   (998790244445, 998790257845, 998790271245), (998859318038, 998859331051, 998859344064),
   (998926364762, 998926377387, 998926390012), (998991384191, 998991396429, 998991408667),
   (999054375919, 999054387769, 999054399619), (999115339549, 999115351011, 999115362473),
   (999174274696, 999174285770, 999174296844), (999231180990, 999231191676, 999231202362)]

private def windowBatch44 : List (ℕ × ℕ × ℕ) :=
  [(999286058075, 999286068373, 999286078671), (999338905606, 999338915516, 999338925426),
   (999389723252, 999389732774, 999389742296), (999438510694, 999438519828, 999438528962),
   (999485267628, 999485276374, 999485285120), (999529993760, 999530002118, 999530010476),
   (999572688812, 999572696781, 999572704750), (999613352516, 999613360097, 999613367678),
   (999651984619, 999651991811, 999651999003), (999688584878, 999688591682, 999688598486),
   (999723153068, 999723159483, 999723165898), (999755688970, 999755694997, 999755701024)]

private def windowBatch45 : List (ℕ × ℕ × ℕ) :=
  [(999786192384, 999786198022, 999786203660), (999814663119, 999814668368, 999814673617),
   (999841100997, 999841105858, 999841110719), (999865505855, 999865510327, 999865514799),
   (999887877540, 999887881623, 999887885706), (999908215912, 999908219607, 999908223302),
   (999926520847, 999926524153, 999926527459), (999942792230, 999942795147, 999942798064),
   (999957029960, 999957032488, 999957035016), (999969233949, 999969236088, 999969238227),
   (999979404119, 999979405869, 999979407619), (999987540409, 999987541771, 999987543133)]

private def windowBatch46 : List (ℕ × ℕ × ℕ) :=
  [(999993642768, 999993643741, 999993644714), (999997711158, 999997711742, 999997712326),
   (999999745554, 999999745749, 999999745944)]

private def windowBatches : List (List (ℕ × ℕ × ℕ)) :=
  [windowBatch0, windowBatch1, windowBatch2, windowBatch3, windowBatch4,
   windowBatch5, windowBatch6, windowBatch7, windowBatch8, windowBatch9,
   windowBatch10, windowBatch11, windowBatch12, windowBatch13, windowBatch14,
   windowBatch15, windowBatch16, windowBatch17, windowBatch18, windowBatch19,
   windowBatch20, windowBatch21, windowBatch22, windowBatch23, windowBatch24,
   windowBatch25, windowBatch26, windowBatch27, windowBatch28, windowBatch29,
   windowBatch30, windowBatch31, windowBatch32, windowBatch33, windowBatch34,
   windowBatch35, windowBatch36, windowBatch37, windowBatch38, windowBatch39,
   windowBatch40, windowBatch41, windowBatch42, windowBatch43, windowBatch44,
   windowBatch45, windowBatch46]

private def windows : List (ℕ × ℕ × ℕ) := windowBatches.flatten

private def scaledAbsProd (x : ℤ) : ℕ :=
  (x + denominator).natAbs ^ mainMultiplicity *
    (windows.map fun w => (x - w.2.1).natAbs).prod

private def target : ℕ := denominator ^ (mainMultiplicity + windows.length)

private theorem denominator_pos : 0 < denominator := by decide

private theorem mainMultiplicity_pos : 0 < mainMultiplicity := by decide

private theorem main_contains :
    mainLeft < -(denominator : ℤ) ∧ -(denominator : ℤ) < mainRight := by decide

set_option maxRecDepth 5000 in
private theorem window_geometry {w : ℕ × ℕ × ℕ} (h : w ∈ windows) :
    w.1 < w.2.1 ∧ w.2.1 < w.2.2 ∧ w.2.1 ≤ denominator := by
  have hall : windows.all (fun w => decide (w.1 < w.2.1 ∧ w.2.1 < w.2.2 ∧ w.2.1 ≤ denominator)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp hall w h)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem main_endpoints :
    target ≤ scaledAbsProd mainLeft ∧ target ≤ scaledAbsProd mainRight := by
  decide +kernel

private def windowEndpointCheck (w : ℕ × ℕ × ℕ) : Bool :=
  decide (target ≤ scaledAbsProd w.1 ∧ target ≤ scaledAbsProd w.2.2)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem window_endpoints {w : ℕ × ℕ × ℕ} (h : w ∈ windows) :
    target ≤ scaledAbsProd w.1 ∧ target ≤ scaledAbsProd w.2.2 := by
  obtain ⟨ws, hws, hw⟩ := List.mem_flatten.mp h
  have hc : ws.all windowEndpointCheck = true := by
    simp only [windowBatches, List.mem_cons, List.not_mem_nil, or_false] at hws
    rcases hws with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp hc w hw)

set_option maxRecDepth 5000 in
private theorem width_lt :
    (1000 : ℤ) * (mainRight - mainLeft + (windows.map (fun w => w.2.2 - w.1)).sum) <
      1835 * (denominator : ℤ) := by
  decide +kernel

end SublevelWitness

theorem OMA.solution : type_of% @Erdos1038.erdos_1038.variants.inf_upperBound := by
  refine SublevelCertificate.proof_from_integer_windows
    SublevelWitness.denominator SublevelWitness.mainMultiplicity
    SublevelWitness.mainLeft SublevelWitness.mainRight SublevelWitness.windows
    SublevelWitness.denominator_pos SublevelWitness.mainMultiplicity_pos
    SublevelWitness.main_contains (fun _ h => SublevelWitness.window_geometry h) ?_
    SublevelWitness.width_lt
  intro x hx
  rcases hx with rfl | rfl | ⟨w, hw, he | he⟩
  · exact SublevelWitness.main_endpoints.1
  · exact SublevelWitness.main_endpoints.2
  · rw [he]
    exact (SublevelWitness.window_endpoints hw).1
  · rw [he]
    exact (SublevelWitness.window_endpoints hw).2