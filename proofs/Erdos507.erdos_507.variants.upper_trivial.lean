import FormalConjectures.ErdosProblems.«507»

/-! Use vertical strips of width proportional to the inverse number of points. -/

open Asymptotics Filter
open scoped EuclideanGeometry

lemma OMA.heilbronn_coord_abs (x : ℝ²) (hx : x ∈ Metric.closedBall (0 : ℝ²) 1)
    (i : Fin 2) : |x i| ≤ 1 := by
  have hnorm : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
  exact (Real.norm_eq_abs (x i) ▸ PiLp.norm_apply_le x i).trans hnorm

lemma OMA.heilbronn_area_le (a b c : ℝ²) (w : ℝ)
    (hac : |a 0 - c 0| ≤ w) (hbc : |b 0 - c 0| ≤ w)
    (hay : |a 1 - c 1| ≤ 2) (hby : |b 1 - c 1| ≤ 2) :
    |EuclideanGeometry.triangle_area a b c| ≤ 2 * w := by
  have hdet : EuclideanGeometry.triangle_area a b c =
      ((a 0 - c 0) * (b 1 - c 1) - (b 0 - c 0) * (a 1 - c 1)) / 2 := by
    rw [EuclideanGeometry.triangle_area_eq_det, Matrix.det_fin_three]
    simp
    ring
  rw [hdet, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ (|(a 0 - c 0) * (b 1 - c 1)| + |(b 0 - c 0) * (a 1 - c 1)|) / 2 :=
      div_le_div_of_nonneg_right (abs_sub _ _) (by norm_num)
    _ ≤ (w * 2 + w * 2) / 2 := by
      rw [abs_mul, abs_mul]
      have hw : 0 ≤ w := (abs_nonneg _).trans hac
      gcongr
    _ = 2 * w := by ring

lemma OMA.heilbronn_min_le (S : Finset ℝ²) (n : ℕ) (hn : 6 ≤ n)
    (hS : S.card = n) (hball : (S : Set ℝ²) ⊆ Metric.closedBall 0 1) :
    Erdos507.minTriangleArea S ≤ 36 * (1 / (n : ℝ)) := by
  classical
  let k : ℕ := n / 3
  have hk : 0 < (k : ℝ) := by
    exact_mod_cast (show 0 < k by dsimp [k]; omega)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  let scaled (p : ℝ²) : ℝ := (p 0 + 1) * (k : ℝ) / 3
  let index (p : ℝ²) : ℕ := ⌊scaled p⌋₊
  have hscaled_nonneg (p : ℝ²) (hp : p ∈ S) : 0 ≤ scaled p := by
    have hx := (abs_le.mp (OMA.heilbronn_coord_abs p (hball hp) 0)).1
    dsimp [scaled]
    exact div_nonneg (mul_nonneg (by linarith) hk.le) (by norm_num)
  have hmaps : ∀ p ∈ S, index p ∈ Finset.range k := by
    intro p hp
    apply Finset.mem_range.mpr
    apply (Nat.floor_lt (hscaled_nonneg p hp)).mpr
    have hx := (abs_le.mp (OMA.heilbronn_coord_abs p (hball hp) 0)).2
    have hb := mul_le_mul_of_nonneg_right (show p 0 + 1 ≤ 2 by linarith) hk.le
    dsimp [scaled]
    linarith
  have hmany : (Finset.range k).card * 2 < S.card := by
    rw [Finset.card_range, hS]
    dsimp [k]
    omega
  obtain ⟨j, _, hj⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hmany
  obtain ⟨p, hp⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 3) (s := S.filter fun x => index x = j) (by simpa using Nat.succ_le_of_lt hj)
  have hpS (i : Fin 3) : p i ∈ S :=
    (Finset.mem_filter.mp (hp (Set.mem_range_self i))).1
  have hpindex (i : Fin 3) : index (p i) = j :=
    (Finset.mem_filter.mp (hp (Set.mem_range_self i))).2
  have hstrip (i : Fin 3) : (j : ℝ) ≤ scaled (p i) ∧ scaled (p i) < (j : ℝ) + 1 :=
    (Nat.floor_eq_iff (hscaled_nonneg _ (hpS i))).mp (hpindex i)
  have hx_one_way (i l : Fin 3) : p i 0 - p l 0 ≤ 3 / (k : ℝ) := by
    apply (le_div_iff₀ hk).mpr
    calc
      _ = 3 * (scaled (p i) - scaled (p l)) := by dsimp [scaled]; ring
      _ ≤ 3 := by linarith [(hstrip i).2, (hstrip l).1]
  have hxdiff (i l : Fin 3) : |p i 0 - p l 0| ≤ 3 / (k : ℝ) := by
    apply abs_le.mpr
    constructor
    · linarith [hx_one_way l i]
    · exact hx_one_way i l
  have hydiff (i l : Fin 3) : |p i 1 - p l 1| ≤ 2 := by
    have hi := abs_le.mp (OMA.heilbronn_coord_abs (p i) (hball (hpS i)) 1)
    have hl := abs_le.mp (OMA.heilbronn_coord_abs (p l) (hball (hpS l)) 1)
    exact abs_le.mpr ⟨by linarith [hi.1, hl.2], by linarith [hi.2, hl.1]⟩
  have hmin : Erdos507.minTriangleArea S ≤
      |EuclideanGeometry.triangle_area (p 0) (p 1) (p 2)| := by
    apply csInf_le
    · exact ⟨0, by rintro x ⟨q, _, _, rfl⟩; exact abs_nonneg _⟩
    · exact ⟨p, p.injective, hpS, rfl⟩
  calc
    Erdos507.minTriangleArea S ≤
        |EuclideanGeometry.triangle_area (p 0) (p 1) (p 2)| := hmin
    _ ≤ 2 * (3 / (k : ℝ)) :=
      OMA.heilbronn_area_le _ _ _ _ (hxdiff 0 2) (hxdiff 1 2) (hydiff 0 2) (hydiff 1 2)
    _ = 6 / (k : ℝ) := by ring
    _ ≤ 36 * (1 / (n : ℝ)) := by
      have hnk : (n : ℝ) ≤ 6 * (k : ℝ) := by
        exact_mod_cast (show n ≤ 6 * k by dsimp [k]; omega)
      rw [← mul_div_assoc, mul_one]
      apply (div_le_div_iff₀ hk hnR).mpr
      linarith

theorem OMA.solution : type_of% @Erdos507.erdos_507.variants.upper_trivial := by
  apply Asymptotics.IsBigO.of_bound 36
  filter_upwards [eventually_ge_atTop (6 : ℕ)] with n hn
  have hnonneg : 0 ≤ Erdos507.α n := by
    apply Real.sSup_nonneg
    rintro x ⟨S, _, rfl⟩
    apply Real.sInf_nonneg
    rintro x ⟨p, _, _, rfl⟩
    exact abs_nonneg _
  rw [Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg (by positivity)]
  apply Real.sSup_le _ (by positivity)
  rintro x ⟨S, ⟨hS, hball, _⟩, rfl⟩
  exact OMA.heilbronn_min_le S n hn hS hball