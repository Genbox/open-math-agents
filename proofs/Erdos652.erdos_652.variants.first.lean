import FormalConjectures.ErdosProblems.«652»

/-! Put one point at the origin and all the remaining points on the unit circle. -/

open scoped EuclideanGeometry

theorem OMA.solution : type_of% @Erdos652.erdos_652.variants.first := by
  classical
  let : DecidableEq ℝ² := Classical.decEq _
  let : DecidableEq ℝ := Classical.decEq _
  intro n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  let t (i : Fin (n - 1)) : ℝ := (i.val : ℝ) / (n : ℝ)
  let point (i : Fin (n - 1)) : ℝ² := WithLp.toLp 2 ![t i, Real.sqrt (1 - (t i) ^ 2)]
  have hpoint_inj : Function.Injective point := by
    intro i j hij
    have hcoord : t i = t j := congrArg (fun p : ℝ² => p 0) hij
    have hcast : (i.val : ℝ) = (j.val : ℝ) :=
      (div_left_inj' hnR.ne').mp hcoord
    exact Fin.ext (by exact_mod_cast hcast)
  have hdist (i : Fin (n - 1)) : dist (point i) (0 : ℝ²) = 1 := by
    have ht_nonneg : 0 ≤ t i := div_nonneg (Nat.cast_nonneg _) hnR.le
    have ht_le : t i ≤ 1 := by
      apply (div_le_iff₀ hnR).mpr
      rw [one_mul]
      have hi := i.isLt
      exact_mod_cast (show i.val ≤ n by omega)
    have hsq : 0 ≤ 1 - (t i) ^ 2 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr ht_le) (add_nonneg zero_le_one ht_nonneg)]
    rw [dist_zero_right, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    change Real.sqrt (‖t i‖ ^ 2 + ‖Real.sqrt (1 - (t i) ^ 2)‖ ^ 2) = 1
    simp only [Real.norm_eq_abs, sq_abs]
    rw [Real.sq_sqrt hsq, show (t i) ^ 2 + (1 - (t i) ^ 2) = 1 by ring, Real.sqrt_one]
  let shell : Finset ℝ² := Finset.univ.map ⟨point, hpoint_inj⟩
  have hs_card : shell.card = n - 1 := by simp [shell]
  have hs_dist (p : ℝ²) (hp : p ∈ shell) : dist p (0 : ℝ²) = 1 := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hp
    exact hdist i
  have hzero : (0 : ℝ²) ∉ shell := by
    intro h
    have hdist_zero := hs_dist 0 h
    norm_num at hdist_zero
  refine ⟨insert 0 shell, ?_, 0, Finset.mem_insert_self _ _, ?_⟩
  · rw [Finset.card_insert_of_notMem hzero, hs_card]
    omega
  · unfold distinctDistancesFrom
    rw [Finset.erase_insert hzero]
    have himage : shell.image (fun p => dist p (0 : ℝ²)) = shell.image (fun _ => (1 : ℝ)) :=
      Finset.image_congr (fun p hp => hs_dist p hp)
    have hne : shell.Nonempty := Finset.card_pos.mp (by rw [hs_card]; omega)
    rw [himage, Finset.image_const hne, Finset.card_singleton]