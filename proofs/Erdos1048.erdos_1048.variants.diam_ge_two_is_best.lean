import FormalConjectures.ErdosProblems.«1048»

/-! The closed unit disk is the whole polynomial lemniscate for a positive power of X. -/

open Polynomial Erdos1043

theorem OMA.solution : type_of% @Erdos1048.erdos_1048.variants.diam_ge_two_is_best := by
  intro n hn
  have hlevel : levelSet ((X : ℂ[X]) ^ n) = Metric.closedBall (0 : ℂ) 1 := by
    ext z
    change ‖((X : ℂ[X]) ^ n).eval z‖ ≤ 1 ↔ dist z 0 ≤ 1
    rw [Polynomial.eval_pow, Polynomial.eval_X, norm_pow, dist_zero_right]
    exact pow_le_one_iff_of_nonneg (norm_nonneg _) (by omega)
  rw [hlevel, Metric.isPreconnected_closedBall.connectedComponentIn (by simp)]
  apply le_antisymm
  · rw [Metric.ediam_le_iff]
    intro x hx y hy
    have hx' := Metric.mem_closedBall.mp hx
    have hy' := Metric.mem_closedBall.mp hy
    have hdist : dist x y ≤ 2 := by
      have h := dist_triangle x (0 : ℂ) y
      rw [dist_comm (0 : ℂ) y] at h
      linarith
    simpa only [edist_dist, ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hdist
  · calc
      2 = edist (1 : ℂ) (-1) := by
        rw [edist_dist, dist_eq_norm, show (1 : ℂ) - (-1) = 2 by ring]
        simp [RCLike.norm_two]
      _ ≤ _ := Metric.edist_le_ediam_of_mem (by simp [Metric.mem_closedBall, dist_zero_right])
        (by simp [Metric.mem_closedBall, dist_zero_right])