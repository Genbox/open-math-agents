import OMAStatements.S_oeis_a114698
import Mathlib

namespace OMA.S_oeis_a114698

theorem gf_pow (f : ℕ → ℚ) (d n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * (1 - PowerSeries.X) ^ d) =
      ∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i * (d.choose i : ℚ) * (if i ≤ n then f (n - i) else 0) := by
  rw [sub_eq_neg_add, add_pow, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h : PowerSeries.mk f * ((-PowerSeries.X) ^ i * 1 ^ (d - i) * (d.choose i : PowerSeries ℚ)) =
      PowerSeries.C (((-1 : ℚ) ^ i * (d.choose i : ℚ))) * (PowerSeries.X ^ i * PowerSeries.mk f) := by
    have hx : (-PowerSeries.X : PowerSeries ℚ) = PowerSeries.C (-1) * PowerSeries.X := by simp
    rw [hx, mul_pow, ← map_pow]
    simp only [one_pow, mul_one, map_mul, map_pow, map_neg, map_one, map_natCast]
    ring
  rw [h, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  simp [PowerSeries.coeff_mk]

open PowerSeries in
theorem gf : (PowerSeries.mk (fun k => (a (k + 1) : ℚ)) * (1 - X) ^ 2 = 1 + 16 * X + 3 * X ^ 2) := by
  have hR : (1 + 16 * X + 3 * X ^ 2 : PowerSeries ℚ) = 1 + 16 • X + 3 • X ^ 2 := by simp [nsmul_eq_mul]
  rw [hR]
  ext n
  rw [gf_pow]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, map_add, coeff_one, coeff_X, map_nsmul, coeff_X_pow]
  rcases n with _ | _ | _ | n
  · simp [a]
  · simp [a]; norm_num
  · simp [a]; norm_num
  · simp [a, Nat.choose]
    norm_num
    ring

theorem solution_aux : type_of% @OMA.S_oeis_a114698.main := by
  refine ⟨gf, ?_⟩
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  simp [a]
  ring

end OMA.S_oeis_a114698

theorem OMA.solution : type_of% @OMA.S_oeis_a114698.main := OMA.S_oeis_a114698.solution_aux
