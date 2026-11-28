import OMAStatements.S_oeis_a004138
import Mathlib

open PowerSeries

namespace OMA.S_oeis_a004138

lemma rec5 (n : ℕ) : (a (n + 6) : ℤ) - 2 * a (n + 5) + 2 * a (n + 3) - 3 * a (n + 2) + 2 * a (n + 1) = 0 := by
  have h1 : ∀ m, a (m + 5) = a (m + 4) + a (m + 3) - a (m + 2) + 2 * a (m + 1) + 2 := fun m => rfl
  have h2 := h1 (n + 1)
  have h3 := h1 n
  have e : ∀ k : ℕ, n + 1 + k = n + (1 + k) := fun k => by omega
  simp only [e] at h2
  norm_num at h2 h3
  linarith

end OMA.S_oeis_a004138

theorem OMA.solution : type_of% @OMA.S_oeis_a004138.main := by
  open OMA.S_oeis_a004138 in
  ext n
  have hP : (PowerSeries.mk (fun k => (a (k + 1) : ℚ))) * ((X - 1) * (2 * X ^ 4 - X ^ 3 + X ^ 2 + X - 1)) =
      C (2:ℚ) * (PowerSeries.mk (fun k => (a (k + 1) : ℚ)) * X ^ 5) - C (3:ℚ) * (PowerSeries.mk (fun k => (a (k + 1) : ℚ)) * X ^ 4)
      + C (2:ℚ) * (PowerSeries.mk (fun k => (a (k + 1) : ℚ)) * X ^ 3) - C (2:ℚ) * (PowerSeries.mk (fun k => (a (k + 1) : ℚ)) * X ^ 1)
      + PowerSeries.mk (fun k => (a (k + 1) : ℚ)) := by
    simp only [map_ofNat]; ring
  have hR : (-(-1 + X ^ 2 - 4 * X ^ 3 + 2 * X ^ 4) : PowerSeries ℚ) = 1 - X ^ 2 + C (4:ℚ) * X ^ 3 - C (2:ℚ) * X ^ 4 := by
    simp only [map_ofNat]; ring
  rw [hP, hR]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_one, coeff_X_pow, coeff_C]
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n <;> simp [a] <;> norm_num
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    have h := OMA.S_oeis_a004138.rec5 m
    have hq : (a (m + 6) : ℚ) - 2 * a (m + 5) + 2 * a (m + 3) - 3 * a (m + 2) + 2 * a (m + 1) = 0 := by
      exact_mod_cast h
    have e1 : 5 + m - 5 + 1 = m + 1 := by omega
    have e2 : 5 + m - 4 + 1 = m + 2 := by omega
    have e3 : 5 + m - 3 + 1 = m + 3 := by omega
    have e4 : 5 + m - 1 + 1 = m + 5 := by omega
    have e5 : 5 + m + 1 = m + 6 := by omega
    have e6 : 5 + m - 2 + 1 = m + 4 := by omega
    simp [show ¬ (5+m = 2) by omega, show ¬ (5+m=3) by omega, show ¬ (5+m=4) by omega, e1, e2, e3, e4, e5, e6, show 4 + m + 1 = m + 5 by omega]
    split_ifs <;> first | (exfalso; omega) | linarith
