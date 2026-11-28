import OMAStatements.S_oeis_a335756
import Mathlib

namespace OMA.S_oeis_a335756

theorem a_rec (n : ℕ) (hn : 5 < n) : a n = 2 * a (n - 3) - a (n - 6) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have e1 : m + 6 - 3 = m + 3 := by omega
  have e2 : m + 6 - 6 = m := by omega
  rw [e1, e2]
  simp only [a]
  have h1 : (m + 6) % 3 = m % 3 := by omega
  have h2 : (m + 3) % 3 = m % 3 := by omega
  rw [h1, h2]
  split_ifs with h
  · have : (m + 6) / 3 = m / 3 + 2 := by omega
    have h' : (m + 3) / 3 = m / 3 + 1 := by omega
    rw [this, h']
    push_cast
    ring
  · have : (m : ℤ) + 6 - 1 = 2 * 0 + (m + 5) := by ring
    push_cast
    ring

open PowerSeries in
theorem gf : (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X + X ^ 2) ^ 2) =
      2 * (1 + X ^ 2 + 4 * X ^ 3 + 3 * X ^ 4 + 2 * X ^ 5)) := by
  have hP : ((1 - X) ^ 2 * (1 + X + X ^ 2) ^ 2 : PowerSeries ℚ) = 1 - 2 • X ^ 3 + X ^ 6 := by
    simp only [nsmul_eq_mul]; push_cast; ring
  have hR : (2 * (1 + X ^ 2 + 4 * X ^ 3 + 3 * X ^ 4 + 2 * X ^ 5) : PowerSeries ℚ) =
      2 • 1 + 2 • X ^ 2 + 8 • X ^ 3 + 6 • X ^ 4 + 4 • X ^ 5 := by
    simp only [nsmul_eq_mul]; push_cast; ring
  have e : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 2 • X ^ 3 + X ^ 6) =
      PowerSeries.mk (fun n => (a n : ℚ)) - 2 • (X ^ 3 * PowerSeries.mk (fun n => (a n : ℚ)))
        + X ^ 6 * PowerSeries.mk (fun n => (a n : ℚ)) := by
    simp only [nsmul_eq_mul]; push_cast; ring
  rw [hP, hR, e]
  ext n
  simp only [map_add, map_sub, map_nsmul, coeff_X_pow_mul', coeff_mk, coeff_one, coeff_X_pow]
  rcases (by omega : n < 6 ∨ 6 ≤ n) with h | h
  · interval_cases n <;> simp [a] <;> norm_num
  · have hq := a_rec n (by omega)
    have hq' : (a n : ℚ) = 2 * (a (n - 3) : ℚ) - (a (n - 6) : ℚ) := by exact_mod_cast hq
    have n0 : n ≠ 0 := by omega
    have n2 : n ≠ 2 := by omega
    have n3 : n ≠ 3 := by omega
    have n4 : n ≠ 4 := by omega
    have n5 : n ≠ 5 := by omega
    simp [n0, n2, n3, n4, n5, show 3 ≤ n by omega, show 6 ≤ n by omega, hq']

theorem solution_aux : type_of% @OMA.S_oeis_a335756.main := ⟨gf, a_rec⟩

end OMA.S_oeis_a335756

theorem OMA.solution : type_of% @OMA.S_oeis_a335756.main := OMA.S_oeis_a335756.solution_aux
