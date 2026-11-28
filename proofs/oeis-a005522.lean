import OMAStatements.S_oeis_a005522
import Mathlib

namespace OMA.S_oeis_a005522
open PowerSeries

lemma a_succ (n : ℕ) : a (n + 1) = 1 + lucas (n + 1) + (Nat.fib (2 * n + 1) : ℤ) := by
  unfold a
  rw [if_neg (by omega), show 2 * (n + 1) - 1 = 2 * n + 1 by omega]

lemma rec5 (n : ℕ) : a (n + 6) = 5 * a (n + 5) - 7 * a (n + 4) + a (n + 3) + 3 * a (n + 2) - a (n + 1) := by
  rw [show n + 6 = (n + 5) + 1 from rfl, show n + 5 = (n + 4) + 1 from rfl,
    show n + 4 = (n + 3) + 1 from rfl, show n + 3 = (n + 2) + 1 from rfl,
    show n + 2 = (n + 1) + 1 from rfl]
  simp only [a_succ]
  simp only [show 2 * (n + 1) + 1 = 2 * n + 3 by ring, show 2 * (n + 1 + 1) + 1 = 2 * n + 5 by ring,
    show 2 * (n + 1 + 1 + 1) + 1 = 2 * n + 7 by ring,
    show 2 * (n + 1 + 1 + 1 + 1) + 1 = 2 * n + 9 by ring,
    show 2 * (n + 1 + 1 + 1 + 1 + 1) + 1 = 2 * n + 11 by ring]
  simp only [lucas, Nat.fib_add_two]
  push_cast
  ring

lemma coeffD' (f : PowerSeries ℚ) (n : ℕ) :
    coeff n (f * ((X - 1) * (X ^ 2 - 3 * X + 1) * (X ^ 2 + X - 1))) =
      coeff n f - 5 * (if 1 ≤ n then coeff (n - 1) f else 0)
        + 7 * (if 2 ≤ n then coeff (n - 2) f else 0) - (if 3 ≤ n then coeff (n - 3) f else 0)
        - 3 * (if 4 ≤ n then coeff (n - 4) f else 0) + (if 5 ≤ n then coeff (n - 5) f else 0) := by
  have : ((X - 1) * (X ^ 2 - 3 * X + 1) * (X ^ 2 + X - 1) : PowerSeries ℚ) =
      1 - 5 * X + 7 * X ^ 2 - X ^ 3 - 3 * X ^ 4 + X ^ 5 := by ring
  rw [this]
  have h2 : f * (1 - 5 * X + 7 * X ^ 2 - X ^ 3 - 3 * X ^ 4 + X ^ 5) =
      f - C (5:ℚ) * (f * X ^ 1) + C (7:ℚ) * (f * X ^ 2) - f * X ^ 3
        - C (3:ℚ) * (f * X ^ 4) + f * X ^ 5 := by
    simp only [map_ofNat]; ring
  rw [h2]
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_mul_X_pow']

end OMA.S_oeis_a005522

open OMA.S_oeis_a005522 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a005522.main := by
  ext n
  rw [coeffD']
  have hR : (-(-3 + 9 * X - X ^ 2 - 10 * X ^ 3 + 4 * X ^ 4) : PowerSeries ℚ) =
      C (3:ℚ) - C (9:ℚ) * X + X ^ 2 + C (10:ℚ) * X ^ 3 - C (4:ℚ) * X ^ 4 := by
    simp only [map_ofNat]; ring
  rw [hR]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_mk, coeff_C]
  by_cases hn : 5 ≤ n
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    have := rec5 m
    have e : ((a (m + 6) : ℤ) : ℚ) = 5 * (a (m + 5) : ℚ) - 7 * a (m + 4) + a (m + 3) + 3 * a (m + 2) - a (m + 1) := by
      rw [this]; push_cast; ring
    simp only [if_pos (show 1 ≤ 5 + m by omega), if_pos (show 2 ≤ 5 + m by omega),
      if_pos (show 3 ≤ 5 + m by omega), if_pos (show 4 ≤ 5 + m by omega), if_pos hn]
    simp only [show 5 + m - 1 = m + 4 by omega, show 5 + m - 2 = m + 3 by omega,
      show 5 + m - 3 = m + 2 by omega, show 5 + m - 4 = m + 1 by omega, show 5 + m - 5 = m by omega,
      show 5 + m + 1 = m + 6 by omega, show m + 4 + 1 = m + 5 by omega, show m + 3 + 1 = m + 4 by omega,
      show m + 2 + 1 = m + 3 by omega, show m + 1 + 1 = m + 2 by omega]
    rw [e]
    have h0 : ¬ (5 + m = 1) := by omega
    have h1 : ¬ (5 + m = 2) := by omega
    have h3 : ¬ (5 + m = 3) := by omega
    have h4 : ¬ (5 + m = 4) := by omega
    have h5 : ¬ (5 + m = 0) := by omega
    simp [h0, h1, h3, h4, h5]
    ring
  · interval_cases n <;> simp [a, Finset.sum_range_succ, Nat.fib_add_two, lucas] <;> norm_num
