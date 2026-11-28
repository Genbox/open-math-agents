import OMAStatements.S_oeis_a200216
import Mathlib

namespace OMA.S_oeis_a200216

lemma x_rec (k : ℕ) : (pw (k + 2)).1 = 1364 * (pw (k + 1)).1 + (pw k).1 := by
  simp only [pw]
  ring

lemma xq4 (k : ℕ) : (((pw (k + 4)).1 : ℤ) : ℚ) = 1860498 * (((pw (k + 2)).1 : ℤ) : ℚ) - ((pw k).1 : ℚ) := by
  have h1 := x_rec (k + 2)
  have h2 := x_rec (k + 1)
  have h3 := x_rec k
  have : (pw (k + 4)).1 = 1860498 * (pw (k + 2)).1 - (pw k).1 := by
    simp only [show k + 2 + 2 = k + 4 from rfl, show k + 2 + 1 = k + 3 from rfl, show k + 1 + 2 = k + 3 from rfl] at *
    linarith
  exact_mod_cast this

end OMA.S_oeis_a200216

theorem OMA.solution : type_of% @OMA.S_oeis_a200216.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have e1 : m + 6 - 1 = m + 5 := by omega
  have e2 : m + 6 - 2 = m + 4 := by omega
  have e3 : m + 6 - 3 = m + 3 := by omega
  have e4 : m + 6 - 4 = m + 2 := by omega
  have e5 : m + 6 - 5 = m + 1 := by omega
  rw [e1, e2, e3, e4, e5]
  have i1 : 2 * (m + 6) - 1 = 2 * m + 11 := by omega
  have i2 : 2 * (m + 5) - 1 = 2 * m + 9 := by omega
  have i3 : 2 * (m + 4) - 1 = 2 * m + 7 := by omega
  have i4 : 2 * (m + 3) - 1 = 2 * m + 5 := by omega
  have i5 : 2 * (m + 2) - 1 = 2 * m + 3 := by omega
  have i6 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  simp only [OMA.S_oeis_a200216.a, OMA.S_oeis_a200216.t, i1, i2, i3, i4, i5, i6]
  have h5 : (((OMA.S_oeis_a200216.pw (2*m+5)).1 : ℤ) : ℚ) = 1860498 * (((OMA.S_oeis_a200216.pw (2*m+3)).1 : ℤ) : ℚ) - ((OMA.S_oeis_a200216.pw (2*m+1)).1 : ℚ) := by
    simpa [add_assoc] using OMA.S_oeis_a200216.xq4 (2*m+1)
  have h7 : (((OMA.S_oeis_a200216.pw (2*m+7)).1 : ℤ) : ℚ) = 1860498 * (((OMA.S_oeis_a200216.pw (2*m+5)).1 : ℤ) : ℚ) - ((OMA.S_oeis_a200216.pw (2*m+3)).1 : ℚ) := by
    simpa [add_assoc] using OMA.S_oeis_a200216.xq4 (2*m+3)
  have h9 : (((OMA.S_oeis_a200216.pw (2*m+9)).1 : ℤ) : ℚ) = 1860498 * (((OMA.S_oeis_a200216.pw (2*m+7)).1 : ℤ) : ℚ) - ((OMA.S_oeis_a200216.pw (2*m+5)).1 : ℚ) := by
    simpa [add_assoc] using OMA.S_oeis_a200216.xq4 (2*m+5)
  have h11 : (((OMA.S_oeis_a200216.pw (2*m+11)).1 : ℤ) : ℚ) = 1860498 * (((OMA.S_oeis_a200216.pw (2*m+9)).1 : ℤ) : ℚ) - ((OMA.S_oeis_a200216.pw (2*m+7)).1 : ℚ) := by
    simpa [add_assoc] using OMA.S_oeis_a200216.xq4 (2*m+7)
  rw [h11, h9, h7, h5]
  rcases neg_one_pow_eq_or ℚ m with h | h <;>
  · simp only [pow_succ, h]
    ring
