import OMAStatements.S_oeis_a129995
import Mathlib

namespace OMA.S_oeis_a129995

lemma dvd24 (n : ℕ) : 24 ∣ numerator n := by
  unfold numerator
  have h : ∀ r : Fin 24, 24 ∣ (r.val + 1) * (r.val ^ 2 + 2) * (r.val ^ 3 + 3) * (r.val ^ 4 + 4) := by decide
  have h2 := h ⟨n % 24, Nat.mod_lt _ (by norm_num)⟩
  simp only at h2
  have hm : ((n % 24 + 1) * ((n % 24) ^ 2 + 2) * ((n % 24) ^ 3 + 3) * ((n % 24) ^ 4 + 4)) % 24
      = ((n + 1) * (n ^ 2 + 2) * (n ^ 3 + 3) * (n ^ 4 + 4)) % 24 := by
    simp [Nat.mul_mod, Nat.add_mod, Nat.pow_mod]
  omega

end OMA.S_oeis_a129995

theorem OMA.solution : type_of% @OMA.S_oeis_a129995.main := by
  intro n
  obtain ⟨k, hk⟩ := OMA.S_oeis_a129995.dvd24 n
  refine ⟨k, ?_⟩
  unfold OMA.S_oeis_a129995.a
  rw [hk]
  push_cast
  norm_num [Nat.factorial]
