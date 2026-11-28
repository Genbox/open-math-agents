import OMAStatements.S_oeis_a273337
import Mathlib

namespace OMA.S_oeis_a273337

open Finset PowerSeries

private def outside (t : ℕ) (x y : ℤ) : Prop :=
  x < -(t : ℤ) ∨ (t : ℤ) < x ∨ y < -(t : ℤ) ∨ (t : ℤ) < y

private def uniform : ℕ → Bool
  | 0 => false
  | _ + 1 => true

private def stableValue (x y : ℤ) : Bool := decide (x ≠ 0 ∨ y ≠ 0)

private theorem outside_uniform (t : ℕ) (x y : ℤ) (h : outside t x y) :
    state t (x, y) = uniform t := by
  induction t generalizing x y with
  | zero =>
    have hp : (x, y) ≠ (0, 0) := by
      intro he
      injection he with hx hy
      simp [outside, hx, hy] at h
    simp [state, uniform, hp]
  | succ t ih =>
    have h0 : outside t x y := by unfold outside at *; push_cast at h; omega
    have h1 : outside t (x + 1) y := by unfold outside at *; push_cast at h; omega
    have h2 : outside t (x - 1) y := by unfold outside at *; push_cast at h; omega
    have h3 : outside t x (y + 1) := by unfold outside at *; push_cast at h; omega
    have h4 : outside t x (y - 1) := by unfold outside at *; push_cast at h; omega
    simp only [state, nbrs, List.countP_cons, List.countP_nil, ih x y h0,
      ih (x + 1) y h1, ih (x - 1) y h2, ih x (y + 1) h3, ih x (y - 1) h4]
    cases t <;> simp [uniform, rule] <;> decide

private theorem first_stable (x y : ℤ) : state 3 (x, y) = stableValue x y := by
  by_cases h : outside 3 x y
  · have hz : x ≠ 0 ∨ y ≠ 0 := by unfold outside at h; omega
    rw [outside_uniform 3 x y h]
    simp [uniform, stableValue, hz]
  · unfold outside at h
    have hx0 : -3 ≤ x := by omega
    have hx1 : x ≤ 3 := by omega
    have hy0 : -3 ≤ y := by omega
    have hy1 : y ≤ 3 := by omega
    interval_cases x <;> interval_cases y <;> decide

private theorem stable_step (x y : ℤ) :
    rule (stableValue x y) ((nbrs (x, y)).countP (fun p => stableValue p.1 p.2)) =
      stableValue x y := by
  by_cases h : outside 1 x y
  · have h0 : x ≠ 0 ∨ y ≠ 0 := by unfold outside at h; omega
    have h1 : x + 1 ≠ 0 ∨ y ≠ 0 := by unfold outside at h; omega
    have h2 : x - 1 ≠ 0 ∨ y ≠ 0 := by unfold outside at h; omega
    have h3 : x ≠ 0 ∨ y + 1 ≠ 0 := by unfold outside at h; omega
    have h4 : x ≠ 0 ∨ y - 1 ≠ 0 := by unfold outside at h; omega
    simp [stableValue, nbrs, h0, h1, h2, h3, h4] <;> decide
  · unfold outside at h
    have hx0 : -1 ≤ x := by omega
    have hx1 : x ≤ 1 := by omega
    have hy0 : -1 ≤ y := by omega
    have hy1 : y ≤ 1 := by omega
    interval_cases x <;> interval_cases y <;> decide

private theorem stable_state (n : ℕ) (hn : 3 ≤ n) (x y : ℤ) :
    state n (x, y) = stableValue x y := by
  induction n, hn using Nat.le_induction generalizing x y with
  | base => exact first_stable x y
  | succ n hn ih =>
    simp only [state, nbrs, List.countP_cons, List.countP_nil, ih]
    simpa only [nbrs, List.countP_cons, List.countP_nil] using stable_step x y

private def liveCount (n : ℕ) : ℕ :=
  ∑ x ∈ range (2 * n + 1), ∑ y ∈ range (2 * n + 1),
    if state n ((x : ℤ) - n, (y : ℤ) - n) then 1 else 0

private theorem liveCount_square (n : ℕ) (hn : 3 ≤ n) :
    liveCount n + 1 = (2 * n + 1) ^ 2 := by
  let S := range (2 * n + 1)
  have hmem : n ∈ S := mem_range.mpr (by omega)
  have singletonSum : (∑ x ∈ S, ∑ y ∈ S, if x = n then if y = n then (1 : ℕ) else 0 else 0) = 1 := by
    rw [sum_eq_single n]
    · simp [hmem]
    · intro x _ hx
      simp [hx]
    · exact fun h => (h hmem).elim
  calc
    liveCount n + 1 =
        ∑ x ∈ S, ∑ y ∈ S,
          ((if state n ((x : ℤ) - n, (y : ℤ) - n) then (1 : ℕ) else 0) +
            (if x = n then if y = n then (1 : ℕ) else 0 else 0)) := by
      simp only [sum_add_distrib, singletonSum, liveCount, S]
    _ = ∑ x ∈ S, ∑ _ ∈ S, (1 : ℕ) := by
      refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
      rw [stable_state n hn]
      by_cases hx : x = n <;> by_cases hy : y = n <;>
        simp [stableValue, Int.sub_eq_zero, hx, hy]
    _ = (2 * n + 1) ^ 2 := by simp [S, pow_two]

private theorem liveCount_q (n : ℕ) (hn : 3 ≤ n) :
    (liveCount n : ℚ) = 4 * n * (1 + n) := by
  have h : (liveCount n : ℚ) + 1 = (2 * (n : ℚ) + 1) ^ 2 := by
    exact_mod_cast liveCount_square n hn
  linear_combination h

private theorem early_counts : liveCount 0 = 1 ∧ liveCount 1 = 4 ∧ liveCount 2 = 17 := by
  decide

private theorem closed (n : ℕ) (hn : 3 ≤ n) :
    (a n : ℚ) = 8 * (1 + n) := by
  change ((↑((liveCount (n + 1) : ℤ) - (liveCount n : ℤ)) : ℚ)) = _
  push_cast
  rw [liveCount_q (n + 1) (by omega), liveCount_q n hn]
  push_cast
  ring

private theorem recurrence (n : ℕ) (hn : 5 ≤ n) :
    (a n : ℚ) - 2 * a (n - 1) + a (n - 2) = 0 := by
  have hi1 : 3 ≤ n - 1 := by omega
  have hi2 : 3 ≤ n - 2 := by omega
  rw [closed n (by omega), closed (n - 1) hi1, closed (n - 2) hi2]
  push_cast [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n)]
  ring

private theorem initial_values : (a 0 : ℚ) = 3 ∧ (a 1 : ℚ) = 13 ∧ (a 2 : ℚ) = 31 := by
  have h3 : (liveCount 3 : ℚ) = 48 := by norm_num [liveCount_q 3 (by decide)]
  rcases early_counts with ⟨h0, h1, h2⟩
  change ((↑((liveCount 1 : ℤ) - (liveCount 0 : ℤ)) : ℚ)) = 3 ∧
    ((↑((liveCount 2 : ℤ) - (liveCount 1 : ℤ)) : ℚ)) = 13 ∧
    ((↑((liveCount 3 : ℤ) - (liveCount 2 : ℤ)) : ℚ)) = 31
  push_cast
  norm_num [h0,h1,h2,h3]

set_option maxHeartbeats 1500000 in
private theorem generating_identity :
    A = (3 + 7 * X + 8 * X ^ 2 - 17 * X ^ 3 + 7 * X ^ 4) * ((1 - X) ^ 2)⁻¹ := by
  have hd : ((1 - X) ^ 2 : ℚ⟦X⟧) = 1 - C 2 * X ^ 1 + X ^ 2 := by
    simp only [map_one, map_ofNat, pow_one]
    ring
  have hp : (3 + 7 * X + 8 * X ^ 2 - 17 * X ^ 3 + 7 * X ^ 4 : ℚ⟦X⟧) = C 3 + C 7 * X ^ 1 + C 8 * X ^ 2 - C 17 * X ^ 3 + C 7 * X ^ 4 := by
    simp only [map_one, map_ofNat, pow_one, one_mul]
  have hmul : A * ((1 - X) ^ 2) = (3 + 7 * X + 8 * X ^ 2 - 17 * X ^ 3 + 7 * X ^ 4) := by
    unfold A
    rw [mul_comm, hd, hp]
    ext n
    simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub, coeff_C_mul,
      coeff_X_pow_mul', coeff_mk, coeff_X_pow, coeff_one, coeff_C]
    by_cases hn : 5 ≤ n
    · have h1 : 1 ≤ n := by omega
      have h2 : 2 ≤ n := by omega
      have h3 : 3 ≤ n := by omega
      have h0' : n ≠ 0 := by omega
      have h1' : n ≠ 1 := by omega
      have h2' : n ≠ 2 := by omega
      have h3' : n ≠ 3 := by omega
      have h4' : n ≠ 4 := by omega
      simpa only [if_pos h1, if_pos h2, if_neg h0', if_neg h1',
        if_neg h2', if_neg h3', if_neg h4', mul_zero, add_zero, sub_zero, zero_add]
        using recurrence n hn
    · rcases initial_values with ⟨a0,a1,a2⟩
      have a3 : (a 3 : ℚ) = 32 := (closed 3 (by decide)).trans (by norm_num)
      have a4 : (a 4 : ℚ) = 40 := (closed 4 (by decide)).trans (by norm_num)
      interval_cases n <;> norm_num [a0, a1, a2, a3, a4]
  have hi := PowerSeries.mul_inv_cancel ((1 - X) ^ 2 : ℚ⟦X⟧) (by simp)
  calc
    A = (A * (1 - X) ^ 2) * ((1 - X) ^ 2)⁻¹ := by rw [mul_assoc, hi, mul_one]
    _ = _ := by rw [hmul]

end OMA.S_oeis_a273337

open OMA.S_oeis_a273337 in
theorem OMA.solution : type_of% @OMA.S_oeis_a273337.main := by
  refine ⟨fun n hn => closed n (by omega), ?_, generating_identity⟩
  intro n hn
  have h : (a n : ℚ) = 2 * a (n - 1) - a (n - 2) := by
    linarith only [recurrence n (by omega)]
  exact_mod_cast h