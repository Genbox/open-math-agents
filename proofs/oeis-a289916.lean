import OMAStatements.S_oeis_a289916
import Mathlib

namespace RoundedSeriesInverse

open PowerSeries

private def rounded (n : ℕ) : ℤ := round (9 * ((n : ℚ) + 1) / 7)

private def S : ℤ⟦X⟧ := mk fun n => (-1 : ℤ) ^ n * rounded n

private noncomputable def B : ℤ⟦X⟧ := (1 + X ^ 7) * (1 + X)

private noncomputable def Q : ℤ⟦X⟧ := (1 - X) ^ 2 - X ^ 3 * (1 - X) - X ^ 5 * (2 - X)

private theorem rounded_period (n : ℕ) : rounded (n + 7) = rounded n + 9 := by
  unfold rounded
  have h : (9 : ℚ) * (((n + 7 : ℕ) : ℚ) + 1) / 7 =
      9 * ((n : ℚ) + 1) / 7 + ((9 : ℤ) : ℚ) := by push_cast; ring
  rw [h, round_add_intCast]

private theorem denominator : S * B = Q := by
  let P := S * (1 + X ^ 7)
  have hbig (k : ℕ) : coeff (k + 7) P = (-1 : ℤ) ^ (k + 7) * 9 := by
    change coeff (k + 7) (S * (1 + X ^ 7)) = _
    rw [mul_add, mul_one, map_add, coeff_mul_X_pow]
    simp only [S, coeff_mk, rounded_period]
    rw [pow_add]
    norm_num
    ring
  have hpoly : Q =
      1 - C (2 : ℤ) * X + X ^ 2 - X ^ 3 + X ^ 4 - C (2 : ℤ) * X ^ 5 + X ^ 6 := by
    simp [Q]
    ring
  have htwo (n : ℕ) : coeff n (2 : ℤ⟦X⟧) = if n = 0 then 2 else 0 := by
    rw [← map_ofNat (C (R := ℤ)) 2]
    exact coeff_C _ _
  have htwo₀ : constantCoeff (2 : ℤ⟦X⟧) = 2 := map_ofNat _ _
  rw [B, ← mul_assoc, hpoly]
  change P * (1 + X) = _
  ext n
  by_cases hn : n < 8
  · interval_cases n <;> norm_num [P, S, rounded, mul_add, coeff_mul_X_pow',
      coeff_one, coeff_X, coeff_X_pow, coeff_C_mul, htwo, htwo₀, round]
  · have hn' : 8 ≤ n := by omega
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 8 := ⟨n - 8, by omega⟩
    have h₁ : k + 8 = (k + 1) + 7 := by omega
    have h₂ : k + 8 = k + 7 + 1 := by omega
    have hp₁ : coeff (k + 8) P = (-1 : ℤ) ^ (k + 8) * 9 := by
      rw [h₁, hbig]
    have hp₂ : coeff (k + 8) (P * X) = (-1 : ℤ) ^ (k + 7) * 9 := by
      rw [h₂, coeff_succ_mul_X, hbig]
    have hq₀ : coeff (k + 8)
        (1 - C (2 : ℤ) * X + X ^ 2 - X ^ 3 + X ^ 4 - C (2 : ℤ) * X ^ 5 + X ^ 6) = 0 := by
      simp only [map_add, map_sub, coeff_one, coeff_C_mul, coeff_X, coeff_X_pow,
        if_neg (show k + 8 ≠ 0 by omega), if_neg (show k + 8 ≠ 1 by omega),
        if_neg (show k + 8 ≠ 2 by omega), if_neg (show k + 8 ≠ 3 by omega),
        if_neg (show k + 8 ≠ 4 by omega), if_neg (show k + 8 ≠ 5 by omega),
        if_neg (show k + 8 ≠ 6 by omega), mul_zero, sub_zero, add_zero]
    rw [mul_add, mul_one, map_add, hp₁, hp₂, hq₀, h₂, pow_succ]
    ring

private theorem increasing : StrictMono OMA.S_oeis_a289916.sequence := by
  let F := invOfUnit S 1
  let G := F * (1 - X)
  have hSF : S * F = 1 := by
    apply mul_invOfUnit
    norm_num [S, rounded, round, ← coeff_zero_eq_constantCoeff]
  have hQ : F * Q = B := by
    rw [← denominator]
    calc
      F * (S * B) = (S * F) * B := by ring
      _ = B := by rw [hSF, one_mul]
  have hrec : G * (1 - X) = B + G * X ^ 3 + (F + G) * X ^ 5 := by
    calc
      G * (1 - X) = F * Q + G * X ^ 3 + (F + G) * X ^ 5 := by
        dsimp [G, Q]
        ring
      _ = _ := by rw [hQ]
  have hB (n : ℕ) : 0 ≤ coeff n B := by
    have h : B = 1 + X + X ^ 7 + X ^ 8 := by simp only [B]; ring
    rw [h]
    simp only [map_add, coeff_one, coeff_X, coeff_X_pow]
    positivity
  have hF₀ : coeff 0 F = 1 := by
    rw [coeff_zero_eq_constantCoeff]
    exact constantCoeff_invOfUnit _ _
  have hG₀ : coeff 0 G = 1 := by
    change coeff 0 (F * (1 - X)) = 1
    rw [mul_sub, mul_one, map_sub, coeff_zero_mul_X, hF₀, sub_zero]
  have hG (n : ℕ) : coeff (n + 1) G = coeff (n + 1) F - coeff n F := by
    change coeff (n + 1) (F * (1 - X)) = _
    simp only [mul_sub, mul_one, map_sub, coeff_succ_mul_X]
  have hpos (n : ℕ) : 0 < coeff n G ∧ 0 < coeff n F := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => simp [hG₀, hF₀]
      | succ n =>
        have hn := ih n (Nat.lt_succ_self n)
        have h₃ : 0 ≤ coeff (n + 1) (G * X ^ 3) := by
          rw [coeff_mul_X_pow']
          split
          · exact (ih _ (by omega)).1.le
          · exact le_rfl
        have h₅ : 0 ≤ coeff (n + 1) ((F + G) * X ^ 5) := by
          rw [coeff_mul_X_pow']
          split
          · rw [map_add]
            have hp := ih (n + 1 - 5) (by omega)
            exact add_nonneg hp.2.le hp.1.le
          · exact le_rfl
        have hstep := congrArg (coeff (n + 1)) hrec
        simp only [mul_sub, mul_one, map_sub, coeff_succ_mul_X, map_add] at hstep
        have hb := hB (n + 1)
        have hp : 0 < coeff (n + 1) G := by linarith [hn.1]
        exact ⟨hp, by linarith [hn.2, hG n]⟩
  apply strictMono_nat_of_lt_succ
  intro n
  change coeff n F < coeff (n + 1) F
  linarith [(hpos (n + 1)).1, hG n]

end RoundedSeriesInverse

theorem OMA.solution : type_of% @OMA.S_oeis_a289916.main := RoundedSeriesInverse.increasing