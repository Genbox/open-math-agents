import OMAStatements.S_oeis_a224832
import Mathlib

namespace OMA.S_oeis_a224832

open ArithmeticFunction

def M : ℕ := 154345556085770649600

lemma sig_prime (p : ℕ) (hp : p.Prime) : sigma 1 p = p + 1 := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.Prime.sum_divisors hp]

lemma sigmaM : sigma 1 M = 6 * M := by
  have hm := ArithmeticFunction.isMultiplicative_sigma (k := 1)
  have e : M = 2 ^ 15 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19 * 31 * 43 * 257 := by
    norm_num [M]
  rw [e]
  rw [hm.map_mul_of_coprime (by norm_num), hm.map_mul_of_coprime (by norm_num),
    hm.map_mul_of_coprime (by norm_num), hm.map_mul_of_coprime (by norm_num),
    hm.map_mul_of_coprime (by norm_num), hm.map_mul_of_coprime (by norm_num),
    hm.map_mul_of_coprime (by norm_num), hm.map_mul_of_coprime (by norm_num),
    hm.map_mul_of_coprime (by norm_num), hm.map_mul_of_coprime (by norm_num)]
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num),
    ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num),
    ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num),
    ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num)]
  rw [sig_prime 11 (by norm_num), sig_prime 13 (by norm_num), sig_prime 17 (by norm_num),
    sig_prime 19 (by norm_num), sig_prime 31 (by norm_num), sig_prime 43 (by norm_num),
    sig_prime 257 (by norm_num)]
  norm_num [Finset.sum_range_succ, M]

lemma recip_two_mul (m : ℕ) (hm : 0 < m) :
    recipEven (2 * m) = (sigma 1 m : ℚ) / (2 * m) := by
  have hf : (2 * m).divisors.filter Even = m.divisors.image (fun e => 2 * e) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
    constructor
    · rintro ⟨⟨hd, _⟩, he⟩
      obtain ⟨e, rfl⟩ := he
      refine ⟨e, ⟨?_, hm.ne'⟩, by ring⟩
      have : 2 * e ∣ 2 * m := by simpa [two_mul] using hd
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    · rintro ⟨e, ⟨he, _⟩, rfl⟩
      exact ⟨⟨Nat.mul_dvd_mul_left 2 he, by omega⟩, even_two_mul e⟩
  unfold recipEven
  rw [hf, Finset.sum_image (fun a _ b _ h => by omega)]
  have h1 : ∑ e ∈ m.divisors, (1 : ℚ) / ((2 * e : ℕ) : ℚ) = (1 / 2) * ∑ e ∈ m.divisors, (1 : ℚ) / e := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e he => ?_)
    push_cast
    rw [one_div_mul_one_div_rev]
    ring
  have h2 : ∑ e ∈ m.divisors, (1 : ℚ) / e = (sigma 1 m : ℚ) / m := by
    rw [ArithmeticFunction.sigma_one_apply]
    push_cast
    rw [Finset.sum_div, ← Nat.sum_div_divisors m (fun d => (1 : ℚ) / d)]
    refine Finset.sum_congr rfl (fun e he => ?_)
    have hdv : e ∣ m := Nat.dvd_of_mem_divisors he
    have hq : ((m / e : ℕ) : ℚ) = (m : ℚ) / e := Nat.cast_div hdv (by
      have := Nat.pos_of_mem_divisors he; positivity)
    rw [one_div, hq, inv_div]
  rw [h1, h2]
  field_simp

theorem sol_aux : type_of% @OMA.S_oeis_a224832.main := by
  intro h
  have hM : 0 < M := by norm_num [M]
  have hin : InSeq (2 * M) := by
    refine ⟨by omega, even_two_mul M, 3, ?_⟩
    rw [recip_two_mul M hM, sigmaM]
    have : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
    push_cast
    field_simp
    ring
  have hnot : ¬ TwiceEvenPerfect (2 * M) := by
    rintro ⟨P, _, hP, hk⟩
    have hPM : P = M := by omega
    subst hPM
    have h2 := (Nat.perfect_iff_sum_divisors_eq_two_mul hM).1 hP
    have h3 := sigmaM
    rw [ArithmeticFunction.sigma_one_apply] at h3
    omega
  have := h (2 * M) hin hnot
  rw [recip_two_mul M hM, sigmaM] at this
  have : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  push_cast at *
  field_simp at *
  linarith

end OMA.S_oeis_a224832

theorem OMA.solution : type_of% @OMA.S_oeis_a224832.main := OMA.S_oeis_a224832.sol_aux
