import FormalConjectures.ErdosProblems.«893»
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.Algebra.Field.ZMod

/-! Cyclotomic factors with odd indices and a lower bound on the divisor count. -/

open Finset Polynomial
open scoped ArithmeticFunction.sigma

namespace OMA.Erdos893Unbounded

private theorem odd_order_not_three {d : ℕ} (hd : Odd d) :
    (2 : ZMod 3) ^ d ≠ 1 := by
  rw [show (2 : ZMod 3) = -1 by decide, hd.neg_pow, one_pow]
  decide

private theorem odd_order_not_five {d : ℕ} (hd : Odd d) :
    (2 : ZMod 5) ^ d ≠ 1 := by
  intro h
  have hs : ((2 : ZMod 5) ^ 2) ^ d = 1 := by rw [← pow_mul, mul_comm, pow_mul, h, one_pow]
  rw [show (2 : ZMod 5) ^ 2 = -1 by decide, hd.neg_pow, one_pow] at hs
  exact (by decide : (-1 : ZMod 5) ≠ 1) hs

private theorem primitive_prime (i j : ℕ) (hi : 0 < i) :
    ∃ p : ℕ, p.Prime ∧ IsPrimitiveRoot (2 : ZMod p) (3 ^ i * 5 ^ j) := by
  let d := 3 ^ i * 5 ^ j
  have hd : 1 < d := by
    exact one_lt_mul_of_lt_of_le (one_lt_pow₀ (by decide : 1 < (3 : ℕ)) hi.ne')
      (Nat.succ_le_of_lt (by positivity : 0 < (5 : ℕ) ^ j))
  have hdodd : Odd d := Odd.mul (by decide : Odd (3 : ℕ)).pow (by decide : Odd (5 : ℕ)).pow
  let z := (cyclotomic d ℤ).eval 2
  have hz : 1 < z.natAbs := sub_one_lt_natAbs_cyclotomic_eval (q := 2) hd (by decide)
  obtain ⟨p, hp, hdiv⟩ := Nat.exists_prime_and_dvd hz.ne'
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  have hzero : (z : ZMod p) = 0 :=
    (CharP.intCast_eq_zero_iff (ZMod p) p z).mpr
      (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hdiv))
  have hroot : IsRoot (cyclotomic d (ZMod p)) (2 : ZMod p) := by
    change (cyclotomic d (ZMod p)).eval 2 = 0
    rw [← map_cyclotomic_int]
    have he := eval_intCast_map (Int.castRingHom (ZMod p)) (cyclotomic d ℤ) 2
    simpa only [Int.cast_ofNat] using he.trans hzero
  have hpow : (2 : ZMod p) ^ d = 1 := by
    have he : (X ^ d - 1 : (ZMod p)[X]).eval 2 = 0 := by
      rw [← prod_cyclotomic_eq_X_pow_sub_one (show 0 < d by omega),
        ← Nat.cons_self_properDivisors (show d ≠ 0 by omega), Finset.prod_cons, eval_mul, hroot.eq_zero, zero_mul]
    simpa only [eval_sub, eval_pow, eval_X, eval_one, sub_eq_zero] using he
  have hnd : ¬ p ∣ d := by
    intro h
    rcases hp.dvd_mul.mp h with h | h
    · have e : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (hp.dvd_of_dvd_pow h)
      subst p
      exact odd_order_not_three hdodd hpow
    · have e : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (hp.dvd_of_dvd_pow h)
      subst p
      exact odd_order_not_five hdodd hpow
  let _ : NeZero (d : ZMod p) := ⟨fun h => hnd ((ZMod.natCast_eq_zero_iff d p).mp h)⟩
  exact ⟨p, hp, isRoot_cyclotomic_iff.mp hroot⟩

private theorem exponents_unique (i j i' j' : ℕ) (h : 3 ^ i * 5 ^ j = 3 ^ i' * 5 ^ j') :
    i = i' ∧ j = j' := by
  have hfac (i j : ℕ) : (3 ^ i * 5 ^ j).factorization =
      Finsupp.single 3 i + Finsupp.single 5 j := by
    rw [Nat.factorization_mul (by positivity) (by positivity),
      Nat.Prime.factorization_pow (by decide : Nat.Prime 3),
      Nat.Prime.factorization_pow (by decide : Nat.Prime 5)]
  have heq := congrArg Nat.factorization h
  rw [hfac, hfac] at heq
  exact ⟨by simpa using DFunLike.congr_fun heq 3,
    by simpa using DFunLike.congr_fun heq 5⟩

private theorem many_factors (k : ℕ) : k * k ≤ ((2 ^ (15 ^ k) - 1 : ℕ).primeFactors).card := by
  classical
  have hex (w : Fin k × Fin k) := primitive_prime (w.1.val + 1) (w.2.val + 1) (by omega)
  choose p hp hroot using hex
  have hmem (w : Fin k × Fin k) : p w ∈ (2 ^ (15 ^ k) - 1 : ℕ).primeFactors := by
    have hdvd : 3 ^ (w.1.val + 1) * 5 ^ (w.2.val + 1) ∣ 15 ^ k := by
      rw [show (15 : ℕ) = 3 * 5 by decide, mul_pow]
      exact mul_dvd_mul (Nat.pow_dvd_pow _ w.1.isLt) (Nat.pow_dvd_pow _ w.2.isLt)
    have hpw : (2 : ZMod (p w)) ^ (15 ^ k : ℕ) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp ((hroot w).eq_orderOf ▸ hdvd)
    have hpow : 1 < (2 : ℕ) ^ (15 ^ k : ℕ) := one_lt_pow₀ (by decide) (by positivity)
    refine Nat.mem_primeFactors.mpr ⟨hp w, ?_, by omega⟩
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [Nat.cast_sub hpow.le, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, hpw, sub_self]
  let fn (w : Fin k × Fin k) : ↥(2 ^ (15 ^ k) - 1 : ℕ).primeFactors := ⟨p w, hmem w⟩
  have hinj : Function.Injective fn := by
    intro w w' hh
    have hprime : p w = p w' := congrArg Subtype.val hh
    have ho : orderOf (2 : ZMod (p w)) = orderOf (2 : ZMod (p w')) := by rw [hprime]
    have he := exponents_unique _ _ _ _ ((hroot w).eq_orderOf.trans (ho.trans (hroot w').eq_orderOf.symm))
    exact Prod.ext (Fin.ext (by omega : w.1.val = w'.1.val)) (Fin.ext (by omega : w.2.val = w'.2.val))
  simpa using Fintype.card_le_of_injective fn hinj

private theorem lower (k : ℕ) : 2 ^ (k * k) ≤ Erdos893.f (15 ^ k) := by
  let M : ℕ := 2 ^ (15 ^ k) - 1
  have hM : M ≠ 0 := by
    have : 1 < (2 : ℕ) ^ (15 ^ k : ℕ) := one_lt_pow₀ (by decide) (by positivity)
    dsimp [M]
    omega
  have hdiv : 2 ^ (k * k) ≤ σ 0 M := calc
    2 ^ (k * k) ≤ 2 ^ M.primeFactors.card := Nat.pow_le_pow_right (by decide) (many_factors k)
    _ = ∏ _ ∈ M.primeFactors, 2 := by simp
    _ ≤ σ 0 M := by
      rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hM]
      exact prod_le_prod' fun p hp => by
        have hp' := Nat.mem_primeFactors.mp hp
        have hx := hp'.1.factorization_pos_of_dvd hM hp'.2.1
        omega
  exact hdiv.trans (single_le_sum (f := fun m : ℕ => σ 0 (2 ^ m - 1))
    (fun _ _ => Nat.zero_le _) (mem_Icc.mpr ⟨Nat.succ_le_of_lt (by positivity : 0 < (15 : ℕ) ^ k), le_rfl⟩))

private theorem f_mono : Monotone Erdos893.f := by
  intro a b hab
  exact sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hab) (fun _ _ _ => Nat.zero_le _)

end OMA.Erdos893Unbounded

open OMA.Erdos893Unbounded in
theorem OMA.solution : type_of% @Erdos893.erdos_893.variants.unbounded := by
  rintro ⟨C, hC⟩
  have hC' (n : ℕ) : (Erdos893.f (2 * n) : ℝ) / Erdos893.f n ≤ C := hC ⟨n, rfl⟩
  have hf1 : Erdos893.f 1 = 1 := by
    simp [Erdos893.f, ArithmeticFunction.sigma_zero_apply]
  have hfpos (n : ℕ) (hn : 1 ≤ n) : 0 < (Erdos893.f n : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt (hf1 ▸ f_mono hn : 1 ≤ Erdos893.f n))
  have hg (i : ℕ) : (Erdos893.f (2 ^ i) : ℝ) ≤ C ^ i := by
    induction i with
    | zero => simp [hf1]
    | succ i ih =>
      rw [pow_succ', pow_succ' C]
      exact ((div_le_iff₀ (hfpos _ (Nat.succ_le_of_lt (by positivity : 0 < (2 : ℕ) ^ i)))).mp (hC' (2 ^ i))).trans
        (mul_le_mul_of_nonneg_left ih (by
          have h := hC' 1
          rw [hf1, Nat.cast_one, div_one] at h
          exact (Nat.cast_nonneg _).trans h))
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (max 1 (C ^ 4)) (by norm_num : (1 : ℝ) < 2)
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have hc4 : C ^ 4 < (2 : ℝ) ^ k := (le_max_right _ _).trans_lt hk
  have hs := pow_lt_pow_left₀ hc4 (by positivity) hk0
  rw [← pow_mul, ← pow_mul] at hs
  have hle : (15 : ℕ) ^ k ≤ 2 ^ (4 * k) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (by decide) _
  have hf : (Erdos893.f (15 ^ k) : ℝ) ≤ Erdos893.f (2 ^ (4 * k)) := by
    exact_mod_cast f_mono hle
  exact (not_lt_of_ge (le_trans (by exact_mod_cast lower k) (hf.trans (hg (4 * k))))) hs