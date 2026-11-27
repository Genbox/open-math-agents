import FormalConjectures.ErdosProblems.«940»
import Mathlib.Analysis.PSeries
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-! An elementary finite congruence sieve with a square–cube tail bound. -/

open Finset Filter
open scoped Topology Pointwise Function NumberTheorySymbols

namespace PowerfulSums

theorem square_cube {n : ℕ} (hn : 0 < n) (hfull : (2 : ℕ).Full n) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ^ 2 * b ^ 3 = n := by
  obtain ⟨b, c, hb, hc, heq, hsq⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hb0 : b ≠ 0 := by positivity
  have hc0 : c ≠ 0 := by positivity
  have hbcdvd : b ∣ c := by
    apply (Nat.factorization_le_iff_dvd hb0 hc0).mp
    intro p
    by_cases hp : p.Prime
    · by_cases hpdvd : p ∣ b
      · have hbp := Nat.factorization_eq_one_of_squarefree hsq hp hpdvd
        have hpn : p ∣ n := by rw [← heq]; exact dvd_mul_of_dvd_right hpdvd _
        have hp2 : p ^ 2 ∣ n := hfull p (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn.ne'⟩)
        have hp2 := (hp.pow_dvd_iff_le_factorization hn.ne').mp hp2
        rw [← heq, Nat.factorization_mul (pow_ne_zero _ hc0) hb0,
          Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hbp] at hp2
        omega
      · rw [Nat.factorization_eq_zero_of_not_dvd hpdvd]
        exact Nat.zero_le _
    · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
      exact Nat.zero_le _
  obtain ⟨a, ha⟩ := hbcdvd
  have ha0 : 0 < a := by
    by_contra! h
    have : a = 0 := by omega
    simp [this] at ha
    contradiction
  refine ⟨a, b, ha0, hb, ?_⟩
  rw [← heq, ha]
  ring

theorem nonresidue_excludes_single_divisibility {A B p x y : ℕ} (hp : p.Prime)
    (hχ : jacobiSym (-((A : ℤ) * B)) p = -1)
    (h : p ∣ A * x ^ 2 + B * y ^ 2) :
    p ^ 2 ∣ A * x ^ 2 + B * y ^ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  have hnon : ¬ IsSquare (-((A : ZMod p) * B)) := by
    have h' := ZMod.nonsquare_of_jacobiSym_eq_neg_one hχ
    simpa only [Int.cast_neg, Int.cast_mul, Int.cast_natCast] using h'
  have hA : (A : ZMod p) ≠ 0 := by
    intro hz
    exact hnon (by rw [hz, zero_mul, neg_zero]; exact ⟨0, by simp⟩)
  have hs : (A : ZMod p) * (x : ZMod p) ^ 2 + (B : ZMod p) * (y : ZMod p) ^ 2 = 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).mpr h
  have hy : (y : ZMod p) = 0 := by
    by_contra hy
    apply hnon
    refine ⟨(A : ZMod p) * (x : ZMod p) / (y : ZMod p), ?_⟩
    rw [← pow_two]
    field_simp
    linear_combination -hs
  rw [hy, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hs
  have hx : (x : ZMod p) = 0 := by
    by_contra hx
    exact (pow_ne_zero _ hx) ((mul_eq_zero.mp hs).resolve_left hA)
  have hdX : p ∣ x := (ZMod.natCast_eq_zero_iff _ _).mp hx
  have hdY : p ∣ y := (ZMod.natCast_eq_zero_iff _ _).mp hy
  exact dvd_add (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hdX 2) A)
    (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hdY 2) B)

end PowerfulSums

namespace PowerfulSums

private theorem jacobi_last_residue {d : ℕ} (hd : 0 < d) :
    J(-(d : ℤ) | 4 * d - 1) = -1 := by
  let q := 4 * d - 1
  have hq : 0 < q := by dsimp [q]; omega
  have hqm : q % 4 = 3 := by dsimp [q]; omega
  have ho : Odd q := Nat.odd_iff.mpr (by omega)
  have htwo : (2 : ℤ).gcd (q : ℤ) = 1 := by
    simpa [Int.gcd_eq_natAbs, Nat.Coprime] using ho.coprime_two_left
  have hfour : J(4 | q) = 1 := by
    convert jacobiSym.sq_one' htwo using 2
    norm_num
  have hn : J(-1 | q) = -1 := by
    rw [jacobiSym.at_neg_one ho, ZMod.χ₄_nat_three_mod_four hqm]
  have hm : J((-(d : ℤ)) * 4 | q) = J(-1 | q) := by
    apply jacobiSym.mod_left'
    have heq : (-(d : ℤ)) * 4 = -1 - (q : ℤ) := by
      dsimp [q]
      push_cast [Nat.cast_sub (show 1 ≤ 4 * d by omega)]
      ring
    rw [heq, Int.sub_emod_right]
  rw [jacobiSym.mul_left, hfour, mul_one, hn] at hm
  exact hm

private theorem jacobi_negative_prime {d : ℤ} {m : ℕ}
    (h : J(d | m) = -1) : ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ J(d | p) = -1 := by
  by_contra! hnone
  have hpos : 0 ≤ J(d | m) := by
    unfold jacobiSym
    apply List.prod_nonneg
    intro z hz
    obtain ⟨p, hp, rfl⟩ := List.mem_pmap.mp hz
    have hp' := Nat.prime_of_mem_primeFactorsList hp
    let : Fact p.Prime := ⟨hp'⟩
    rw [jacobiSym.legendreSym.to_jacobiSym]
    rcases jacobiSym.trichotomy d p with h0 | h1 | hn
    · simp [h0]
    · simp [h1]
    · exact False.elim (hnone p hp' (Nat.dvd_of_mem_primeFactorsList hp) hn)
  omega

private theorem residue_count (M N p : ℕ) (hp : p.Prime) (hM : 2 ≤ M) :
    ((Icc 1 N).filter (fun j => p ∣ M * j - 1)).card ≤ N / p + 1 := by
  let : Fact p.Prime := ⟨hp⟩
  rw [← card_range (N / p + 1)]
  apply card_le_card_of_injOn (fun j : ℕ => j / p) (t := range (N / p + 1))
  · intro j hj
    have h := (mem_Icc.mp (mem_filter.mp hj).1).2
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right h))
  · intro i hi j hj hij
    change i / p = j / p at hij
    obtain ⟨hiR, hiD⟩ := mem_filter.mp hi
    obtain ⟨hjR, hjD⟩ := mem_filter.mp hj
    have hi0 := (mem_Icc.mp hiR).1
    have hj0 := (mem_Icc.mp hjR).1
    have h_i : (M : ZMod p) * i = 1 := by
      have he := (ZMod.natCast_eq_zero_iff _ _).mpr hiD
      push_cast [Nat.cast_sub (show 1 ≤ M * i by nlinarith)] at he
      exact sub_eq_zero.mp he
    have h_j : (M : ZMod p) * j = 1 := by
      have he := (ZMod.natCast_eq_zero_iff _ _).mpr hjD
      push_cast [Nat.cast_sub (show 1 ≤ M * j by nlinarith)] at he
      exact sub_eq_zero.mp he
    have hM0 : (M : ZMod p) ≠ 0 := by
      intro h
      simp [h] at h_i
    have hq : i % p = j % p := (ZMod.natCast_eq_natCast_iff' _ _ _).mp
      (mul_left_cancel₀ hM0 (h_i.trans h_j.symm))
    calc
      i = p * (i / p) + i % p := (Nat.div_add_mod i p).symm
      _ = p * (j / p) + j % p := by rw [hij, hq]
      _ = j := Nat.div_add_mod j p

private def negativePrime (d p : ℕ) : Prop := p.Prime ∧ J(-(d : ℤ) | p) = -1

open scoped Classical in
private noncomputable def primeWeight (d p : ℕ) : ℝ :=
  if negativePrime d p then (p : ℝ)⁻¹ else 0

private theorem weight_nonneg (d p : ℕ) : 0 ≤ primeWeight d p := by
  classical
  unfold primeWeight
  split <;> positivity

theorem not_summable_negative_primes {d : ℕ} (hd : 0 < d) :
    ¬ Summable (primeWeight d) := by
  classical
  intro hsumAll
  obtain ⟨s, hs⟩ := hsumAll.vanishing (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
  obtain ⟨K, hK⟩ := exists_nat_subset_range s
  let M := (4 * d) * K.factorial
  have hM : 2 ≤ M := by
    have hfac := Nat.factorial_pos K
    dsimp [M]
    nlinarith
  obtain ⟨t, ht⟩ := hsumAll.vanishing
    (Iio_mem_nhds (show (0 : ℝ) < 1 / (4 * M) by positivity))
  obtain ⟨N₀, hN₀⟩ := exists_nat_subset_range t
  let N := max N₀ 1
  have hN : 0 < N := by dsimp [N]; omega
  let P := (Icc (K + 1) (M * N)).filter (negativePrime d)
  have hcover : Icc 1 N ⊆ P.biUnion (fun p => (Icc 1 N).filter (fun j => p ∣ M * j - 1)) := by
    intro j hj
    obtain ⟨hj₁, hj₂⟩ := mem_Icc.mp hj
    have hMj : 1 ≤ M * j := by nlinarith
    have hMj' : 0 < M * j - 1 := by
      have hmj : M ≤ M * j := by simpa using Nat.mul_le_mul_left M hj₁
      omega
    have hmod : M * j ≡ 4 * d [MOD 4 * d] := by
      change (M * j) % (4 * d) = (4 * d) % (4 * d)
      rw [Nat.mod_self, Nat.mod_eq_zero_of_dvd]
      exact ⟨K.factorial * j, by dsimp [M]; ring⟩
    have hmod' := Nat.ModEq.sub hMj (show 1 ≤ 4 * d by omega) hmod
      (show 1 ≡ 1 [MOD 4 * d] from rfl)
    have hjodd : Odd (M * j - 1) := by
      refine Nat.odd_iff.mpr ?_
      obtain ⟨z, hz⟩ : ∃ z, M * j = 4 * z := by
        exact ⟨d * K.factorial * j, by dsimp [M]; ring⟩
      omega
    have hjχ : J(-(d : ℤ) | M * j - 1) = -1 := by
      rw [jacobiSym.mod_right _ hjodd]
      rw [show (-(d : ℤ)).natAbs = d by simp]
      change (M * j - 1) % (4 * d) = (4 * d - 1) % (4 * d) at hmod'
      rw [hmod', Nat.mod_eq_of_lt (by omega : 4 * d - 1 < 4 * d)]
      exact jacobi_last_residue hd
    obtain ⟨p, hpp, hpdiv, hpχ⟩ := jacobi_negative_prime hjχ
    have hpK : K < p := by
      by_contra! hle
      have hpM : p ∣ M := dvd_mul_of_dvd_right (Nat.dvd_factorial hpp.pos hle) _
      have hpMj : p ∣ M * j := dvd_mul_of_dvd_left hpM _
      have hpone : p ∣ 1 := by
        convert Nat.dvd_sub hpMj hpdiv using 1
        omega
      exact hpp.not_dvd_one hpone
    have hpN : p ≤ M * N := (Nat.le_of_dvd hMj' hpdiv).trans
      (Nat.sub_le _ _ |>.trans (Nat.mul_le_mul_left _ hj₂))
    exact mem_biUnion.mpr ⟨p, mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hpN⟩, hpp, hpχ⟩,
      mem_filter.mpr ⟨hj, hpdiv⟩⟩
  let Q := P.filter (· ≤ N)
  let R := P.filter (fun p => ¬ p ≤ N)
  have hQ : ∑ p ∈ Q, primeWeight d p < 1 / 8 := by
    apply hs Q
    refine disjoint_left.mpr (fun p hq hps => ?_)
    have hp := (mem_Icc.mp (mem_filter.mp (mem_filter.mp hq).1).1).1
    have hsmall := mem_range.mp (hK hps)
    omega
  have hR : ∑ p ∈ R, primeWeight d p < 1 / (4 * M) := by
    apply ht R
    refine disjoint_left.mpr (fun p hq hps => ?_)
    have hp := (mem_filter.mp hq).2
    have hsmall := mem_range.mp (hN₀ hps)
    dsimp [N] at hp
    omega
  have hsum : (N : ℝ) ≤ ∑ p ∈ P, (((Icc 1 N).filter (fun j => p ∣ M * j - 1)).card : ℝ) := by
    exact_mod_cast (by
      calc
        N = (Icc 1 N).card := by simp [Nat.card_Icc]
        _ ≤ _ := (card_le_card hcover).trans (card_biUnion_le))
  have hQbound : (∑ p ∈ Q, (((Icc 1 N).filter (fun j => p ∣ M * j - 1)).card : ℝ)) ≤
      2 * N * ∑ p ∈ Q, primeWeight d p := by
    rw [mul_sum]
    refine sum_le_sum fun p hp => ?_
    obtain ⟨hpP, hpN⟩ := mem_filter.mp hp
    have hpneg := (mem_filter.mp hpP).2
    have hp' : (0 : ℝ) < p := by exact_mod_cast hpneg.1.pos
    have hrat : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := by
      rw [le_div_iff₀ hp']
      exact_mod_cast Nat.div_mul_le_self N p
    have hrat1 : (1 : ℝ) ≤ (N : ℝ) / p := by
      rw [le_div_iff₀ hp', one_mul]
      exact_mod_cast hpN
    have hbound : (((Icc 1 N).filter (fun j => p ∣ M * j - 1)).card : ℝ) ≤
        ((N / p : ℕ) : ℝ) + 1 := by exact_mod_cast residue_count M N p hpneg.1 hM
    rw [primeWeight, if_pos hpneg, ← div_eq_mul_inv, mul_div_assoc]
    linarith
  have hRbound : (∑ p ∈ R, (((Icc 1 N).filter (fun j => p ∣ M * j - 1)).card : ℝ)) ≤
      M * N * ∑ p ∈ R, primeWeight d p := by
    rw [mul_sum]
    refine sum_le_sum fun p hp => ?_
    obtain ⟨hpP, hpN⟩ := mem_filter.mp hp
    have hpneg := (mem_filter.mp hpP).2
    have hp' : (0 : ℝ) < p := by exact_mod_cast hpneg.1.pos
    have hpdiv : N / p = 0 := Nat.div_eq_of_lt (by omega)
    have hb : (((Icc 1 N).filter (fun j => p ∣ M * j - 1)).card : ℝ) ≤ 1 := by
      exact_mod_cast (by simpa [hpdiv] using residue_count M N p hpneg.1 hM)
    refine hb.trans ?_
    rw [primeWeight, if_pos hpneg, ← div_eq_mul_inv, le_div_iff₀ hp', one_mul]
    exact_mod_cast (mem_Icc.mp (mem_filter.mp hpP).1).2
  rw [← sum_filter_add_sum_filter_not P (· ≤ N)] at hsum
  have h₁ := mul_lt_mul_of_pos_left hQ (by positivity : 0 < (2 : ℝ) * N)
  have h₂ := mul_lt_mul_of_pos_left hR (by positivity : 0 < (M : ℝ) * N)
  have h₂' : (M : ℝ) * N * (1 / (4 * M)) = N / 4 := by field_simp
  rw [h₂'] at h₂
  change (N : ℝ) ≤ (∑ p ∈ Q, (((Icc 1 N).filter (fun j => p ∣ M * j - 1)).card : ℝ)) +
    ∑ p ∈ R, (((Icc 1 N).filter (fun j => p ∣ M * j - 1)).card : ℝ) at hsum
  linarith

end PowerfulSums

namespace PowerfulSums

private def allowed (p : ℕ) : Finset ℕ :=
  (range (p ^ 2)).filter (fun r => ¬ p ∣ r ∨ r = 0)

private theorem card_allowed {p : ℕ} (hp : p.Prime) : (allowed p).card = p ^ 2 - (p - 1) := by
  let f : ℕ ↪ ℕ := ⟨fun k => p * k, by
    intro i j h
    exact mul_left_cancel₀ hp.ne_zero h⟩
  let bad := (Ico 1 p).map f
  have hbad : bad ⊆ range (p ^ 2) := by
    intro r hr
    obtain ⟨k, hk, rfl⟩ := mem_map.mp hr
    have hkm := (mem_Ico.mp hk).2
    exact mem_range.mpr (by change p * k < p ^ 2; rw [sq]; exact Nat.mul_lt_mul_of_pos_left hkm hp.pos)
  have heq : allowed p = range (p ^ 2) \ bad := by
    ext r
    simp only [allowed, mem_filter, Finset.mem_sdiff]
    refine and_congr_right fun hr => ⟨?_, ?_⟩
    · rintro (h | rfl) hb
      · obtain ⟨x, hx, hxeq⟩ := mem_map.mp hb
        exact h ⟨x, hxeq.symm⟩
      · obtain ⟨x, hx, hxeq⟩ := mem_map.mp hb
        have hxx := (mem_Ico.mp hx).1
        change p * x = 0 at hxeq
        nlinarith [hp.pos]
    · intro hb
      by_cases hd : p ∣ r
      · right
        obtain ⟨x, rfl⟩ := hd
        by_contra hm
        apply hb
        have hx : 0 < x := by cases x <;> simp_all
        have hx' : x < p := by
          have h := mem_range.mp hr
          rw [sq] at h
          exact Nat.lt_of_mul_lt_mul_left h
        exact mem_map.mpr ⟨x, mem_Ico.mpr ⟨hx, hx'⟩, rfl⟩
      · exact Or.inl hd
  rw [heq, card_sdiff_of_subset hbad, card_range]
  simp [bad, Nat.card_Ico]

/-- Cardinal bounds for the allowed residues modulo the product of the prime squares. -/
theorem finite_sieve_card (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (N : ℕ) (A : Finset ℕ) (hA : A ⊆ range N)
    (hgood : ∀ x ∈ A, ∀ p ∈ P, p ∣ x → p ^ 2 ∣ x) :
    A.card ≤ (N / (∏ p : ↥P, p.val ^ 2) + 1) * ∏ p : ↥P, (p.val ^ 2 - (p.val - 1)) := by
  classical
  let square (p : ↥P) := p.val ^ 2
  let M := ∏ p : ↥P, square p
  have hS (p : ↥P) : 0 < square p := pow_pos (hP p.val p.property).pos _
  have hcoprime : Pairwise (Nat.Coprime on square) := by
    intro a b hab
    have hne : a.val ≠ b.val := fun h => hab (Subtype.ext h)
    have hcop := (Nat.coprime_primes (hP a.val a.property) (hP b.val b.property)).mpr hne
    exact (hcop.pow_left _).pow_right _
  let iso := ZMod.prodEquivPi square hcoprime
  let tag : ↥A → Fin (N / M + 1) × ((p : ↥P) → ↥(allowed p.val)) := fun a =>
    (⟨a.val / M, Nat.lt_succ_of_le (Nat.div_le_div_right (mem_range.mp (hA a.property)).le)⟩,
      fun p => ⟨a.val % square p, by
        refine mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (hS p)), ?_⟩
        by_cases hlocal : p.val ∣ a.val % square p
        · right
          have hpD : p.val ∣ square p := ⟨p.val, by simp [square, sq]⟩
          have hpa : p.val ∣ a.val := by
            rw [Nat.dvd_iff_mod_eq_zero, ← Nat.mod_mod_of_dvd a.val hpD]
            exact Nat.mod_eq_zero_of_dvd hlocal
          exact Nat.mod_eq_zero_of_dvd (hgood a.val a.property p.val p.property hpa)
        · exact Or.inl hlocal⟩)
  have htag : Function.Injective tag := by
    intro a b hab
    have hquo : a.val / M = b.val / M := congrArg (fun x => x.1.val) hab
    have hrem : a.val % M = b.val % M := by
      apply (ZMod.natCast_eq_natCast_iff' _ _ _).mp
      apply iso.injective
      funext p
      have hlocal : a.val % square p = b.val % square p :=
        congrArg (fun x => (x.2 p).val) hab
      change ZMod.prodEquivPi square hcoprime (a.val : ZMod M) p =
        ZMod.prodEquivPi square hcoprime (b.val : ZMod M) p
      simp only [ZMod.prodEquivPi_apply, map_natCast]
      exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hlocal
    apply Subtype.ext
    calc
      a.val = M * (a.val / M) + a.val % M := (Nat.div_add_mod _ _).symm
      _ = M * (b.val / M) + b.val % M := by rw [hquo, hrem]
      _ = b.val := Nat.div_add_mod _ _
  have hc := Fintype.card_le_of_injective tag htag
  change Fintype.card (↥A) ≤ Fintype.card (Fin (N / M + 1) × ((p : ↥P) → ↥(allowed p.val))) at hc
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_pi] at hc
  have hlocal (p : ↥P) : (allowed p.val).card = p.val ^ 2 - (p.val - 1) :=
    card_allowed (hP p.val p.property)
  simpa only [Fintype.card_coe, hlocal, M, square] using hc

theorem finite_sieve_ratio (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (N : ℕ) (hN : (∏ p : ↥P, p.val ^ 2) ≤ N) (A : Finset ℕ) (hA : A ⊆ range N)
    (hgood : ∀ x ∈ A, ∀ p ∈ P, p ∣ x → p ^ 2 ∣ x) :
    (A.card : ℝ) / N ≤ 2 * ∏ p ∈ P, (1 - 1 / (2 * (p : ℝ))) := by
  let M := ∏ p : ↥P, p.val ^ 2
  let K := ∏ p : ↥P, (p.val ^ 2 - (p.val - 1))
  have hM : 0 < M := prod_pos (fun p _ => pow_pos (hP _ p.property).pos _)
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hNp : (0 : ℝ) < N := by exact_mod_cast hM.trans_le hN
  have hNM : (1 : ℝ) ≤ (N : ℝ) / M := by
    rw [le_div_iff₀ hMp, one_mul]
    exact_mod_cast hN
  have hdiv : ((N / M : ℕ) : ℝ) ≤ (N : ℝ) / M := by
    rw [le_div_iff₀ hMp]
    exact_mod_cast Nat.div_mul_le_self N M
  have hprod : (K : ℝ) / M ≤ ∏ p ∈ P, (1 - 1 / (2 * (p : ℝ))) := by
    calc
      (K : ℝ) / M = ∏ p : ↥P, (((p.val ^ 2 - (p.val - 1) : ℕ) : ℝ) / (p.val : ℝ) ^ 2) := by
        dsimp [K, M]
        push_cast
        rw [prod_div_distrib]
      _ ≤ ∏ p : ↥P, (1 - 1 / (2 * (p.val : ℝ))) := by
        apply Finset.prod_le_prod
        · intro p _
          positivity
        · intro p _
          have hp : p.val.Prime := hP _ p.property
          have hcast : (2 : ℝ) ≤ (p.val : ℝ) := by exact_mod_cast hp.two_le
          have hcast' : (0 : ℝ) < (p.val : ℝ) := by linarith
          have h₁ : 1 ≤ p.val := hp.pos
          have h₂ : p.val - 1 ≤ p.val ^ 2 :=
            (Nat.sub_le ..).trans (Nat.le_self_pow (by decide) _)
          rw [Nat.cast_sub h₂, Nat.cast_sub h₁]
          push_cast
          field_simp
          nlinarith
      _ = ∏ p ∈ P, (1 - 1 / (2 * (p : ℝ))) := by
        exact prod_attach P (fun p => (1 : ℝ) - 1 / (2 * p))
  have hc : (A.card : ℝ) ≤ (((N / M : ℕ) : ℝ) + 1) * K := by
    exact_mod_cast finite_sieve_card P hP N A hA hgood
  calc
    (A.card : ℝ) / N ≤ (((N / M : ℕ) : ℝ) + 1) * K / N := by gcongr
    _ ≤ ((N : ℝ) / M + (N : ℝ) / M) * K / N := by gcongr
    _ = 2 * ((K : ℝ) / M) := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by norm_num)

end PowerfulSums

namespace PowerfulSums

private def products (B N : ℕ) : Finset ℕ :=
  (Icc B N).biUnion fun b =>
    (Icc 1 (Nat.sqrt (N / b ^ 3))).image fun a => a ^ 2 * b ^ 3

private noncomputable def cubeWeight (b : ℕ) : ℝ := ((b : ℝ) ^ (3 / 2 : ℝ))⁻¹

private theorem cubeWeight_nonneg (b : ℕ) : 0 ≤ cubeWeight b := by
  unfold cubeWeight
  positivity

private theorem cube_summable : Summable cubeWeight :=
  Real.summable_nat_rpow_inv.mpr (by norm_num)

theorem mem_products {a b B N : ℕ} (ha : 0 < a) (hb : 0 < b) (hbB : B ≤ b)
    (hab : a ^ 2 * b ^ 3 ≤ N) : a ^ 2 * b ^ 3 ∈ products B N := by
  have hbb : b ≤ N := by
    refine le_trans (Nat.le_self_pow (by decide : 3 ≠ 0) b) ?_
    exact (Nat.le_mul_of_pos_left _ (by positivity : 0 < a ^ 2)).trans hab
  refine mem_biUnion.mpr ⟨b, mem_Icc.mpr ⟨hbB, hbb⟩, mem_image.mpr ⟨a, ?_, rfl⟩⟩
  refine mem_Icc.mpr ⟨ha, Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le (by positivity)).mpr hab)⟩

private theorem root_estimate (b N : ℕ) (hb : 0 < b) :
    (Nat.sqrt (N / b ^ 3) : ℝ) ≤ Real.sqrt N * cubeWeight b := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hnat : (Nat.sqrt (N / b ^ 3)) ^ 2 * b ^ 3 ≤ N :=
    (Nat.mul_le_mul_right _ (Nat.sqrt_le' _)).trans (Nat.div_mul_le_self _ _)
  have hreal : (Nat.sqrt (N / b ^ 3) : ℝ) ^ 2 ≤ (N : ℝ) / (b : ℝ) ^ 3 := by
    rw [le_div_iff₀ (by positivity : 0 < (b : ℝ) ^ 3)]
    exact_mod_cast hnat
  have h := Real.le_sqrt_of_sq_le hreal
  rw [Real.sqrt_div (by positivity), div_eq_mul_inv] at h
  have heq : Real.sqrt ((b : ℝ) ^ 3) = (b : ℝ) ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast_mul hb'.le]
    norm_num
  simpa only [heq, cubeWeight] using h

private theorem card_products (B N : ℕ) (hB : 0 < B) :
    ((products B N).card : ℝ) ≤ Real.sqrt N * ∑ b ∈ Icc B N, cubeWeight b := by
  calc
    ((products B N).card : ℝ) ≤
        ∑ b ∈ Icc B N,
          (((Icc 1 (Nat.sqrt (N / b ^ 3))).image fun a => a ^ 2 * b ^ 3).card : ℝ) := by
      exact_mod_cast card_biUnion_le
    _ ≤ ∑ b ∈ Icc B N, (Nat.sqrt (N / b ^ 3) : ℝ) := by
      refine sum_le_sum fun b _ => ?_
      exact_mod_cast (by
        exact card_image_le.trans (by simp [Nat.card_Icc]))
    _ ≤ ∑ b ∈ Icc B N, Real.sqrt N * cubeWeight b := by
      refine sum_le_sum fun b hb => root_estimate b N (hB.trans_le (mem_Icc.mp hb).1)
    _ = _ := (mul_sum ..).symm

theorem tail_products (ε : ℝ) (hε : 0 < ε) :
    ∃ B > 1, ∀ N : ℕ, ((products B N).card : ℝ) ≤ ε * Real.sqrt N := by
  obtain ⟨s, hs⟩ := cube_summable.vanishing (Iio_mem_nhds hε)
  obtain ⟨B₀, hB₀⟩ := exists_nat_subset_range s
  let B := max B₀ 2
  have hB : 2 ≤ B := le_max_right _ _
  refine ⟨B, by omega, fun N => ?_⟩
  have hdisj : Disjoint (Icc B N) s := disjoint_left.mpr fun x hx hx' => by
    have hlo := (mem_Icc.mp hx).1
    have hhi := mem_range.mp (hB₀ hx')
    have hB' : B₀ ≤ B := le_max_left _ _
    omega
  have hsum := hs (Icc B N) hdisj
  refine (card_products B N (by omega)).trans ?_
  rw [mul_comm ε]
  exact mul_le_mul_of_nonneg_left (Set.mem_Iio.mp hsum).le (Real.sqrt_nonneg _)

theorem all_products_bound :
    ∃ C > (0 : ℝ), ∀ N ≥ 1, ((insert 0 (products 1 N)).card : ℝ) ≤ C * Real.sqrt N := by
  let T := ∑' b : ℕ, cubeWeight b
  have hT : 0 ≤ T := tsum_nonneg cubeWeight_nonneg
  refine ⟨1 + T, by positivity, fun N hN => ?_⟩
  have hsum : (∑ b ∈ Icc 1 N, cubeWeight b) ≤ T :=
    cube_summable.sum_le_tsum _ (fun b _ => cubeWeight_nonneg b)
  have hs : (1 : ℝ) ≤ Real.sqrt N := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast (show 1 ^ 2 ≤ N by simpa using hN)
  calc
    ((insert 0 (products 1 N)).card : ℝ) ≤ (products 1 N).card + 1 := by
      exact_mod_cast card_insert_le 0 (products 1 N)
    _ ≤ Real.sqrt N * T + Real.sqrt N := by
      apply add_le_add _ hs
      exact (card_products 1 N (by decide)).trans (mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _))
    _ = _ := by ring

end PowerfulSums

namespace PowerfulSums

open scoped Classical in
private theorem fixed_form_bound (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop,
    (((range N).filter (fun x => ∃ y z : ℕ, a * y ^ 2 + b * z ^ 2 = x)).card : ℝ) ≤ ε * N := by
  classical
  let d := a * b
  have hsum := (not_summable_iff_tendsto_nat_atTop_of_nonneg (weight_nonneg d)).mp
    (not_summable_negative_primes (show 0 < d by dsimp [d]; positivity))
  obtain ⟨K, hK⟩ := ((tendsto_atTop.1 hsum) (-2 * Real.log (ε / 2))).exists
  let P := (range K).filter (negativePrime d)
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime := (mem_filter.mp hp).2.1
  have hbig : -Real.log (ε / 2) ≤ ∑ p ∈ P, 1 / (2 * (p : ℝ)) := by
    have h : (∑ p ∈ range K, primeWeight d p) = ∑ p ∈ P, (p : ℝ)⁻¹ := by
      simp only [primeWeight, P, sum_filter]
    rw [h] at hK
    have hs : (∑ p ∈ P, (p : ℝ)⁻¹) / 2 = ∑ p ∈ P, 1 / (2 * (p : ℝ)) := by
      rw [sum_div]
      apply sum_congr rfl
      intro p _
      rw [one_div, mul_inv]
      ring
    rw [← hs]
    linarith
  have hsmall : 2 * ∏ p ∈ P, (1 - 1 / (2 * (p : ℝ))) ≤ ε := by
    have hle : (∏ p ∈ P, (1 - 1 / (2 * (p : ℝ)))) ≤
        Real.exp (-(∑ p ∈ P, 1 / (2 * (p : ℝ)))) := by
      rw [← sum_neg_distrib, Real.exp_sum]
      apply Finset.prod_le_prod
      · intro p hp
        apply sub_nonneg.mpr
        have hp' : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
        rw [div_le_one₀ (by linarith : (0 : ℝ) < 2 * p)]
        linarith
      · intro p _
        simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-(1 / (2 * (p : ℝ))))
    have he : 0 < ε / 2 := by positivity
    calc
      _ ≤ 2 * Real.exp (-(∑ p ∈ P, 1 / (2 * (p : ℝ)))) := by gcongr
      _ ≤ 2 * Real.exp (Real.log (ε / 2)) := by
        gcongr
        linarith
      _ = ε := by rw [Real.exp_log he]; ring
  let M := ∏ p : ↥P, p.val ^ 2
  have hM : 0 < M := prod_pos (fun p _ => pow_pos (hP _ p.property).pos _)
  filter_upwards [eventually_ge_atTop M] with N hn
  let A := (range N).filter (fun x => ∃ y z : ℕ, a * y ^ 2 + b * z ^ 2 = x)
  have hlocal (x : ℕ) (hx : x ∈ A) (p : ℕ) (hp : p ∈ P) (hpx : p ∣ x) : p ^ 2 ∣ x := by
    obtain ⟨_, y, z, rfl⟩ := mem_filter.mp hx
    have hχ := (mem_filter.mp hp).2.2
    have hχ' : jacobiSym (-((a : ℤ) * b)) p = -1 := by simpa [d] using hχ
    exact nonresidue_excludes_single_divisibility (hP p hp) hχ' hpx
  have hh := (finite_sieve_ratio P hP N hn A (filter_subset _ _) hlocal).trans hsmall
  exact (div_le_iff₀ (show (0 : ℝ) < N by exact_mod_cast hM.trans_le hn)).mp hh

private theorem two_entries {S : Multiset ℕ} (hS : S.card ≤ 2)
    (hfull : ∀ s ∈ S, (2 : ℕ).Full s) :
    ∃ u v : ℕ, (2 : ℕ).Full u ∧ (2 : ℕ).Full v ∧ u + v = S.sum := by
  have hc : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
  rcases hc with h0 | h1 | h2
  · rw [Multiset.card_eq_zero.mp h0]
    exact ⟨0, 0, Nat.Full.zero_right _, Nat.Full.zero_right _, by simp⟩
  · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp h1
    exact ⟨a, 0, hfull a (by simp), Nat.Full.zero_right _, by simp⟩
  · obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp h2
    exact ⟨a, b, hfull a (by simp), hfull b (by simp), by simp⟩

private theorem square_cube_or_zero {x : ℕ} (hfull : (2 : ℕ).Full x) :
    ∃ a b : ℕ, 0 < b ∧ a ^ 2 * b ^ 3 = x ∧ (0 < a ∨ b = 1 ∧ x = 0) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · exact ⟨0, 1, by decide, by simp, by simp⟩
  · obtain ⟨a, b, ha, hb, he⟩ := square_cube hx hfull
    exact ⟨a, b, hb, he, Or.inl ha⟩

end PowerfulSums

open PowerfulSums in
theorem OMA.solution : type_of% @Erdos940.erdos_940.variants.two := by
  classical
  let T : Set ℕ := {n | ∃ S : Multiset ℕ,
    S.card ≤ 2 ∧ (∀ s ∈ S, (2 : ℕ).Full s) ∧ n = S.sum}
  change T.HasDensity 0
  rw [Set.HasDensity, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨C, hC, hCbound⟩ := all_products_bound
  let δ := ε / (4 * C)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨B, hB, htail⟩ := tail_products δ hδ
  let P := Ico 1 B ×ˢ Ico 1 B
  let η := ε / (4 * (P.card + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  let forms (N : ℕ) (p : ℕ × ℕ) :=
    (range N).filter (fun x => ∃ y z : ℕ, p.1 ^ 3 * y ^ 2 + p.2 ^ 3 * z ^ 2 = x)
  have hevent : ∀ᶠ N : ℕ in atTop, ∀ p ∈ P, ((forms N p).card : ℝ) ≤ η * N := by
    apply (eventually_all_finset P).mpr
    intro p hp
    obtain ⟨h₁, h₂⟩ := mem_product.mp hp
    exact fixed_form_bound _ _ (pow_pos (mem_Ico.mp h₁).1 _) (pow_pos (mem_Ico.mp h₂).1 _) η hη
  filter_upwards [eventually_ge_atTop (1 : ℕ), hevent] with N hN hsmall
  let A := (range N).filter (· ∈ T)
  let Small := P.biUnion (forms N)
  let Large := products B N + insert 0 (products 1 N)
  have hcover : A ⊆ Small ∪ Large := by
    intro x hx
    obtain ⟨hxN, S, hS, hfull, hsum⟩ := mem_filter.mp hx
    have hxN' : x < N := mem_range.mp hxN
    obtain ⟨u, v, hu, hv, huv⟩ := two_entries hS hfull
    obtain ⟨a₁, b₁, hb₁, ha₁, hz₁⟩ := square_cube_or_zero hu
    obtain ⟨a₂, b₂, hb₂, ha₂, hz₂⟩ := square_cube_or_zero hv
    have hsum' : u + v = x := huv.trans hsum.symm
    have hat₁ : u ∈ insert 0 (products 1 N) := by
      rcases hz₁ with hz | ⟨_, rfl⟩
      · apply mem_insert_of_mem
        rw [← ha₁]
        exact mem_products hz hb₁ hb₁ (by omega)
      · exact mem_insert_self _ _
    have hat₂ : v ∈ insert 0 (products 1 N) := by
      rcases hz₂ with hz | ⟨_, rfl⟩
      · apply mem_insert_of_mem
        rw [← ha₂]
        exact mem_products hz hb₂ hb₂ (by omega)
      · exact mem_insert_self _ _
    by_cases ht₁ : B ≤ b₁
    · apply mem_union_right
      have h₁ : u ∈ products B N := by
        rw [← ha₁]
        exact mem_products (hz₁.resolve_right (by omega)) hb₁ ht₁ (by omega)
      exact mem_add.mpr ⟨u, h₁, v, hat₂, hsum'⟩
    by_cases ht₂ : B ≤ b₂
    · apply mem_union_right
      have h₂ : v ∈ products B N := by
        rw [← ha₂]
        exact mem_products (hz₂.resolve_right (by omega)) hb₂ ht₂ (by omega)
      exact mem_add.mpr ⟨v, h₂, u, hat₁, (add_comm v u).trans hsum'⟩
    · apply mem_union_left
      refine mem_biUnion.mpr ⟨(b₁, b₂), mem_product.mpr ⟨?_, ?_⟩, ?_⟩
      · exact mem_Ico.mpr ⟨hb₁, by omega⟩
      · exact mem_Ico.mpr ⟨hb₂, by omega⟩
      · exact mem_filter.mpr ⟨hxN, a₁, a₂, by
          dsimp
          rw [mul_comm _ (a₁ ^ 2), mul_comm _ (a₂ ^ 2), ha₁, ha₂, hsum']⟩
  have hsmall' : (Small.card : ℝ) ≤ (ε / 4) * N := by
    calc
      (Small.card : ℝ) ≤ ∑ p ∈ P, ((forms N p).card : ℝ) := by exact_mod_cast card_biUnion_le
      _ ≤ ∑ p ∈ P, η * N := sum_le_sum hsmall
      _ = (P.card : ℝ) * (η * N) := by simp
      _ ≤ (P.card + 1 : ℝ) * (η * N) := by gcongr; linarith
      _ = (ε / 4) * N := by dsimp [η]; field_simp
  have hlarge : (Large.card : ℝ) ≤ (ε / 4) * N := by
    calc
      (Large.card : ℝ) ≤ ((products B N).card : ℝ) * (insert 0 (products 1 N)).card := by
        exact_mod_cast card_add_le
      _ ≤ (δ * Real.sqrt N) * (C * Real.sqrt N) := by
        exact mul_le_mul (htail N) (hCbound N hN) (by positivity) (by positivity)
      _ = (δ * C) * (Real.sqrt N) ^ 2 := by ring
      _ = (ε / 4) * N := by
        rw [Real.sq_sqrt (by positivity)]
        dsimp [δ]
        field_simp
  have ha : (A.card : ℝ) ≤ (ε / 2) * N := by
    have hb : (A.card : ℝ) ≤ (Small.card : ℝ) + Large.card := by
      exact_mod_cast (card_le_card hcover).trans (card_union_le _ _)
    linarith
  have hset : (A : Set ℕ) = T ∩ Set.Iio N := by ext x; simp [A, and_comm]
  have hpd : T.partialDensity Set.univ N = (A.card : ℝ) / N := by
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio, ← hset,
      Set.ncard_coe_finset]
  rw [Real.dist_eq, hpd, sub_zero, abs_of_nonneg (by positivity)]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  exact ((div_le_iff₀ hNr).mpr ha).trans_lt (by linarith)