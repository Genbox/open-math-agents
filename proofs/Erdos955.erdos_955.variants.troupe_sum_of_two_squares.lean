import FormalConjectures.ErdosProblems.«955»
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
A congruence sieve for the sum of proper divisors.

For each fixed modulus d, primes in the class −1 modulo d have a divergent
reciprocal sum. Outside a set of density zero, one of these primes divides n
exactly once, so d divides the divisor sum σ(n). For finitely many small primes
q in the class 3 modulo 4, apply this with d = q². Then s(n) = σ(n) − n
has the same residue as −n modulo q². The Chinese remainder theorem bounds
the set of n that avoid exact divisibility by all these small primes.
-/

open Filter Finset ArithmeticFunction
open scoped Topology Function ArithmeticFunction.sigma

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

namespace DivisorSieve

private noncomputable def reciprocal {q : ℕ} (a : ZMod q) (n : ℕ) : ℝ :=
  if n.Prime ∧ (n : ZMod q) = a then (n : ℝ)⁻¹ else 0

private theorem reciprocal_nonneg {q : ℕ} (a : ZMod q) (n : ℕ) : 0 ≤ reciprocal a n := by
  unfold reciprocal
  split <;> positivity

/-- Remove the logarithmic weight from the pole of the von Mangoldt series. -/
private theorem ap_reciprocal_diverges {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a) :
    ¬ Summable (reciprocal a) := by
  classical
  intro hs
  let R := vonMangoldt.residueClass a
  let d (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  let F (k n : ℕ) : ℝ := d k * (R n / (n : ℝ)^(1 + d k))
  let G (n : ℕ) : ℝ := (if n.Prime then 0 else R n / (n : ℝ)) + reciprocal a n
  have hd (k : ℕ) : 0 < d k := by dsimp [d]; positivity
  have hd₁ (k : ℕ) : d k ≤ 1 := by
    dsimp [d]
    rw [div_le_one₀ (by positivity : 0 < (k : ℝ) + 1)]
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hdlim : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hG : Summable G := by
    convert (vonMangoldt.summable_residueClass_non_primes_div a).add hs using 1
    funext n
    dsimp [G, R]
    split <;> simp_all
  have hF (k n : ℕ) : 0 ≤ F k n := by
    dsimp [F, R]
    exact mul_nonneg (hd k).le (div_nonneg (vonMangoldt.residueClass_nonneg a n) (by positivity))
  have hdom (k n : ℕ) : ‖F k n‖ ≤ G n := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hF k n)]
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [F, G, R, reciprocal]
    have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
    have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    by_cases hp : n.Prime
    · by_cases he : (n : ZMod q) = a
      · have hR : R n = Real.log n := by
          simp [R, vonMangoldt.residueClass, Set.indicator_of_mem, he, vonMangoldt_apply_prime hp]
        simp only [F, G, hp, if_true, zero_add, reciprocal, he, and_self, hR]
        rw [Real.rpow_add hn', Real.rpow_one, Real.rpow_def_of_pos hn',
          show d k * (Real.log n / ((n : ℝ) * Real.exp (Real.log n * d k))) =
            (Real.log n * d k / Real.exp (Real.log n * d k)) * (n : ℝ)⁻¹ by ring]
        have haux : Real.log n * d k / Real.exp (Real.log n * d k) ≤ 1 :=
          (div_le_one₀ (Real.exp_pos _)).mpr (by linarith [Real.add_one_le_exp (Real.log n * d k)])
        simpa only [one_mul] using mul_le_mul_of_nonneg_right haux (inv_nonneg.mpr hn'.le)
      · have hR : R n = 0 := by simp [R, vonMangoldt.residueClass, Set.indicator_of_notMem, he]
        simp [F, G, reciprocal, hp, he, hR]
    · simp only [G, hp, if_false, reciprocal, false_and, add_zero]
      calc
        F k n ≤ 1 * (R n / (n : ℝ)^(1 + d k)) :=
          mul_le_mul_of_nonneg_right (hd₁ k)
            (div_nonneg (vonMangoldt.residueClass_nonneg a n) (by positivity))
        _ ≤ _ := by
          rw [one_mul]
          apply div_le_div_of_nonneg_left (vonMangoldt.residueClass_nonneg a n) hn'
          calc
            (n : ℝ) = (n : ℝ)^(1 : ℝ) := (Real.rpow_one _).symm
            _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn₁ (by linarith [hd k])
  have hpt n : Tendsto (fun k => F k n) atTop (𝓝 0) := by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [F, R]
    have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
    have hp : Tendsto (fun k => (n : ℝ)^(1 + d k)) atTop (𝓝 (n : ℝ)) := by
      simp_rw [Real.rpow_def_of_pos hn']
      have harg : Tendsto (fun k => Real.log n * (1 + d k)) atTop (𝓝 (Real.log n)) := by
        simpa only [add_zero, mul_one] using
          (((tendsto_const_nhds (x := (1 : ℝ))).add hdlim).const_mul (Real.log n))
      simpa only [Function.comp_def, Real.exp_log hn'] using
        Real.continuous_exp.continuousAt.tendsto.comp harg
    simpa only [F, Pi.div_apply, Pi.mul_apply, zero_mul] using
      hdlim.mul ((tendsto_const_nhds (x := R n)).div hp hn'.ne')
  have hf_lim : Tendsto (fun k => ∑' n, F k n) atTop (𝓝 0) := by
    simpa using tendsto_tsum_of_dominated_convergence hG hpt
      (Filter.Eventually.of_forall hdom)
  obtain ⟨C, hC⟩ := vonMangoldt.LSeries_residueClass_lower_bound ha
  have hpositive : 0 < (q.totient : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast q.totient.pos_of_neZero)
  have hlo (k : ℕ) : (q.totient : ℝ)⁻¹ - d k * C ≤ ∑' n, F k n := by
    have harg : (1 + d k) ∈ Set.Ioc (1 : ℝ) 2 := ⟨by linarith [hd k], by linarith [hd₁ k]⟩
    have hb := mul_le_mul_of_nonneg_left (hC harg) (hd k).le
    rw [show 1 + d k - 1 = d k by ring,
      show d k * ((q.totient : ℝ)⁻¹ / d k - C) =
        (q.totient : ℝ)⁻¹ - d k * C by field_simp [ne_of_gt (hd k)], ← tsum_mul_left] at hb
    exact hb
  have hl : Tendsto (fun k => (q.totient : ℝ)⁻¹ - d k * C) atTop
      (𝓝 ((q.totient : ℝ)⁻¹)) := by
    simpa using tendsto_const_nhds.sub (hdlim.mul_const C)
  have := le_of_tendsto_of_tendsto' hl hf_lim hlo
  exact (not_le_of_gt hpositive) this

private theorem small_sieve {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ (p : ZMod q) = a) ∧
      ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, A ⊆ range N →
        (∀ n ∈ A, ∀ p ∈ P, p ∣ n → p^2 ∣ n) → (A.card : ℝ) ≤ ε * N := by
  classical
  have hs := (not_summable_iff_tendsto_nat_atTop_of_nonneg (reciprocal_nonneg a)).mp
    (ap_reciprocal_diverges a ha)
  obtain ⟨K, hK⟩ := ((tendsto_atTop.mp hs) (-2 * Real.log (ε / 2))).exists
  let P := (range K).filter (fun p : ℕ => p.Prime ∧ (p : ZMod q) = a)
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime ∧ (p : ZMod q) = a := (mem_filter.mp hp).2
  refine ⟨P, hP, ?_⟩
  have hbig : -Real.log (ε / 2) ≤ ∑ p ∈ P, 1 / (2 * (p : ℝ)) := by
    have heq : (∑ p ∈ range K, reciprocal a p) = ∑ p ∈ P, (p : ℝ)⁻¹ := by
      simp only [reciprocal, P, sum_filter]
    have hhalf : (∑ p ∈ P, (p : ℝ)⁻¹) / 2 = ∑ p ∈ P, 1 / (2 * (p : ℝ)) := by
      rw [sum_div]
      apply sum_congr rfl
      intro p _
      rw [one_div, mul_inv]
      ring
    rw [heq] at hK
    rw [← hhalf]
    linarith
  have hsmall : 2 * ∏ p ∈ P, (1 - 1 / (2 * (p : ℝ))) ≤ ε := by
    have hle : (∏ p ∈ P, (1 - 1 / (2 * (p : ℝ)))) ≤
        Real.exp (-(∑ p ∈ P, 1 / (2 * (p : ℝ)))) := by
      rw [← sum_neg_distrib, Real.exp_sum]
      apply Finset.prod_le_prod
      · intro p hp
        apply sub_nonneg.mpr
        have hp' : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).1.two_le
        rw [div_le_one₀ (by linarith : (0 : ℝ) < 2 * p)]
        linarith
      · intro p _
        simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-(1 / (2 * (p : ℝ))))
    calc
      _ ≤ 2 * Real.exp (-(∑ p ∈ P, 1 / (2 * (p : ℝ)))) := by gcongr
      _ ≤ 2 * Real.exp (Real.log (ε / 2)) := by gcongr; linarith
      _ = ε := by rw [Real.exp_log (by positivity : 0 < ε/2)]; ring
  let M := ∏ p : ↥P, p.val ^ 2
  have hM : 0 < M := prod_pos (fun p _ => pow_pos (hP _ p.property).1.pos _)
  filter_upwards [eventually_ge_atTop M] with N hN A hA hgood
  have hh := (PowerfulSums.finite_sieve_ratio P (fun p hp => (hP p hp).1) N hN A hA hgood).trans hsmall
  exact (div_le_iff₀ (show (0 : ℝ) < N by exact_mod_cast hM.trans_le hN)).mp hh

private theorem congruence_divisor {d p n : ℕ} (hp : p.Prime)
    (hmod : (p : ZMod d) = -1) (hp₁ : p ∣ n) (hp₂ : ¬ p^2 ∣ n) :
    d ∣ σ 1 n := by
  obtain ⟨m, rfl⟩ := hp₁
  have hpm : ¬ p ∣ m := by
    intro hd
    obtain ⟨l, rfl⟩ := hd
    exact hp₂ ⟨l, by ring⟩
  have hco := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
  have hplus : d ∣ p + 1 := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    push_cast
    rw [hmod, neg_add_cancel]
  have hσ : σ 1 p = p+1 := by
    simpa [hp.divisors, hp.ne_one, hp.ne_one.symm, add_comm] using ArithmeticFunction.sigma_one_apply p
  rw [isMultiplicative_sigma.map_mul_of_coprime hco, hσ]
  exact dvd_mul_of_dvd_left hplus _

private theorem sigma_exceptions (d : ℕ) [NeZero d] (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (((range N).filter (fun n => ¬ d ∣ σ 1 n)).card : ℝ) ≤ ε * N := by
  obtain ⟨P, hP, happly⟩ := small_sieve (-1 : ZMod d) (isUnit_one.neg) ε hε
  filter_upwards [happly] with N hN
  apply hN _ (filter_subset _ _)
  intro n hn p hp hpn
  by_contra hp₂
  exact (mem_filter.mp hn).2 (congruence_divisor (hP p hp).1 (hP p hp).2 hpn hp₂)

/-- A set has density zero when its elements avoid exact divisibility by every
sufficiently small prime in the class 3 mod 4 whose square divides their divisor sum. -/
private theorem density_of_local (E : ℕ → Prop)
    (hloc : ∀ q : ℕ, q.Prime → (q : ZMod 4) = -1 → ∀ n : ℕ, q^2 < n →
      E n → q^2 ∣ σ 1 n → q ∣ n → q^2 ∣ n) :
    {n | E n}.HasDensity 0 := by
  classical
  rw [Set.HasDensity, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨P, hp, hsieve⟩ := small_sieve (-1 : ZMod 4) isUnit_one.neg (ε/4) (by positivity)
  let η := ε / (4 * (P.card + 1))
  let T := P.sup (fun q => q^2 + 1)
  let badSigma (N q : ℕ) := (range N).filter (fun n => ¬ q^2 ∣ σ 1 n)
  have hbadSigma : ∀ᶠ N : ℕ in atTop, ∀ q ∈ P,
      ((badSigma N q).card : ℝ) ≤ η * N := by
    apply (eventually_all_finset P).mpr
    intro q hq
    let : NeZero (q^2) := ⟨pow_ne_zero _ (hp q hq).1.ne_zero⟩
    exact sigma_exceptions (q^2) η (by dsimp [η]; positivity)
  have hlarge : ∀ᶠ N : ℕ in atTop, 4 * (T : ℝ) / ε ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop (1 : ℕ), hsieve, hbadSigma, hlarge] with N hN hs hσ hT
  let A := (range N).filter E
  let allSigma (n : ℕ) : Prop := ∀ q ∈ P, q^2 ∣ σ 1 n
  let B := A.filter (fun n => T ≤ n ∧ allSigma n)
  let C := P.biUnion (badSigma N)
  have hcover : A ⊆ B ∪ (range T ∪ C) := by
    intro n hn
    by_cases hsmall : n < T
    · exact mem_union_right _ (mem_union_left _ (mem_range.mpr hsmall))
    by_cases hgood : allSigma n
    · exact mem_union_left _ (mem_filter.mpr ⟨hn, Nat.le_of_not_gt hsmall, hgood⟩)
    · change ¬ ∀ q ∈ P, q^2 ∣ σ 1 n at hgood
      push Not at hgood
      obtain ⟨q, hq, hnq⟩ := hgood
      exact mem_union_right _ (mem_union_right _ (mem_biUnion.mpr ⟨q, hq,
        mem_filter.mpr ⟨(mem_filter.mp hn).1, hnq⟩⟩))
  have hB : (B.card : ℝ) ≤ ε/4 * N := by
    apply hs B ((filter_subset _ _).trans (filter_subset _ _))
    intro n hn q hq hqn
    obtain ⟨hna, hnT, hnq⟩ := mem_filter.mp hn
    have hqT : q^2 + 1 ≤ T := Finset.le_sup (f := fun q : ℕ => q^2 + 1) hq
    exact hloc q (hp q hq).1 (hp q hq).2 n (by omega) (mem_filter.mp hna).2 (hnq q hq) hqn
  have hC : (C.card : ℝ) ≤ ε/4 * N := by
    calc
      _ ≤ ∑ q ∈ P, ((badSigma N q).card : ℝ) := by exact_mod_cast card_biUnion_le
      _ ≤ ∑ _q ∈ P, η * N := sum_le_sum hσ
      _ = (P.card : ℝ) * (η * N) := by simp
      _ ≤ ((P.card : ℝ) + 1) * (η * N) := by
        apply mul_le_mul_of_nonneg_right (by linarith)
        dsimp [η]
        positivity
      _ = _ := by dsimp [η]; field_simp
  have hT' : (T : ℝ) ≤ ε/4 * N := by
    have h' := (div_le_iff₀ hε).mp hT
    linarith
  have hA : (A.card : ℝ) ≤ (3*ε/4) * N := by
    have hcount : (A.card : ℝ) ≤ (B.card : ℝ) + (T : ℝ) + (C.card : ℝ) := by
      exact_mod_cast (show A.card ≤ B.card + T + C.card from by
        have h₁ := (card_le_card hcover).trans (card_union_le _ _)
        have h₂ := card_union_le (range T) C
        rw [card_range] at h₂
        omega)
    linarith
  have hset : (A : Set ℕ) = {n | E n} ∩ Set.Iio N := by ext n; simp [A, and_comm]
  have hpd : ({n | E n} : Set ℕ).partialDensity Set.univ N = (A.card : ℝ) / N := by
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio, ← hset,
      Set.ncard_coe_finset]
  rw [Real.dist_eq, hpd, sub_zero, abs_of_nonneg (by positivity)]
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  exact ((div_le_iff₀ hN').mpr hA).trans_lt (by linarith)

private theorem sigma_ge (n : ℕ) : n ≤ σ 1 n := by
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  exact Nat.le_add_left _ _

private theorem troupe : {n | ∃ a b : ℕ, Erdos955.s n = a^2 + b^2}.HasDensity 0 := by
  apply density_of_local
  intro q hq hres n _ hn hσ hqn
  obtain ⟨a, b, hab⟩ := hn
  have hmod : q % 4 = 3 := by
    have h : (q : ZMod 4) = ((3 : ℕ) : ZMod 4) := by
      rw [hres]
      decide
    simpa using (ZMod.natCast_eq_natCast_iff' _ _ _).mp h
  have hodd : Odd q := Nat.odd_iff.mpr (by omega)
  have hχ : jacobiSym (-((1 : ℤ) * (1 : ℕ))) q = -1 := by
    simpa [jacobiSym.at_neg_one hodd] using ZMod.χ₄_nat_three_mod_four hmod
  have hqs : q ∣ Erdos955.s n := Nat.dvd_sub (dvd_trans (dvd_pow_self q (by decide : 2 ≠ 0)) hσ) hqn
  have hqs₂ : q^2 ∣ Erdos955.s n := by
    rw [hab] at hqs ⊢
    simpa only [one_mul] using
      (PowerfulSums.nonresidue_excludes_single_divisibility (A := 1) (B := 1) hq hχ
        (show q ∣ 1*a^2 + 1*b^2 by simpa only [one_mul] using hqs))
  have h := Nat.dvd_sub hσ hqs₂
  rwa [Erdos955.s, Nat.sub_sub_self (sigma_ge n)] at h

end DivisorSieve

theorem OMA.solution : type_of% @Erdos955.erdos_955.variants.troupe_sum_of_two_squares := by
  exact DivisorSieve.troupe