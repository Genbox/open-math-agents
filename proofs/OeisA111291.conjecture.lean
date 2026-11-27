import FormalConjectures.OEIS.«111291»
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.SumPrimeReciprocals

/-! Products of 128 and two distinct odd primes are refactorable. A finite set
of small prime factors can have arbitrarily large reciprocal sum. Counting
the other prime factor by Chebyshev's inequality gives the desired bound. -/

open Nat Finset

namespace RefactorableProducts

private theorem products_refactorable {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp₂ : 2 < p) (hpq : p < q) : (128 * p * q).IsRefactorable := by
  have hc_p : (128 : ℕ).Coprime p :=
    ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega)).pow_left 7
  have hc_q : (128 : ℕ).Coprime q :=
    ((Nat.coprime_primes Nat.prime_two hq).mpr (by omega)).pow_left 7
  have hc_pq : p.Coprime q := (Nat.coprime_primes hp hq).mpr hpq.ne
  have hcard {p : ℕ} (hp : p.Prime) : p.divisors.card = 2 := by
    rw [hp.divisors]
    simp [hp.ne_one, eq_comm]
  have hp₀ := hp.pos
  have hq₀ := hq.pos
  refine ⟨Nat.succ_le_of_lt (by positivity), ?_⟩
  rw [Nat.Coprime.card_divisors_mul (hc_q.mul_left hc_pq), Nat.Coprime.card_divisors_mul hc_p,
    hcard hp, hcard hq, show (128 : ℕ).divisors.card = 8 by decide]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by decide : 8 * 2 * 2 ∣ (128 : ℕ)) p) q

private theorem primes_sdiff_card_le (a b : ℕ) :
    a.primeCounting - b.primeCounting ≤ (Nat.primesLE a \ Nat.primesLE b).card := by
  rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting,
    Finset.card_sdiff]
  exact Nat.sub_le_sub_left (Finset.card_le_card Finset.inter_subset_left) _

theorem count_products (s : Finset ℕ) {n B : ℕ}
    (hs : ∀ p ∈ s, p.Prime ∧ 2 < p ∧ p ≤ B) :
    (∑ p ∈ s, (Nat.primeCounting (n / (128 * p)) - Nat.primeCounting B)) ≤
      OeisA111291.countRefactorableNat n := by
  let choices (p : ℕ) := Nat.primesLE (n / (128 * p)) \ Nat.primesLE B
  have hchoices {p q : ℕ} (hq : q ∈ choices p) :
      q.Prime ∧ B < q ∧ q ≤ n / (128 * p) := by
    obtain ⟨hq₁, hq₂⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨hqu, hqp⟩ := Nat.mem_primesLE.mp hq₁
    exact ⟨hqp, lt_of_not_ge (fun h => hq₂ (Nat.mem_primesLE.mpr ⟨h, hqp⟩)), hqu⟩
  calc
    _ ≤ ∑ p ∈ s, (choices p).card := Finset.sum_le_sum (fun p _ => primes_sdiff_card_le _ _)
    _ = (s.sigma choices).card := (Finset.card_sigma _ _).symm
    _ ≤ _ := by
      unfold OeisA111291.countRefactorableNat
      refine Finset.card_le_card_of_injOn (fun z : Sigma (fun _ : ℕ => ℕ) => 128 * z.1 * z.2)
        ?_ ?_
      · rintro ⟨p, q⟩ hz
        obtain ⟨hps, hqs⟩ := Finset.mem_sigma.mp hz
        obtain ⟨hp, hp₂, hpB⟩ := hs p hps
        obtain ⟨hq, hBq, hqn⟩ := hchoices hqs
        have hprod := products_refactorable hp hq hp₂ (hpB.trans_lt hBq)
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hprod.1, ?_⟩, hprod⟩
        simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le (by positivity)).mp hqn
      · rintro ⟨p, q⟩ hz ⟨p', q'⟩ hz' h
        obtain ⟨hps, hqs⟩ := Finset.mem_sigma.mp hz
        obtain ⟨hps', hqs'⟩ := Finset.mem_sigma.mp hz'
        obtain ⟨hp, _, hpB⟩ := hs p hps
        obtain ⟨hp', _, _⟩ := hs p' hps'
        obtain ⟨hq', hBq', _⟩ := hchoices hqs'
        have heq : p * q = p' * q' :=
          Nat.eq_of_mul_eq_mul_left (by decide : 0 < (128 : ℕ)) (by simpa [Nat.mul_assoc] using h)
        have hdiv : p ∣ p' * q' := heq ▸ dvd_mul_right p q
        have heq_p : p = p' := by
          rcases hp.dvd_mul.mp hdiv with hpdiv | hqdiv
          · exact (Nat.prime_dvd_prime_iff_eq hp hp').mp hpdiv
          · have he := (Nat.prime_dvd_prime_iff_eq hp hq').mp hqdiv
            omega
        subst p'
        have heq_q := Nat.eq_of_mul_eq_mul_left hp.pos heq
        cases heq_q
        rfl

end RefactorableProducts

namespace OMA

open Filter Topology

lemma eventually_div_log_le_primeCounting_sub (p B : ℕ) (hp : 0 < p) :
    ∀ᶠ x : ℝ in atTop,
      x / (1024 * (p : ℝ) * Real.log x) ≤
        ((Nat.primeCounting (⌊x⌋₊ / (128 * p)) - Nat.primeCounting B : ℕ) : ℝ) := by
  let D : ℝ := 128 * (p : ℝ)
  let b : ℝ := Nat.primeCounting B
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hD : 2 ≤ D := by dsimp [D]; linarith
  have hDpos : 0 < D := by linarith
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hCpos : 0 < 8 * D * (b + 1) := by positivity
  have hlim : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hsmall : ∀ᶠ x : ℝ in atTop, Real.log x / x < 1 / (8 * D * (b + 1)) :=
    hlim.eventually (eventually_lt_nhds (one_div_pos.mpr hCpos))
  filter_upwards [eventually_ge_atTop (2 * D), hsmall] with x hx hsmallx
  let y := x / D
  have hy : 2 ≤ y := (le_div_iff₀ hDpos).mpr hx
  have hyx : y + 2 ≤ x := by
    calc
      y + 2 ≤ y * 2 := by linarith
      _ ≤ y * D := mul_le_mul_of_nonneg_left hD (by linarith)
      _ = x := div_mul_cancel₀ _ hDpos.ne'
  have hxpos : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogyx : Real.log y ≤ Real.log x := Real.log_le_log (by linarith) (by linarith)
  have hlogyp : Real.log (y + 2) ≤ Real.log x := Real.log_le_log (by linarith) hyx
  have herr : (b + 1) * Real.log x ≤ y / 8 := by
    have herr := (div_lt_div_iff₀ hxpos hCpos).mp hsmallx
    apply le_of_lt
    apply (lt_div_iff₀ (by norm_num : 0 < (8 : ℝ))).mpr
    change (b + 1) * Real.log x * 8 < x / D
    apply (lt_div_iff₀ hDpos).mpr
    convert herr using 1 <;> ring
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    convert Real.one_sub_inv_le_log_of_pos (by norm_num : 0 < (2 : ℝ)) using 1
    norm_num
  have hquarter : y / 4 ≤ (y - 1) * Real.log 2 := by
    calc
      y / 4 ≤ (y - 1) * (1 / 2) := by linarith
      _ ≤ (y - 1) * Real.log 2 := mul_le_mul_of_nonneg_left hlog2 (by linarith)
  let N := (y - 1) * Real.log 2 - Real.log (y + 2)
  have hnum : y / 8 + b * Real.log x ≤ N := by dsimp [N]; linarith
  have hN : 0 ≤ N :=
    le_trans (add_nonneg (by positivity) (mul_nonneg hb hlogx.le)) hnum
  have hfloor : ⌊y⌋₊ = ⌊x⌋₊ / (128 * p) := by
    simpa only [y, D, Nat.cast_mul, Nat.cast_ofNat] using Nat.floor_div_natCast x (128 * p)
  have hscaled : y / 8 / Real.log x = x / (1024 * (p : ℝ) * Real.log x) := by
    dsimp [y, D]
    simp only [div_div]
    congr 1
    ring
  have hcount :
      x / (1024 * (p : ℝ) * Real.log x) + b ≤
        (Nat.primeCounting (⌊x⌋₊ / (128 * p)) : ℝ) := by
    calc
      _ = (y / 8 + b * Real.log x) / Real.log x := by
        rw [add_div, mul_div_cancel_right₀ _ hlogx.ne', hscaled]
      _ ≤ N / Real.log x := div_le_div_of_nonneg_right hnum hlogx.le
      _ ≤ N / Real.log y := div_le_div_of_nonneg_left hN hlogy hlogyx
      _ ≤ _ := by simpa only [N, hfloor] using Chebyshev.pi_ge' (show 1 < y by linarith)
  have hcountN : Nat.primeCounting B ≤ Nat.primeCounting (⌊x⌋₊ / (128 * p)) := by
    have hc : (Nat.primeCounting B : ℝ) ≤ (Nat.primeCounting (⌊x⌋₊ / (128 * p)) : ℝ) :=
      le_trans (le_add_of_nonneg_left (by positivity)) hcount
    exact_mod_cast hc
  rw [Nat.cast_sub hcountN]
  exact (le_sub_iff_add_le).mpr hcount

end OMA

namespace RefactorableLower
open Filter Finset OeisA111291

private theorem finite_primes :
    ∃ (B : ℕ) (s : Finset ℕ), (∀ p ∈ s, p.Prime ∧ 2 < p ∧ p ≤ B) ∧
      512 ≤ ∑ p ∈ s, (1 : ℝ) / p := by
  classical
  let f := Set.indicator {p : ℕ | p.Prime} (fun p : ℕ => (1 : ℝ) / p)
  have hpos (p : ℕ) : 0 ≤ f p := Set.indicator_nonneg (fun _ _ => by positivity) _
  have ht : Tendsto (fun k : ℕ => ∑ p ∈ range k, f p) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hpos).mp not_summable_one_div_on_primes
  obtain ⟨B, hB⟩ := ((tendsto_atTop.mp ht) (513 : ℝ)).exists
  have hsum : (513 : ℝ) ≤ ∑ p ∈ B.primesBelow, 1 / (p : ℝ) := by
    simpa only [f, Nat.primesBelow_eq_filter_range, sum_filter, Set.indicator_apply,
      Set.mem_ofPred_eq] using hB
  refine ⟨B, B.primesBelow.erase 2, ?_, ?_⟩
  · intro p hp
    obtain ⟨hne, hmem⟩ := mem_erase.mp hp
    obtain ⟨hlt, hprime⟩ := Nat.mem_primesBelow.mp hmem
    exact ⟨hprime, lt_of_le_of_ne hprime.two_le hne.symm, hlt.le⟩
  · by_cases h2 : 2 ∈ B.primesBelow
    · rw [← sum_erase_add _ _ h2] at hsum
      norm_num at hsum
      simp only [one_div]
      linarith
    · rw [erase_eq_of_notMem h2]
      linarith

theorem conclusion
    (count_products : ∀ (s : Finset ℕ) {n B : ℕ}, (∀ p ∈ s, p.Prime ∧ 2 < p ∧ p ≤ B) →
      (∑ p ∈ s, (Nat.primeCounting (n / (128*p)) - Nat.primeCounting B)) ≤ countRefactorableNat n)
    (fixed_prime : ∀ (p B : ℕ), 0 < p → ∀ᶠ x : ℝ in atTop,
      x / (1024 * (p : ℝ) * Real.log x) ≤
        ((Nat.primeCounting (⌊x⌋₊ / (128*p)) - Nat.primeCounting B : ℕ) : ℝ)) :
    ∀ᶠ x : ℝ in atTop, (countRefactorable x : ℝ) ≥ x / (2 * Real.log x) := by
  classical
  obtain ⟨B, s, hs, hw⟩ := finite_primes
  have hall := (eventually_all_finset s).2 (fun p hp => fixed_prime p B (hs p hp).1.pos)
  filter_upwards [hall, eventually_ge_atTop (2 : ℝ)] with x hxe hx
  have hx1 : 1 ≤ x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hxpos : 0 ≤ x / (1024 * Real.log x) := by positivity
  have hcnt := count_products (n := ⌊x⌋₊) s hs
  rw [countRefactorable, dif_pos hx1, Int.toNat_natCast]
  calc
    x / (2 * Real.log x) = (x / (1024 * Real.log x)) * 512 := by ring
    _ ≤ (x / (1024 * Real.log x)) * (∑ p ∈ s, (1 : ℝ) / p) :=
      mul_le_mul_of_nonneg_left hw hxpos
    _ = ∑ p ∈ s, x / (1024 * (p : ℝ) * Real.log x) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ ∑ p ∈ s, ((Nat.primeCounting (⌊x⌋₊ / (128*p)) - Nat.primeCounting B : ℕ) : ℝ) :=
      sum_le_sum hxe
    _ ≤ _ := by exact_mod_cast hcnt

end RefactorableLower

theorem OMA.solution : type_of% @OeisA111291.conjecture :=
  RefactorableLower.conclusion RefactorableProducts.count_products OMA.eventually_div_log_le_primeCounting_sub