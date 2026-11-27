import FormalConjectures.ErdosProblems.«1142»

/-!
# Erdős 1142 through 2^44

A qualifying number above a prime-dependent threshold is divisible by that prime
when the positive powers of two cover its nonzero residues. On each resulting interval,
write the odd candidates as `(2 * m + 1) * d`, where `d` is their forced odd divisor.
A bit at position `m` certifies a proper divisor of one of the required prime differences.
Repeating masks by shifts and taking their union lets the kernel check the entire interval
with a single equality.
-/

namespace OMA

open Erdos1142

private def indexMask (indices : List ℕ) : ℕ :=
  indices.foldr (fun r mask => (1 <<< r) ||| mask) 0

private def residueMask (d p k : ℕ) : ℕ :=
  indexMask   ((List.range p).filter fun r =>
    (List.range k).any fun e => ((2 * r + 1) * d) % p == (2 ^ (e + 1)) % p)

private def periodicMask (p mask : ℕ) : ℕ → ℕ
  | 0 => mask
  | t + 1 =>
    let earlier := periodicMask p mask t
    earlier ||| (earlier <<< (p * 2 ^ t))

private def coveringMask (d top : ℕ) (rules : List (ℕ × ℕ)) : ℕ :=
  rules.foldr (fun (p, k) mask =>
    periodicMask p (residueMask d p k) (top.log2 + 1 - p.log2) ||| mask) 0

private def allCovered (mask lo hi : ℕ) : Prop :=
  (mask >>> lo) &&& ((1 <<< (hi + 1 - lo)) - 1) = (1 <<< (hi + 1 - lo)) - 1

private instance (mask lo hi : ℕ) : Decidable (allCovered mask lo hi) := by
  unfold allCovered
  infer_instance

-- Each pair lists a modulus and the highest power of two used with it.
private def band0 : List (ℕ × ℕ) :=
  [(11, 6), (13, 6), (7, 6), (17, 6)]

private def band1 : List (ℕ × ℕ) :=
  [(13, 9), (19, 9), (17, 9), (7, 10), (23, 9), (29, 9), (37, 9), (41, 9),
    (43, 9), (47, 9)]

private def band2 : List (ℕ × ℕ) :=
  [(19, 11), (23, 11), (17, 11), (7, 12), (29, 11), (37, 11), (41, 11), (43, 11),
    (47, 11), (53, 11), (59, 11), (61, 11), (67, 11), (31, 11), (71, 11), (79, 11),
    (83, 11), (89, 11), (73, 11), (97, 11), (101, 11), (103, 11), (107, 11), (109, 11),
    (113, 11), (131, 11), (137, 11), (139, 11)]

private def band3 : List (ℕ × ℕ) :=
  [(29, 17), (23, 17), (17, 18), (37, 17), (7, 18), (41, 17), (47, 17), (43, 17),
    (53, 17), (59, 17), (61, 17), (67, 17), (71, 17), (79, 17), (83, 17), (97, 17),
    (101, 17), (103, 17), (31, 17), (107, 17)]

private def band4 : List (ℕ × ℕ) :=
  [(37, 27), (53, 27), (47, 27), (41, 27), (23, 28), (17, 28), (59, 27), (61, 27),
    (7, 28), (67, 27), (71, 27), (79, 27), (43, 27), (83, 27), (97, 27), (101, 27),
    (103, 27), (107, 27), (109, 27), (113, 27)]

private def band5 : List (ℕ × ℕ) :=
  [(53, 35), (59, 35), (61, 35), (67, 35), (71, 35), (47, 35), (41, 35), (23, 36),
    (17, 36), (79, 35), (7, 36), (83, 35), (97, 35), (101, 35), (103, 35), (107, 35),
    (43, 35), (109, 35), (131, 35), (137, 35), (139, 35), (113, 35), (149, 35), (157, 35)]

private lemma indexMask_sound {indices : List ℕ} {r : ℕ}
    (h : (indexMask indices).testBit r = true) : r ∈ indices := by
  induction indices with
  | nil => simp [indexMask] at h
  | cons x xs ih =>
    change ((1 <<< x) ||| indexMask xs).testBit r = true at h
    simp only [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
      decide_eq_true_eq] at h
    exact h.elim (fun he => he ▸ List.mem_cons_self) (fun hxs => List.mem_cons_of_mem _ (ih hxs))

private lemma periodicMask_sound (p mask : ℕ)
    (hmask : ∀ r, mask.testBit r = true → r < p) :
    ∀ t m, (periodicMask p mask t).testBit m = true → mask.testBit (m % p) = true := by
  intro t
  induction t with
  | zero =>
    intro m h
    change mask.testBit m = true at h
    simpa only [Nat.mod_eq_of_lt (hmask m h)] using h
  | succ t ih =>
    intro m h
    simp only [periodicMask, Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨hle, h⟩
    · exact ih m h
    · have hm : m % p = (m - p * 2 ^ t) % p := by
        conv_lhs => rw [← Nat.sub_add_cancel hle]
        exact Nat.add_mul_mod_self_left _ _ _
      exact hm ▸ ih _ h

private lemma not_property_of_residue {n p e : ℕ}
    (hp : 1 < p) (he : 0 < e) (hl : 2 ^ e + p < n)
    (hmod : n % p = 2 ^ e % p) : ¬ Erdos1142Prop n := by
  intro h
  have hprime := h.2 e he (by omega)
  have hdvd := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmod)
  rcases hprime.eq_one_or_self_of_dvd p hdvd with h | h <;> omega

private lemma coveringMask_sound {d top start m : ℕ} {rules : List (ℕ × ℕ)}
    (hstart : start ≤ (2 * m + 1) * d)
    (hrules : ∀ r ∈ rules, 1 < r.1 ∧ 2 ^ r.2 + r.1 < start)
    (hbit : (coveringMask d top rules).testBit m = true) :
    ¬ Erdos1142Prop ((2 * m + 1) * d) := by
  induction rules with
  | nil => simp [coveringMask] at hbit
  | cons rule rules ih =>
    obtain ⟨p, k⟩ := rule
    change (periodicMask p (residueMask d p k) (top.log2 + 1 - p.log2) |||
      coveringMask d top rules).testBit m = true at hbit
    rw [Nat.testBit_or, Bool.or_eq_true] at hbit
    rcases hbit with h | h
    · have hm := periodicMask_sound p (residueMask d p k) (fun r hr =>
        List.mem_range.mp (List.mem_filter.mp (indexMask_sound hr)).1) _ _ h
      have hres := (List.mem_filter.mp (indexMask_sound hm)).2
      obtain ⟨i, hi, hres⟩ := List.any_eq_true.mp hres
      obtain ⟨hp, hpk⟩ : 1 < p ∧ 2 ^ k + p < start := hrules (p, k) List.mem_cons_self
      have hpows : (2 : ℕ) ^ (i + 1) ≤ 2 ^ k :=
        Nat.pow_le_pow_right (by decide) (Nat.succ_le_of_lt (List.mem_range.mp hi))
      refine not_property_of_residue hp (Nat.succ_pos i) (by omega) ?_
      have hmod : m % p ≡ m [MOD p] := Nat.mod_mod m p
      have hmd := (hmod.mul_left 2).add_right 1 |>.mul_right d
      exact hmd.symm.trans (beq_iff_eq.mp hres)
    · exact ih (fun r hr => hrules r (List.mem_cons_of_mem _ hr)) h

private lemma allCovered_sound {mask lo hi m : ℕ} (h : allCovered mask lo hi)
    (hlo : lo ≤ m) (hhi : m ≤ hi) : mask.testBit m = true := by
  unfold allCovered at h
  have h' := congrArg (fun x => x.testBit (m - lo)) h
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.one_shiftLeft,
    Nat.testBit_two_pow_sub_one] at h'
  have hm : m - lo < hi + 1 - lo := by omega
  simpa only [hm, decide_true, Bool.and_true, Nat.add_sub_of_le hlo] using h'

private lemma criticalPrime_dvd {n p : ℕ} (h : Erdos1142Prop n) (hp : 1 < p)
    (hbound : 2 ^ (p - 1) + p < n)
    (hcover : (List.range p).all (fun r => r == 0 ||
      (List.range (p - 1)).any (fun e => r == 2 ^ (e + 1) % p)) = true) : p ∣ n := by
  by_contra hndvd
  have hnmod : n % p ≠ 0 := fun hz => hndvd (Nat.dvd_of_mod_eq_zero hz)
  have hzero : (n % p == 0) = false := by simp [hnmod]
  have hres := List.all_eq_true.mp hcover (n % p) (List.mem_range.mpr (Nat.mod_lt _ (by omega)))
  simp only [hzero, Bool.false_or] at hres
  obtain ⟨e, he, hres⟩ := List.any_eq_true.mp hres
  have hpow : (2 : ℕ) ^ (e + 1) ≤ 2 ^ (p - 1) :=
    Nat.pow_le_pow_right (by decide) (Nat.succ_le_of_lt (List.mem_range.mp he))
  exact not_property_of_residue hp (Nat.succ_pos e) (by omega) (beq_iff_eq.mp hres) h

private lemma no_property_in_band {n d start stop lo hi : ℕ} {rules : List (ℕ × ℕ)}
    (hstart : start ≤ n) (hstop : n ≤ stop) (hnodd : n % 2 = 1)
    (hdiv : d ∣ n) (hodd : d % 2 = 1)
    (hlower : (2 * lo - 1) * d < start) (hupper : stop < (2 * hi + 3) * d)
    (hrules : ∀ r ∈ rules, 1 < r.1 ∧ 2 ^ r.2 + r.1 < start)
    (hcover : allCovered (coveringMask d hi rules) lo hi) : ¬ Erdos1142Prop n := by
  obtain ⟨a, ha⟩ := hdiv
  have haodd : a % 2 = 1 := by simpa only [ha, Nat.mul_mod, hodd, one_mul, Nat.mod_mod] using hnodd
  let m := a / 2
  have hrepr : n = (2 * m + 1) * d := by
    have : a = 2 * m + 1 := by omega
    rw [ha, this, Nat.mul_comm]
  have hlo : lo ≤ m := by
    by_contra hbad
    have hle : (2 * m + 1) * d ≤ (2 * lo - 1) * d := Nat.mul_le_mul_right d (by omega)
    omega
  have hhi : m ≤ hi := by
    by_contra hbad
    have hle : (2 * hi + 3) * d ≤ (2 * m + 1) * d := Nat.mul_le_mul_right d (by omega)
    omega
  rw [hrepr] at hstart ⊢
  exact coveringMask_sound hstart hrules (allCovered_sound hcover hlo hhi)

private def examples : List ℕ := [4, 7, 15, 21, 45, 75, 105]

private def smallMask : ℕ := indexMask ((List.range 106).filter fun n =>
  examples.contains n || (List.range 6).any fun e =>
    (n == 2 ^ (e + 1) + 1) || [2, 3, 5, 7].any fun p =>
      decide (2 ^ (e + 1) + p < n) && (n % p == 2 ^ (e + 1) % p))

private lemma small_property {n : ℕ} (hn : n < 106) (h : Erdos1142Prop n) : n ∈ examples := by
  have hchecked : allCovered smallMask 3 105 := by decide +kernel
  have hm := (List.mem_filter.mp (indexMask_sound (allCovered_sound hchecked
    (show 3 ≤ n from h.1) (show n ≤ 105 by omega)))).2
  rw [Bool.or_eq_true] at hm
  rcases hm with hg | hb
  · simpa using hg
  · obtain ⟨e, _, he⟩ := List.any_eq_true.mp hb
    rw [Bool.or_eq_true] at he
    rcases he with he | he
    · have heq := beq_iff_eq.mp he
      have hp := h.2 (e + 1) (Nat.succ_pos e) (by omega)
      have hsub : n - 2 ^ (e + 1) = 1 := by omega
      simp [hsub] at hp
    · obtain ⟨p, hp, he⟩ := List.any_eq_true.mp he
      rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at he
      have hp' : 1 < p := (show ∀ q ∈ ([2, 3, 5, 7] : List ℕ), 1 < q by decide) p hp
      exact (not_property_of_residue hp' (Nat.succ_pos e) he.1 he.2 h).elim

set_option maxHeartbeats 600000 in
private lemma classify {n : ℕ} (hn : n ≤ 2 ^ 44) (h : Erdos1142Prop n) :
    n ∈ examples := by
  by_cases hsmall : n < 106
  · exact small_property hsmall h
  exfalso
  have hodd : n % 2 = 1 := by
    have hp := h.2 1 (by decide) (by simpa using h.1)
    refine (Nat.Prime.mod_two_eq_one_iff_ne_two hp).2 (by omega) |> fun hmod => ?_
    simp only [pow_one] at hmod
    omega
  have hlarge : 106 ≤ n := Nat.le_of_not_lt hsmall
  have h3 : 3 ∣ n := criticalPrime_dvd h (by decide) (lt_of_lt_of_le (by decide) hlarge)
    (by decide +kernel)
  have h5 : 5 ∣ n := criticalPrime_dvd h (by decide) (lt_of_lt_of_le (by decide) hlarge)
    (by decide +kernel)
  have h15 : 15 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h3 h5
  by_cases hband0 : n ≤ 1035
  · -- The residue masks on this interval leave the single candidate 465.
    rcases lt_trichotomy n 465 with hlt | rfl | hgt
    · exact no_property_in_band (start := 106) (stop := 464) (lo := 4) (hi := 14)
        (rules := band0) hlarge (Nat.le_of_lt_succ hlt) hodd h15 (by decide) (by decide) (by decide)
        (by decide +kernel) (by decide +kernel) h
    · exact not_property_of_residue (p := 11) (e := 8) (by decide) (by decide) (by decide)
        (by decide) h
    · exact no_property_in_band (start := 466) (stop := 1035) (lo := 16) (hi := 34)
        (rules := band0) hgt hband0 hodd h15 (by decide) (by decide) (by decide)
        (by decide +kernel) (by decide +kernel) h
  have h11 : 11 ∣ n := criticalPrime_dvd h (by decide) (Nat.lt_of_not_ge hband0)
    (by decide +kernel)
  have h165 : 165 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h15 h11
  by_cases hband1 : n ≤ 4109
  · exact no_property_in_band (start := 1036) (lo := 3) (hi := 11) (rules := band1)
      (Nat.lt_of_not_ge hband0) hband1 hodd h165 (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) h
  have h13 : 13 ∣ n := criticalPrime_dvd h (by decide) (Nat.lt_of_not_ge hband1)
    (by decide +kernel)
  have h2145 : 2145 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h165 h13
  by_cases hband2 : n ≤ 262163
  · exact no_property_in_band (start := 4110) (lo := 1) (hi := 60) (rules := band2)
      (Nat.lt_of_not_ge hband1) hband2 hodd h2145 (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) h
  have h19 : 19 ∣ n := criticalPrime_dvd h (by decide) (Nat.lt_of_not_ge hband2)
    (by decide +kernel)
  have h40755 : 40755 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h2145 h19
  by_cases hband3 : n ≤ 268435485
  · exact no_property_in_band (start := 262164) (lo := 3) (hi := 3292) (rules := band3)
      (Nat.lt_of_not_ge hband2) hband3 hodd h40755 (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) h
  have h29 : 29 ∣ n := criticalPrime_dvd h (by decide) (Nat.lt_of_not_ge hband3)
    (by decide +kernel)
  have h1181895 : 1181895 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h40755 h29
  by_cases hband4 : n ≤ 68719476773
  · exact no_property_in_band (start := 268435486) (lo := 114) (hi := 29071) (rules := band4)
      (Nat.lt_of_not_ge hband3) hband4 hodd h1181895 (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) h
  have h37 : 37 ∣ n := criticalPrime_dvd h (by decide) (Nat.lt_of_not_ge hband4)
    (by decide +kernel)
  have h43730115 : 43730115 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h1181895 h37
  exact no_property_in_band (start := 68719476774) (lo := 786) (hi := 201144) (rules := band5)
    (Nat.lt_of_not_ge hband4) hn hodd h43730115 (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) h

end OMA

theorem OMA.solution : type_of% @Erdos1142.erdos_1142.variants.mientka_weitzenkamp := by
  ext n
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro ⟨hn, h⟩
    simpa [OMA.examples] using OMA.classify hn h
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals
      refine ⟨by decide, ?_⟩
      first
      | exact Erdos1142.erdos_1142.test_4
      | exact Erdos1142.erdos_1142.test_7
      | exact Erdos1142.erdos_1142.test_15
      | exact Erdos1142.erdos_1142.test_21
      | exact Erdos1142.erdos_1142.test_45
      | exact Erdos1142.erdos_1142.test_75
      | exact Erdos1142.erdos_1142.test_105