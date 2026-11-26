import FormalConjectures.ErdosProblems.«292»

-- Problem: Erdős Problem 292 — prime pow
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/292.lean:78 (declaration Erdos292.erdos_292.variants.prime_pow)
-- Credit: @GuillaumeBAUD-coder (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! The reciprocal of the largest denominator has strictly smallest p-adic valuation. -/

theorem OMA.solution : type_of% @Erdos292.erdos_292.variants.prime_pow := by
  intro n hn hpow
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpow
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS, hn_mem, hsum⟩ := hn
  let term (d : ℕ) : ℚ := 1 / ((max 1 d : ℕ) : ℚ)
  have term_pos (d : ℕ) : 0 < term d := by
    apply one_div_pos.mpr
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 d))
  have term_val (d : ℕ) (hd : 1 ≤ d) :
      padicValRat p (term d) = -(padicValNat p d : ℤ) := by
    dsimp only [term]
    rw [max_eq_right hd, one_div, padicValRat.inv, padicValRat.of_nat]
  have hn_val : padicValRat p (term (p ^ k)) = -(k : ℤ) := by
    rw [term_val _ (Finset.mem_Icc.mp (hS hn_mem)).1, padicValNat.prime_pow]

  have hsum_term : (∑ d ∈ S, term d) = 1 := by
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro d hd
    dsimp only [term]
    rw [max_eq_right (Finset.mem_Icc.mp (hS hd)).1]
  let rest := S.erase (p ^ k)
  have hsum_split : (∑ d ∈ rest, term d) + term (p ^ k) = 1 :=
    (Finset.sum_erase_add S term hn_mem).trans hsum_term

  have rest_nonempty : rest.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hterm : term (p ^ k) = 1 := by simpa [h] using hsum_split
    rw [hterm, padicValRat.one] at hn_val
    omega

  have rest_gt : ∀ d ∈ rest, padicValRat p (term (p ^ k)) < padicValRat p (term d) := by
    intro d hd
    obtain ⟨hd_ne, hd_mem⟩ := Finset.mem_erase.mp hd
    obtain ⟨hd_one, hd_le⟩ := Finset.mem_Icc.mp (hS hd_mem)
    have hd_lt := lt_of_le_of_ne hd_le hd_ne
    have hval_lt : padicValNat p d < k := by
      by_contra! h
      have hdvd : p ^ k ∣ d := (padicValNat_dvd_iff_le (by omega)).mpr h
      have := Nat.le_of_dvd (by omega : 0 < d) hdvd
      omega
    rw [hn_val, term_val d hd_one]
    omega

  have hrest_val := padicValRat.lt_sum_of_lt rest_nonempty rest_gt term_pos
  have hrest_pos : 0 < ∑ d ∈ rest, term d :=
    Finset.sum_pos (fun d _ => term_pos d) rest_nonempty
  have htotal : term (p ^ k) + (∑ d ∈ rest, term d) = 1 := by
    rwa [add_comm]
  have htotal_ne : term (p ^ k) + (∑ d ∈ rest, term d) ≠ 0 := by
    rw [htotal]
    exact one_ne_zero
  have hv := padicValRat.add_eq_of_lt htotal_ne
    (ne_of_gt (term_pos (p ^ k))) (ne_of_gt hrest_pos) hrest_val
  rw [htotal, padicValRat.one, hn_val] at hv
  omega
