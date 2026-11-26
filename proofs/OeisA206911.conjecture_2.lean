import FormalConjectures.OEIS.«206911»

/-! The limiting ratio of gaps in A206911. -/

open Filter Topology OeisA206911

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma OMA.harmonic800_bounds :
    (7.2624 : ℚ) < harmonic 800 ∧ harmonic 800 < (7.2625 : ℚ) := by
  decide +kernel

lemma OMA.exp_gamma_bounds :
    (16 : ℝ) / 9 < Real.exp Real.eulerMascheroniConstant ∧
      Real.exp Real.eulerMascheroniConstant < (41 : ℝ) / 23 := by
  have hleft : Real.exp (Real.eulerMascheroniSeq 800) <
      Real.exp Real.eulerMascheroniConstant :=
    Real.exp_lt_exp.mpr (Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 800)
  have hright : Real.exp Real.eulerMascheroniConstant <
      Real.exp (Real.eulerMascheroniSeq' 800) :=
    Real.exp_lt_exp.mpr (Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 800)
  simp only [Real.eulerMascheroniSeq, Real.eulerMascheroniSeq', OfNat.ofNat_ne_zero,
    if_false, Real.exp_sub] at hleft hright
  rw [Real.exp_log (by positivity)] at hleft hright
  change Real.exp (harmonic 800 : ℝ) / ((800 : ℝ) + 1) < _ at hleft
  change _ < Real.exp (harmonic 800 : ℝ) / (800 : ℝ) at hright
  rw [show (800 : ℝ) + 1 = 801 by norm_num] at hleft
  have hlo : (7.2624 : ℝ) < (harmonic 800 : ℝ) := by
    rw [← show ((7.2624 : ℚ) : ℝ) = 7.2624 by norm_num]
    exact Rat.cast_lt.mpr OMA.harmonic800_bounds.1
  have hhi : (harmonic 800 : ℝ) < (7.2625 : ℝ) := by
    rw [← show ((7.2625 : ℚ) : ℝ) = 7.2625 by norm_num]
    exact Rat.cast_lt.mpr OMA.harmonic800_bounds.2
  have exp_lo : (1424 : ℝ) < Real.exp 7.2624 := by
    have hsum := Real.sum_le_exp_of_nonneg (x := (0.2624 : ℝ)) (by norm_num) 8
    have hseven : Real.exp 7 = (Real.exp 1) ^ 7 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [show (7.2624 : ℝ) = 7 + 0.2624 by norm_num, Real.exp_add, hseven]
    calc
      (1424 : ℝ) < 2.7182818283 ^ 7 *
          (∑ k ∈ Finset.range 8, (0.2624 : ℝ) ^ k / k.factorial) := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ _ := by
        gcongr
        exact Real.exp_one_gt_d9.le
  have exp_hi : Real.exp 7.2625 < (800 : ℝ) * (41 / 23) := by
    have hsum := Real.exp_bound' (x := (0.2625 : ℝ)) (by norm_num) (by norm_num)
      (n := 8) (by decide)
    have hseven : Real.exp 7 = (Real.exp 1) ^ 7 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [show (7.2625 : ℝ) = 7 + 0.2625 by norm_num, Real.exp_add, hseven]
    calc
      _ ≤ (2.7182818286 : ℝ) ^ 7 *
          ((∑ k ∈ Finset.range 8, (0.2625 : ℝ) ^ k / k.factorial) +
            (0.2625 : ℝ) ^ 8 * (8 + 1) / ((8 : ℕ).factorial * 8)) := by
        gcongr
        · exact Real.exp_one_lt_d9.le
        · exact hsum
      _ < _ := by norm_num [Finset.sum_range_succ, Nat.factorial]
  constructor
  · refine lt_trans ?_ hleft
    apply (lt_div_iff₀ (by norm_num)).mpr
    rw [show (16 : ℝ) / 9 * 801 = 1424 by norm_num]
    exact exp_lo.trans (Real.exp_lt_exp.mpr hlo)
  · refine hright.trans ?_
    exact (div_lt_iff₀ (by norm_num)).mpr (by
      rw [mul_comm]
      exact (Real.exp_lt_exp.mpr hhi).trans exp_hi)

lemma OMA.oeis_gap (n : ℕ) (hn : 1 ≤ n) : diff n = 2 ∨ diff n = 3 := by
  by_cases hsmall : n < 5
  · interval_cases n <;> norm_num [diff, a_1, a_2, a_3, a_4, a_5]
  have hn₅ : 5 ≤ n := Nat.le_of_not_gt hsmall
  let E (k : ℕ) : ℝ := Real.exp (harmonic k : ℝ)
  have step (k : ℕ) :
      E (k + 1) = E k * Real.exp (((k : ℝ) + 1)⁻¹) := by
    simp only [E, harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast, Rat.cast_one,
      Nat.cast_add, Nat.cast_one, Real.exp_add]
  have exp_upper (k : ℕ) (hk : 0 < k) :
      Real.exp (((k : ℝ) + 1)⁻¹) ≤ 1 + (k : ℝ)⁻¹ := by
    have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
    have hc : ((k : ℝ) + 1)⁻¹ < 1 := by
      apply inv_lt_one_of_one_lt₀
      linarith
    calc
      Real.exp (((k : ℝ) + 1)⁻¹) ≤ 1 / (1 - ((k : ℝ) + 1)⁻¹) :=
        Real.exp_bound_div_one_sub_of_interval (by positivity) hc
      _ = 1 + (k : ℝ)⁻¹ := by field_simp <;> simp [ne_of_gt hk']
  have hE_upper (k : ℕ) (hk : 5 ≤ k) : E k ≤ 2 * (k : ℝ) := by
    induction k, hk using Nat.le_induction with
    | base =>
      have hsum : (harmonic 5 : ℝ) = 137 / 60 := by
        norm_num [harmonic, Finset.sum_range_succ]
      change Real.exp (harmonic 5 : ℝ) ≤ 2 * (5 : ℝ)
      rw [hsum]
      have hpow : (Real.exp (137 / 60)) ^ 60 = (Real.exp 1) ^ 137 := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        ring_nf
      have hlt : (Real.exp (137 / 60)) ^ 60 < (10 : ℝ) ^ 60 := by
        rw [hpow]
        calc
          (Real.exp 1) ^ 137 < 2.7182818286 ^ 137 := by
            gcongr
            exact Real.exp_one_lt_d9
          _ < (10 : ℝ) ^ 60 := by norm_num
      have : Real.exp (137 / 60) < (10 : ℝ) :=
        lt_of_pow_lt_pow_left₀ 60 (by norm_num) hlt
      norm_num
      exact this.le
    | succ k hk ih =>
      have hk' : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
      calc
        E (k + 1) = E k * Real.exp (((k : ℝ) + 1)⁻¹) := step k
        _ ≤ (2 * (k : ℝ)) * (1 + (k : ℝ)⁻¹) :=
          mul_le_mul ih (exp_upper k (by omega)) (Real.exp_nonneg _) (by positivity)
        _ = 2 * (↑(k + 1) : ℝ) := by push_cast; field_simp
  have hE_lower (k : ℕ) : (k : ℝ) + 1 ≤ E k := by
    have hlog : Real.log ((k : ℝ) + 1) ≤ harmonic k := by
      simpa only [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic k
    have hp : 0 < (k : ℝ) + 1 := by positivity
    rw [← Real.exp_log hp]
    exact Real.exp_le_exp.mpr hlog
  have hlower : E n + 1 ≤ E (n + 1) := by
    rw [step]
    have hmul : 1 ≤ E n * (Real.exp (((n : ℝ) + 1)⁻¹) - 1) := by
      calc
        1 = ((n : ℝ) + 1) * ((n : ℝ) + 1)⁻¹ := by field_simp
        _ ≤ E n * (Real.exp (((n : ℝ) + 1)⁻¹) - 1) :=
          mul_le_mul (hE_lower n) (by linarith [Real.add_one_le_exp (((n : ℝ) + 1)⁻¹)])
            (by positivity) (Real.exp_nonneg _)
    linarith
  have hupper : E (n + 1) ≤ E n + 2 := by
    rw [step]
    have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
    have hmul : E n * (n : ℝ)⁻¹ ≤ 2 := by
      rw [← div_eq_mul_inv]
      exact (div_le_iff₀ hn').mpr (hE_upper n hn₅)
    calc
      E n * Real.exp (((n : ℝ) + 1)⁻¹) ≤ E n * (1 + (n : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left (exp_upper n hn) (Real.exp_nonneg _)
      _ ≤ E n + 2 := by linarith
  let u : ℝ := E n - 1
  let v : ℝ := E (n + 1) - 1
  have hfloor_lower : ⌊u⌋ + 1 ≤ ⌊v⌋ := by
    apply Int.le_floor.mpr
    push_cast
    have h := Int.floor_le u
    dsimp [u, v] at *
    linarith
  have hfloor_upper : ⌊v⌋ ≤ ⌊u⌋ + 2 := by
    apply Int.floor_le_iff.mpr
    push_cast
    have h := Int.lt_floor_add_one u
    dsimp [u, v] at *
    linarith
  have floor_nonneg (k : ℕ) : 0 ≤ ⌊E k - 1⌋ := by
    apply Int.floor_nonneg.mpr
    linarith [hE_lower k, Nat.cast_nonneg (α := ℝ) k]
  unfold diff a
  push_cast
  change (n : ℤ) + 1 + (↑⌊v⌋.toNat : ℤ) -
    ((n : ℤ) + (↑⌊u⌋.toNat : ℤ)) = 2 ∨
    (n : ℤ) + 1 + (↑⌊v⌋.toNat : ℤ) -
      ((n : ℤ) + (↑⌊u⌋.toNat : ℤ)) = 3
  rw [Int.toNat_of_nonneg (floor_nonneg (n + 1)), Int.toNat_of_nonneg (floor_nonneg n)]
  dsimp only [u, v] at hfloor_lower hfloor_upper
  omega

lemma OMA.count_balance (N : ℕ) :
    (count3 N : ℤ) + count2 N = N ∧
      (count3 N : ℤ) + 2 * (N : ℤ) + a 1 = a (N + 1) := by
  induction N with
  | zero => simp [count2, count3]
  | succ N ih =>
    have htwo : count2 (N + 1) = count2 N + if diff (N + 1) = 2 then 1 else 0 := by
      simp only [count2, Finset.sum_range_succ]
    have hthree : count3 (N + 1) = count3 N + if diff (N + 1) = 3 then 1 else 0 := by
      simp only [count3, Finset.sum_range_succ]
    rw [htwo, hthree]
    rcases OMA.oeis_gap (N + 1) (by omega) with h | h
    · change (a (N + 1 + 1) : ℤ) - a (N + 1) = 2 at h
      have hd : diff (N + 1) = 2 := h
      norm_num [hd] <;> constructor <;> push_cast <;> omega
    · change (a (N + 1 + 1) : ℤ) - a (N + 1) = 3 at h
      have hd : diff (N + 1) = 3 := h
      norm_num [hd] <;> constructor <;> push_cast <;> omega

theorem OMA.solution : type_of% @OeisA206911.conjecture_2 := by
  let c := Real.exp Real.eulerMascheroniConstant
  let den (N : ℕ) : ℝ := (N : ℝ) + 1
  let Y (N : ℕ) : ℝ := Real.exp (harmonic (N + 1) : ℝ)
  let err (N : ℕ) : ℝ := (⌊Y N - 1⌋ : ℝ) - Y N
  have hden (N : ℕ) : 0 < den N := by dsimp [den]; positivity
  have hinv : Tendsto (fun N : ℕ => (den N)⁻¹) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).comp
      (tendsto_add_atTop_nat 1)
    change Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) at h
    simpa only [Nat.cast_add, Nat.cast_one, den] using h
  have hsmall (b : ℝ) : Tendsto (fun N : ℕ => b / den N) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => b) atTop (𝓝 b)).mul hinv)
  have hY : Tendsto (fun N : ℕ => Y N / den N) atTop (𝓝 c) := by
    have h := ((Real.continuous_exp.tendsto _).comp Real.tendsto_harmonic_sub_log).comp
      (tendsto_add_atTop_nat 1)
    refine h.congr ?_
    intro N
    change Real.exp ((harmonic (N + 1) : ℝ) - Real.log ((N + 1 : ℕ) : ℝ)) = Y N / den N
    rw [Real.exp_sub, Real.exp_log (by positivity)]
    simp only [Y, den, Nat.cast_add, Nat.cast_one]
  have herr : Tendsto (fun N : ℕ => err N / den N) atTop (𝓝 0) := by
    refine (hsmall (-2)).squeeze (hsmall (-1)) ?_ ?_
    · intro N
      apply div_le_div_of_nonneg_right _ (hden N).le
      dsimp [err]
      linarith [Int.lt_floor_add_one (Y N - 1)]
    · intro N
      apply div_le_div_of_nonneg_right _ (hden N).le
      dsimp [err]
      linarith [Int.floor_le (Y N - 1)]
  have hA_eq (N : ℕ) : (a (N + 1) : ℝ) / den N = 1 + Y N / den N + err N / den N := by
    have hY_one : 1 ≤ Y N := by
      apply Real.one_le_exp
      exact Rat.cast_nonneg.mpr (Finset.sum_nonneg fun _ _ => by positivity)
    have hf : 0 ≤ ⌊Y N - 1⌋ := Int.floor_nonneg.mpr (sub_nonneg.mpr hY_one)
    have hcast : ((⌊Y N - 1⌋.toNat : ℕ) : ℝ) = (⌊Y N - 1⌋ : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hf)
    have ha : (a (N + 1) : ℝ) = den N + (⌊Y N - 1⌋ : ℝ) := by
      simp only [a, Nat.cast_add, Nat.cast_one, den]
      rw [← hcast]
    rw [ha]
    dsimp only [err]
    field_simp [ne_of_gt (hden N)] <;> ring
  have hA : Tendsto (fun N : ℕ => (a (N + 1) : ℝ) / den N) atTop (𝓝 (1 + c)) := by
    have h := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hY).add herr
    simpa only [add_zero] using h.congr (fun N => (hA_eq N).symm)
  have hthree_eq (N : ℕ) :
      (count3 N : ℝ) / den N = (a (N + 1) : ℝ) / den N - 2 := by
    have heq : (count3 N : ℝ) + 2 * (N : ℝ) + (a 1 : ℝ) = a (N + 1) := by
      exact_mod_cast (OMA.count_balance N).2
    rw [a_1] at heq
    field_simp [ne_of_gt (hden N)]
    dsimp [den]
    push_cast at heq
    linarith
  have htwo_eq (N : ℕ) :
      (count2 N : ℝ) / den N = 1 - 1 / den N - (count3 N : ℝ) / den N := by
    have heq : (count3 N : ℝ) + (count2 N : ℝ) = N := by
      exact_mod_cast (OMA.count_balance N).1
    field_simp [ne_of_gt (hden N)]
    dsimp [den]
    linarith
  have hthree : Tendsto (fun N : ℕ => (count3 N : ℝ) / den N) atTop (𝓝 (c - 1)) := by
    rw [show c - 1 = (1 + c) - 2 by ring]
    exact (hA.sub tendsto_const_nhds).congr (fun N => (hthree_eq N).symm)
  have htwo : Tendsto (fun N : ℕ => (count2 N : ℝ) / den N) atTop (𝓝 (2 - c)) := by
    rw [show 2 - c = 1 - 0 - (c - 1) by ring]
    exact ((tendsto_const_nhds.sub (hsmall 1)).sub hthree).congr (fun N => (htwo_eq N).symm)
  have hc : (16 : ℝ) / 9 < c ∧ c < (41 : ℝ) / 23 := OMA.exp_gamma_bounds
  have hpos : 0 < 2 - c := by linarith [hc.2]
  refine ⟨(c - 1) / (2 - c), (lt_div_iff₀ hpos).mpr ?_, (div_lt_iff₀ hpos).mpr ?_, ?_⟩
  · linarith [hc.1]
  · linarith [hc.2]
  · exact (hthree.div htwo hpos.ne').congr
      (fun N => div_div_div_cancel_right₀ (ne_of_gt (hden N)) _ _)