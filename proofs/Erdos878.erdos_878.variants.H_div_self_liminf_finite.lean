import FormalConjectures.ErdosProblems.«878»
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds

/-! A logarithmic average bound for the summatory prime-power function. -/

open Finset Filter Real

namespace OMA.Erdos878Liminf

private theorem inverse_sq_sum_le (T : Finset ℕ) {a : ℕ} (ha : 0 < a)
    (hT : ∀ n ∈ T, a ≤ n) : (∑ n ∈ T, 1 / (n : ℝ) ^ 2) ≤ 2 / (a : ℝ) := by
  let b := max a (T.sup id + 1)
  have hab : a ≤ b := le_max_left _ _
  have hsub : T ⊆ Ico a b := by
    intro n hn
    have hn' : n ≤ T.sup id := Finset.le_sup (f := id) hn
    exact mem_Ico.mpr ⟨hT n hn, (Nat.lt_succ_of_le hn').trans_le (le_max_right _ _)⟩
  have hs : (∑ n ∈ Ico a b, (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ))) =
      1 / (a : ℝ) - 1 / (b : ℝ) := by
    rw [sum_Ico_eq_sub _ hab, sum_range_sub', sum_range_sub']
    ring
  calc
    ∑ n ∈ T, 1 / (n : ℝ) ^ 2 ≤ ∑ n ∈ Ico a b, 1 / (n : ℝ) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ ∑ n ∈ Ico a b, 2 * (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)) := by
      refine sum_le_sum fun n hn => ?_
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (ha.trans_le (mem_Ico.mp hn).1)
      push_cast
      field_simp
      nlinarith only [hn1]
    _ = 2 * (1 / (a : ℝ) - 1 / (b : ℝ)) := by rw [← mul_sum, hs]
    _ ≤ 2 / (a : ℝ) := by
      have hb : 0 ≤ (1 : ℝ) / b := by positivity
      calc
        _ ≤ 2 * (1 / (a : ℝ)) := mul_le_mul_of_nonneg_left (sub_le_self _ hb) (by norm_num)
        _ = _ := by ring

private theorem weighted_prime_block (P : Finset ℕ) {j : ℕ} (hj : 0 < j)
    (hP : ∀ p ∈ P, p.Prime ∧ Nat.log 2 p = j) :
    (∑ p ∈ P, 1 / ((p : ℝ) * Real.log p)) ≤
      (4 / Real.log 2) * (1 / (j : ℝ) ^ 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hjR : 0 < (j : ℝ) := by exact_mod_cast hj
  have hb : P ⊆ (2 ^ (j + 1)).primesLE := by
    intro p hp
    obtain ⟨hp', hlog⟩ := hP p hp
    refine Nat.mem_primesLE.mpr ⟨?_, hp'⟩
    have h := Nat.lt_pow_succ_log_self (b := 2) (by decide) p
    rw [hlog] at h
    exact h.le
  have hθ := Chebyshev.theta_le_log4_mul_x (x := ((2 ^ (j + 1) : ℕ) : ℝ)) (by positivity)
  rw [Chebyshev.theta_eq_sum_primesLE_log] at hθ
  have hPt := sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => Real.log (p : ℝ)) hb
    (fun p hp _ => by
      have h := Nat.one_lt_of_mem_primesLE hp
      exact Real.log_nonneg (by exact_mod_cast h.le))
  let d : ℝ := 2 ^ j * ((j : ℝ) * Real.log 2) ^ 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hterm (p : ℕ) (hp : p ∈ P) :
      1 / ((p : ℝ) * Real.log p) ≤ Real.log p / d := by
    obtain ⟨hp', hlog⟩ := hP p hp
    have h₁ : (2 : ℝ) ^ j ≤ p := by
      exact_mod_cast (hlog ▸ Nat.pow_log_le_self 2 hp'.ne_zero)
    have h₂ : (j : ℝ) * Real.log 2 ≤ Real.log p := by
      simpa [Real.log_pow] using (Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ j) h₁)
    have hPlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp'.one_lt)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.pos
    rw [div_le_div_iff₀ (mul_pos hp0 hPlog) hd, one_mul]
    dsimp [d]
    calc
      (2 : ℝ) ^ j * ((j : ℝ) * Real.log 2) ^ 2 ≤ p * (Real.log p) ^ 2 :=
        mul_le_mul h₁ (pow_le_pow_left₀ (by positivity) h₂ 2) (by positivity) (by positivity)
      _ = Real.log p * ((p : ℝ) * Real.log p) := by ring
  calc
    (∑ p ∈ P, 1 / ((p : ℝ) * Real.log p)) ≤ ∑ p ∈ P, Real.log p / d :=
      sum_le_sum hterm
    _ = (∑ p ∈ P, Real.log (p : ℝ)) / d := (sum_div ..).symm
    _ ≤ (Real.log 4 * ((2 ^ (j + 1) : ℕ) : ℝ)) / d :=
      div_le_div_of_nonneg_right (hPt.trans hθ) hd.le
    _ = (4 / Real.log 2) * (1 / (j : ℝ) ^ 2) := by
      dsimp [d]
      push_cast
      have he : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
        norm_num
      rw [pow_succ, he]
      field_simp
      ring

private theorem weighted_prime_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P, 1 / ((p : ℝ) * Real.log p)) ≤ 8 / Real.log 2 := by
  let J := P.image (Nat.log 2)
  have hJ (j : ℕ) (hj : j ∈ J) : 1 ≤ j := by
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hj
    exact Nat.le_log_of_pow_le (by decide) (by simpa using (hP p hp).two_le)
  have hconst : 0 ≤ 4 / Real.log 2 := div_nonneg (by norm_num) (Real.log_nonneg (by norm_num))
  calc
    ∑ p ∈ P, (1 / ((p : ℝ) * Real.log p)) =
        ∑ j ∈ J, ∑ p ∈ P.filter (fun p => Nat.log 2 p = j), 1 / ((p : ℝ) * Real.log p) :=
      (sum_fiberwise_of_maps_to (fun _ hp => mem_image_of_mem _ hp) _).symm
    _ ≤ ∑ j ∈ J, (4 / Real.log 2) * (1 / (j : ℝ) ^ 2) := by
      exact sum_le_sum fun j hj => weighted_prime_block _ (hJ j hj)
        (fun p hp => ⟨hP p (mem_filter.mp hp).1, (mem_filter.mp hp).2⟩)
    _ ≤ (4 / Real.log 2) * (2 / (1 : ℝ)) := by
      rw [← mul_sum]
      have h := mul_le_mul_of_nonneg_left (inverse_sq_sum_le J (a := 1) (by decide) hJ) hconst
      simpa only [Nat.cast_one] using h
    _ = 8 / Real.log 2 := by ring

private theorem one_prime_block (B : Finset ℕ) {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hB : ∀ n ∈ B, 0 < n ∧ p ∣ n ∧ Nat.log p n = k) :
    (∑ n ∈ B, (p : ℝ) ^ Nat.log p n / (n : ℝ) ^ 2) ≤ 2 / (p : ℝ) := by
  let T := B.image (· / p)
  have hinj : Set.InjOn (fun n : ℕ => n / p) (B : Set ℕ) := by
    intro n hn m hm heq
    have hn' := Nat.div_mul_cancel (hB n (mem_coe.mp hn)).2.1
    have hm' := Nat.div_mul_cancel (hB m (mem_coe.mp hm)).2.1
    exact hn'.symm.trans ((congrArg (· * p) heq).trans hm')
  have hfac : p ^ k = p ^ (k - 1) * p := by
    rw [← pow_succ, Nat.sub_add_cancel hk]
  have hT (m : ℕ) (hm : m ∈ T) : p ^ (k - 1) ≤ m := by
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
    obtain ⟨hn0, hnp, hnk⟩ := hB n hn
    have hn' := Nat.pow_log_le_self p hn0.ne'
    rw [hnk, hfac] at hn'
    exact (Nat.le_div_iff_mul_le hp.pos).mpr hn'
  have hcon (n : ℕ) (hn : n ∈ B) :
      (p : ℝ) ^ Nat.log p n / (n : ℝ) ^ 2 =
        ((p : ℝ) ^ k / (p : ℝ) ^ 2) * (1 / (((n / p : ℕ) : ℝ)) ^ 2) := by
    obtain ⟨hn0, hnp, hnk⟩ := hB n hn
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hm0 : (n / p : ℕ) ≠ 0 := by
      intro h
      have hd := Nat.div_mul_cancel hnp
      simp only [h, zero_mul] at hd
      exact hn0.ne' hd.symm
    have hn' : (((n / p : ℕ) : ℝ)) * (p : ℝ) = (n : ℝ) := by
      exact_mod_cast Nat.div_mul_cancel hnp
    rw [hnk, ← hn', mul_pow]
    field_simp
  calc
    (∑ n ∈ B, (p : ℝ) ^ Nat.log p n / (n : ℝ) ^ 2) =
        ((p : ℝ) ^ k / (p : ℝ) ^ 2) * ∑ m ∈ T, 1 / (m : ℝ) ^ 2 := by
      rw [mul_sum, sum_image hinj]
      exact sum_congr rfl hcon
    _ ≤ ((p : ℝ) ^ k / (p : ℝ) ^ 2) * (2 / ((p ^ (k - 1) : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (inverse_sq_sum_le T (Nat.pow_pos hp.pos) hT) (by positivity)
    _ = 2 / (p : ℝ) := by
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      push_cast
      rw [show k = (k - 1) + 1 by omega, pow_succ]
      rw [show (k - 1 + 1 - 1) = k - 1 by omega]
      field_simp

private theorem one_prime_sum {p X : ℕ} (hp : p.Prime) :
    (∑ n ∈ (Icc 1 X).filter (fun n => p ∣ n), (p : ℝ) ^ Nat.log p n / (n : ℝ) ^ 2) ≤
      2 * Real.log X * (1 / ((p : ℝ) * Real.log p)) := by
  let B := (Icc 1 X).filter (fun n => p ∣ n)
  let J := Icc 1 (Nat.log p X)
  have hm (n : ℕ) (hn : n ∈ B) : Nat.log p n ∈ J := by
    obtain ⟨hn, hpn⟩ := mem_filter.mp hn
    obtain ⟨hn0, hnX⟩ := mem_Icc.mp hn
    exact mem_Icc.mpr ⟨Nat.le_log_of_pow_le hp.one_lt (by
      simpa using Nat.le_of_dvd hn0 hpn), Nat.log_monotone hnX⟩
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hL : (Nat.log p X : ℝ) * Real.log p ≤ Real.log X := by
    rcases eq_or_ne X 0 with rfl | hX
    · simp
    · have hh : (p : ℝ) ^ Nat.log p X ≤ (X : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self p hX
      simpa [Real.log_pow] using
        (Real.log_le_log (by positivity : 0 < (p : ℝ) ^ Nat.log p X) hh)
  have hpl : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  calc
    (∑ n ∈ B, (p : ℝ) ^ Nat.log p n / (n : ℝ) ^ 2) =
        ∑ k ∈ J, ∑ n ∈ B.filter (fun n => Nat.log p n = k),
          (p : ℝ) ^ Nat.log p n / (n : ℝ) ^ 2 :=
      (sum_fiberwise_of_maps_to hm _).symm
    _ ≤ ∑ _ ∈ J, 2 / (p : ℝ) := by
      refine sum_le_sum fun k hk => one_prime_block _ hp (mem_Icc.mp hk).1 ?_
      intro n hn
      obtain ⟨hn, hnk⟩ := mem_filter.mp hn
      exact ⟨(mem_Icc.mp (mem_filter.mp hn).1).1, (mem_filter.mp hn).2, hnk⟩
    _ = (Nat.log p X : ℝ) * (2 / (p : ℝ)) := by simp [J, Nat.card_Icc, nsmul_eq_mul]
    _ ≤ (Real.log X / Real.log p) * (2 / (p : ℝ)) :=
      mul_le_mul_of_nonneg_right ((le_div_iff₀ hpl).mpr hL) (by positivity)
    _ = _ := by ring

private theorem f_weighted (X : ℕ) :
    (∑ n ∈ Icc 1 X, (Erdos878.f n : ℝ) / (n : ℝ) ^ 2) ≤
      2 * Real.log X * (8 / Real.log 2) := by
  let P := X.primesLE
  let term (p n : ℕ) : ℝ := if p ∣ n then (p : ℝ) ^ Nat.log p n / (n : ℝ) ^ 2 else 0
  have hp (n : ℕ) (hn : n ∈ Icc 1 X) : n.primeFactors = P.filter (· ∣ n) := by
    ext p
    obtain ⟨hn₀, hnX⟩ := mem_Icc.mp hn
    simp only [Nat.mem_primeFactors, mem_filter, P, Nat.mem_primesLE]
    refine ⟨fun ⟨hp, hpn, _⟩ => ⟨⟨(Nat.le_of_dvd hn₀ hpn).trans hnX, hp⟩, hpn⟩,
      fun ⟨⟨_, hp⟩, hpn⟩ => ⟨hp, hpn, by omega⟩⟩
  have hterm (n : ℕ) (hn : n ∈ Icc 1 X) :
      (Erdos878.f n : ℝ) / (n : ℝ) ^ 2 = ∑ p ∈ P, term p n := by
    rw [Erdos878.f, Nat.cast_sum, sum_div, hp n hn, sum_filter]
    simp [term, Nat.cast_pow]
  calc
    (∑ n ∈ Icc 1 X, (Erdos878.f n : ℝ) / (n : ℝ) ^ 2) =
        ∑ n ∈ Icc 1 X, ∑ p ∈ P, term p n := sum_congr rfl hterm
    _ = ∑ p ∈ P, ∑ n ∈ Icc 1 X, term p n := sum_comm
    _ ≤ ∑ p ∈ P, 2 * Real.log X * (1 / ((p : ℝ) * Real.log p)) := by
      refine sum_le_sum fun p hp => ?_
      unfold term
      rw [← sum_filter]
      exact one_prime_sum (Nat.prime_of_mem_primesLE hp)
    _ ≤ (2 * Real.log X) * (8 / Real.log 2) := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (weighted_prime_bound _ (fun _ => Nat.prime_of_mem_primesLE))
        (by positivity)

private theorem H_weighted (X : ℕ) :
    (∑ x ∈ Icc 1 X, Erdos878.H x / (x : ℝ) ^ 2) ≤ 4 * (8 / Real.log 2) * Real.log X := by
  let I := Icc 1 X
  let term (x n : ℕ) : ℝ :=
    if n < x then ((Erdos878.f n : ℝ) / n) * (1 / (x : ℝ) ^ 2) else 0
  have hterm (x : ℕ) (hx : x ∈ I) :
      Erdos878.H x / (x : ℝ) ^ 2 = ∑ n ∈ I, term x n := by
    have hI : I.filter (· < x) = Ico 1 x := by
      ext n
      have hxX := (mem_Icc.mp hx).2
      simp only [I, mem_filter, mem_Icc, mem_Ico]
      omega
    rw [Erdos878.H, sum_div]
    unfold term
    rw [← sum_filter, hI]
    exact sum_congr rfl (fun _ _ => by ring)
  have hsum (n : ℕ) (hn : n ∈ I) :
      (∑ x ∈ I, term x n) ≤ 2 * ((Erdos878.f n : ℝ) / (n : ℝ) ^ 2) := by
    have hn0 := (mem_Icc.mp hn).1
    unfold term
    rw [← sum_filter, ← mul_sum]
    have htail := inverse_sq_sum_le (I.filter (n < ·)) (a := n) hn0
      (fun _ hx => (mem_filter.mp hx).2.le)
    calc
      ((Erdos878.f n : ℝ) / n) * ∑ x ∈ I.filter (n < ·), 1 / (x : ℝ) ^ 2 ≤
          ((Erdos878.f n : ℝ) / n) * (2 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ = _ := by ring
  calc
    (∑ x ∈ I, Erdos878.H x / (x : ℝ) ^ 2) = ∑ x ∈ I, ∑ n ∈ I, term x n :=
      sum_congr rfl hterm
    _ = ∑ n ∈ I, ∑ x ∈ I, term x n := sum_comm
    _ ≤ ∑ n ∈ I, 2 * ((Erdos878.f n : ℝ) / (n : ℝ) ^ 2) := sum_le_sum hsum
    _ ≤ 2 * (2 * Real.log X * (8 / Real.log 2)) := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (f_weighted X) (by norm_num)
    _ = _ := by ring

end OMA.Erdos878Liminf

open OMA.Erdos878Liminf in
theorem OMA.solution : type_of% @Erdos878.erdos_878.variants.H_div_self_liminf_finite := by
  let C := 4 * (8 / Real.log 2) + 1
  refine ⟨C, ?_⟩
  by_contra h
  obtain ⟨M, hM⟩ := eventually_atTop.mp (not_frequently.mp h)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let K := C * (∑ x ∈ Ico 1 M, (1 / (x : ℝ)))
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop K)
  let N := max (max M X) 1
  have hMN : M ≤ N := (le_max_left _ _).trans (le_max_left _ _)
  have hXN : X ≤ N := (le_max_right _ _).trans (le_max_left _ _)
  have hN : 1 ≤ N := le_max_right _ _
  have hNK : K < Real.log (N : ℝ) := hX N hXN
  let T := (Icc 1 N).filter (M ≤ ·)
  have hsum (x : ℕ) (hx : x ∈ T) :
      C * (1 / (x : ℝ)) ≤ Erdos878.H x / (x : ℝ) ^ 2 := by
    have hx0 : (0 : ℝ) < x := by
      exact_mod_cast (mem_Icc.mp (mem_filter.mp hx).1).1
    have hlt : C < Erdos878.H x / x := lt_of_not_ge (hM x (mem_filter.mp hx).2)
    exact (le_div_iff₀ (by positivity)).mpr (by
      calc
        C * (1 / (x : ℝ)) * (x : ℝ) ^ 2 = C * (x : ℝ) := by field_simp
        _ ≤ Erdos878.H x := (le_div_iff₀ hx0).mp hlt.le)
  have ht : (∑ x ∈ T, 1 / (x : ℝ)) + ∑ x ∈ Ico 1 M, (1 / (x : ℝ)) =
      ∑ x ∈ Icc 1 N, (1 / (x : ℝ)) := by
    classical
    have hs : (Icc 1 N).filter (fun x => ¬ M ≤ x) = Ico 1 M := by
      ext x
      simp only [mem_filter, mem_Icc, mem_Ico]
      omega
    rw [← hs, show T = (Icc 1 N).filter (M ≤ ·) by rfl, sum_filter_add_sum_filter_not]
  have harm : Real.log (N : ℝ) ≤ ∑ x ∈ Icc 1 N, (1 / (x : ℝ)) := by
    have h1 := log_add_one_le_harmonic N
    rw [harmonic_eq_sum_Icc] at h1
    push_cast at h1
    have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
    have hNext : (N : ℝ) ≤ (N : ℝ) + 1 := by linarith
    exact (Real.log_le_log hN0 hNext).trans (by simpa [one_div] using h1)
  have htotal :
      C * (∑ x ∈ Icc 1 N, (1 / (x : ℝ))) ≤
        4 * (8 / Real.log 2) * Real.log N + K := by
    rw [← ht, mul_add]
    refine add_le_add ?_ le_rfl
    rw [mul_sum]
    refine (sum_le_sum hsum).trans ?_
    refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => ?_)).trans (H_weighted N)
    unfold Erdos878.H
    positivity
  have hbound := (mul_le_mul_of_nonneg_left harm hC).trans htotal
  dsimp [C] at hbound
  linarith