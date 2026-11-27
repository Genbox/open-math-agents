import FormalConjectures.ErdosProblems.«878»
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Data.Fintype.Pigeonhole

/-! Simultaneous approximate prime powers and an average lower bound. -/

open Finset Filter

namespace OMA.Erdos878Average

private theorem division_bounds (n d : ℕ) (hd : 0 < d) :
    (n / d) * d ≤ n ∧ n < (n / d + 1) * d := by
  refine ⟨Nat.div_mul_le_self n d, ?_⟩
  have hm := Nat.mod_lt n hd
  have he := Nat.div_add_mod n d
  rw [Nat.add_mul, one_mul]
  calc
    n = n / d * d + n % d := by simpa [Nat.mul_comm] using he.symm
    _ < n / d * d + d := Nat.add_lt_add_left hm _

private theorem mantissa_compatible {x y a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hq : 1 ≤ x / a) (heq : x / a = (x * y) / (a * b)) :
    b ≤ 2 * y ∧ y ≤ 2 * b := by
  let q := x / a
  have hA := division_bounds x a ha
  have hB := division_bounds (x * y) (a * b) (Nat.mul_pos ha hb)
  rw [← heq] at hB
  change q * a ≤ x ∧ x < (q + 1) * a at hA
  change q * (a * b) ≤ x * y ∧ x * y < (q + 1) * (a * b) at hB
  have hq2 : q + 1 ≤ 2 * q := by omega
  have hl : q * b ≤ q * (2 * y) := by
    refine Nat.le_of_mul_le_mul_left (c := a) ?_ ha
    calc
      a * (q * b) = q * (a * b) := by ring
      _ ≤ x * y := hB.1
      _ ≤ ((q + 1) * a) * y := Nat.mul_le_mul_right _ hA.2.le
      _ ≤ ((2 * q) * a) * y := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hq2)
      _ = a * (q * (2 * y)) := by ring
  have hr : q * y ≤ q * (2 * b) := by
    refine Nat.le_of_mul_le_mul_left (c := a) ?_ ha
    calc
      a * (q * y) = (q * a) * y := by ring
      _ ≤ x * y := Nat.mul_le_mul_right _ hA.1
      _ ≤ (q + 1) * (a * b) := hB.2.le
      _ ≤ (2 * q) * (a * b) := Nat.mul_le_mul_right _ hq2
      _ = a * (q * (2 * b)) := by ring
  exact ⟨Nat.le_of_mul_le_mul_left hl (by omega), Nat.le_of_mul_le_mul_left hr (by omega)⟩

private theorem aligned_powers (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (L : ℕ) (hL : 0 < L) :
    ∃ y : ℕ, L ≤ y ∧ ∀ p ∈ S, ∃ a : ℕ, p ^ a ≤ 2 * y ∧ y ≤ 2 * p ^ a := by
  classical
  let M := S.sup id + 1
  let bin (n : ℕ) (p : ↥S) : Fin M :=
    ⟨2 ^ n / p.val ^ Nat.log p.val (2 ^ n), by
      have hpow := Nat.lt_pow_succ_log_self (hS p p.2).one_lt (2 ^ n)
      rw [pow_succ] at hpow
      have hq := (Nat.div_lt_iff_lt_mul (Nat.pow_pos (hS p p.2).pos)).mpr (by
        simpa [Nat.mul_comm] using hpow)
      exact hq.trans_le (by
        have hsup := Finset.le_sup (f := id) p.2
        exact hsup.trans (Nat.le_succ _))⟩
  let N := Fintype.card (↥S → Fin M)
  let boxes (i : Fin (N + 1)) : ↥S → Fin M := bin (L * i.val)
  obtain ⟨i, j, hij, hbox⟩ := Fintype.exists_ne_map_eq_of_card_lt boxes (by simp [N])
  have horder : ∃ i j : Fin (N + 1), i < j ∧ boxes i = boxes j := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, h, hbox⟩
    · exact ⟨j, i, h, hbox.symm⟩
  obtain ⟨i, j, hij, hbox⟩ := horder
  let u := L * i.val
  let v := L * j.val
  have huv : u + L ≤ v := by
    dsimp [u, v]
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hij)
  let y := 2 ^ (v - u)
  have hLy : L ≤ y := by
    have h : v - u ≤ (2 : ℕ) ^ (v - u) := (Nat.lt_pow_self (by decide : 1 < 2)).le
    exact (show L ≤ v - u by omega).trans h
  refine ⟨y, hLy, ?_⟩
  intro p hp
  let a := Nat.log p (2 ^ v) - Nat.log p (2 ^ u)
  have hlog : Nat.log p (2 ^ u) ≤ Nat.log p (2 ^ v) :=
    Nat.log_monotone (Nat.pow_le_pow_right (by decide) (by omega))
  have htwo : (2 : ℕ) ^ v = 2 ^ u * y := by
    dsimp [y]
    rw [← pow_add, Nat.add_sub_of_le (show u ≤ v by omega)]
  have hpw : p ^ Nat.log p (2 ^ v) = p ^ Nat.log p (2 ^ u) * p ^ a := by
    dsimp [a]
    rw [← pow_add, Nat.add_sub_of_le hlog]
  have he := congrArg Fin.val (congrFun hbox ⟨p, hp⟩)
  change 2 ^ u / p ^ Nat.log p (2 ^ u) = 2 ^ v / p ^ Nat.log p (2 ^ v) at he
  rw [hpw, htwo] at he
  have hp0 := (hS p hp).pos
  have hq : 1 ≤ 2 ^ u / p ^ Nat.log p (2 ^ u) := by
    exact (Nat.le_div_iff_mul_le (Nat.pow_pos hp0)).mpr (by
      simpa using Nat.pow_log_le_self p (by positivity : 2 ^ u ≠ 0))
  exact ⟨a, mantissa_compatible (Nat.pow_pos hp0) (Nat.pow_pos hp0) hq he⟩

private theorem many_multiples {p y : ℕ} (hp : 0 < p) (hle : p ≤ y) :
    (y : ℝ) / (2 * p) ≤ (((Ico (2 * y) (4 * y)).filter fun n => p ∣ n).card : ℝ) := by
  classical
  let f : ℕ ↪ ℕ :=
    ⟨fun j => (2 * y / p + (j + 1)) * p, fun i j h => by
      have he := Nat.eq_of_mul_eq_mul_right hp h
      omega⟩
  have hsub : (range (y / p)).map f ⊆ (Ico (2 * y) (4 * y)).filter (fun n => p ∣ n) := by
    intro n hn
    obtain ⟨j, hj, rfl⟩ := mem_map.mp hn
    have hj' := Nat.succ_le_of_lt (mem_range.mp hj)
    change (2 * y / p + (j + 1)) * p ∈ (Ico (2 * y) (4 * y)).filter (fun n => p ∣ n)
    refine mem_filter.mpr ⟨mem_Ico.mpr ⟨?_, ?_⟩, dvd_mul_left _ _⟩
    · exact ((division_bounds (2 * y) p hp).2.le).trans (Nat.mul_le_mul_right _ (by omega))
    · calc
        (2 * y / p + (j + 1)) * p ≤ (2 * y / p + y / p) * p :=
          Nat.mul_le_mul_right _ (Nat.add_le_add_left hj' _)
        _ = (2 * y / p) * p + (y / p) * p := Nat.add_mul ..
        _ ≤ 2 * y + y := Nat.add_le_add (Nat.div_mul_le_self _ _) (Nat.div_mul_le_self _ _)
        _ < 4 * y := by omega
  have hcard := card_le_card hsub
  rw [card_map, card_range] at hcard
  have hround : y ≤ 2 * (y / p) * p := by
    have hd := (division_bounds y p hp).2
    have hz : 1 ≤ y / p := (Nat.le_div_iff_mul_le hp).mpr (by simpa using hle)
    exact hd.le.trans (Nat.mul_le_mul_right _ (by omega))
  have hr : (y : ℝ) / (2 * p) ≤ ((y / p : ℕ) : ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hr' : (y : ℝ) ≤ 2 * ((y / p : ℕ) : ℝ) * p := by exact_mod_cast hround
    linarith only [hr', show (↑(y / p) : ℝ) * (2 * p) = 2 * ↑(y / p) * p by ring]
  exact hr.trans (by exact_mod_cast hcard)

private theorem average_lower (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {y : ℕ} (hy : 0 < y)
    (hlarge : ∀ p ∈ S, p ≤ y) (halign : ∀ p ∈ S, ∃ a : ℕ, p ^ a ≤ 2 * y ∧ y ≤ 2 * p ^ a) :
    (∑ p ∈ S, (1 / p : ℝ)) / 64 ≤ Erdos878.H (4 * y) / (4 * y : ℕ) := by
  classical
  let I := Ico (2 * y) (4 * y)
  let term (p n : ℕ) : ℝ := if p ∣ n then 1 / 8 else 0
  have hterms (p : ℕ) (hp : p ∈ S) : (y : ℝ) / 16 * (1 / p) ≤ ∑ n ∈ I, term p n := by
    have hm := many_multiples (hS p hp).pos (hlarge p hp)
    unfold term
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    calc
      (y : ℝ) / 16 * (1 / p) = (y : ℝ) / (2 * p) * (1 / 8) := by
        have hpos : (0 : ℝ) < p := by exact_mod_cast (hS p hp).pos
        field_simp; ring
      _ ≤ ((I.filter fun n => p ∣ n).card : ℝ) * (1 / 8) :=
        mul_le_mul_of_nonneg_right hm (by norm_num)
      _ = _ := by norm_cast
  have hswap (n : ℕ) (hn : n ∈ I) :
      ∑ p ∈ S, term p n ≤ (Erdos878.f n : ℝ) / n := by
    obtain ⟨hnl, hnr⟩ := mem_Ico.mp hn
    have hn0 : 0 < n := by omega
    rw [Erdos878.f, Nat.cast_sum, Finset.sum_div]
    unfold term
    rw [← sum_filter]
    refine (sum_le_sum fun p hp => ?_).trans
      (sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun p _ _ => by positivity))
    · have hp' := (mem_filter.mp hp).1
      obtain ⟨a, ha, hy'⟩ := halign p hp'
      have hlog := Nat.le_log_of_pow_le (hS p hp').one_lt (ha.trans hnl)
      have hpow := Nat.pow_le_pow_right (hS p hp').pos hlog
      have hbound : n ≤ 8 * p ^ Nat.log p n := by omega
      apply (le_div_iff₀ (by exact_mod_cast hn0)).mpr
      have hc : (n : ℝ) ≤ 8 * ((p ^ Nat.log p n : ℕ) : ℝ) := by exact_mod_cast hbound
      linarith
    · exact Nat.mem_primeFactors.mpr ⟨hS p (mem_filter.mp hp).1, (mem_filter.mp hp).2, hn0.ne'⟩
  have hsub : I ⊆ Ico 1 (4 * y) := by
    intro n hn
    obtain ⟨h₁, h₂⟩ := mem_Ico.mp hn
    exact mem_Ico.mpr ⟨by omega, h₂⟩
  have hmain : (y : ℝ) / 16 * (∑ p ∈ S, 1 / (p : ℝ)) ≤ Erdos878.H (4 * y) := by
    rw [Finset.mul_sum]
    calc
      ∑ p ∈ S, (y : ℝ) / 16 * (1 / p) ≤ ∑ p ∈ S, ∑ n ∈ I, term p n :=
        sum_le_sum hterms
      _ = ∑ n ∈ I, ∑ p ∈ S, term p n := sum_comm
      _ ≤ ∑ n ∈ I, (Erdos878.f n : ℝ) / n := sum_le_sum hswap
      _ ≤ Erdos878.H (4 * y) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have he : (∑ p ∈ S, (1 / p : ℝ)) / 64 * ((4 * y : ℕ) : ℝ) =
      (y : ℝ) / 16 * (∑ p ∈ S, (1 / p : ℝ)) := by
    push_cast
    ring
  exact (le_div_iff₀ (by positivity)).mpr (he.trans_le hmain)

private theorem prime_reciprocals (R : ℝ) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧ R < ∑ p ∈ S, (1 / p : ℝ) := by
  classical
  have hex : ∃ S : Finset Nat.Primes, R < ∑ p ∈ S, (1 / (p : ℕ) : ℝ) := by
    by_contra! h
    exact Nat.Primes.not_summable_one_div (summable_of_sum_le (fun _ => by positivity) h)
  obtain ⟨S, hS⟩ := hex
  let e : Nat.Primes ↪ ℕ := Function.Embedding.subtype _
  refine ⟨S.map e, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, _, rfl⟩ := mem_map.mp hp
    exact q.2
  · rw [Finset.sum_map]
    exact hS

end OMA.Erdos878Average

open OMA.Erdos878Average in
theorem OMA.solution : type_of% @Erdos878.erdos_878.variants.H_div_self_limsup_infinite := by
  intro C
  obtain ⟨S, hS, hsum⟩ := prime_reciprocals (64 * C)
  refine frequently_atTop.mpr fun n => ?_
  let L := n + S.sup id + 1
  obtain ⟨y, hy, halign⟩ := aligned_powers S hS L (by dsimp [L]; omega)
  have hlarge (p : ℕ) (hp : p ∈ S) : p ≤ y := by
    have hs : p ≤ S.sup id := Finset.le_sup (f := id) hp
    dsimp [L] at hy
    omega
  have hY : 0 < y := by dsimp [L] at hy; omega
  have hlow := average_lower S hS hY hlarge halign
  refine ⟨4 * y, by dsimp [L] at hy; omega, ?_⟩
  exact ((le_div_iff₀ (by norm_num : (0 : ℝ) < 64)).mpr (by linarith)).trans hlow