import FormalConjectures.GreensOpenProblems.«38»
import Mathlib.Analysis.Fourier.ZMod

/-! The Fourier certificate for Lovász's seven-cycle bound. -/

open Finset Green38 ComplexConjugate
open scoped Pointwise
namespace CycleFourier

private noncomputable def c := Real.cos (Real.pi/7)
private theorem cpos : 0 < c :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

private noncomputable abbrev χ := (ZMod.stdAddChar : AddChar (ZMod 7) ℂ)
private noncomputable def weight (k : ZMod 7) := 1 + (χ k).re/c

private theorem char_re (k : ZMod 7) : (χ k).re = Real.cos (2*Real.pi*k.val/7) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_eq_circleExp, Circle.coe_exp]
  rw [Complex.exp_re]
  norm_num
  ring_nf

private theorem w_nonneg (k : ZMod 7) : 0 ≤ weight k := by
  have hp := Real.pi_pos
  have hk := k.val_lt
  have he : 0 ≤ Real.pi/7 := by positivity
  have hb : -c ≤ Real.cos (2*Real.pi*k.val/7) := by
    rw [show -c = Real.cos (Real.pi-Real.pi/7) by rw [Real.cos_pi_sub]; rfl]
    by_cases h : k.val ≤ 3
    · have hk' : (k.val:ℝ) ≤ 3 := by exact_mod_cast h
      apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith)
      nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hk')]
    · have h4 : (4:ℝ) ≤ k.val := by exact_mod_cast (show 4 ≤ k.val by omega)
      have h7 : (k.val:ℝ) ≤ 7 := by exact_mod_cast (Nat.le_of_lt hk)
      rw [← Real.cos_two_pi_sub (2*Real.pi*k.val/7)]
      apply Real.cos_le_cos_of_nonneg_of_le_pi _ (by linarith)
      · nlinarith [mul_nonneg hp.le (sub_nonneg.mpr h4)]
      · nlinarith [mul_nonneg hp.le (sub_nonneg.mpr h7)]
  rw [weight,char_re]
  have h := (le_div_iff₀ cpos).mpr (show (-1)*c ≤ _ by linarith [hb])
  linarith

private theorem char_neg (k : ZMod 7) : χ (-k) = conj (χ k) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

private theorem char_sum (d : ZMod 7) : (∑ k : ZMod 7, χ (k*d)) = if d=0 then 7 else 0 := by
  simpa using AddChar.sum_mulShift d (ZMod.isPrimitive_stdAddChar 7)

private noncomputable def kernel (d : ZMod 7) := ∑ k : ZMod 7, (weight k:ℂ)*χ (k*d)

private theorem formula (d : ZMod 7) : kernel d =
    (if d=0 then 7 else 0) + ((if d+1=0 then 7 else 0) +
      (if d-1=0 then 7 else 0))/(2*(c:ℂ)) := by
  calc
    _ = ∑ k : ZMod 7, (χ (k*d) + (χ (k*(d+1)) + χ (k*(d-1)))/(2*(c:ℂ))) := by
      apply sum_congr rfl
      intro k _
      rw [weight, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one, Complex.re_eq_add_conj,
        mul_add, mul_sub, mul_one, sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
        char_neg]
      ring
    _ = _ := by rw [sum_add_distrib, ← sum_div, sum_add_distrib, char_sum, char_sum, char_sum]

private theorem kernel_zero : kernel 0 = 7 := by
  simp [formula, show (1:ZMod 7) ≠ 0 by decide]

private theorem kernel_far {d : ZMod 7} (h : d ∉ ({-1,0,1} : Finset (ZMod 7))) :
    kernel d = 0 := by
  simp only [mem_insert, mem_singleton, not_or] at h
  have h1 : d+1 ≠ 0 := fun he => h.1 (by linear_combination he)
  have h2 : d-1 ≠ 0 := sub_ne_zero.mpr h.2.2
  simp [formula,h.2.1,h1,h2]


private abbrev Word (n : ℕ) := Fin n → ZMod 7
private noncomputable def W {n : ℕ} (k : Word n) := ∏ i, weight (k i)
private noncomputable def phase {n : ℕ} (k x : Word n) := ∏ i, χ (k i*x i)
private noncomputable def K {n : ℕ} (x y : Word n) : ℂ := ∏ i, kernel (x i - y i)
private noncomputable def energy {n : ℕ} (A : Finset (Word n)) (k : Word n) : ℝ :=
  W k * Complex.normSq (∑ x ∈ A, phase k x)

private theorem sum_phase {n : ℕ} (x y : Word n) :
    (∑ k : Word n, (W k:ℂ)*phase k x*conj (phase k y)) = K x y := by
  classical
  unfold W phase K kernel
  simp only [Complex.ofReal_prod, map_prod, ← Finset.prod_mul_distrib]
  calc
    _ = ∑ k : Word n, ∏ i, (weight (k i):ℂ)*χ (k i*(x i-y i)) := by
      apply sum_congr rfl
      intro k _
      apply prod_congr rfl
      intro i _
      rw [mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, char_neg, mul_assoc]
    _ = _ := by rw [prod_univ_sum,Fintype.piFinset_univ]

private theorem energy_expand {n : ℕ} (A : Finset (Word n)) :
    ((∑ k : Word n, energy A k : ℝ):ℂ) = ∑ x ∈ A, ∑ y ∈ A, K x y := by
  classical
  rw [Complex.ofReal_sum]
  calc
    _ = ∑ k : Word n, ∑ x ∈ A, ∑ y ∈ A, (W k:ℂ)*phase k x*conj (phase k y) := by
      apply sum_congr rfl
      intro k _
      rw [energy, Complex.ofReal_mul, ← Complex.mul_conj, map_sum]
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      ring
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro x _
      rw [sum_comm]
      exact sum_congr rfl (fun y _ => sum_phase x y)

private theorem diag {n : ℕ} (A : Finset (Word n)) (hA : IntersectsOnlyAtZero A)
    {x y : Word n} (hx : x ∈ A) (hy : y ∈ A) :
    K x y = if x=y then (7:ℂ)^n else 0 := by
  classical
  by_cases hh : x=y
  · subst y; simp [K,kernel_zero]
  · have hmem : x-y ∈ A-A := Finset.mem_sub.mpr ⟨x,hx,y,hy,rfl⟩
    have ht : ¬ ∀ i, (x-y) i ∈ ({-1,0,1} : Finset (ZMod 7)) :=
      fun h => hh (sub_eq_zero.mp (hA _ hmem h))
    obtain ⟨i,hi⟩ := not_forall.mp ht
    rw [if_neg hh]
    exact prod_eq_zero (mem_univ i) (kernel_far hi)

private theorem card_bound {n : ℕ} {A : Finset (Word n)} (hA : IntersectsOnlyAtZero A) :
    (A.card:ℝ) ≤ C₂^n := by
  classical
  have hsum : ∑ k : Word n, energy A k = A.card*(7:ℝ)^n := by
    apply Complex.ofReal_injective
    rw [energy_expand]
    simp only [Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_pow, Complex.ofReal_ofNat]
    calc
      _ = ∑ x ∈ A, ∑ y ∈ A, (if x=y then (7:ℂ)^n else 0) := by
        exact sum_congr rfl fun x hx => sum_congr rfl fun y hy => diag A hA hx hy
      _ = _ := by simp
  have hpos (k : Word n) : 0 ≤ energy A k := mul_nonneg
    (Finset.prod_nonneg (fun i _ => w_nonneg (k i))) (Complex.normSq_nonneg _)
  have hb := (single_le_sum (fun k _ => hpos k) (mem_univ (0 : Word n))).trans_eq hsum
  have h0 : energy A 0 = (1+1/c)^n*((A.card:ℝ)*(A.card:ℝ)) := by
    simp [energy,W,weight,phase,Complex.normSq_natCast]
  rw [h0] at hb
  have hw : 0 < 1+1/c := by have := cpos; positivity
  have hbase : C₂ = 7/(1+1/c) := by
    change 7*c/(1+c) = 7/(1+1/c)
    field_simp [ne_of_gt cpos]
    rw [add_comm c 1]
  rw [hbase,div_pow,le_div_iff₀ (pow_pos hw _)]
  rcases eq_or_lt_of_le (Nat.cast_nonneg (α:=ℝ) A.card) with he|he
  · rw [← he,zero_mul]; positivity
  · exact le_of_mul_le_mul_left (a:= (A.card:ℝ)) (by nlinarith [hb]) he

end CycleFourier

theorem OMA.solution : type_of% @Green38.green_38.variants.best_upper := by
  intro ε hε
  apply Filter.Eventually.of_forall
  intro n
  have hmem := Nat.sSup_mem (show (Green38.ValidCardinalities n).Nonempty from
    ⟨0,Green38.green_38.test_zero_mem_validCardinalities⟩) Green38.green_38.test_bound_above
  obtain ⟨A,hA,he⟩ := hmem
  have hbound := CycleFourier.card_bound hA
  rw [he] at hbound
  apply hbound.trans
  apply pow_le_pow_left₀ _ (by linarith)
  change 0 ≤ 7*CycleFourier.c/(1+CycleFourier.c)
  have := CycleFourier.cpos
  positivity