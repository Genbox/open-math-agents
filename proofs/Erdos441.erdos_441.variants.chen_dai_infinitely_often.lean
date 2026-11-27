import FormalConjectures.ErdosProblems.«441»
import Mathlib.NumberTheory.Primorial

/-! Chen and Dai's bounded least-common-multiple construction, with a scaled primorial. -/

open Finset Filter
open scoped BigOperators

namespace OMA.E441

def primorialStep (d : ℕ) : ℕ := 4 * primorial (2*d-1)

theorem step_pos (d : ℕ) : 0 < primorialStep d := by
  unfold primorialStep
  exact Nat.mul_pos (by decide) (primorial_pos _)

theorem step_ge {d : ℕ} (hd : 2 ≤ d) : 4*d ≤ primorialStep d := by
  exact Nat.mul_le_mul_left _ ((show d ≤ 2*d-1 by omega).trans le_primorial_self)

theorem step_le (d : ℕ) (hd : 2 ≤ d) : primorialStep d ≤ 4^(2*d) := by
  have h := Nat.mul_le_mul_left 4 (primorial_le_four_pow (2*d-1))
  rw [← pow_succ'] at h
  simpa [primorialStep, show 2*d-1+1=2*d by omega] using h

theorem prime_dvd_step {p d : ℕ} (hp : p.Prime) (h : p ≤ 2*d-1) :
    p ∣ primorialStep d :=
  dvd_mul_of_dvd_right (hp.dvd_primorial_iff.mpr h) _

def stages : ℕ → ℕ
  | 0 => 2
  | n+1 => stages n + primorialStep (stages n)

theorem stages_strict : StrictMono stages :=
  strictMono_nat_of_lt_succ (fun n => by
    change stages n < stages n + primorialStep (stages n)
    have := step_pos (stages n)
    omega)

theorem stage_lower (n : ℕ) : n+2 ≤ stages n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h : stages n < stages (n+1) := stages_strict (Nat.lt_succ_self n)
    change n+1+2 ≤ stages (n+1)
    omega

theorem stage_even (n : ℕ) : 2 ∣ stages n := by
  induction n with
  | zero => decide
  | succ n ih =>
    change 2 ∣ stages n + primorialStep (stages n)
    exact dvd_add ih (dvd_mul_of_dvd_left (by decide : 2 ∣ 4) _)

def middle (n : ℕ) : ℕ := primorialStep (stages n) - stages n

def indexN (n : ℕ) : ℕ := 2 * middle n ^ 2

theorem three_stage_le (n : ℕ) : 3*stages n ≤ middle n := by
  have h := step_ge (show 2 ≤ stages n by have := stage_lower n; omega)
  unfold middle
  omega

theorem middle_pos (n : ℕ) : 0 < middle n := by
  have h := three_stage_le n
  have := stage_lower n
  omega

theorem middle_add_stage (n : ℕ) : middle n + stages n = primorialStep (stages n) := by
  have h := step_ge (show 2 ≤ stages n by have := stage_lower n; omega)
  unfold middle
  omega

theorem middle_even (n : ℕ) : 2 ∣ middle n :=
  Nat.dvd_sub (dvd_mul_of_dvd_left (by decide : 2 ∣ 4) _) (stage_even n)

theorem congruence_stages {p i n : ℕ} (hp : p.Prime) (hpi : p ≤ 2*stages i-1) (hin : i ≤ n) :
    stages n ≡ stages i [MOD p] := by
  induction n, hin using Nat.le_induction with
  | base => rfl
  | succ n h hmod =>
    have hd := stages_strict.monotone h
    have hdiv := prime_dvd_step hp (show p ≤ 2*stages n-1 by omega)
    change stages n + primorialStep (stages n) ≡ stages i [MOD p]
    simpa using hmod.add (Nat.modEq_zero_iff_dvd.mpr hdiv)

theorem prime_dvd_shift {p i n : ℕ} (hp : p.Prime) (hpi : p ≤ 2*stages i-1) (hin : i ≤ n) :
    p ∣ middle n + stages i := by
  have hd := stages_strict.monotone hin
  have hdiv := prime_dvd_step hp (show p ≤ 2*stages n-1 by omega)
  have hsum : middle n + stages n ≡ 0 [MOD p] :=
    Nat.modEq_zero_iff_dvd.mpr (middle_add_stage n ▸ hdiv)
  exact Nat.modEq_zero_iff_dvd.mp (((congruence_stages hp hpi hin).add_left (middle n)).symm.trans hsum)

theorem lcm_le_of_common_dvd {a b D N : ℕ} (ha : 0 < a) (hDa : D ∣ a) (hDb : D ∣ b)
    (hprod : a*b ≤ D*N) (hD : 0 < D) : a.lcm b ≤ N := by
  have hG : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b ha
  have hDg : D ≤ a.gcd b := Nat.le_of_dvd hG (Nat.dvd_gcd hDa hDb)
  have h := (Nat.mul_le_mul_left (a.lcm b) hDg).trans
    (show a.lcm b * a.gcd b ≤ N*D by rw [mul_comm (a.lcm b), Nat.gcd_mul_lcm, mul_comm N]; exact hprod)
  exact Nat.le_of_mul_le_mul_right h hD

theorem base_mem {k a : ℕ} (hk : 0 < k) :
    a ∈ Erdos441.erdosConstruction (2*k^2) ↔
      (1 ≤ a ∧ a ≤ k) ∨ ∃ b, 1 ≤ b ∧ b ≤ k ∧ a = 2*b := by
  simp only [Erdos441.erdosConstruction, mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨ha,_⟩,h | ⟨he,h⟩⟩
    · exact Or.inl ⟨ha,by
        by_contra! hbad
        have hp := Nat.pow_lt_pow_left hbad (by decide : (2:ℕ) ≠ 0)
        omega⟩
    · obtain ⟨b,rfl⟩ := he
      refine Or.inr ⟨b,by omega,?_ ,rfl⟩
      by_contra! hb
      have hp := Nat.pow_lt_pow_left hb (by decide : (2:ℕ) ≠ 0)
      simp only [mul_pow] at h
      norm_num at h
      omega
  · rintro (⟨ha,hak⟩ | ⟨b,hb,hbk,rfl⟩)
    · have H := Nat.pow_le_pow_left hak 2
      exact ⟨⟨ha,by nlinarith⟩,Or.inl (Nat.mul_le_mul_left 2 H)⟩
    · have H := Nat.pow_le_pow_left hbk 2
      exact ⟨⟨by omega,by nlinarith⟩,Or.inr ⟨dvd_mul_right _ _,by nlinarith⟩⟩

theorem base_dvd_double {k a : ℕ} (hk : 0 < k) (h : a ∈ Erdos441.erdosConstruction (2*k^2)) :
    ∃ b, 1 ≤ b ∧ b ≤ k ∧ a ∣ 2*b := by
  rcases (base_mem hk).mp h with ⟨ha,hak⟩ | ⟨b,hb,hbk,rfl⟩
  · exact ⟨a,ha,hak,dvd_mul_left _ _⟩
  · exact ⟨b,hb,hbk,dvd_refl _⟩

theorem lcm_monotone_dvd {a b c d : ℕ} (ha : a ∣ c) (hb : b ∣ d) :
    a.lcm b ∣ c.lcm d :=
  Nat.lcm_dvd (ha.trans (Nat.dvd_lcm_left _ _)) (hb.trans (Nat.dvd_lcm_right _ _))

theorem base_pair {n a b : ℕ}
    (ha : a ∈ Erdos441.erdosConstruction (indexN n))
    (hb : b ∈ Erdos441.erdosConstruction (indexN n)) :
    a.lcm b ≤ indexN n := by
  obtain ⟨u,_,hu,hua⟩ := base_dvd_double (middle_pos n) ha
  obtain ⟨v,_,hv,hvb⟩ := base_dvd_double (middle_pos n) hb
  have hpos : 0 < (2*u).lcm (2*v) := Nat.lcm_pos (by positivity) (by positivity)
  apply (Nat.le_of_dvd hpos (lcm_monotone_dvd hua hvb)).trans
  rw [indexN,Nat.lcm_mul_left]
  have H := Nat.mul_le_mul hu hv
  exact Nat.mul_le_mul_left _ ((Nat.lcm_le_mul (by omega) (by omega)).trans (by simpa [pow_two] using H))

theorem extra_pair {n i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) :
    (2*(middle n+stages i)).lcm (2*(middle n+stages j)) ≤ indexN n := by
  rw [indexN,Nat.lcm_mul_left]
  apply Nat.mul_le_mul_left
  have h₁ := stages_strict.monotone hi
  have h₂ := stages_strict.monotone hj
  have h3 := three_stage_le n
  have hsq := Nat.pow_le_pow_left
    (show 3*(middle n+stages n) ≤ 4*middle n by omega) 2
  have hbound : (middle n+stages n)^2 ≤ 2*middle n^2 := by
    simp only [mul_pow] at hsq
    norm_num at hsq
    omega
  refine lcm_le_of_common_dvd (D := 2) (by have := middle_pos n; omega)
    (dvd_add (middle_even n) (stage_even i)) (dvd_add (middle_even n) (stage_even j)) ?_ (by decide)
  calc
    _ ≤ (middle n+stages n)^2 := by
      simpa [pow_two] using Nat.mul_le_mul (Nat.add_le_add_left h₁ (middle n))
        (Nat.add_le_add_left h₂ (middle n))
    _ ≤ _ := hbound

theorem extra_base {n i a : ℕ} (hi : i ≤ n)
    (ha : a ∈ Erdos441.erdosConstruction (indexN n)) :
    (2*(middle n+stages i)).lcm a ≤ indexN n := by
  obtain ⟨b,hb,hbk,hab⟩ := base_dvd_double (middle_pos n) ha
  have hp : 0 < (2*(middle n+stages i)).lcm (2*b) :=
    Nat.lcm_pos (by have := middle_pos n; omega) (by omega)
  apply (Nat.le_of_dvd hp (lcm_monotone_dvd (dvd_refl _) hab)).trans
  rw [indexN,Nat.lcm_mul_left]
  apply Nat.mul_le_mul_left
  let k := middle n
  let d := stages i
  let j := k-b
  have hj : b+j = k := by omega
  have hd : 2 ≤ d := by have := stage_lower i; omega
  have hdk : 3*d ≤ k := (Nat.mul_le_mul_left 3 (stages_strict.monotone hi)).trans (three_stage_le n)
  change (k+d).lcm b ≤ k^2
  by_cases hFar : d ≤ j
  · apply (Nat.lcm_le_mul (by omega) (by omega)).trans
    have H : b+d ≤ k := by omega
    have hM := Nat.mul_le_mul_left (k+d) H
    nlinarith
  · obtain ⟨p,hp,hdiv⟩ := (d+j).exists_prime_and_dvd (by omega)
    have hpp : p ≤ 2*d-1 := by
      have h := Nat.le_of_dvd (show 0 < d+j by omega) hdiv
      omega
    have hp₁ : p ∣ k+d := prime_dvd_shift hp hpp hi
    have hp₂ : p ∣ b := by
      have h := Nat.dvd_sub hp₁ hdiv
      rwa [show k+d-(d+j)=b by omega] at h
    refine lcm_le_of_common_dvd (by omega) hp₁ hp₂ ?_ hp.pos
    have H := Nat.mul_le_mul_left (k+d) hbk
    have hp2 : 2 ≤ p := hp.two_le
    have hM := Nat.mul_le_mul_right (k^2) hp2
    have hD : d ≤ k := by omega
    have hP := Nat.mul_le_mul_right k hD
    nlinarith

def extra (n : ℕ) : Finset ℕ :=
  (range (n+1)).image (fun i => 2*(middle n+stages i))

theorem extra_card (n : ℕ) : (extra n).card = n+1 := by
  unfold extra
  rw [card_image_of_injective,card_range]
  intro i j h
  change 2*(middle n+stages i) = 2*(middle n+stages j) at h
  apply stages_strict.injective
  omega

theorem extra_disjoint (n : ℕ) : Disjoint (Erdos441.erdosConstruction (indexN n)) (extra n) := by
  refine disjoint_left.mpr ?_
  intro a ha hx
  obtain ⟨i,_,rfl⟩ := mem_image.mp hx
  have hd := stage_lower i
  rcases (base_mem (middle_pos n)).mp ha with h | ⟨b,_,hb,he⟩
  · omega
  · omega

theorem extra_in_range {n a : ℕ} (ha : a ∈ extra n) : a ∈ Icc 1 (indexN n) := by
  obtain ⟨i,hi,rfl⟩ := mem_image.mp ha
  have hin : i ≤ n := by have := mem_range.mp hi; omega
  have hd := stages_strict.monotone hin
  have hk := three_stage_le n
  have hs := stage_lower n
  rw [mem_Icc,indexN]
  constructor <;> nlinarith

theorem lower_construct (n : ℕ) :
    (Erdos441.erdosConstruction (indexN n)).card + (n+1) ≤ Erdos441.g (indexN n) := by
  classical
  let B := Erdos441.erdosConstruction (indexN n)
  let A := B ∪ extra n
  unfold Erdos441.g
  apply le_csSup ?_ ?_
  · refine ⟨(indexN n),?_⟩
    rintro k ⟨S,hS,_,rfl⟩
    have h := card_le_card hS
    simpa using h
  have hc : A.card = B.card+(n+1) := by
    dsimp [A,B]
    rw [card_union_of_disjoint (extra_disjoint n),extra_card]
  refine ⟨A,?_,?_,hc⟩
  · intro a ha
    rcases mem_union.mp ha with hb | hx
    · exact (mem_filter.mp hb).1
    · exact extra_in_range hx
  · intro a ha b hb
    rcases mem_union.mp ha with ha | ha <;> rcases mem_union.mp hb with hb | hb
    · exact base_pair ha hb
    · obtain ⟨j,hj,rfl⟩ := mem_image.mp hb
      rw [Nat.lcm_comm]
      exact extra_base (Nat.le_of_lt_succ (mem_range.mp hj)) ha
    · obtain ⟨i,hi,rfl⟩ := mem_image.mp ha
      exact extra_base (Nat.le_of_lt_succ (mem_range.mp hi)) hb
    · obtain ⟨i,hi,rfl⟩ := mem_image.mp ha
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hb
      exact extra_pair (Nat.le_of_lt_succ (mem_range.mp hi)) (Nat.le_of_lt_succ (mem_range.mp hj))

noncomputable def tower : ℕ → ℝ
  | 0 => 1
  | n+1 => Real.exp (tower n)

theorem log_iterate_le {x : ℝ} {h : ℕ} (hx : x ≤ tower h) :
    ∃ k ≤ h, Real.log^[k] x ≤ 1 := by
  induction h generalizing x with
  | zero => exact ⟨0,le_rfl,hx⟩
  | succ h ih =>
    by_cases xle : x ≤ 1
    · exact ⟨0,Nat.zero_le _,xle⟩
    have xpos : 0 < x := by linarith
    have logle : Real.log x ≤ tower h := (Real.log_le_iff_le_exp xpos).mpr hx
    obtain ⟨k,hk,hw⟩ := ih logle
    exact ⟨k+1,Nat.succ_le_succ hk,by rwa [Function.iterate_succ_apply]⟩

theorem log_step (d : ℕ) (hd : 2 ≤ d) :
    Real.log (primorialStep d : ℝ) ≤ 4*(d : ℝ)*Real.log 2 := by
  have hpos : 0 < (primorialStep d : ℝ) := by exact_mod_cast step_pos d
  have h := Real.log_le_log hpos
    (show (primorialStep d : ℝ) ≤ (4 : ℝ)^(2*d : ℕ) by exact_mod_cast step_le d hd)
  rw [Real.log_pow, show Real.log 4 = 2*Real.log 2 by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num] at h
  push_cast at h
  nlinarith only [h]

theorem log_twelve_lt : Real.log 12 < 2.6 := by
  rw [show (12 : ℝ) = 8*(3/2) by norm_num,Real.log_mul (by norm_num) (by norm_num),
    show (8 : ℝ)=2^3 by norm_num, Real.log_pow]
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ)<3/2 by norm_num)
  linarith only [Real.log_two_lt_d9,h]

theorem log_scaled_next (n : ℕ) :
    Real.log (6*(stages (n+1) : ℝ)) ≤ 6*(stages n : ℝ) := by
  have hd : 2 ≤ stages n := by have := stage_lower n; omega
  have hP := step_ge hd
  have hle : 6*stages (n+1) ≤ 12*primorialStep (stages n) := by
    change 6*(stages n+primorialStep (stages n)) ≤ _
    omega
  have hpos : (0:ℝ) < 6*(stages (n+1) : ℝ) := by
    have H := stage_lower (n+1)
    exact_mod_cast (show 0 < 6*stages (n+1) by omega)
  have h := Real.log_le_log hpos (show 6*(stages (n+1) : ℝ) ≤
    12*(primorialStep (stages n) : ℝ) by exact_mod_cast hle)
  rw [Real.log_mul (x := 12) (y := (primorialStep (stages n) : ℝ))
    (by norm_num) (by exact_mod_cast (step_pos (stages n)).ne')] at h
  have hlog := log_step (stages n) hd
  have hd' : (2:ℝ) ≤ stages n := by exact_mod_cast hd
  have hm : 4*(stages n : ℝ)*Real.log 2 ≤ 4*(stages n : ℝ) := by
    simpa using mul_le_mul_of_nonneg_left (show Real.log 2 ≤ 1 by linarith [Real.log_two_lt_d9])
      (show (0:ℝ) ≤ 4*(stages n : ℝ) by positivity)
  linarith only [h,hlog,log_twelve_lt,hd',hm]

theorem scaled_stage_tower (n : ℕ) : 6*(stages n : ℝ) ≤ tower (n+2) := by
  induction n with
  | zero =>
    norm_num [stages,tower]
    apply (Real.log_le_iff_le_exp (by norm_num)).mp
    linarith only [log_twelve_lt, Real.exp_one_gt_d9]
  | succ n ih =>
    change 6*(stages (n+1) : ℝ) ≤ Real.exp (tower (n+2))
    apply (Real.log_le_iff_le_exp ?_).mp ((log_scaled_next n).trans ih)
    have H := stage_lower (n+1)
    exact_mod_cast (show 0 < 6*stages (n+1) by omega)

theorem log_N_le (n : ℕ) : Real.log (indexN n : ℝ) ≤ 6*(stages n : ℝ) := by
  have hn : 2 ≤ stages n := by have := stage_lower n; omega
  have hnr : (2:ℝ) ≤ stages n := by exact_mod_cast hn
  have hk : 0 < (middle n : ℝ) := by exact_mod_cast middle_pos n
  have hle : (middle n : ℝ) ≤ primorialStep (stages n) := by
    exact_mod_cast (Nat.sub_le (primorialStep (stages n)) (stages n))
  have h := (Real.log_le_log hk hle).trans (log_step (stages n) hn)
  unfold indexN
  push_cast
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow]
  norm_num
  have hm : (8*(stages n : ℝ)+1)*Real.log 2 ≤ (8*(stages n : ℝ)+1)*0.7 :=
    mul_le_mul_of_nonneg_left (by linarith only [Real.log_two_lt_d9]) (by positivity)
  linarith only [h, hm, hnr]

theorem log_star_bound (n : ℕ) : Real.iteratedLog (indexN n : ℝ) ≤ n+3 := by
  have ht : (indexN n : ℝ) ≤ tower (n+3) := by
    apply (Real.log_le_iff_le_exp ?_).mp ((log_N_le n).trans (scaled_stage_tower n))
    unfold indexN
    exact_mod_cast (show 0 < 2*middle n ^ 2 from Nat.mul_pos (by decide) (Nat.pow_pos (middle_pos n)))
  obtain ⟨k,hk,hw⟩ := log_iterate_le ht
  exact (Nat.sInf_le hw).trans hk

end OMA.E441

theorem OMA.solution : type_of% @Erdos441.erdos_441.variants.chen_dai_infinitely_often := by
  rw [frequently_atTop]
  intro N
  refine ⟨OMA.E441.indexN N,?_ ,?_⟩
  · have h := OMA.E441.three_stage_le N
    have hl := OMA.E441.stage_lower N
    unfold OMA.E441.indexN
    nlinarith
  · have h := OMA.E441.lower_construct N
    have ht := OMA.E441.log_star_bound N
    omega