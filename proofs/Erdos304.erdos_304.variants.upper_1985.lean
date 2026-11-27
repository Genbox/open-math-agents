import FormalConjectures.ErdosProblems.«304»

/-!
Use products of the odd integers `2^i + 1` to obtain divisors with closely
spaced logarithms. The multiplicative gaps shrink toward the center of
the divisor range, which bounds the length of greedy divisor expansions.

The bound is due to M. D. Vose, Egyptian fractions (1985).
Credit: @Genbox.
-/

open Filter Finset Real
open scoped Asymptotics

namespace OMA

private noncomputable def weight (i : ℕ) : ℝ := log (1 + ((2 : ℝ)^i)⁻¹)

private def denom (k : ℕ) : ℕ :=
  2^(4*k^2) * ∏ i ∈ Icc 1 k, (2^i+1)

private theorem weight_pos (i : ℕ) : 0 < weight i :=
  log_pos (by
    have h : 0 < ((2 : ℝ)^i)⁻¹ := by positivity
    linarith)

private theorem weight_double (i : ℕ) : weight i ≤ 2 * weight (i+1) := by
  unfold weight
  have hpos : 0 < 1 + ((2 : ℝ)^i)⁻¹ := by positivity
  have hpos' : 0 < 1 + ((2 : ℝ)^(i+1))⁻¹ := by positivity
  have h : 1 + ((2 : ℝ)^i)⁻¹ ≤ (1 + ((2 : ℝ)^(i+1))⁻¹)^2 := by
    rw [pow_succ (2:ℝ) i, mul_inv]
    norm_num
    nlinarith [sq_nonneg (((2 : ℝ)^i)⁻¹)]
  have hlog := (log_le_log_iff hpos (pow_pos hpos' 2)).mpr h
  simpa only [log_pow, Nat.cast_ofNat] using hlog

private theorem log_two_le_twice_weight : log 2 ≤ 2 * weight 1 := by
  have h := (log_le_log_iff (by norm_num : 0 < (2 : ℝ))
    (by norm_num : 0 < (3/2 : ℝ)^2)).mpr (by norm_num : (2 : ℝ) ≤ (3/2)^2)
  simpa only [weight, pow_one, log_pow, Nat.cast_ofNat, show 1 + (2:ℝ)⁻¹ = 3/2 by norm_num]
    using h

private theorem interval_succ {j : ℕ} : Icc 1 (j+1) = insert (j+1) (Icc 1 j) := by
  ext i
  simp only [mem_insert, mem_Icc]
  omega

private theorem log_two_le_total {j : ℕ} (hj : 0 < j) :
    log 2 ≤ (∑ i ∈ Icc 1 j, weight i) + weight j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rw [interval_succ, sum_insert (by simp)]
    by_cases hz : j = 0
    · subst j
      simpa [two_mul] using log_two_le_twice_weight
    · linarith [ih (by omega), weight_double j]

private theorem subset_approx {j : ℕ} (hj : 0 < j) {x : ℝ}
    (hx : 0 ≤ x) (hmax : x ≤ ∑ i ∈ Icc 1 j, weight i) :
    ∃ A ⊆ Icc 1 j, ∑ i ∈ A, weight i ≤ x ∧ x - (∑ i ∈ A, weight i) ≤ weight j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rw [interval_succ, sum_insert (by simp)] at hmax
    by_cases hlast : x ≤ ∑ i ∈ Icc 1 j, weight i
    · by_cases hz : 0 < j
      · obtain ⟨A, hA, hlow, hgap⟩ := ih hz hlast
        have hAs : A ⊆ Icc 1 (j+1) := by
          rw [interval_succ]
          exact hA.trans (subset_insert _ _)
        by_cases ha : weight (j+1) ≤ x - ∑ i ∈ A, weight i
        · have hnot : j+1 ∉ A := fun h => by simpa using hA h
          refine ⟨insert (j+1) A, insert_subset (by simp) hAs, ?_⟩
          rw [sum_insert hnot]
          constructor <;> linarith [weight_double j]
        · exact ⟨A, hAs, hlow, by linarith⟩
      · have hz0 : j = 0 := by omega
        subst j
        simp at hlast
        refine ⟨∅, empty_subset _, by simpa using hx, ?_⟩
        simp
        linarith [weight_pos 1]
    · refine ⟨Icc 1 j, ?_, ?_, ?_⟩
      · rw [interval_succ]
        exact subset_insert _ _
      · exact le_of_not_ge hlast
      · linarith

private theorem adjust_dvd {k E : ℕ} {J : Finset ℕ} (hJ : J ⊆ Icc 1 k)
    (hE : E ≤ 4*k^2) : (2^(E - ∑ i ∈ J, i) * ∏ i ∈ J, (2^i+1) : ℕ) ∣ denom k := by
  unfold denom
  exact Nat.mul_dvd_mul (pow_dvd_pow _ (by omega)) (prod_dvd_prod_of_subset _ _ _ hJ)

private theorem adjust_log {E : ℕ} {J : Finset ℕ} (hE : ∑ i ∈ J, i ≤ E) :
    log ((2^(E - ∑ i ∈ J, i) * ∏ i ∈ J, (2^i+1) : ℕ) : ℝ) =
      (E:ℝ)*log 2 + ∑ i ∈ J, weight i := by
  have hone (i : ℕ) : log ((2:ℝ)^i+1) = (i:ℝ)*log 2 + weight i := by
    rw [weight, ← log_pow, ← log_mul (by positivity) (by positivity)]
    congr 1
    rw [mul_add, mul_one, mul_inv_cancel₀ (by positivity)]
  push_cast
  rw [log_mul (by positivity) (by positivity), log_pow, log_prod (fun i hi => by positivity)]
  simp_rw [hone]
  rw [sum_add_distrib, ← sum_mul, Nat.cast_sub hE, Nat.cast_sum]
  ring

private theorem denom_lower (k : ℕ) : 2^(4*k^2) ≤ denom k := by
  unfold denom
  have hp : 0 < ∏ i ∈ Icc 1 k, ((2:ℕ)^i+1) := by positivity
  exact Nat.le_mul_of_pos_right _ hp

private theorem denom_upper {k : ℕ} (hk : 0 < k) : denom k ≤ 2^(6*k^2) := by
  have hsum : ∑ i ∈ Icc 1 k, (i+1) ≤ 2*k^2 := by
    calc
      _ ≤ ∑ _i ∈ Icc 1 k, (k+1) := sum_le_sum (fun i hi => by
        have := (mem_Icc.mp hi).2
        omega)
      _ = k*(k+1) := by simp [Nat.card_Icc]
      _ ≤ _ := by nlinarith
  calc
    denom k ≤ 2^(4*k^2) * ∏ i ∈ Icc 1 k, (2:ℕ)^(i+1) := by
      apply Nat.mul_le_mul_left
      apply prod_le_prod'
      intro i hi
      rw [pow_succ]
      have hp : 0 < (2:ℕ)^i := by positivity
      omega
    _ = 2^(4*k^2 + ∑ i ∈ Icc 1 k, (i+1)) := by rw [pow_add, ← prod_pow_eq_pow_sum]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

private theorem adjust_range {j E : ℕ} {J : Finset ℕ} (hJ : J ⊆ Icc 1 j)
    (hE : j^2 ≤ E) : ∑ i ∈ J, i ≤ E := by
  have hcard : J.card ≤ j := (card_le_card hJ).trans (by simp [Nat.card_Icc])
  calc
    _ ≤ ∑ _i ∈ J, j := sum_le_sum (fun i hi => (mem_Icc.mp (hJ hi)).2)
    _ = J.card * j := by simp
    _ ≤ _ := (Nat.mul_le_mul_right j hcard).trans (by simpa [pow_two] using hE)

-- Approximate the logarithmic mantissa from below, then from above by complementation.
private theorem log_bracket {k j E : ℕ} {x : ℝ}
    (hj : 0 < j) (hjk : j ≤ k) (he : j^2 ≤ E) (hek : E+1 ≤ 4*k^2)
    (hlo : (E:ℝ)*log 2 ≤ log x) (hhi : log x ≤ ((E:ℝ)+1)*log 2) :
    ∃ l u : ℕ, l ∣ denom k ∧ u ∣ denom k ∧ 0 < l ∧ 0 < u ∧
      log (l : ℝ) ≤ log x ∧ log x ≤ log (u : ℝ) ∧
      log x - log (l : ℝ) ≤ weight j ∧ log (u : ℝ) - log x ≤ weight j := by
  classical
  let t := log x - (E:ℝ)*log 2
  let T := ∑ i ∈ Icc 1 j, weight i
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht' : t ≤ log 2 := by dsimp [t]; linarith
  have hT : log 2 ≤ T + weight j := log_two_le_total hj
  have hbelow : ∃ A ⊆ Icc 1 j, (∑ i ∈ A, weight i) ≤ t ∧ t - (∑ i ∈ A, weight i) ≤ weight j := by
    by_cases h : t ≤ T
    · exact subset_approx hj ht h
    · exact ⟨Icc 1 j, Subset.rfl, by dsimp [T] at h; linarith,
        by change t - T ≤ _; linarith⟩
  obtain ⟨A, hA, hAlo, hAhi⟩ := hbelow
  let l : ℕ := 2^(E - ∑ i ∈ A, i) * ∏ i ∈ A, (2^i+1)
  have hls : l ∣ denom k := adjust_dvd (hA.trans (Icc_subset_Icc_right hjk)) (by omega)
  have hlpos : 0 < l := by unfold l; positivity
  have hllog : log (l:ℝ) = (E:ℝ)*log 2 + ∑ i ∈ A, weight i := adjust_log (adjust_range hA he)
  have hl : log (l:ℝ) ≤ log x := by dsimp [t] at hAlo; linarith
  have hlg : log x - log (l:ℝ) ≤ weight j := by dsimp [t] at hAhi; linarith
  by_cases h : t ≤ T
  · obtain ⟨B, hB, hBlo, hBhi⟩ := subset_approx hj (show 0 ≤ T - t by linarith)
      (show T - t ≤ ∑ i ∈ Icc 1 j, weight i by change T - t ≤ T; linarith)
    let C := Icc 1 j \ B
    have hC : C ⊆ Icc 1 j := sdiff_subset
    have hcs : (∑ i ∈ C, weight i) = T - ∑ i ∈ B, weight i :=
      (eq_sub_iff_add_eq).mpr (sum_sdiff hB)
    let u : ℕ := 2^(E - ∑ i ∈ C, i) * ∏ i ∈ C, (2^i+1)
    have hu : u ∣ denom k := adjust_dvd (hC.trans (Icc_subset_Icc_right hjk)) (by omega)
    have hupos : 0 < u := by unfold u; positivity
    have hulog : log (u:ℝ) = (E:ℝ)*log 2 + ∑ i ∈ C, weight i := adjust_log (adjust_range hC he)
    rw [hcs] at hulog
    refine ⟨l, u, hls, hu, hlpos, hupos, hl, ?_, hlg, ?_⟩ <;> dsimp [t] at hBlo hBhi <;> linarith
  · let u : ℕ := 2^(E+1)
    have hu : u ∣ denom k := (pow_dvd_pow _ hek).trans (dvd_mul_right _ _)
    have hupos : 0 < u := by unfold u; positivity
    have hulog : log (u:ℝ) = ((E:ℝ)+1)*log 2 := by simp [u, log_pow]
    refine ⟨l, u, hls, hu, hlpos, hupos, hl, hulog ▸ hhi, hlg, ?_⟩
    dsimp [t] at h
    linarith

private noncomputable def scale (x : ℝ) : ℝ := log x / log 2

private noncomputable def precision (x : ℝ) : ℕ := ⌊√(scale x / 4)⌋₊

private theorem log_pos_two : 0 < log (2:ℝ) := log_pos (by norm_num)

private theorem scale_upper {k : ℕ} (hk : 0 < k) :
    scale (denom k) ≤ 6*(k:ℝ)^2 := by
  unfold scale
  apply (div_le_iff₀ log_pos_two).mpr
  have h : (denom k : ℝ) ≤ (2:ℝ)^(6*k^2) := by exact_mod_cast denom_upper hk
  have hpos : 0 < (denom k : ℝ) := by unfold denom; positivity
  have hh := (log_le_log_iff hpos (by positivity)).mpr h
  simpa [log_pow] using hh

private theorem value_bracket {k : ℕ} (hk : 0 < k) {x : ℝ}
    (hx : 1 ≤ x) (hmid : scale x ≤ 3*(k:ℝ)^2) :
    ∃ l u : ℕ, l ∣ denom k ∧ u ∣ denom k ∧ 0 < l ∧ 0 < u ∧
      (l:ℝ) ≤ x ∧ x ≤ u ∧ x < 2*l ∧ (u:ℝ) < 2*x ∧
      x ≤ (l:ℝ)*(1 + ((2:ℝ)^precision x)⁻¹) ∧
      (u:ℝ) ≤ x*(1 + ((2:ℝ)^precision x)⁻¹) := by
  let E := ⌊scale x⌋₊
  let j := precision x
  have hx0 : 0 < x := by linarith
  have hs0 : 0 ≤ scale x := div_nonneg (log_nonneg hx) log_pos_two.le
  have hj₂ : (j:ℝ)^2 ≤ scale x := by
    have hf : (j:ℝ) ≤ √(scale x/4) := Nat.floor_le (sqrt_nonneg _)
    have hs := sq_sqrt (show 0 ≤ scale x/4 by positivity)
    have hsq := (sq_le_sq₀ (Nat.cast_nonneg j) (sqrt_nonneg _)).mpr hf
    linarith
  have hjk : j ≤ k := by
    have hf : (j:ℝ) ≤ √(scale x/4) := Nat.floor_le (sqrt_nonneg _)
    have h : √(scale x/4) ≤ (k:ℝ) :=
      sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
    exact_mod_cast hf.trans h
  have hE : (E:ℝ) ≤ scale x := Nat.floor_le hs0
  have hE' : scale x < (E:ℝ)+1 := Nat.lt_floor_add_one _
  have hjE : j^2 ≤ E := Nat.le_floor (by exact_mod_cast hj₂)
  have hEk : E+1 ≤ 4*k^2 := by
    have h : ((E:ℝ)+1) ≤ 4*(k:ℝ)^2 := by
      have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
      nlinarith [sq_nonneg ((k:ℝ)-1)]
    exact_mod_cast h
  have hlo : (E:ℝ)*log 2 ≤ log x := (le_div_iff₀ log_pos_two).mp hE
  have hhi : log x < ((E:ℝ)+1)*log 2 := (div_lt_iff₀ log_pos_two).mp hE'
  by_cases hj : 0 < j
  · obtain ⟨l,u,hld,hud,hl0,hu0,hl,hu,hgl,hgu⟩ :=
      log_bracket hj hjk hjE hEk hlo hhi.le
    have hl0' : 0 < (l:ℝ) := by positivity
    have hu0' : 0 < (u:ℝ) := by positivity
    have hl' := (log_le_log_iff hl0' hx0).mp hl
    have hu' := (log_le_log_iff hx0 hu0').mp hu
    let a := (1 + ((2:ℝ)^j)⁻¹)
    have ha0 : 0 < a := by dsimp [a]; positivity
    have ha : a < 2 := by
      have hp : (1:ℝ) < 2^j := one_lt_pow₀ (by norm_num) (by omega)
      have h := inv_lt_one_of_one_lt₀ hp
      dsimp [a]
      linarith
    have hlm : x ≤ (l:ℝ)*a := by
      apply (log_le_log_iff hx0 (mul_pos hl0' ha0)).mp
      rw [log_mul hl0'.ne' ha0.ne']
      change log x - log (l:ℝ) ≤ log a at hgl
      linarith
    have hum : (u:ℝ) ≤ x*a := by
      apply (log_le_log_iff hu0' (mul_pos hx0 ha0)).mp
      rw [log_mul hx0.ne' ha0.ne']
      change log (u:ℝ) - log x ≤ log a at hgu
      linarith
    exact ⟨l,u,hld,hud,hl0,hu0,hl',hu',
      hlm.trans_lt (by linarith [mul_lt_mul_of_pos_left ha hl0']),
      hum.trans_lt (by linarith [mul_lt_mul_of_pos_left ha hx0]),hlm,hum⟩
  · have hj0 : precision x = 0 := by change j = 0; omega
    let l : ℕ := 2^E
    let u : ℕ := 2^(E+1)
    have hld : l ∣ denom k := (pow_dvd_pow _ (show E ≤ 4*k^2 by omega)).trans
      (dvd_mul_right _ _)
    have hud : u ∣ denom k := (pow_dvd_pow _ hEk).trans (dvd_mul_right _ _)
    have hl0' : 0 < (l:ℝ) := by dsimp [l]; positivity
    have hu0' : 0 < (u:ℝ) := by dsimp [u]; positivity
    have hl : (l:ℝ) ≤ x := (log_le_log_iff hl0' hx0).mp (by simpa [l, log_pow] using hlo)
    have hu : x < (u:ℝ) := (log_lt_log_iff hx0 hu0').mp (by simpa [u, log_pow] using hhi)
    have heq : (u:ℝ) = 2*l := by simp [l, u, pow_succ, mul_comm]
    have hln : 0 < l := by exact_mod_cast hl0'
    have hun : 0 < u := by exact_mod_cast hu0'
    rw [hj0, pow_zero, inv_one, show (1:ℝ)+1=2 by norm_num]
    rcases eq_or_lt_of_le hl with he | he
    · exact ⟨l,l,hld,hld,hln,hln,hl,he.ge,by linarith,by linarith,by linarith,by linarith⟩
    · exact ⟨l,u,hld,hud,hln,hun,hl,hu.le,by linarith,by linarith,by linarith,by linarith⟩

private theorem denom_pos (k : ℕ) : 0 < denom k := by unfold denom; positivity

private theorem scale_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ scale x :=
  div_nonneg (log_nonneg hx) log_pos_two.le

private theorem scale_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : scale x ≤ scale y :=
  div_le_div_of_nonneg_right (log_le_log hx hxy) log_pos_two.le

private theorem scale_div {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    scale (x/y) = scale x - scale y := by simp [scale, log_div hx hy, sub_div]

private theorem scale_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    scale (x*y) = scale x + scale y := by simp [scale, log_mul hx hy, add_div]

private theorem scale_pow (j : ℕ) : scale ((2:ℝ)^j) = j := by
  unfold scale
  rw [log_pow, mul_div_cancel_right₀ _ log_pos_two.ne']

private theorem min_input_mid {k y : ℕ} (hk : 0 < k) (hy : 0 < y) (hyM : y ≤ denom k) :
    let x := min (y:ℝ) ((denom k:ℝ)/y)
    1 ≤ x ∧ scale x = min (scale y) (scale (denom k) - scale y) ∧
      scale x ≤ 3*(k:ℝ)^2 := by
  have hy' : 1 ≤ (y:ℝ) := by exact_mod_cast hy
  have hp : 0 < (y:ℝ) := by positivity
  have hm : 0 < (denom k:ℝ) := by exact_mod_cast denom_pos k
  have hratio : 1 ≤ ((denom k:ℝ)/y) := by
    apply (le_div_iff₀ hp).mpr
    simpa using (show (y:ℝ) ≤ denom k by exact_mod_cast hyM)
  refine ⟨le_min hy' hratio, ?_, ?_⟩
  · rcases le_total (y:ℝ) ((denom k:ℝ)/y) with h | h
    · rw [min_eq_left h, min_eq_left]
      exact scale_div hm.ne' hp.ne' ▸ scale_le hp h
    · rw [min_eq_right h, scale_div hm.ne' hp.ne', min_eq_right]
      exact (scale_div hm.ne' hp.ne') ▸ scale_le (by positivity) h
  · have h : scale (min (y:ℝ) ((denom k:ℝ)/y)) ≤ scale y :=
      scale_le (by linarith [le_min hy' hratio]) (min_le_left ..)
    have h' : scale (min (y:ℝ) ((denom k:ℝ)/y)) ≤ scale (denom k) - scale y := by
      rw [← scale_div hm.ne' hp.ne']
      exact scale_le (by linarith [le_min hy' hratio]) (min_le_right ..)
    linarith [scale_upper hk]

private theorem subtract_divisor {k y : ℕ} (hk : 0 < k) (hy : 0 < y) (hyM : y ≤ denom k) :
    let x := min (y:ℝ) ((denom k:ℝ)/y)
    ∃ d ∈ (denom k).divisors, d ≤ y ∧ y-d < d ∧
      ∀ (_ : 0 < y-d), max (1:ℝ) (precision x : ℝ) ≤ scale y - scale (y-d : ℕ) := by
  let x := min (y:ℝ) ((denom k:ℝ)/y)
  obtain ⟨hx, -, hmid⟩ := min_input_mid hk hy hyM
  obtain ⟨l,u,hld,hud,hl0,hu0,hl,hu,hlo,hhi,hls,hus⟩ := value_bracket hk hx hmid
  let e := 1 + ((2:ℝ)^precision x)⁻¹
  have hp : 0 < (y:ℝ) := by positivity
  have hm : 0 < (denom k:ℝ) := by exact_mod_cast denom_pos k
  have hd : ∃ d : ℕ, 0 < d ∧ d ∣ denom k ∧ (d:ℝ) ≤ y ∧ (y:ℝ) < 2*d ∧ (y:ℝ) ≤ d*e := by
    rcases le_total (y:ℝ) ((denom k:ℝ)/y) with h | h
    · have he : x = y := min_eq_left h
      exact ⟨l,hl0,hld,he ▸ hl,he ▸ hlo,he ▸ hls⟩
    · have he : x = (denom k:ℝ)/y := min_eq_right h
      let d := denom k / u
      have hdu : d*u = denom k := Nat.div_mul_cancel hud
      have hd0 : 0 < d := by
        by_contra! hdz
        have := Nat.eq_zero_of_le_zero hdz
        simp [this] at hdu
        exact (denom_pos k).ne' hdu.symm
      have hdiv : (d:ℝ)*(u:ℝ) = denom k := by exact_mod_cast hdu
      have hu0' : 0 < (u:ℝ) := by positivity
      have hel : (denom k:ℝ)/y ≤ u := he ▸ hu
      have hupper : (u:ℝ) < 2*((denom k:ℝ)/y) := he ▸ hhi
      have hquant : (u:ℝ) ≤ ((denom k:ℝ)/y)*e := he ▸ hus
      refine ⟨d, hd0, ⟨u,hdu.symm⟩, ?_, ?_, ?_⟩
      · apply (le_of_mul_le_mul_right _ hu0')
        rw [hdiv, mul_comm]
        exact (div_le_iff₀ hp).mp hel
      · apply (lt_of_mul_lt_mul_right _ hu0'.le)
        calc
          (y:ℝ)*(u:ℝ) < (y:ℝ)*(2*((denom k:ℝ)/y)) := mul_lt_mul_of_pos_left hupper hp
          _ = (2*(d:ℝ))*(u:ℝ) := by rw [mul_assoc, hdiv]; field_simp
      · apply (le_of_mul_le_mul_right _ hu0')
        calc
          (y:ℝ)*(u:ℝ) ≤ (y:ℝ)*(((denom k:ℝ)/y)*e) :=
            mul_le_mul_of_nonneg_left hquant hp.le
          _ = ((d:ℝ)*e)*(u:ℝ) := by rw [mul_right_comm _ e, hdiv]; field_simp
  obtain ⟨d,hd0,hdiv,hd,hhalf,hquant⟩ := hd
  have hd' : d ≤ y := by exact_mod_cast hd
  let r := y-d
  have hsub : (r:ℝ) = (y:ℝ) - (d:ℝ) := Nat.cast_sub hd'
  have hh : (r:ℝ)*2 < (y:ℝ) := by linarith
  refine ⟨d, Nat.mem_divisors.mpr ⟨hdiv,(denom_pos k).ne'⟩, hd', ?_, ?_⟩
  · exact_mod_cast (show (r:ℝ) < (d:ℝ) by linarith)
  · intro hr
    have hr0 : 0 < (r:ℝ) := by exact_mod_cast hr
    change max (1:ℝ) (precision x : ℝ) ≤ scale y - scale r
    apply max_le
    · have h := scale_le (mul_pos hr0 (by norm_num : 0 < (2:ℝ))) hh.le
      rw [scale_mul hr0.ne' (by norm_num), show scale 2 = 1 by
        exact div_self log_pos_two.ne'] at h
      linarith
    · let P := (2:ℝ)^precision x
      have hP : 0 < P := by unfold P; positivity
      have hq : (r:ℝ) ≤ (d:ℝ)*P⁻¹ := by change (y:ℝ) ≤ (d:ℝ)*(1+P⁻¹) at hquant; linarith
      have h' : (r:ℝ)*P ≤ (d:ℝ) := by
        apply (le_div_iff₀ hP).mp
        simpa [div_eq_mul_inv] using hq
      have h := scale_le (mul_pos hr0 hP) (h'.trans hd)
      rw [scale_mul hr0.ne' hP.ne', show scale P = precision x by exact scale_pow _] at h
      linarith

-- The unit jump covers the step in which the remainder crosses the midpoint.
private noncomputable def potential (L t : ℝ) : ℝ :=
  if t ≤ L/2 then √(t+1) else 1 + 2*√(L/2+1) - √(L-t+1)

private theorem potential_bounds {L t : ℝ} (ht : 0 ≤ t) :
    1 ≤ potential L t ∧ potential L t ≤ 1 + 2*√(L/2+1) := by
  unfold potential
  split_ifs with h
  · have hlow : (1:ℝ) ≤ √(t+1) := by
      rw [le_sqrt (by norm_num) (by positivity)]
      nlinarith
    have hhigh := sqrt_le_sqrt (show t+1 ≤ L/2+1 by linarith)
    exact ⟨hlow, by linarith [sqrt_nonneg (L/2+1)]⟩
  · have hhigh := sqrt_le_sqrt (show L-t+1 ≤ L/2+1 by linarith)
    exact ⟨by linarith [sqrt_nonneg (L/2+1)], by linarith [sqrt_nonneg (L-t+1)]⟩

private theorem potential_drop {L s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ L)
    (hg : √(min t (L-t)+1)/5 ≤ t-s) : 1/12 ≤ potential L t - potential L s := by
  unfold potential
  by_cases h : t ≤ L/2
  · rw [if_pos h, if_pos (hst.trans h), min_eq_left (by linarith)] at *
    have hT : (1:ℝ) ≤ √(t+1) := by
      rw [le_sqrt (by norm_num) (by linarith)]
      nlinarith
    have hsq := sq_sqrt (show 0 ≤ t+1 by linarith)
    have hz : √(s+1) ≤ √(t+1)-1/12 :=
      sqrt_le_iff.mpr ⟨by linarith, by nlinarith only [hsq, hT, hg]⟩
    linarith
  · rw [if_neg h]
    by_cases h' : s ≤ L/2
    · rw [if_pos h']
      have hhi := sqrt_le_sqrt (show L-t+1 ≤ L/2+1 by linarith)
      have hlo := sqrt_le_sqrt (show s+1 ≤ L/2+1 by linarith)
      linarith
    · rw [if_neg h', min_eq_right (by linarith)] at *
      have hU : (1:ℝ) ≤ √(L-t+1) := by
        rw [le_sqrt (by norm_num) (by linarith)]
        nlinarith
      have hsq := sq_sqrt (show 0 ≤ L-t+1 by linarith)
      have hz := (le_sqrt (show 0 ≤ √(L-t+1)+1/12 by linarith)
        (show 0 ≤ L-s+1 by linarith)).mpr (by nlinarith only [hsq,hU,hg])
      linarith

private theorem precision_gain {x : ℝ} (hx : 1 ≤ x) :
    √(scale x + 1)/5 ≤ max (1:ℝ) (precision x : ℝ) := by
  let w := scale x
  let g := max (1:ℝ) (precision x : ℝ)
  have hw : 0 ≤ w := scale_nonneg hx
  have hg : 1 ≤ g := le_max_left _ _
  have hj : (precision x:ℝ) ≤ g := le_max_right _ _
  have hf : √(w/4) < (precision x:ℝ)+1 := Nat.lt_floor_add_one _
  have h4 : √w ≤ 4*g := by
    have h := sqrt_div hw (4:ℝ)
    have h' : √(4:ℝ) = 2 := by norm_num
    rw [h'] at h
    linarith
  have hsq := sq_sqrt hw
  have hsum : √(w+1) ≤ √w+1 :=
    sqrt_le_iff.mpr ⟨by positivity, by nlinarith [sqrt_nonneg w]⟩
  change √(w+1)/5 ≤ g
  linarith

private theorem short_divisor_expansion {k : ℕ} (hk : 0 < k) {y : ℕ} (hyM : y ≤ denom k) :
    ∃ S : Finset ℕ, S ⊆ (denom k).divisors ∧ S.sum id = y ∧ S.card ≤ 60*k := by
  let L := scale (denom k)
  suffices hb : ∀ y : ℕ, y ≤ denom k → 0 < y →
      ∃ S : Finset ℕ, S ⊆ (denom k).divisors ∧ S.sum id = y ∧
        (S.card:ℝ) ≤ 12*potential L (scale y) by
    by_cases hy0 : y = 0
    · exact ⟨∅, empty_subset _, by simp [hy0], by simp⟩
    have hy : 0 < y := by omega
    obtain ⟨S,hS,hSy,hcard⟩ := hb y hyM hy
    refine ⟨S,hS,hSy,?_⟩
    have hy1 : (1:ℝ) ≤ y := by exact_mod_cast hy
    have hpo := (potential_bounds (L := L) (scale_nonneg hy1)).2
    have hK : (1:ℝ) ≤ k := by exact_mod_cast hk
    have hL : L ≤ 6*(k:ℝ)^2 := scale_upper hk
    have hroot : √(L/2+1) ≤ 2*(k:ℝ) :=
      sqrt_le_iff.mpr ⟨by positivity, by nlinarith [sq_nonneg ((k:ℝ)-1)]⟩
    exact_mod_cast (show (S.card:ℝ) ≤ 60*(k:ℝ) by linarith)
  intro y
  induction y using Nat.strong_induction_on with
  | h y ih =>
    intro hyM hy
    let x := min (y:ℝ) ((denom k:ℝ)/y)
    obtain ⟨d,hd,hdy,hhalf,hgap⟩ := subtract_divisor hk hy hyM
    have hdp : 0 < d := Nat.pos_of_mem_divisors hd
    let r := y-d
    have hrlt : r < y := by dsimp [r]; omega
    have hy1 : (1:ℝ) ≤ y := by exact_mod_cast hy
    have hyL : scale y ≤ L := scale_le (by positivity) (by exact_mod_cast hyM)
    by_cases hr : 0 < r
    · obtain ⟨S,hS,hSy,hcard⟩ := ih r hrlt (hrlt.le.trans hyM) hr
      have hnot : d ∉ S := by
        intro hdS
        have hle : d ≤ S.sum id := single_le_sum (f := id) (fun i _ => Nat.zero_le i) hdS
        omega
      have hr1 : (1:ℝ) ≤ r := by exact_mod_cast hr
      have hrle : scale r ≤ scale y := scale_le (by positivity) (by exact_mod_cast hrlt.le)
      obtain ⟨hX, hxscale, -⟩ := min_input_mid hk hy hyM
      have hg := (precision_gain hX).trans (hgap hr)
      change √(scale x+1)/5 ≤ scale y - scale r at hg
      rw [show scale x = min (scale y) (L-scale y) from hxscale] at hg
      have hdif := potential_drop (scale_nonneg hr1) hrle hyL hg
      refine ⟨insert d S, insert_subset hd hS, ?_, ?_⟩
      · rw [sum_insert hnot, hSy]
        dsimp [r]
        omega
      · rw [card_insert_of_notMem hnot, Nat.cast_add, Nat.cast_one]
        linarith
    · have he : d = y := by dsimp [r] at hr; omega
      refine ⟨{d}, singleton_subset_iff.mpr hd, by simp [he], ?_⟩
      have h := (potential_bounds (L := L) (scale_nonneg hy1)).1
      simp only [card_singleton, Nat.cast_one]
      linarith

private theorem division_injective {M : ℕ} (hM : 0 < M) {S : Finset ℕ}
    (hS : ∀ d ∈ S, d ∣ M) : (S : Set ℕ).InjOn (fun d => M/d) := by
  intro a ha b hb he
  have h₁ := Nat.div_mul_cancel (hS a (mem_coe.mp ha))
  have h₂ := Nat.div_mul_cancel (hS b (mem_coe.mp hb))
  have hp : 0 < M/a := by
    by_contra! hz
    rw [Nat.eq_zero_of_le_zero hz, zero_mul] at h₁
    omega
  change M/a = M/b at he
  apply Nat.eq_of_mul_eq_mul_left hp
  rw [h₁, he, h₂]

private theorem unit_expansion {M : ℕ} (hM : 0 < M) {S : Finset ℕ}
    (hS : ∀ d ∈ S, 0 < d ∧ d ∣ M) :
    (∑ n ∈ S.image (fun d => M/d), (n : ℚ)⁻¹) = ((S.sum id : ℕ) : ℚ)/M := by
  have hc d (hd : d ∈ S) : ((M/d : ℕ) : ℚ)⁻¹ = (d:ℚ)/M := by
    have h : ((M/d : ℕ) : ℚ)*(d:ℚ) = (M:ℚ) := by exact_mod_cast Nat.div_mul_cancel (hS d hd).2
    have hd0 : (d:ℚ) ≠ 0 := by have := (hS d hd).1; positivity
    have hM0 : (M:ℚ) ≠ 0 := by positivity
    have hz : ((M/d : ℕ):ℚ) ≠ 0 := by
      intro h'
      rw [h', zero_mul] at h
      exact hM0 h.symm
    field_simp
    linarith
  rw [sum_image (division_injective hM (fun d hd => (hS d hd).2))]
  rw [sum_congr rfl hc, ← sum_div, Nat.cast_sum]
  rfl

private theorem short_egyptian {a b k : ℕ} (ha : a < b) (hk : 0 < k) (hb : 2 ≤ b)
    (hbM : b ≤ denom k) : Erdos304.smallestCollection a b ≤ 120*k := by
  let M := denom k
  let q := a*M/b
  let r := a*M%b
  have hM : 0 < M := denom_pos k
  have hb0 : 0 < b := by omega
  have hq : q < M := (Nat.div_lt_iff_lt_mul hb0).mpr (by
    simpa [mul_comm] using Nat.mul_lt_mul_of_pos_right ha hM)
  have hr : r < b := Nat.mod_lt _ hb0
  have hqr : r + b*q = a*M := Nat.mod_add_div _ _
  obtain ⟨S,hS,hs,hsc⟩ := short_divisor_expansion hk hq.le
  obtain ⟨T,hT,ht,htc⟩ := short_divisor_expansion hk (hr.le.trans hbM)
  -- The first group has denominators at most M, the second strictly greater.
  let B := S.image (fun d => M/d)
  let D := T.image (fun d => b*M/d)
  have hsprops d (hd : d ∈ S) : 0 < d ∧ d ∣ M :=
    ⟨Nat.pos_of_mem_divisors (hS hd), Nat.dvd_of_mem_divisors (hS hd)⟩
  have htprops d (hd : d ∈ T) : 0 < d ∧ d ∣ b*M :=
    ⟨Nat.pos_of_mem_divisors (hT hd), dvd_mul_of_dvd_right (Nat.dvd_of_mem_divisors (hT hd)) _⟩
  have hB n (hn : n ∈ B) : 1 < n ∧ n ≤ M := by
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hn
    obtain ⟨hd0,hdd⟩ := hsprops d hd
    have hdq : d ≤ q := hs ▸ single_le_sum (f := id) (fun i _ => Nat.zero_le i) hd
    have hdM : d < M := hdq.trans_lt hq
    have hmul := Nat.div_mul_cancel hdd
    refine ⟨?_, Nat.div_le_self ..⟩
    by_contra! h
    have hh := Nat.mul_le_mul_right d h
    simp only [one_mul, hmul] at hh
    omega
  have hD n (hn : n ∈ D) : M < n := by
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hn
    obtain ⟨hd0,hdd⟩ := htprops d hd
    have hds : d ≤ r := ht ▸ single_le_sum (f := id) (fun i _ => Nat.zero_le i) hd
    have hdb : d < b := hds.trans_lt hr
    have hlt : M*d < b*M := by
      simpa [mul_comm] using Nat.mul_lt_mul_of_pos_right hdb hM
    have hmul := Nat.div_mul_cancel hdd
    by_contra! h
    have hle := Nat.mul_le_mul_right d h
    omega
  have hdis : Disjoint B D := disjoint_left.mpr (fun n hn hd =>
    (not_lt_of_ge (hB n hn).2) (hD n hd))
  have hBs : (∑ n ∈ B, (n:ℚ)⁻¹) = (q:ℚ)/M := by
    simpa only [B, hs] using unit_expansion hM hsprops
  have hDs : (∑ n ∈ D, (n:ℚ)⁻¹) = (r:ℚ)/(b*M) := by
    simpa only [D, ht, Nat.cast_mul] using unit_expansion (Nat.mul_pos hb0 hM) htprops
  let U := B ∪ D
  have hU : U.card ≤ 120*k := by
    have hBcard : B.card ≤ 60*k := card_image_le.trans hsc
    have hDcard : D.card ≤ 60*k := card_image_le.trans htc
    have hu := card_union_le B D
    change U.card ≤ B.card + D.card at hu
    omega
  refine (Nat.sInf_le (s := Erdos304.unitFractionExpressible a b) (m := U.card)
    ⟨U, rfl, ?_, ?_⟩).trans hU
  · intro n hn
    rcases mem_union.mp hn with hn | hn
    · exact (hB n hn).1
    · have hh := hD n hn
      omega
  · change (a:ℚ)/b = ∑ n ∈ B ∪ D, (n:ℚ)⁻¹
    rw [sum_union hdis, hBs, hDs]
    have h : (r:ℚ) + (b:ℚ)*(q:ℚ) = (a:ℚ)*(M:ℚ) := by exact_mod_cast hqr
    have hM' : (M:ℚ) ≠ 0 := by positivity
    have hb' : (b:ℚ) ≠ 0 := by positivity
    field_simp
    linarith

private theorem vose :
    (fun b => (Erdos304.smallestCollectionTo b : ℝ)) =O[atTop]
      (fun b => √(log b)) := by
  refine Asymptotics.IsBigO.of_bound 240 ?_
  have hlog : Tendsto (fun b : ℕ => log (b:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop (1:ℝ)), eventually_ge_atTop (2:ℕ)]
    with b hblog hb
  let k := ⌈√(log (b:ℝ))⌉₊
  have hsr : 0 ≤ √(log (b:ℝ)) := sqrt_nonneg _
  have hsb : 1 ≤ √(log (b:ℝ)) := (le_sqrt (by norm_num) (by linarith)).mpr (by simpa using hblog)
  have hkl : √(log (b:ℝ)) ≤ (k:ℝ) := Nat.le_ceil _
  have hk : 0 < k := by exact_mod_cast (show (0:ℝ) < k by linarith)
  have hku : (k:ℝ) ≤ 2*√(log (b:ℝ)) := by linarith [(Nat.ceil_lt_add_one hsr).le]
  have hbM : b ≤ denom k := by
    suffices hp : b ≤ 2^(4*k^2) from hp.trans (denom_lower k)
    have hlog2 := one_sub_inv_le_log_of_pos (show 0 < (2:ℝ) by norm_num)
    norm_num at hlog2
    have hk2 := (sq_le_sq₀ hsr (Nat.cast_nonneg k)).mpr hkl
    rw [sq_sqrt (log_natCast_nonneg b)] at hk2
    have hp : (b:ℝ) ≤ (2:ℝ)^(4*k^2) := by
      apply (log_le_log_iff (by positivity) (by positivity)).mp
      rw [log_pow]
      push_cast
      nlinarith [mul_nonneg (sq_nonneg (k:ℝ)) (sub_nonneg.mpr hlog2)]
    exact_mod_cast hp
  have hs : Erdos304.smallestCollectionTo b ≤ 120*k := by
    unfold Erdos304.smallestCollectionTo
    apply csSup_le
    · exact ⟨Erdos304.smallestCollection 1 b, 1, mem_Ico.mpr ⟨le_rfl, by omega⟩, rfl⟩
    · rintro m ⟨a,ha,rfl⟩
      exact short_egyptian (mem_Ico.mp ha).2 hk hb hbM
  have hs' : (Erdos304.smallestCollectionTo b:ℝ) ≤ 120*(k:ℝ) := by exact_mod_cast hs
  change ‖(Erdos304.smallestCollectionTo b:ℝ)‖ ≤ 240*‖√(log (b:ℝ))‖
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg hsr]
  linarith

end OMA

theorem OMA.solution : type_of% @Erdos304.erdos_304.variants.upper_1985 :=
  OMA.vose