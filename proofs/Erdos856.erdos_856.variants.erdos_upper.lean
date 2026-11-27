import FormalConjectures.ErdosProblems.«856»
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
Count representations as a product of a member of the set and a prime.
Representations of the same product form an equal-LCM tuple.

Reference: P. Erdős, Some extremal problems in combinatorial number theory (1970), p. 127.
Credit: @Genbox.
-/

open Finset Nat Filter Real

namespace OMA

private theorem harmonic_real (N : ℕ) :
    (harmonic N : ℝ) = ∑ m ∈ Icc 1 N, (m : ℝ)⁻¹ := by
  simp [harmonic_eq_sum_Icc]

private theorem harmonic_le_euler (N : ℕ) :
    (harmonic N : ℝ) ≤ ∏ p ∈ (N+1).primesBelow, (1 - (p : ℝ)⁻¹)⁻¹ := by
  classical
  let f : ℕ → ℝ := fun n => (n : ℝ)⁻¹
  have hf₁ : f 1 = 1 := by simp [f]
  have hmul : ∀ {m n : ℕ}, m.Coprime n → f (m*n) = f m * f n := by
    intro m n _
    simp [f, mul_comm]
  have hp_bound {p : ℕ} (hp : p.Prime) : (p : ℝ)⁻¹ ≤ 1/2 := by
    have h : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    rw [one_div]
    exact inv_anti₀ (by norm_num) h
  have hs {p : ℕ} (hp : p.Prime) : Summable (fun n : ℕ => ‖f (p ^ n)‖) := by
    have hh : (p : ℝ)⁻¹ < 1 := (hp_bound hp).trans_lt (by norm_num)
    simpa [f, mul_inv, inv_pow, Real.norm_eq_abs, abs_of_nonneg] using
      summable_geometric_of_lt_one (show 0 ≤ (p : ℝ)⁻¹ by positivity) hh
  obtain ⟨-, heuler⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum hf₁ hmul
      (fun hp => hs hp) (N+1)
  have hprod : (∏ p ∈ (N+1).primesBelow, (1 - (p : ℝ)⁻¹)⁻¹) =
      (∏ p ∈ (N+1).primesBelow, ∑' n : ℕ, f (p^n)) := by
    apply prod_congr rfl
    intro p hp
    have hlt : (p : ℝ)⁻¹ < 1 :=
      (hp_bound (prime_of_mem_primesBelow hp)).trans_lt (by norm_num)
    simp only [f, Nat.cast_pow, ← inv_pow]
    exact (tsum_geometric_of_lt_one (by positivity) hlt).symm
  rw [← hprod] at heuler
  let s := Icc 1 N
  let emb : s ↪ (N+1).smoothNumbers :=
    ⟨fun m => ⟨m.val, Nat.mem_smoothNumbers_of_lt
      (by have := (mem_Icc.mp m.prop).1; omega)
      (by have := (mem_Icc.mp m.prop).2; omega)⟩,
      fun m n h => Subtype.ext (congrArg (fun t : (N+1).smoothNumbers => t.val) h)⟩
  rw [harmonic_real, ← sum_attach s]
  change (∑ m ∈ s.attach, f (emb m).val) ≤ _
  rw [← sum_map s.attach emb (fun m => f m.val)]
  rw [← heuler.tsum_eq]
  exact heuler.summable.sum_le_tsum _ (fun m _ => by dsimp [f]; positivity)

private theorem loglog_le_twice_sum_primes {N : ℕ} (hN : 2 ≤ N) :
    log (log (N : ℝ)) ≤ 2 * ∑ p ∈ (N+1).primesBelow, (p : ℝ)⁻¹ := by
  have hf {p : ℕ} (hp : p ∈ (N+1).primesBelow) : (p : ℝ)⁻¹ ≤ 1/2 := by
    have h : (2 : ℝ) ≤ p := by exact_mod_cast (prime_of_mem_primesBelow hp).two_le
    rw [one_div]
    exact inv_anti₀ (by norm_num) h
  have hpos : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  have hple : log (N : ℝ) ≤ ∏ p ∈ (N+1).primesBelow, (1 - (p : ℝ)⁻¹)⁻¹ :=
    (log_le_harmonic_floor (N : ℝ) (by positivity)).trans
      (by simpa using harmonic_le_euler N)
  have hprodpos p (hp : p ∈ (N+1).primesBelow) : 0 < (1 - (p : ℝ)⁻¹)⁻¹ :=
    inv_pos.mpr (by linarith [hf hp])
  calc
    log (log (N : ℝ)) ≤ log (∏ p ∈ (N+1).primesBelow, (1 - (p : ℝ)⁻¹)⁻¹) :=
      (log_le_log_iff hpos (prod_pos hprodpos)).mpr hple
    _ = ∑ p ∈ (N+1).primesBelow, log ((1 - (p : ℝ)⁻¹)⁻¹) := by
      exact log_prod (fun p hp => (hprodpos p hp).ne')
    _ ≤ ∑ p ∈ (N+1).primesBelow, 2 * (p : ℝ)⁻¹ := by
      apply sum_le_sum
      intro p hp
      let u := (p : ℝ)⁻¹
      have hu0 : 0 ≤ u := by dsimp [u]; positivity
      have hu : u ≤ 1/2 := hf hp
      have hu1 : 0 < 1 - u := by linarith
      change log (1-u)⁻¹ ≤ 2*u
      calc
        log (1-u)⁻¹ ≤ (1-u)⁻¹ - 1 := log_le_sub_one_of_pos (inv_pos.mpr hu1)
        _ = u / (1-u) := by field_simp; ring
        _ ≤ 2*u := (div_le_iff₀ hu1).mpr (by nlinarith)
    _ = _ := (mul_sum ..).symm

private theorem equal_product_lcm {a b p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (h : a*p = b*q) : Nat.lcm a b = a*p := by
  have hco := (Nat.coprime_primes hp hq).mpr hne
  have hqa : q ∣ a := hco.symm.dvd_of_dvd_mul_right
    (h.symm ▸ dvd_mul_left q b)
  obtain ⟨c, hc⟩ := hqa
  have hb : b = c*p := by
    apply Nat.eq_of_mul_eq_mul_right hq.pos
    rw [← h, hc]
    ac_rfl
  rw [hc, hb, mul_comm q c, ← lcm_eq_nat_lcm, _root_.lcm_mul_left, normalize_eq,
    lcm_eq_nat_lcm, hco.symm.lcm_eq_mul]
  ac_rfl

private theorem reciprocal_product_bound {k N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Icc 1 N) (hfree : ¬ Erdos856.HasEqualLcmTuple k A) :
    (∑ a ∈ A, (a : ℝ)⁻¹) * (∑ p ∈ (N+1).primesBelow, (p : ℝ)⁻¹) ≤
      (k : ℝ) * (harmonic (N^2) : ℝ) := by
  classical
  let P := (N+1).primesBelow
  let S := A ×ˢ P
  let product (v : ℕ × ℕ) := v.1 * v.2
  let fiber (t : ℕ) := S.filter (fun v => product v = t)
  have hmaps : (S : Set (ℕ × ℕ)).MapsTo product (Icc 1 (N^2) : Finset ℕ) := by
    intro v hv
    obtain ⟨ha, hp⟩ := mem_product.mp (mem_coe.mp hv)
    have has := mem_Icc.mp (hA ha)
    have hps := mem_primesBelow.mp hp
    exact mem_coe.mpr (mem_Icc.mpr ⟨Nat.mul_pos (by omega) hps.2.pos,
      by rw [pow_two]; exact Nat.mul_le_mul has.2 (by omega)⟩)
  have hfib t : (fiber t).card ≤ k := by
    by_contra! hbad
    obtain ⟨h, hsub, hcard⟩ := exists_subset_card_eq hbad.le
    have hpair v (hv : v ∈ h) : v.1 ∈ A ∧ v.2.Prime ∧ v.1*v.2=t := by
      have hm := mem_filter.mp (hsub hv)
      have hv' := mem_product.mp hm.1
      exact ⟨hv'.1, prime_of_mem_primesBelow hv'.2, hm.2⟩
    have hinj : (h : Set (ℕ × ℕ)).InjOn Prod.fst := by
      intro v hv w hw he
      have hprod := (hpair v (mem_coe.mp hv)).2.2.trans (hpair w (mem_coe.mp hw)).2.2.symm
      have hvp := (mem_Icc.mp (hA (hpair v (mem_coe.mp hv)).1)).1
      have hvpos : 0 < v.1 := by omega
      refine Prod.ext he (Nat.eq_of_mul_eq_mul_left hvpos ?_)
      simpa only [← he] using hprod
    apply hfree
    refine ⟨h.image Prod.fst, ?_, (Finset.card_image_of_injOn hinj).trans hcard, t, ?_⟩
    · intro a ha
      obtain ⟨v, hv, rfl⟩ := mem_image.mp ha
      exact (hpair v hv).1
    · intro a ha b hb hne
      obtain ⟨v, hv, rfl⟩ := mem_image.mp ha
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hb
      have hv' := hpair v hv
      have hw' := hpair w hw
      have hprod := hv'.2.2.trans hw'.2.2.symm
      have hpq : v.2 ≠ w.2 := by
        intro he
        rw [← he] at hprod
        exact hne (Nat.eq_of_mul_eq_mul_right hv'.2.1.pos hprod)
      exact (equal_product_lcm hv'.2.1 hw'.2.1 hpq hprod).trans hv'.2.2
  have hsum : (∑ v ∈ S, (product v : ℝ)⁻¹) =
      (∑ a ∈ A, (a : ℝ)⁻¹) * (∑ p ∈ P, (p : ℝ)⁻¹) := by
    simp only [S, product, sum_product, Nat.cast_mul, mul_inv, sum_mul, mul_sum]
    exact sum_comm
  rw [← hsum, ← sum_fiberwise_of_maps_to hmaps, harmonic_real, mul_sum]
  apply sum_le_sum
  intro t ht
  change (∑ v ∈ fiber t, (product v : ℝ)⁻¹) ≤ (k : ℝ) * (t : ℝ)⁻¹
  calc
    _ = (fiber t).card * (t : ℝ)⁻¹ := by
      rw [← nsmul_eq_mul, ← sum_const]
      exact sum_congr rfl (fun v hv => by rw [(mem_filter.mp hv).2])
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hfib t) (by positivity)

private theorem erdos_upper (k : ℕ) (hk : 3 ≤ k) :
    ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, Erdos856.f k N ≤ C * (Real.log N / Real.log (Real.log N)) := by
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun N : ℕ => log (log (N : ℝ))) atTop atTop :=
    tendsto_log_atTop.comp hlog
  refine ⟨6 * (k : ℝ), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    hlog.eventually (eventually_ge_atTop (1 : ℝ)),
    hloglog.eventually (eventually_gt_atTop (0 : ℝ))] with N hN hlogN hloglogN
  unfold Erdos856.f
  apply csSup_le
  · exact ⟨0, ∅, empty_subset _, (by
      rintro ⟨S, hS, hcard, L, hL⟩
      have he : S.card ≤ (∅ : Finset ℕ).card := card_le_card hS
      have hzero : (∅ : Finset ℕ).card = 0 := card_empty
      omega), by simp⟩
  rintro s ⟨A, hA, hfree, rfl⟩
  have he := reciprocal_product_bound hA hfree
  have hlogsum := loglog_le_twice_sum_primes hN
  have hsum0 : 0 ≤ ∑ a ∈ A, (a : ℝ)⁻¹ := sum_nonneg (fun _ _ => by positivity)
  have hH : (harmonic (N^2) : ℝ) ≤ 3 * log (N : ℝ) := by
    have h := harmonic_le_one_add_log (N^2)
    rw [Nat.cast_pow, Real.log_pow] at h
    norm_num at h
    linarith only [hlogN, h]
  rw [← mul_div_assoc, le_div_iff₀ hloglogN]
  calc
    _ ≤ (∑ a ∈ A, (a : ℝ)⁻¹) * (2 * ∑ p ∈ (N+1).primesBelow, (p : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left hlogsum hsum0
    _ = 2 * ((∑ a ∈ A, (a : ℝ)⁻¹) * (∑ p ∈ (N+1).primesBelow, (p : ℝ)⁻¹)) := by ring
    _ ≤ 2 * ((k : ℝ) * (harmonic (N^2) : ℝ)) := mul_le_mul_of_nonneg_left he (by norm_num)
    _ ≤ 2 * ((k : ℝ) * (3 * log (N : ℝ))) := by gcongr
    _ = _ := by ring

end OMA

theorem OMA.solution : type_of% @Erdos856.erdos_856.variants.erdos_upper :=
  OMA.erdos_upper