import FormalConjectures.ErdosProblems.«338»
import Mathlib.Algebra.BigOperators.ModEq

/-!
# Ordinary and restricted orders of a modular basis

For order `e + 2`, take modulus `3 * 2^e - 1`. The finite coins are `2, 4, ..., 2^e`
and `2^e` distinct representatives of residue one. Multiples of the modulus supply
the unbounded summand. The ordinary lower bound uses the cost of a binary expansion
whose highest denomination may repeat. The restricted lower bound uses the sum of
all the coin residues.
-/

namespace OMA

open Finset Filter
open scoped BigOperators ENat

private def cost : ℕ → ℕ → ℕ
  | 0, v => v
  | e + 1, v => v % 2 + cost e (v / 2)

private lemma cost_add_pow (e i v : ℕ) (hi : i ≤ e) :
    cost e (v + 2 ^ i) ≤ cost e v + 1 := by
  induction e generalizing i v with
  | zero =>
    have : i = 0 := by omega
    simp [this, cost]
  | succ e ih =>
    cases i with
    | zero =>
      simp only [pow_zero, cost]
      by_cases hv : v % 2 = 0
      · have hdiv : (v + 1) / 2 = v / 2 := by omega
        have hmod : (v + 1) % 2 = 1 := by omega
        rw [hdiv, hmod, hv]
        omega
      · have hdiv : (v + 1) / 2 = v / 2 + 2 ^ 0 := by simp; omega
        have hmod : (v + 1) % 2 = 0 := by omega
        rw [hdiv, hmod]
        have h := ih 0 (v / 2) (by omega)
        omega
    | succ i =>
      have hp : (2 : ℕ) ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ, mul_comm]
      have hdiv : (v + 2 * 2 ^ i) / 2 = v / 2 + 2 ^ i := by omega
      have hmod : (v + 2 * 2 ^ i) % 2 = v % 2 := by omega
      rw [hp, cost, cost, hdiv, hmod]
      exact Nat.add_le_add_left (ih i (v / 2) (by omega)) _

private lemma cost_add_ones (e v u : ℕ) : cost e (v + u) ≤ cost e v + u := by
  induction u with
  | zero => simp
  | succ u ih =>
    have h := cost_add_pow e 0 (v + u) (by omega)
    simp only [pow_zero] at h
    rw [← Nat.add_assoc]
    omega

private lemma cost_full (e q : ℕ) :
    cost e (q * 2 ^ e + (2 ^ e - 1)) = q + e := by
  induction e with
  | zero => simp [cost]
  | succ e ih =>
    let v := q * 2 ^ e + (2 ^ e - 1)
    have hp : 0 < (2 : ℕ) ^ e := by positivity
    have hterm : (2 : ℕ) ^ (e + 1) - 1 = 2 * (2 ^ e - 1) + 1 := by
      rw [pow_succ]
      omega
    have hv : q * 2 ^ (e + 1) + (2 ^ (e + 1) - 1) = 2 * v + 1 := by
      rw [hterm, pow_succ]
      dsimp [v]
      ring
    rw [hv, cost, show (2 * v + 1) % 2 = 1 by omega, show (2 * v + 1) / 2 = v by omega]
    rw [show cost e v = q + e from ih]
    omega

private lemma cost_bound (e q r : ℕ) (hr : r < 2 ^ e) :
    cost e (q * 2 ^ e + r) ≤ q + e ∧ (r + 1 < 2 ^ e → cost e (q * 2 ^ e + r) < q + e) := by
  induction e generalizing r with
  | zero =>
    have : r = 0 := by simpa using hr
    simp [this, cost]
  | succ e ih =>
    have heq : q * 2 ^ (e + 1) + r = 2 * (q * 2 ^ e) + r := by rw [pow_succ]; ring
    have hdiv : (q * 2 ^ (e + 1) + r) / 2 = q * 2 ^ e + r / 2 := by rw [heq]; omega
    have hmod : (q * 2 ^ (e + 1) + r) % 2 = r % 2 := by rw [heq]; omega
    have hr' : r / 2 < 2 ^ e := by rw [pow_succ] at hr; omega
    rw [cost, hdiv, hmod]
    obtain ⟨hweak, hstrict⟩ := ih (r / 2) hr'
    refine ⟨by omega, ?_⟩
    intro h
    by_cases hv : r % 2 = 0
    · omega
    · have hr'' : r / 2 + 1 < 2 ^ e := by rw [pow_succ] at h; omega
      have := hstrict hr''
      omega

private lemma cost_rep (e v : ℕ) :
    ∃ S : Multiset ℕ, S.sum = v ∧ S.card = cost e v ∧
      ∀ x ∈ S, ∃ i ≤ e, x = 2 ^ i := by
  induction e generalizing v with
  | zero =>
    refine ⟨Multiset.replicate v 1, by simp, by simp [cost], ?_⟩
    intro x hx
    exact ⟨0, by omega, by simpa using (Multiset.mem_replicate.mp hx).2⟩
  | succ e ih =>
    obtain ⟨S, hsum, hcard, hS⟩ := ih (v / 2)
    let D := S.map (fun x => 2 * x)
    have hD (x : ℕ) (hx : x ∈ D) : ∃ i ≤ e + 1, x = 2 ^ i := by
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
      obtain ⟨i, hi, rfl⟩ := hS a ha
      exact ⟨i + 1, by omega, by rw [pow_succ, mul_comm]⟩
    have hDsum : D.sum = 2 * (v / 2) := by
      have h := Multiset.sum_map_mul_left (s := S) (a := 2) (f := id)
      simpa [D, hsum] using h
    have hDcard : D.card = cost e (v / 2) := by simp [D, hcard]
    by_cases hv : v % 2 = 0
    · refine ⟨D, by omega, ?_, hD⟩
      simp [cost, hv, hDcard]
    · refine ⟨1 ::ₘ D, by simp only [Multiset.sum_cons, hDsum]; omega, ?_, ?_⟩
      · have he : v % 2 = 1 := by omega
        simp [cost, he, hDcard, add_comm]
      · intro x hx
        rcases Multiset.mem_cons.mp hx with rfl | hx
        · exact ⟨0, by omega, by simp⟩
        · exact hD x hx

private lemma cost_multiset_le (e : ℕ) (S : Multiset ℕ)
    (h : ∀ x ∈ S, x = 0 ∨ ∃ i ≤ e, x = 2 ^ i) : cost e S.sum ≤ S.card := by
  induction S using Multiset.induction_on with
  | empty =>
    induction e with
    | zero => simp [cost]
    | succ e ih => simpa [cost] using ih (by simp)
  | cons a S ih =>
    have hs := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    rcases h a (Multiset.mem_cons_self _ _) with rfl | ⟨i, hi, rfl⟩
    · simpa [Multiset.sum_cons] using hs.trans (Nat.le_succ _)
    · rw [Multiset.sum_cons, Multiset.card_cons, add_comm (2 ^ i)]
      exact (cost_add_pow e i S.sum hi).trans (Nat.add_le_add_right hs 1)

private lemma binary_subset (e r : ℕ) (hr : r < 2 ^ e) :
    ∃ D : Finset ℕ, D ⊆ range e ∧ ∑ i ∈ D, 2 ^ i = r := by
  induction e generalizing r with
  | zero =>
    have : r = 0 := by simpa using hr
    exact ⟨∅, empty_subset _, by simp [this]⟩
  | succ e ih =>
    by_cases he : r < 2 ^ e
    · obtain ⟨S, hsub, hsum⟩ := ih r he
      exact ⟨S, hsub.trans (range_mono (by omega)), hsum⟩
    · have hsmall : r - 2 ^ e < 2 ^ e := by rw [pow_succ] at hr; omega
      obtain ⟨S, hsub, hsum⟩ := ih _ hsmall
      have hnot : e ∉ S := fun h => Nat.lt_irrefl e (mem_range.mp (hsub h))
      refine ⟨insert e S, insert_subset (mem_range.mpr (by omega))
        (hsub.trans (range_mono (by omega))), ?_⟩
      rw [sum_insert hnot, hsum]
      omega

end OMA

namespace OMA

open Finset Filter
open scoped BigOperators ENat

private def period (e : ℕ) : ℕ := 3 * 2 ^ e - 1

private lemma pow_lt_period (e : ℕ) : 2 ^ e < period e := by
  have h : 0 < (2 : ℕ) ^ e := by positivity
  unfold period
  omega

private lemma period_pos (e : ℕ) : 0 < period e :=
  lt_of_le_of_lt (Nat.zero_le _) (pow_lt_period e)

private def largeCoins (e : ℕ) : Finset ℕ :=
  (range e).image fun i => 2 ^ (i + 1)

private def unitCoins (e : ℕ) : Finset ℕ :=
  (range (2 ^ e)).image fun j => 1 + period e * j

private def coins (e : ℕ) := unitCoins e ∪ largeCoins e

private def basis (e : ℕ) : Set ℕ := {x | period e ∣ x} ∪ ↑(coins e)

private lemma unit_value (e j : ℕ) : (1 + period e * j) % period e = 1 := by
  have h : 1 < period e := lt_of_le_of_lt (one_le_pow₀ (by decide)) (pow_lt_period e)
  simp [Nat.mod_eq_of_lt h]

private lemma large_value {e x : ℕ} (hx : x ∈ largeCoins e) :
    1 < x ∧ x ≤ 2 ^ e ∧ ∃ i ≤ e, x = 2 ^ i := by
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
  have he : i + 1 ≤ e := Nat.succ_le_of_lt (mem_range.mp hi)
  exact ⟨Nat.one_lt_two_pow (by omega), Nat.pow_le_pow_right (by decide) he, i + 1, he, rfl⟩

private lemma unit_injective (e : ℕ) : Function.Injective (fun j : ℕ => 1 + period e * j) := by
  intro a b hab
  change 1 + period e * a = 1 + period e * b at hab
  exact Nat.eq_of_mul_eq_mul_left (period_pos e) (by omega)

private lemma large_injective : Function.Injective (fun i : ℕ => (2 : ℕ) ^ (i + 1)) :=
  ((pow_right_strictMono₀ (by decide : (1 : ℕ) < 2)).comp
    (strictMono_nat_of_lt_succ fun i => by omega)).injective

private lemma coin_disjoint (e : ℕ) : Disjoint (unitCoins e) (largeCoins e) := by
  apply disjoint_left.mpr
  intro x hx hy
  obtain ⟨j, _, rfl⟩ := mem_image.mp hx
  obtain ⟨h1, h2, _⟩ := large_value hy
  have hm := unit_value e j
  rw [Nat.mod_eq_of_lt (h2.trans_lt (pow_lt_period e))] at hm
  omega

private lemma coin_card (e : ℕ) : (coins e).card = 2 ^ e + e := by
  rw [coins, card_union_of_disjoint (coin_disjoint e), unitCoins, largeCoins,
    card_image_of_injective _ (unit_injective e), card_image_of_injective _ large_injective,
    card_range, card_range]

private lemma coin_residue {e x : ℕ} (hx : x ∈ coins e) :
    ∃ i ≤ e, x % period e = 2 ^ i := by
  rcases mem_union.mp hx with hx | hx
  · obtain ⟨j, _, rfl⟩ := mem_image.mp hx
    exact ⟨0, Nat.zero_le _, by rw [unit_value, pow_zero]⟩
  · obtain ⟨_, hupper, i, hi, heq⟩ := large_value hx
    exact ⟨i, hi, (Nat.mod_eq_of_lt (hupper.trans_lt (pow_lt_period e))).trans heq⟩

private lemma coin_pos {e x : ℕ} (hx : x ∈ coins e) : 0 < x % period e := by
  obtain ⟨i, _, hi⟩ := coin_residue hx
  rw [hi]
  positivity

private lemma pow_mem_coins {e i : ℕ} (hi : i ≤ e) : 2 ^ i ∈ coins e := by
  cases i with
  | zero =>
    apply mem_union_left
    refine mem_image.mpr ⟨0, mem_range.mpr (by positivity), ?_⟩
    simp
  | succ i =>
    apply mem_union_right
    exact mem_image.mpr ⟨i, mem_range.mpr (by omega), rfl⟩

private lemma large_total (e : ℕ) : (∑ i ∈ range e, (2 : ℕ) ^ (i + 1)) + 2 = 2 * 2 ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [sum_range_succ, pow_succ 2 e]
    omega

private lemma residue_total (e : ℕ) : ∑ x ∈ coins e, x % period e = period e - 1 := by
  rw [coins, sum_union (coin_disjoint e), unitCoins, largeCoins,
    sum_image (unit_injective e).injOn, sum_image large_injective.injOn]
  simp_rw [unit_value]
  have hterm (i : ℕ) (hi : i ∈ range e) :
      2 ^ (i + 1) % period e = 2 ^ (i + 1) :=
    Nat.mod_eq_of_lt ((Nat.pow_le_pow_right (by decide)
      (Nat.succ_le_of_lt (mem_range.mp hi))).trans_lt (pow_lt_period e))
  rw [sum_congr rfl hterm]
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one, Nat.cast_id]
  have htotal := large_total e
  unfold period
  omega

private lemma small_cost (e r : ℕ) (hr : r < period e) : cost e r ≤ e + 1 := by
  let p := (2 : ℕ) ^ e
  let q := r / p
  let u := r % p
  have hpos : 0 < p := by dsimp [p]; positivity
  have hrepr : q * p + u = r := by simpa [q, u, mul_comm, add_comm] using Nat.mod_add_div r p
  have hlt : r < 3 * p - 1 := hr
  have hq : q ≤ 2 := by
    by_contra! h
    have hmul := Nat.mul_le_mul_right p h
    omega
  have hu : u < p := Nat.mod_lt _ hpos
  have hc := cost_bound e q u hu
  change cost e (q * p + u) ≤ q + e ∧
      (u + 1 < p → cost e (q * p + u) < q + e) at hc
  rw [hrepr] at hc
  by_cases h : q = 2
  · have hrepr' : 2 * p + u = r := h ▸ hrepr
    have hsmall : u + 1 < p := by omega
    have hb := hc.2 hsmall
    omega
  · omega

private lemma ordinary_upper (e : ℕ) : Erdos338.HasOrder (basis e) (e + 2) := by
  refine Filter.Eventually.of_forall fun n => ?_
  let M := period e
  let r := n % M
  obtain ⟨S, hsum, hcard, hmem⟩ := cost_rep e r
  have hc := small_cost e r (Nat.mod_lt _ (period_pos e))
  refine ⟨M * (n / M) ::ₘ S, ?_, ?_, ?_⟩
  · intro x hx
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · exact Or.inl (dvd_mul_right _ _)
    · obtain ⟨i, hi, rfl⟩ := hmem x hx
      exact Or.inr (pow_mem_coins hi)
  · simp only [Multiset.card_cons, hcard]
    omega
  · rw [Multiset.sum_cons, hsum, add_comm]
    exact Nat.mod_add_div n M

private lemma residue_cover (e r : ℕ) (hr : r < period e) :
    ∃ S ⊆ coins e, ∑ x ∈ S, x % period e = r := by
  let p := (2 : ℕ) ^ e
  let a := min (r / 2) (p - 1)
  let b := r - 2 * a
  have hpos : 0 < p := by dsimp [p]; positivity
  have ha : a < p := by dsimp [a]; omega
  have hab : 2 * a + b = r := by dsimp [a, b]; omega
  have hb : b ≤ p := by
    change r < 3 * p - 1 at hr
    dsimp [a, b]
    omega
  obtain ⟨D, hsub, hsum⟩ := binary_subset e a ha
  let S := D.image (fun i => 2 ^ (i + 1))
  let T := (range b).image (fun j => 1 + period e * j)
  have hS : S ⊆ largeCoins e := image_subset_image hsub
  have hT : T ⊆ unitCoins e := image_subset_image (range_mono hb)
  have hSsum : ∑ x ∈ S, x % period e = 2 * a := by
    calc
      _ = ∑ x ∈ S, x := sum_congr rfl fun x hx =>
        Nat.mod_eq_of_lt ((large_value (hS hx)).2.1.trans_lt (pow_lt_period e))
      _ = 2 * a := by
        dsimp [S]
        rw [sum_image large_injective.injOn]
        simp_rw [pow_succ, ← sum_mul, hsum, Nat.mul_comm]
  have hTsum : ∑ x ∈ T, x % period e = b := by
    dsimp [T]
    rw [sum_image (unit_injective e).injOn]
    simp_rw [unit_value]
    simp
  refine ⟨T ∪ S, union_subset_union hT hS, ?_⟩
  rw [sum_union ((coin_disjoint e).mono hT hS), hTsum, hSsum, add_comm, hab]

private lemma restricted_upper (e : ℕ) : Erdos338.HasRestrictedOrder (basis e) (2 ^ e + e + 1) := by
  let M := period e
  filter_upwards [eventually_gt_atTop (∑ x ∈ coins e, x)] with n hn
  let r := n % M
  obtain ⟨S, hsub, hsum⟩ := residue_cover e r (Nat.mod_lt _ (period_pos e))
  let t := ∑ x ∈ S, x
  have ht : t < n := lt_of_le_of_lt
    (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)) hn
  have hmods : t ≡ r [MOD M] := by
    rw [← hsum]
    exact Nat.ModEq.sum (fun x _ => (Nat.mod_mod x M).symm)
  have hdvd : M ∣ n - t :=
    (Nat.modEq_iff_dvd' ht.le).mp (hmods.trans (Nat.mod_mod n M))
  have hnot : n - t ∉ S := fun hs =>
    (coin_pos (hsub hs)).ne' (Nat.mod_eq_zero_of_dvd hdvd)
  refine ⟨insert (n - t) S, ?_, ?_, ?_⟩
  · intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact Or.inl hdvd
    · exact Or.inr (hsub hx)
  · have hc := card_le_card hsub
    rw [coin_card] at hc
    rw [card_insert_of_notMem hnot]
    omega
  · rw [sum_insert hnot]
    change n - t + t = n
    omega

private lemma large_congruent {M : ℕ} (hM : 0 < M) (r bound : ℕ) :
    ∃ n ≥ bound, n ≡ r [MOD M] := by
  refine ⟨r + M * bound, ?_, ?_⟩
  · have h := Nat.mul_le_mul_right bound (show 1 ≤ M by omega)
    simp only [one_mul] at h
    omega
  · unfold Nat.ModEq
    simp

private lemma cost_excludes_residue (e v : ℕ)
    (hmod : v ≡ 2 * 2 ^ e - 1 [MOD period e]) : e < cost e v := by
  let p := (2 : ℕ) ^ e
  let M := period e
  let u := v / M
  have hpos : 0 < p := by dsimp [p]; positivity
  have hM : M + 1 = 3 * p := by dsimp [M, period, p] at *; omega
  have hsmall : 2 * p - 1 < M := by omega
  have hm : v % M = 2 * p - 1 := by
    have := hmod
    change v % M = (2 * p - 1) % M at this
    simpa only [Nat.mod_eq_of_lt hsmall] using this
  have hv : v = M * u + (2 * p - 1) := by
    have h := Nat.mod_add_div v M
    rw [hm] at h
    change (2 * p - 1) + M * u = v at h
    omega
  have hA : v + u = (3 * u + 1) * p + (p - 1) := by
    calc
      _ = (M + 1) * u + (2 * p - 1) := by rw [hv]; ring
      _ = _ := by rw [hM, show 2 * p - 1 = p + (p - 1) by omega]; ring
  have hcost := cost_add_ones e v u
  rw [hA, show cost e ((3 * u + 1) * p + (p - 1)) = 3 * u + 1 + e from cost_full _ _] at hcost
  omega

private lemma ordinary_lower (e : ℕ) : ¬ Erdos338.HasOrder (basis e) (e + 1) := by
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  let M := period e
  let B := ∑ x ∈ coins e, x
  obtain ⟨n, hn, hmod⟩ :=
    large_congruent (period_pos e) (2 * 2 ^ e - 1) (max N ((e + 1) * B + 1))
  obtain ⟨S, hS, hcard, hsum⟩ := hN n (le_trans (le_max_left _ _) hn)
  have hnlarge : (e + 1) * B < n := lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_right _ _).trans hn)
  have hzero : ∃ x ∈ S, x % M = 0 := by
    by_contra! hnone
    have hB : ∀ x ∈ S, x ≤ B := by
      intro x hx
      have hc : x ∈ coins e := (hS x hx).resolve_left
        (fun hd => hnone x hx (Nat.mod_eq_zero_of_dvd hd))
      exact single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hc
    have hs := Multiset.sum_le_card_nsmul S B hB
    rw [hsum, nsmul_eq_mul] at hs
    exact hnlarge.not_ge (hs.trans (Nat.mul_le_mul_right _ hcard))
  obtain ⟨z, hz, hzmod⟩ := hzero
  let W := (S.erase z).map (fun x => x % M)
  have hwcard : W.card ≤ e := by
    change ((S.erase z).map _).card ≤ e
    rw [Multiset.card_map]
    have h := Multiset.card_erase_add_one hz
    omega
  have hwmod : W.sum ≡ 2 * 2 ^ e - 1 [MOD M] := by
    have hsumall : (S.map (fun x => x % M)).sum ≡ S.sum [MOD M] := by
      simpa using (Nat.ModEq.multisetSum_map (s := S) (g := id) (fun x _ => Nat.mod_mod x M))
    have he : (S.map (fun x => x % M)).sum = W.sum := by
      conv_lhs => rw [← Multiset.cons_erase hz]
      simp [W, hzmod]
    rw [he, hsum] at hsumall
    exact hsumall.trans hmod
  have hcost := cost_multiset_le e W (by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp ha
    rcases hS x (Multiset.mem_of_mem_erase hx) with hd | hc
    · exact Or.inl (Nat.mod_eq_zero_of_dvd hd)
    · exact Or.inr (coin_residue hc))
  exact (cost_excludes_residue e W.sum hwmod).not_ge (hcost.trans hwcard)

private lemma restricted_lower (e t : ℕ) (ht : Erdos338.HasRestrictedOrder (basis e) t) :
    2 ^ e + e + 1 ≤ t := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp ht
  let M := period e
  let B := ∑ x ∈ coins e, x
  obtain ⟨n, hn, hmod⟩ := large_congruent (period_pos e) (M - 1) (max N (B + 1))
  obtain ⟨S, hS, hcard, hsum⟩ := hN n (le_trans (le_max_left _ _) hn)
  have hnlarge : B < n := lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_right _ _).trans hn)
  let Q := S.filter (· ∈ coins e)
  have hQ : Q ⊆ coins e := fun _ hx => (mem_filter.mp hx).2
  have hQS : Q ⊆ S := filter_subset _ _
  have hQsum : (∑ x ∈ Q, x % M) = ∑ x ∈ S, x % M := by
    unfold Q
    rw [sum_filter]
    refine sum_congr rfl fun x hx => ?_
    by_cases hx' : x ∈ coins e
    · simp [hx']
    · have hzero : x % M = 0 := Nat.mod_eq_zero_of_dvd ((hS x hx).resolve_right hx')
      simp [hx', hzero]
  have hQmod : (∑ x ∈ Q, x % M) ≡ M - 1 [MOD M] := by
    rw [hQsum]
    have hc : (∑ x ∈ S, x % M) ≡ ∑ x ∈ S, x [MOD M] :=
      Nat.ModEq.sum (fun x _ => Nat.mod_mod x M)
    rw [hsum] at hc
    exact hc.trans hmod
  have hupper : (∑ x ∈ Q, x % M) ≤ M - 1 := by
    have h := sum_le_sum_of_subset_of_nonneg (f := fun x => x % M) hQ
      (fun _ _ _ => Nat.zero_le _)
    exact h.trans_eq (residue_total e)
  have hlt : M - 1 < M := by have := period_pos e; omega
  have hqeq : (∑ x ∈ Q, x % M) = M - 1 := by
    change (∑ x ∈ Q, x % M) % M = (M - 1) % M at hQmod
    rwa [Nat.mod_eq_of_lt (hupper.trans_lt hlt), Nat.mod_eq_of_lt hlt] at hQmod
  have hfull : coins e ⊆ Q := by
    by_contra hbad
    obtain ⟨x, hx, hxQ⟩ := not_subset.mp hbad
    have hsub : insert x Q ⊆ coins e := insert_subset hx hQ
    have hle := sum_le_sum_of_subset_of_nonneg (f := fun x => x % M) hsub
      (fun _ _ _ => Nat.zero_le _)
    have htotal : (∑ x ∈ coins e, x % M) = M - 1 := residue_total e
    rw [sum_insert hxQ, hqeq, htotal] at hle
    have hxpos : 0 < x % M := coin_pos hx
    omega
  have hcS : coins e ⊆ S := hfull.trans hQS
  have hne : coins e ≠ S := by
    intro heq
    apply hnlarge.not_ge
    rw [← hsum, ← heq]
  have hstrict := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hcS, hne⟩)
  rw [coin_card] at hstrict
  exact hstrict.trans_le hcard

end OMA

theorem OMA.solution : type_of% @Erdos338.erdos_338.variants.hegyvari_hennecart_plagne := by
  intro k hk
  obtain ⟨e, rfl⟩ : ∃ e, k = e + 2 := ⟨k - 2, by omega⟩
  refine ⟨OMA.basis e, ?_, ?_⟩
  · unfold Erdos338.basisOrder
    apply le_antisymm
    · exact iInf_le_of_le _ (iInf_le_of_le (OMA.ordinary_upper e) le_rfl)
    · refine le_iInf₂ fun t ht => ?_
      norm_cast
      by_contra! h
      apply OMA.ordinary_lower e
      refine ht.mono fun n hn => ?_
      obtain ⟨S, hmem, hc, hs⟩ := hn
      exact ⟨S, hmem, by omega, hs⟩
  · have hnum : (2 ^ ((e + 2) - 2) + (e + 2) - 1 : ℕ) = 2 ^ e + e + 1 := by
      rw [Nat.add_sub_cancel]
      have he : (2 : ℕ) ^ e + (e + 2) = 2 ^ e + e + 1 + 1 := by ring
      rw [he, Nat.add_sub_cancel]
    rw [hnum]
    unfold Erdos338.restrictedOrder
    apply le_antisymm
    · exact iInf_le_of_le _ (iInf_le_of_le (OMA.restricted_upper e) le_rfl)
    · refine le_iInf₂ fun t ht => ?_
      exact_mod_cast OMA.restricted_lower e t ht