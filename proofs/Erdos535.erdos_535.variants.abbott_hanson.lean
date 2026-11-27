import FormalConjectures.ErdosProblems.«535»
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
A pairwise GCD bound for families of positive integers.

For squarefree integers with a fixed number of prime factors, combine the sunflower
bound on the size of the family with a reciprocal moment bound on its prime supports.
The factorial from the sunflower bound cancels the factorial in the moment estimate.
A fixed power of the ambient bound absorbs the dependence on the number of prime
factors and leaves a summable geometric bound across the layers. Factoring out the
powerful part then costs only a convergent sum, by the square–cube representation.
-/

open Finset

namespace PowerfulSums

theorem square_cube {n : ℕ} (hn : 0 < n) (hfull : (2 : ℕ).Full n) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ^ 2 * b ^ 3 = n := by
  obtain ⟨b, c, hb, hc, heq, hsq⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hb0 : b ≠ 0 := by positivity
  have hc0 : c ≠ 0 := by positivity
  have hbcdvd : b ∣ c := by
    apply (Nat.factorization_le_iff_dvd hb0 hc0).mp
    intro p
    by_cases hp : p.Prime
    · by_cases hpdvd : p ∣ b
      · have hbp := Nat.factorization_eq_one_of_squarefree hsq hp hpdvd
        have hpn : p ∣ n := by rw [← heq]; exact dvd_mul_of_dvd_right hpdvd _
        have hp2 : p ^ 2 ∣ n := hfull p (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn.ne'⟩)
        have hp2 := (hp.pow_dvd_iff_le_factorization hn.ne').mp hp2
        rw [← heq, Nat.factorization_mul (pow_ne_zero _ hc0) hb0,
          Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hbp] at hp2
        omega
      · rw [Nat.factorization_eq_zero_of_not_dvd hpdvd]
        exact Nat.zero_le _
    · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
      exact Nat.zero_le _
  obtain ⟨a, ha⟩ := hbcdvd
  have ha0 : 0 < a := by
    by_contra! h
    have : a = 0 := by omega
    simp [this] at ha
    contradiction
  refine ⟨a, b, ha0, hb, ?_⟩
  rw [← heq, ha]
  ring

end PowerfulSums

namespace GcdFamilyBound

private def Sunless (r : ℕ) (F : Finset (Finset ℕ)) : Prop :=
  ∀ D ⊆ F, D.card = r → ¬ ∃ s : Finset ℕ,
    (D : Set (Finset ℕ)).Pairwise (fun U V => U ∩ V = s)

private theorem erase_fiber {r k : ℕ} {F : Finset (Finset ℕ)} (hfree : Sunless r F)
    (hsize : ∀ U ∈ F, U.card = k + 1) (p : ℕ) :
    let H := (F.filter (fun U => p ∈ U)).image (fun U => U.erase p)
    (∀ U ∈ H, U.card = k) ∧ Sunless r H ∧
      H.card = (F.filter (fun U => p ∈ U)).card := by
  dsimp
  have hmap : (↑(F.filter (fun U => p ∈ U)) : Set (Finset ℕ)).InjOn (fun U => U.erase p) := by
    intro U hU V hV h
    change U.erase p = V.erase p at h
    have hUp := (mem_filter.mp hU).2
    have hVp := (mem_filter.mp hV).2
    rw [← insert_erase hUp, ← insert_erase hVp, h]
  refine ⟨?_, ?_, card_image_of_injOn hmap⟩
  · intro U hU
    obtain ⟨V, hV, rfl⟩ := mem_image.mp hU
    obtain ⟨hVF, hpV⟩ := mem_filter.mp hV
    rw [card_erase_of_mem hpV, hsize V hVF]
    omega
  · intro D hD hd
    rintro ⟨s, hs⟩
    have hnot (U : Finset ℕ) (hU : U ∈ D) : p ∉ U := by
      obtain ⟨V, _, rfl⟩ := mem_image.mp (hD hU)
      exact notMem_erase _ _
    let L := D.image (insert p)
    have hLF : L ⊆ F := by
      intro U hU
      obtain ⟨V, hV, rfl⟩ := mem_image.mp hU
      obtain ⟨W, hW, rfl⟩ := mem_image.mp (hD hV)
      obtain ⟨hWF, hpW⟩ := mem_filter.mp hW
      rwa [insert_erase hpW]
    have hinj : (D : Set (Finset ℕ)).InjOn (insert p) := by
      intro U hU V hV h
      have he := congrArg (fun x : Finset ℕ => x.erase p) h
      simpa only [erase_insert (hnot U hU), erase_insert (hnot V hV)] using he
    have hL : L.card = r := (card_image_of_injOn hinj).trans hd
    apply hfree L hLF hL
    refine ⟨insert p s, ?_⟩
    intro U hU V hV huv
    obtain ⟨W, hW, rfl⟩ := mem_image.mp hU
    obtain ⟨Z, hZ, rfl⟩ := mem_image.mp hV
    have hWZ := hs hW hZ (ne_of_apply_ne _ huv)
    rw [← hWZ]
    ext q
    simp only [mem_inter, mem_insert]
    tauto

private theorem sunflower_card {r : ℕ} (hr : 2 ≤ r) (k : ℕ) (F : Finset (Finset ℕ))
    (hsize : ∀ U ∈ F, U.card = k) (hfree : Sunless r F) :
    F.card ≤ k.factorial * (r - 1) ^ k := by
  classical
  induction k generalizing F with
  | zero =>
    have hsub : F ⊆ {∅} := by
      intro U hU
      simpa using card_eq_zero.mp (hsize U hU)
    simpa using card_le_card hsub
  | succ k ih =>
    let G : Finset (Finset (Finset ℕ)) := F.powerset.filter (fun D => (D : Set (Finset ℕ)).Pairwise Disjoint)
    have hG : G.Nonempty := ⟨∅, by simp [G]⟩
    obtain ⟨D, hD, hmax⟩ := Finset.exists_max_image G (fun D : Finset (Finset ℕ) => D.card) hG
    obtain ⟨hDF, hdisj⟩ := mem_filter.mp hD
    have hDF := mem_powerset.mp hDF
    have hDcard : D.card ≤ r - 1 := by
      by_contra! h
      obtain ⟨L, hLD, hcard⟩ := exists_subset_card_eq (s := D) (n := r) (by omega)
      apply hfree L (hLD.trans hDF) hcard
      refine ⟨∅, fun U hU V hV hUV => ?_⟩
      exact disjoint_iff_inter_eq_empty.mp (hdisj (hLD hU) (hLD hV) hUV)
    let B := D.biUnion id
    have hBcard : B.card ≤ (r - 1) * (k + 1) := by
      calc
        _ ≤ ∑ U ∈ D, U.card := card_biUnion_le
        _ = D.card * (k + 1) := by
          rw [sum_congr rfl (fun U hU => hsize U (hDF hU))]
          simp
        _ ≤ _ := Nat.mul_le_mul_right _ hDcard
    have hmeet (U : Finset ℕ) (hU : U ∈ F) : ∃ p ∈ U, p ∈ B := by
      by_cases hUD : U ∈ D
      · obtain ⟨p, hp⟩ := card_pos.mp (show 0 < U.card by rw [hsize U hU]; omega)
        exact ⟨p, hp, mem_biUnion.mpr ⟨U, hUD, hp⟩⟩
      · by_contra! hn
        have hins : insert U D ∈ G := by
          refine mem_filter.mpr ⟨mem_powerset.mpr (insert_subset_iff.mpr ⟨hU, hDF⟩), ?_⟩
          intro V hV W hW hVW
          simp only [coe_insert, Set.mem_insert_iff] at hV hW
          have hd (V : Finset ℕ) (hVD : V ∈ D) : Disjoint U V :=
            disjoint_left.mpr fun p hp hpV => hn p hp (mem_biUnion.mpr ⟨V, hVD, hpV⟩)
          rcases hV with rfl | hVD <;> rcases hW with rfl | hWD
          · exact (hVW rfl).elim
          · exact hd W hWD
          · exact (hd V hVD).symm
          · exact hdisj hVD hWD hVW
        have hh := hmax (insert U D) hins
        rw [card_insert_of_notMem hUD] at hh
        omega
    have hcover : F ⊆ B.biUnion (fun p => F.filter (fun U => p ∈ U)) := by
      intro U hU
      obtain ⟨p, hpU, hpB⟩ := hmeet U hU
      exact mem_biUnion.mpr ⟨p, hpB, mem_filter.mpr ⟨hU, hpU⟩⟩
    have hfiber (p : ℕ) : (F.filter (fun U => p ∈ U)).card ≤ k.factorial * (r - 1) ^ k := by
      obtain ⟨hs, hf, hc⟩ := erase_fiber hfree hsize p
      rw [← hc]
      exact ih _ hs hf
    calc
      F.card ≤ ∑ p ∈ B, (F.filter (fun U => p ∈ U)).card :=
        (card_le_card hcover).trans card_biUnion_le
      _ ≤ ∑ p ∈ B, k.factorial * (r - 1) ^ k := sum_le_sum fun p _ => hfiber p
      _ = B.card * (k.factorial * (r - 1) ^ k) := by simp
      _ ≤ ((r - 1) * (k + 1)) * (k.factorial * (r - 1) ^ k) :=
        Nat.mul_le_mul_right _ hBcard
      _ = (k + 1).factorial * (r - 1) ^ (k + 1) := by
        rw [Nat.factorial_succ, pow_succ]
        ring

private def elementary (P : Finset ℕ) (w : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ U ∈ P.powersetCard k, ∏ p ∈ U, w p

-- Mark a member of each support and remove it to count the weighted supports.
private theorem elementary_step (P : Finset ℕ) (w : ℕ → ℝ) (k : ℕ) :
    (k + 1 : ℝ) * elementary P w (k + 1) =
      ∑ p ∈ P, w p * elementary (P.erase p) w k := by
  unfold elementary
  rw [mul_sum]
  calc
    _ = ∑ U ∈ P.powersetCard (k + 1), ∑ _p ∈ U, (∏ q ∈ U, w q) := by
      apply sum_congr rfl
      intro U hU
      simp [(mem_powersetCard.mp hU).2]
    _ = ∑ x ∈ (P.powersetCard (k + 1)).sigma (fun U => U), ∏ q ∈ x.1, w q := by
      rw [sum_sigma]
    _ = ∑ x ∈ P.sigma (fun p => (P.erase p).powersetCard k), w x.1 * ∏ q ∈ x.2, w q := by
      apply sum_bij (fun x _ => ⟨x.2, x.1.erase x.2⟩)
      · intro x hx
        obtain ⟨hx₁, hx₂⟩ := mem_sigma.mp hx
        obtain ⟨hxP, hxk⟩ := mem_powersetCard.mp hx₁
        exact mem_sigma.mpr ⟨hxP hx₂, mem_powersetCard.mpr ⟨erase_subset_erase _ hxP, by
          rw [card_erase_of_mem hx₂, hxk]
          omega⟩⟩
      · intro x hx y hy hxy
        obtain ⟨_, hx₂⟩ := mem_sigma.mp hx
        obtain ⟨_, hy₂⟩ := mem_sigma.mp hy
        have h₂ := congrArg (fun z : (Σ _ : ℕ, Finset ℕ) => z.1) hxy
        have h₁ := congrArg (fun z : (Σ _ : ℕ, Finset ℕ) => z.2) hxy
        change x.2 = y.2 at h₂
        change x.1.erase x.2 = y.1.erase y.2 at h₁
        have hxy' : x.1 = y.1 := by
          rw [← insert_erase hx₂, ← insert_erase hy₂, h₁, h₂]
        exact Sigma.ext hxy' (heq_of_eq h₂)
      · intro x hx
        obtain ⟨hp, hx₂⟩ := mem_sigma.mp hx
        obtain ⟨hxP, hxk⟩ := mem_powersetCard.mp hx₂
        have hnp : x.1 ∉ x.2 := notMem_mono hxP (notMem_erase _ _)
        refine ⟨⟨insert x.1 x.2, x.1⟩, mem_sigma.mpr ⟨?_, mem_insert_self _ _⟩, ?_⟩
        · exact mem_powersetCard.mpr ⟨insert_subset_iff.mpr ⟨hp, hxP.trans (erase_subset _ _)⟩,
            by rw [card_insert_of_notMem hnp, hxk]⟩
        · simp [erase_insert hnp]
      · intro x hx
        have hxp := (mem_sigma.mp hx).2
        rw [← prod_insert (notMem_erase x.2 x.1), insert_erase hxp]
    _ = _ := by rw [sum_sigma]; simp_rw [mul_sum]

private theorem elementary_le (P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p, 0 ≤ w p) (k : ℕ) :
    (k.factorial : ℝ) * elementary P w k ≤ (∑ p ∈ P, w p) ^ k := by
  induction k with
  | zero => simp [elementary]
  | succ k ih =>
    have hmono (p : ℕ) : elementary (P.erase p) w k ≤ elementary P w k :=
      sum_le_sum_of_subset_of_nonneg (powersetCard_mono (erase_subset _ _)) (fun U _ _ => Finset.prod_nonneg fun p _ => hw p)
    calc
      ((k + 1).factorial : ℝ) * elementary P w (k + 1) =
          (k.factorial : ℝ) * ((k + 1 : ℝ) * elementary P w (k + 1)) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      _ = (k.factorial : ℝ) * ∑ p ∈ P, w p * elementary (P.erase p) w k := by
        rw [elementary_step]
      _ ≤ (k.factorial : ℝ) * ∑ p ∈ P, w p * elementary P w k := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hmono p) (hw p)
      _ = ((k.factorial : ℝ) * elementary P w k) * (∑ p ∈ P, w p) := by
        rw [← sum_mul]
        ring
      _ ≤ (∑ p ∈ P, w p) ^ (k + 1) := by
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_right ih (sum_nonneg fun _ _ => hw _)

private def GcdFree (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ S ⊆ A, S.card = r → ¬ ∃ d : ℕ, (S : Set ℕ).Pairwise (fun a b => Nat.gcd a b = d)

private theorem support_injective {A : Finset ℕ} (hA : ∀ n ∈ A, Squarefree n) :
    (A : Set ℕ).InjOn Nat.primeFactors := by
  intro a ha b hb hab
  rw [← Nat.prod_primeFactors_of_squarefree (hA a ha), hab,
    Nat.prod_primeFactors_of_squarefree (hA b hb)]

private theorem support_sunless {r : ℕ} {A : Finset ℕ} (hA : ∀ n ∈ A, Squarefree n)
    (hfree : GcdFree r A) : Sunless r (A.image Nat.primeFactors) := by
  classical
  intro D hD hDr
  rintro ⟨s, hs⟩
  let S := A.filter (fun n => n.primeFactors ∈ D)
  have hSA : S ⊆ A := filter_subset _ _
  have himage : S.image Nat.primeFactors = D := by
    ext U
    constructor
    · rintro hU
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hU
      exact (mem_filter.mp hn).2
    · intro hU
      obtain ⟨n, hn, rfl⟩ := mem_image.mp (hD hU)
      exact mem_image.mpr ⟨n, mem_filter.mpr ⟨hn, hU⟩, rfl⟩
  have hi := (support_injective hA).mono (show (S : Set ℕ) ⊆ A from hSA)
  apply hfree S hSA ((card_image_of_injOn hi).symm.trans (congrArg card himage |>.trans hDr))
  refine ⟨∏ p ∈ s, p, ?_⟩
  intro a ha b hb hab
  have hga : Squarefree (Nat.gcd a b) := (hA a (hSA ha)).squarefree_of_dvd (Nat.gcd_dvd_left a b)
  have haD := (mem_filter.mp ha).2
  have hbD := (mem_filter.mp hb).2
  have hcore := hs haD hbD (fun he => hab (hi ha hb he))
  rw [← Nat.prod_primeFactors_of_squarefree hga]
  congr 1
  rw [Nat.primeFactors_gcd (hA a (hSA ha)).ne_zero (hA b (hSA hb)).ne_zero, hcore]

private theorem support_range {n X : ℕ} (hNX : n ≤ X) :
    n.primeFactors ⊆ Icc 1 X := by
  intro p hp
  obtain ⟨hprime, hdiv, hn⟩ := Nat.mem_primeFactors.mp hp
  exact mem_Icc.mpr ⟨hprime.pos, (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv).trans hNX⟩

private theorem support_weight {n : ℕ} (hn : Squarefree n) (t : ℝ) :
    (∏ p ∈ n.primeFactors, (p : ℝ) ^ t) = (n : ℝ) ^ t := by
  rw [Real.finsetProd_rpow _ (fun p : ℕ => (p : ℝ)) (fun p _ => Nat.cast_nonneg p) t,
    ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hn]

private theorem squarefree_layer {r X k : ℕ} (hr : 2 ≤ r) (hX : 0 < X)
    (s : ℝ) (hs : 1 < s) {C : Finset ℕ} (hCX : C ⊆ Icc 1 X)
    (hC : ∀ n ∈ C, Squarefree n) (hk : ∀ n ∈ C, n.primeFactors.card = k)
    (hfree : GcdFree r C) :
    (C.card : ℝ)^2 ≤ (X : ℝ)^s *
      ((∑' n : ℕ, (n : ℝ)^(-s)) * ((r - 1 : ℕ) : ℝ))^k := by
  classical
  let P := Icc 1 X
  let w (n : ℕ) : ℝ := (n : ℝ)^(-s)
  let H := ∑' n : ℕ, w n
  have hw (n : ℕ) : 0 ≤ w n := Real.rpow_nonneg (by positivity) _
  have hsum : Summable w := Real.summable_nat_rpow.mpr (by linarith)
  have hH : 0 ≤ H := tsum_nonneg hw
  have hm1 : (C.card : ℝ) ≤ (X : ℝ)^s * ∑ n ∈ C, ∏ p ∈ n.primeFactors, w p := by
    rw [mul_sum]
    calc
      (C.card : ℝ) = ∑ _n ∈ C, (1 : ℝ) := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro n hn
        have hnX := (mem_Icc.mp (hCX hn)).2
        have hpos : 0 < (n : ℝ) := by exact_mod_cast (hC n hn).ne_zero.bot_lt
        rw [show (∏ p ∈ n.primeFactors, w p) = (n : ℝ)^(-s) from support_weight (hC n hn) _,
          Real.rpow_neg hpos.le, ← div_eq_mul_inv]
        exact (le_div_iff₀ (Real.rpow_pos_of_pos hpos s)).mpr
          (by simpa only [one_mul] using Real.rpow_le_rpow hpos.le (by exact_mod_cast hnX) (by linarith))
  have hsubset : C.image Nat.primeFactors ⊆ P.powersetCard k := by
    intro U hU
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hU
    exact mem_powersetCard.mpr ⟨support_range (mem_Icc.mp (hCX hn)).2, hk n hn⟩
  have hi := support_injective hC
  have hsumle : (∑ n ∈ C, ∏ p ∈ n.primeFactors, w p) ≤ elementary P w k := by
    rw [← sum_image (f := fun U : Finset ℕ => ∏ p ∈ U, w p) hi]
    exact sum_le_sum_of_subset_of_nonneg hsubset (fun U _ _ => Finset.prod_nonneg fun p _ => hw p)
  have hm2 : (C.card : ℝ) * (k.factorial : ℝ) ≤ (X : ℝ)^s * H^k := by
    calc
      (C.card : ℝ) * (k.factorial : ℝ) ≤
          ((X : ℝ)^s * elementary P w k) * (k.factorial : ℝ) :=
        mul_le_mul_of_nonneg_right
          (hm1.trans (mul_le_mul_of_nonneg_left hsumle (by positivity))) (by positivity)
      _ = (X : ℝ)^s * ((k.factorial : ℝ) * elementary P w k) := by ring
      _ ≤ (X : ℝ)^s * H^k := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (elementary_le P w hw k).trans
          (pow_le_pow_left₀ (sum_nonneg fun p _ => hw p) (hsum.sum_le_tsum P (fun p _ => hw p)) k)
  have her := sunflower_card hr k (C.image Nat.primeFactors)
    (by intro U hU; obtain ⟨n, hn, rfl⟩ := mem_image.mp hU; exact hk n hn)
    (support_sunless hC hfree)
  rw [card_image_of_injOn hi] at her
  have her' : (C.card : ℝ) ≤ (k.factorial : ℝ) * ((r - 1 : ℕ) : ℝ)^k := by
    exact_mod_cast her
  have hc : (C.card : ℝ)^2 * (k.factorial : ℝ) ≤
      ((X : ℝ)^s * (H * ((r - 1 : ℕ) : ℝ))^k) * (k.factorial : ℝ) := by
    calc
      _ = ((C.card : ℝ) * (k.factorial : ℝ)) * (C.card : ℝ) := by ring
      _ ≤ ((X : ℝ)^s * H^k) * ((k.factorial : ℝ) * ((r - 1 : ℕ) : ℝ)^k) :=
        mul_le_mul hm2 her' (Nat.cast_nonneg _) (by positivity)
      _ = _ := by rw [mul_pow]; ring
  exact (mul_le_mul_iff_of_pos_right (by exact_mod_cast Nat.factorial_pos k)).mp hc

open Filter

-- Only the primes below B can contribute an extra factor Q.
private theorem pow_card_le {X k : ℕ} (Q δ : ℝ) (hQ : 1 ≤ Q) (hδ : 0 < δ)
    (B : ℕ) (hB : ∀ p : ℕ, B ≤ p → Q ≤ (p : ℝ)^δ)
    (n : ℕ) (hn : Squarefree n) (hnX : n ≤ X) (hk : n.primeFactors.card = k) :
    Q^k ≤ Q^B * (X : ℝ)^δ := by
  let U := n.primeFactors
  let L := U.filter (· < B)
  let W := U.filter (fun p => ¬ p < B)
  have hL : L.card ≤ B := by
    rw [← Finset.card_range B]
    apply card_le_card
    intro p hp
    exact mem_range.mpr (mem_filter.mp hp).2
  have hpos (p : ℕ) (hp : p ∈ U) : 1 ≤ (p : ℝ) := by
    exact_mod_cast (Nat.mem_primeFactors.mp hp).1.pos
  have hω (p : ℕ) (hp : p ∈ U) : 1 ≤ (p : ℝ)^δ := Real.one_le_rpow (hpos p hp) hδ.le
  calc
    Q^k = (∏ _p ∈ U, Q) := by simp [U, hk]
    _ = (∏ _p ∈ L, Q) * (∏ _p ∈ W, Q) :=
      (prod_filter_mul_prod_filter_not U (· < B) _).symm
    _ ≤ Q^B * ∏ p ∈ W, (p : ℝ)^δ := by
      refine mul_le_mul (by simpa only [prod_const] using pow_le_pow_right₀ hQ hL)
        (prod_le_prod (fun _ _ => by linarith) (fun p hp => hB p (by
          have := (mem_filter.mp hp).2
          omega))) (by positivity) (by positivity)
    _ ≤ Q^B * ∏ p ∈ U, (p : ℝ)^δ :=
      mul_le_mul_of_nonneg_left (prod_le_prod_of_subset_of_one_le (filter_subset _ _)
        (fun p hp => (Real.rpow_nonneg (by positivity) _))
        (fun p hp _ => hω p hp)) (by positivity)
    _ = Q^B * (n : ℝ)^δ := by rw [support_weight hn δ]
    _ ≤ Q^B * (X : ℝ)^δ := by gcongr

private theorem squarefree_bound {r : ℕ} (hr : 2 ≤ r) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ X : ℕ, 0 < X → ∀ A : Finset ℕ,
      A ⊆ Icc 1 X → (∀ n ∈ A, Squarefree n) → GcdFree r A →
      (A.card : ℝ) ≤ C₀ * (X : ℝ)^((1 : ℝ)/2 + δ) := by
  classical
  let H := ∑' n : ℕ, (n : ℝ)^(-(1 + δ))
  let J : ℝ := max 1 (H * ((r - 1 : ℕ) : ℝ))
  let Q := 4 * J
  have hJ : 1 ≤ J := le_max_left _ _
  have hHJ : H * ((r - 1 : ℕ) : ℝ) ≤ J := le_max_right _ _
  have hH : 0 ≤ H := tsum_nonneg fun _ => by positivity
  have hQ : 1 ≤ Q := by dsimp [Q]; linarith
  have hevent : ∀ᶠ p : ℕ in atTop, Q ≤ (p : ℝ)^δ :=
    ((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop Q
  obtain ⟨B, hB⟩ := eventually_atTop.mp hevent
  let K := Q^B
  have hK : 1 ≤ K := one_le_pow₀ hQ
  refine ⟨2*K, by linarith, ?_⟩
  intro X hX A hAX hA hf
  let t : ℝ := 1/2 + δ
  let L (k : ℕ) := A.filter (fun n => n.primeFactors.card = k)
  have hX' : 0 < (X : ℝ) := by exact_mod_cast hX
  have hlayer (k : ℕ) : ((L k).card : ℝ) ≤ K * (X : ℝ)^t * (1/2 : ℝ)^k := by
    by_cases he : (L k).Nonempty
    · obtain ⟨n, hn⟩ := he
      obtain ⟨hnA, hnk⟩ := mem_filter.mp hn
      have hnX := (mem_Icc.mp (hAX hnA)).2
      have hpow := pow_card_le Q δ hQ hδ B hB n (hA n hnA) hnX hnk
      have hsub : L k ⊆ A := filter_subset _ _
      have hmoment := squarefree_layer hr hX (1 + δ) (by linarith)
        (hsub.trans hAX) (fun m hm => hA m (hsub hm))
        (fun m hm => (mem_filter.mp hm).2)
        (fun S hS => hf S (hS.trans hsub))
      have hmoment' : ((L k).card : ℝ)^2 ≤ (X : ℝ)^(1 + δ)*J^k :=
        hmoment.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hHJ k) (by positivity))
      have hsquare : (((L k).card : ℝ)*2^k)^2 ≤ (K*(X : ℝ)^t)^2 := by
        calc
          _ = ((L k).card : ℝ)^2 * 4^k := by
            rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul]
            norm_num
          _ ≤ ((X : ℝ)^(1 + δ)*J^k)*4^k := mul_le_mul_of_nonneg_right hmoment' (by positivity)
          _ = (X : ℝ)^(1 + δ)*Q^k := by dsimp [Q]; rw [mul_pow]; ring
          _ ≤ (X : ℝ)^(1 + δ)*(K*(X : ℝ)^δ) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
          _ = K*((X : ℝ)^t)^2 := by
            rw [← Real.rpow_mul_natCast hX'.le t 2]
            rw [show (X : ℝ)^(1 + δ)*(K*(X : ℝ)^δ) =
              K*((X : ℝ)^(1 + δ)*(X : ℝ)^δ) by ring, ← Real.rpow_add hX']
            rw [show 1 + δ + δ = t * (2 : ℕ) by dsimp [t]; ring]
          _ ≤ (K*(X : ℝ)^t)^2 := by
            rw [mul_pow]
            exact mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
      have hle : ((L k).card : ℝ)*2^k ≤ K*(X : ℝ)^t :=
        le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (by positivity) hsquare
      rw [div_pow, one_pow, one_div, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      exact hle
    · rw [not_nonempty_iff_eq_empty.mp he]
      simp only [card_empty, Nat.cast_zero]
      positivity
  have hsub : A ⊆ (range (X+1)).biUnion L := by
    intro n hn
    have hcard := card_le_card (support_range (mem_Icc.mp (hAX hn)).2)
    simp at hcard
    exact mem_biUnion.mpr ⟨n.primeFactors.card, mem_range.mpr (by omega), mem_filter.mpr ⟨hn, rfl⟩⟩
  have hAc : (A.card : ℝ) ≤ ∑ k ∈ range (X+1), ((L k).card : ℝ) := by
    exact_mod_cast (card_le_card hsub).trans card_biUnion_le
  have hsummable := summable_geometric_of_lt_one (by norm_num : 0 ≤ (1/2 : ℝ))
    (by norm_num : (1/2 : ℝ) < 1)
  have hseries : ∑ k ∈ range (X+1), (1/2 : ℝ)^k ≤ 2 := by
    let hs := hsummable.sum_le_tsum (range (X+1)) (fun k _ => by positivity)
    refine hs.trans_eq ?_
    rw [tsum_geometric_of_lt_one (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num)]
    norm_num
  calc
    (A.card : ℝ) ≤ ∑ k ∈ range (X+1), ((L k).card : ℝ) := hAc
    _ ≤ ∑ k ∈ range (X+1), K*(X : ℝ)^t*(1/2 : ℝ)^k := sum_le_sum fun k _ => hlayer k
    _ ≤ (2*K)*(X : ℝ)^t := by
      rw [← mul_sum]
      nlinarith [mul_le_mul_of_nonneg_left hseries (show 0 ≤ K*(X : ℝ)^t by positivity)]

private theorem powerful_squarefree {n : ℕ} (hn : 0 < n) :
    ∃ q b : ℕ, 0 < q ∧ 0 < b ∧ (2 : ℕ).Full q ∧ Squarefree b ∧ q*b = n := by
  let H := n.factorization.filter (fun p => 2 ≤ n.factorization p)
  let L := n.factorization.filter (fun p => ¬ 2 ≤ n.factorization p)
  let q := H.prod (fun p e => p^e)
  let b := L.prod (fun p e => p^e)
  have hq_b : q*b = n := by
    change H.prod _ * L.prod _ = n
    rw [← Finsupp.prod_add_index' (fun p : ℕ => pow_zero p) (fun p a b => pow_add p a b)]
    rw [Finsupp.filter_add_filter_not, Nat.prod_factorization_pow_eq_self hn.ne']
  have hq : 0 < q := by
    by_contra! h
    simp [Nat.eq_zero_of_le_zero h] at hq_b
    omega
  have hb : 0 < b := by
    by_contra! h
    simp [Nat.eq_zero_of_le_zero h] at hq_b
    omega
  have hH : H ≤ n.factorization := by
    intro p
    dsimp [H]
    rw [Finsupp.filter_apply]
    split <;> omega
  have hL : L ≤ n.factorization := by
    intro p
    dsimp [L]
    rw [Finsupp.filter_apply]
    split <;> omega
  have hqf : q.factorization = H := Nat.factorization_prod_pow_eq_self_of_le_factorization hH
  have hbf : b.factorization = L := Nat.factorization_prod_pow_eq_self_of_le_factorization hL
  refine ⟨q, b, hq, hb, ?_, ?_, hq_b⟩
  · intro p hp
    have hp' := (Nat.mem_primeFactors.mp hp).1
    apply (hp'.pow_dvd_iff_le_factorization hq.ne').mpr
    have hnz : q.factorization p ≠ 0 := by
      exact Finsupp.mem_support_iff.mp (by simpa only [Nat.support_factorization] using hp)
    rw [hqf] at hnz ⊢
    dsimp [H] at hnz ⊢
    rw [Finsupp.filter_apply] at hnz ⊢
    split at hnz <;> simp_all
  · apply Nat.squarefree_of_factorization_le_one hb.ne'
    intro p
    rw [hbf]
    dsimp [L]
    rw [Finsupp.filter_apply]
    split <;> omega

private theorem gcd_free_fiber {r X q : ℕ} (hq : 0 < q) {A : Finset ℕ} (hf : GcdFree r A) :
    GcdFree r ((Icc 1 X).filter (fun b => Squarefree b ∧ q*b ∈ A)) := by
  intro S hS hSr
  rintro ⟨d, hd⟩
  have hi : Function.Injective (fun b : ℕ => q * b) := fun _ _ he =>
    Nat.eq_of_mul_eq_mul_left hq he
  let D := S.image (fun b => q*b)
  have hDA : D ⊆ A := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
    exact (mem_filter.mp (hS hb)).2.2
  have hDr : D.card = r := (card_image_of_injective S hi).trans hSr
  apply hf D hDA hDr
  refine ⟨q*d, ?_⟩
  intro a ha b hb hab
  obtain ⟨x, hx, rfl⟩ := mem_image.mp ha
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hb
  rw [Nat.gcd_mul_left, hd hx hy (ne_of_apply_ne _ hab)]

private def powerfulUpTo (N : ℕ) : Finset ℕ := (Icc 1 N).filter (Nat.Full 2)

private theorem powerful_weight (N : ℕ) (t : ℝ) (ht : 1/2 < t) :
    (∑ q ∈ powerfulUpTo N, (q : ℝ)^(-t)) ≤
      (∑' a : ℕ, (a : ℝ)^(-(2*t))) * (∑' b : ℕ, (b : ℝ)^(-(3*t))) := by
  classical
  let P := Icc 1 N
  let T := P ×ˢ P
  let f (x : ℕ × ℕ) := x.1^2 * x.2^3
  have hex (q : ℕ) (hq : q ∈ powerfulUpTo N) : ∃ x ∈ T, f x = q := by
    obtain ⟨hqI, hfull⟩ := mem_filter.mp hq
    obtain ⟨hq1, hqN⟩ := mem_Icc.mp hqI
    obtain ⟨a, b, ha, hb, hab⟩ := PowerfulSums.square_cube hq1 hfull
    have haN := (Nat.le_of_dvd hq1 (show a ∣ q by
      rw [← hab]
      exact dvd_mul_of_dvd_left (dvd_pow_self a (by decide : 2 ≠ 0)) _)).trans hqN
    have hbN := (Nat.le_of_dvd hq1 (show b ∣ q by
      rw [← hab]
      exact dvd_mul_of_dvd_right (dvd_pow_self b (by decide : 3 ≠ 0)) _)).trans hqN
    exact ⟨(a,b), mem_product.mpr ⟨mem_Icc.mpr ⟨ha, haN⟩, mem_Icc.mpr ⟨hb, hbN⟩⟩, hab⟩
  let g (q : ℕ) := if h : q ∈ powerfulUpTo N then (hex q h).choose else (0,0)
  have hg (q : ℕ) (hq : q ∈ powerfulUpTo N) : g q ∈ T ∧ f (g q) = q := by
    simpa only [g, dif_pos hq] using (hex q hq).choose_spec
  have hsub : (powerfulUpTo N).image g ⊆ T := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hx
    exact (hg q hq).1
  have hi : ((powerfulUpTo N : Finset ℕ) : Set ℕ).InjOn g := by
    intro q hq q' hq' h
    rw [← (hg q hq).2, ← (hg q' hq').2, h]
  let w (x : ℕ × ℕ) : ℝ := (f x : ℝ)^(-t)
  have hw_eq (x : ℕ × ℕ) :
      w x = (x.1 : ℝ)^(-(2*t)) * (x.2 : ℝ)^(-(3*t)) := by
    dsimp [w, f]
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast_mul (by positivity),
      ← Real.rpow_natCast_mul (by positivity)]
    push_cast
    rw [mul_neg, mul_neg]
  have hs₂ : Summable (fun a : ℕ => (a : ℝ)^(-(2*t))) := Real.summable_nat_rpow.mpr (by linarith)
  have hs₃ : Summable (fun b : ℕ => (b : ℝ)^(-(3*t))) := Real.summable_nat_rpow.mpr (by linarith)
  calc
    _ = ∑ q ∈ powerfulUpTo N, w (g q) := by
      apply sum_congr rfl
      intro q hq
      dsimp [w]
      rw [(hg q hq).2]
    _ = ∑ x ∈ (powerfulUpTo N).image g, w x := (sum_image hi).symm
    _ ≤ ∑ x ∈ T, w x := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = (∑ a ∈ P, (a : ℝ)^(-(2*t))) * (∑ b ∈ P, (b : ℝ)^(-(3*t))) := by
      simp_rw [hw_eq]
      rw [sum_product, sum_mul]
      simp_rw [mul_sum]
    _ ≤ _ := mul_le_mul (hs₂.sum_le_tsum _ (fun _ _ => by positivity))
      (hs₃.sum_le_tsum _ (fun _ _ => by positivity)) (by positivity) (by positivity)

private theorem gcd_free_bound {r : ℕ} (hr : 2 ≤ r) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, ∀ N : ℕ, 0 < N → ∀ A : Finset ℕ, A ⊆ Icc 1 N → GcdFree r A →
      (A.card : ℝ) ≤ K * (N : ℝ)^((1 : ℝ)/2 + δ) := by
  classical
  obtain ⟨C₀, hC₀, hsq⟩ := squarefree_bound hr hδ
  let t : ℝ := 1/2 + δ
  let H : ℝ := (∑' a : ℕ, (a : ℝ)^(-(2*t))) * (∑' b : ℕ, (b : ℝ)^(-(3*t)))
  refine ⟨C₀ * H, ?_⟩
  intro N hN A hAX hf
  let B (q : ℕ) := (Icc 1 (N / q)).filter (fun b => Squarefree b ∧ q*b ∈ A)
  have hcover : A ⊆ (powerfulUpTo N).biUnion (fun q => (B q).image (fun b => q*b)) := by
    intro n hn
    obtain ⟨hnpos, hnN⟩ := mem_Icc.mp (hAX hn)
    obtain ⟨q, b, hq, hb, hfull, hsq, hqb⟩ := powerful_squarefree hnpos
    have hqN : q ≤ N := (Nat.le_of_dvd hnpos (show q ∣ n from ⟨b, hqb.symm⟩)).trans hnN
    have hbN : b ≤ N / q := (Nat.le_div_iff_mul_le hq).mpr (by rw [mul_comm, hqb]; exact hnN)
    refine mem_biUnion.mpr ⟨q, mem_filter.mpr ⟨mem_Icc.mpr ⟨hq, hqN⟩, hfull⟩, ?_⟩
    exact mem_image.mpr ⟨b, mem_filter.mpr ⟨mem_Icc.mpr ⟨hb,hbN⟩, hsq, hqb ▸ hn⟩, hqb⟩
  have hfiber (q : ℕ) (hq : q ∈ powerfulUpTo N) :
      ((B q).card : ℝ) ≤ C₀ * (N : ℝ)^t * (q : ℝ)^(-t) := by
    obtain ⟨hq₀, hqN⟩ := mem_Icc.mp (mem_filter.mp hq).1
    have hBq : ((B q).card : ℝ) ≤ C₀ * ((N / q : ℕ) : ℝ)^t :=
      hsq (N / q) (Nat.div_pos hqN hq₀) (B q) (filter_subset _ _)
        (fun b hb => (mem_filter.mp hb).2.1) (gcd_free_fiber hq₀ hf)
    have hdiv : ((N / q : ℕ) : ℝ) ≤ (N : ℝ)/(q : ℝ) := by
      apply (le_div_iff₀ (by exact_mod_cast hq₀ : 0 < (q : ℝ))).mpr
      exact_mod_cast Nat.div_mul_le_self N q
    have ht : 0 < t := by dsimp [t]; linarith
    calc
      _ ≤ C₀ * ((N / q : ℕ) : ℝ)^t := hBq
      _ ≤ C₀ * ((N : ℝ)/(q : ℝ))^t :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hdiv ht.le) (by linarith)
      _ = _ := by
        rw [Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity), div_eq_mul_inv]
        ring
  have hAc : (A.card : ℝ) ≤ ∑ q ∈ powerfulUpTo N, ((B q).card : ℝ) := by
    have hcount : A.card ≤ ∑ q ∈ powerfulUpTo N, (B q).card := by
      calc
        _ ≤ ∑ q ∈ powerfulUpTo N, ((B q).image (fun b => q*b)).card :=
          (card_le_card hcover).trans card_biUnion_le
        _ ≤ _ := sum_le_sum fun q _ => card_image_le
    exact_mod_cast hcount
  have hweight : (∑ q ∈ powerfulUpTo N, (q : ℝ)^(-t)) ≤ H :=
    powerful_weight N t (by dsimp [t]; linarith)
  calc
    _ ≤ ∑ q ∈ powerfulUpTo N, ((B q).card : ℝ) := hAc
    _ ≤ ∑ q ∈ powerfulUpTo N, C₀ * (N : ℝ)^t * (q : ℝ)^(-t) := sum_le_sum hfiber
    _ ≤ C₀ * (N : ℝ)^t * H := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left hweight (mul_nonneg (by linarith) (by positivity))
    _ = _ := by ring

private theorem f_le {r : ℕ} (hr : 2 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (Erdos535.f r N : ℝ) ≤ (N : ℝ)^((1 : ℝ)/2 + ε) := by
  obtain ⟨K, hK⟩ := gcd_free_bound hr (show 0 < ε/2 by linarith)
  have hlarge : ∀ᶠ N : ℕ in atTop, K ≤ (N : ℝ)^(ε/2) :=
    ((tendsto_rpow_atTop (show 0 < ε/2 by linarith)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop K
  filter_upwards [hlarge, eventually_ge_atTop (1 : ℕ)] with N hKN hN
  let C := {k : ℕ | ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧ GcdFree r A ∧ A.card = k}
  have hC₁ : C.Nonempty := by
    refine ⟨0, ∅, empty_subset _, ?_, card_empty⟩
    intro S hS hSr
    have he : S = ∅ := subset_empty.mp hS
    simp [he] at hSr
    omega
  have hC₂ : BddAbove C := by
    refine ⟨N, ?_⟩
    intro k hk
    obtain ⟨A, hA, _, rfl⟩ := hk
    simpa using card_le_card hA
  change ((sSup C : ℕ) : ℝ) ≤ _
  obtain ⟨A, hA, hf, he⟩ := Nat.sSup_mem hC₁ hC₂
  have hpos : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [← he]
  calc
    _ ≤ K * (N : ℝ)^((1 : ℝ)/2 + ε/2) := hK N hN A hA hf
    _ ≤ (N : ℝ)^(ε/2) * (N : ℝ)^((1 : ℝ)/2 + ε/2) :=
      mul_le_mul_of_nonneg_right hKN (by positivity)
    _ = _ := by rw [← Real.rpow_add hpos]; congr 1; ring

end GcdFamilyBound

theorem OMA.solution : type_of% @Erdos535.erdos_535.variants.abbott_hanson := by
  intro r hr ε hε
  exact GcdFamilyBound.f_le (by omega) ε hε