import FormalConjectures.ErdosProblems.«636»
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
Choose the edge indicators independently and uniformly. A finite product
average bounds the number of graphs with an edge count far from its mean
on any vertex set, as well as those with a large homogeneous set.

Credit: @Genbox.
-/

open Finset SimpleGraph Real Filter

namespace OMA

private abbrev Labels (n : ℕ) := Sym2 (Fin n) → Bool

private def pairs {n : ℕ} (S : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  S.sym2.filter (fun e => ¬e.IsDiag)

private def graph {n : ℕ} (f : Labels n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e | f e = true}

private theorem pairs_card {n : ℕ} (S : Finset (Fin n)) :
    (pairs S).card = S.card.choose 2 := by
  classical
  have hdiag : S.sym2.filter Sym2.IsDiag = S.image Sym2.diag := by
    ext e
    induction e using Sym2.ind with
    | h a b =>
      simp only [mem_filter, Sym2.mk_isDiag_iff, mem_image]
      constructor
      · rintro ⟨hS, rfl⟩
        exact ⟨a, diag_mem_sym2_iff.mp hS, rfl⟩
      · rintro ⟨c, hC, he⟩
        exact ⟨he ▸ (diag_mem_sym2_iff.mpr hC), Sym2.mk_isDiag_iff.mp (he ▸ Sym2.diag_isDiag c)⟩
  have h := card_filter_add_card_filter_not (s := S.sym2) Sym2.IsDiag
  rw [hdiag, card_image_of_injective _ Sym2.diag_injective, card_sym2,
    Nat.choose_succ_succ] at h
  simp at h
  exact by unfold pairs; omega

private def edgeCount {n : ℕ} (f : Labels n) (S : Finset (Fin n)) : ℕ :=
  ((pairs S).filter (fun e => f e = true)).card

private theorem edgeCount_eq {n : ℕ} (f : Labels n) (S : Finset (Fin n)) :
    ((graph f).induce (S : Set (Fin n))).edgeSet.ncard = edgeCount f S := by
  classical
  let G := graph f
  have h := card_filter_edgeFinset_toFinset_subset (G := G) S
  rw [filter_edgeFinset_toFinset_subset] at h
  have hfin : G.edgeFinset ∩ S.sym2 = (pairs S).filter (fun e => f e = true) := by
    ext e
    rw [mem_inter, mem_edgeFinset]
    simp only [mem_filter, G, graph, edgeSet_fromEdgeSet, Set.mem_sdiff,
      Set.mem_ofPred_eq, Sym2.mem_diagSet, pairs]
    tauto
  rw [hfin] at h
  change (G.induce (S : Set (Fin n))).edgeSet.ncard = _
  rw [← coe_edgeFinset, Set.ncard_coe_finset]
  exact h.symm

private noncomputable def weight {ι : Type*} (S : Finset ι) (p : Bool → ℝ) (f : ι → Bool) : ℝ :=
  ∏ i ∈ S, p (f i)

private theorem sum_weight {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι) (p : Bool → ℝ)
    (hp : p false + p true = 2) :
    ∑ f : ι → Bool, weight S p f = (2:ℝ)^(Fintype.card ι) := by
  classical
  let q (i : ι) (b : Bool) := if i ∈ S then p b else 1
  have h (f : ι → Bool) : weight S p f = ∏ i, q i (f i) := by
    simp [q, weight]
  have hq (i : ι) : (∑ b : Bool, q i b) = 2 := by
    rw [Fintype.sum_bool]
    by_cases hi : i ∈ S <;> norm_num [q, hi, hp, add_comm]
  simp_rw [h, ← Fintype.prod_sum, hq, prod_const, card_univ]

private noncomputable def biased (t : ℝ) (c b : Bool) : ℝ :=
  if b = c then 1+t else 1-t

private def homogeneous (c b : Bool) : ℝ :=
  if b = c then 2 else 0

private theorem log_biased_lower {t : ℝ} (h0 : 0 ≤ t) (ht : t ≤ 1/2) :
    t-2*t^2 ≤ log (1+t) ∧ -t-2*t^2 ≤ log (1-t) := by
  have hp : 0 < 1+t := by linarith
  have hm : 0 < 1-t := by linarith
  constructor
  · refine le_trans ?_ (one_sub_inv_le_log_of_pos hp)
    have h : (1+t)⁻¹ ≤ 1-t+2*t^2 := by
      rw [← one_div]
      apply (div_le_iff₀ (show 0 < 1+t by linarith)).mpr
      nlinarith [mul_nonneg (sq_nonneg t) h0]
    linarith
  · refine le_trans ?_ (one_sub_inv_le_log_of_pos hm)
    have h : (1-t)⁻¹ ≤ 1+t+2*t^2 := by
      rw [← one_div]
      apply (div_le_iff₀ hm).mpr
      nlinarith [mul_nonneg (sq_nonneg t) (show 0 ≤ 1-2*t by linarith)]
    linarith

private theorem weight_log_bound {ι : Type*} (S : Finset ι) (f : ι → Bool) (c : Bool)
    {t : ℝ} (h0 : 0 ≤ t) (ht : t ≤ 1/2) :
    t * (2 * (((S.filter (fun i => f i = c)).card : ℕ):ℝ) - (S.card:ℝ)) -
      2*t^2*S.card ≤ log (weight S (biased t c) f) := by
  classical
  have hpos (b : Bool) : 0 < biased t c b := by
    unfold biased
    split_ifs <;> linarith
  unfold weight
  rw [log_prod (fun i _ => (hpos _).ne')]
  rw [← sum_filter_add_sum_filter_not S (fun i => f i = c)]
  have hcard := card_filter_add_card_filter_not (s := S) (fun i => f i = c)
  have hc : (((S.filter fun i => f i = c).card : ℕ):ℝ) +
      (((S.filter fun i => f i ≠ c).card : ℕ):ℝ) = (S.card:ℝ) := by exact_mod_cast hcard
  have h1 : (∑ i ∈ S.filter (fun i => f i = c), log (biased t c (f i))) =
      ((S.filter (fun i => f i = c)).card:ℝ)*log (1+t) := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_congr rfl (fun i hi => by simp [biased, (mem_filter.mp hi).2])
  have h2 : (∑ i ∈ S.filter (fun i => f i ≠ c), log (biased t c (f i))) =
      ((S.filter (fun i => f i ≠ c)).card:ℝ)*log (1-t) := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_congr rfl (fun i hi => by simp [biased, (mem_filter.mp hi).2])
  rw [h1, h2]
  obtain ⟨hp, hm⟩ := log_biased_lower h0 ht
  have hh1 := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (α:=ℝ) (S.filter (fun i => f i = c)).card)
  have hh2 := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (α:=ℝ) (S.filter (fun i => f i ≠ c)).card)
  linear_combination hh1 + hh2 + (t+2*t^2)*hc

private theorem total_weight {ι β : Type*} [Fintype ι] [DecidableEq ι] (T : Finset β)
    (S : β → Finset ι) (p : Bool → Bool → ℝ)
    (hp : ∀ c, p c false + p c true = 2) (w : ℝ) :
    (∑ f : ι → Bool, ∑ v ∈ T, ∑ c : Bool, w*weight (S v) (p c) f) =
      (2:ℝ)^(Fintype.card ι) * (2*w*T.card) := by
  classical
  rw [sum_comm]
  calc
    _ = ∑ _v ∈ T, ∑ _c : Bool, w*(2:ℝ)^(Fintype.card ι) := by
      apply sum_congr rfl
      intro v hv
      rw [sum_comm]
      simp_rw [← mul_sum, sum_weight (S v) _ (hp _)]
    _ = _ := by simp; ring

private theorem log_two_bounds : (1:ℝ)/2 ≤ log 2 ∧ log 2 ≤ 1 := by
  have h := one_sub_inv_le_log_of_pos (by norm_num : 0 < (2:ℝ))
  have h' := log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ))
  norm_num at h h'
  exact ⟨h,h'⟩

private theorem choose_two_cast {k : ℕ} (hk : 1 ≤ k) :
    2*(k.choose 2:ℝ) = (k:ℝ)*((k:ℝ)-1) := by
  have h : 2 * k.choose 2 = k*(k-1) := by
    rw [Nat.choose_two_right]
    have hd : 2 ∣ k*(k-1) := by
      rcases Nat.even_or_odd k with he | ho
      · exact dvd_mul_of_dvd_left (even_iff_two_dvd.mp he) _
      · obtain ⟨m, hm⟩ := ho
        have he : k-1 = 2*m := by omega
        rw [he]
        exact dvd_mul_of_dvd_right (dvd_mul_right 2 m) _
    exact Nat.mul_div_cancel' hd
  have h' : (2:ℝ)*(k.choose 2:ℝ) = (k:ℝ)*((k-1:ℕ):ℝ) := by exact_mod_cast h
  simpa [Nat.cast_sub hk] using h'

private theorem homogeneous_weight_bound {n k : ℕ} (hn : 4 ≤ n)
    (hk : 8*log (n:ℝ)+1 ≤ (k:ℝ)) :
    2 * ((2:ℝ)^(k.choose 2))⁻¹ * (n.choose k:ℝ) ≤ 1/2 := by
  have hn' : (4:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by positivity
  have hl0 : 0 ≤ log (n:ℝ) := log_nonneg (by linarith)
  have hk' : 1 ≤ k := by exact_mod_cast (show (1:ℝ) ≤ k by linarith)
  have hkc : 0 ≤ (k:ℝ) := by positivity
  have hprod : (n:ℝ)^k * (n:ℝ)^k ≤ (2:ℝ)^(k.choose 2) := by
    apply (log_le_log_iff (by positivity) (by positivity)).mp
    rw [log_mul (by positivity) (by positivity)]
    simp only [log_pow]
    have hchoose := choose_two_cast hk'
    have hA := mul_le_mul_of_nonneg_left (show 8*log (n:ℝ) ≤ (k:ℝ)-1 by linarith) hkc
    have hB := mul_le_mul_of_nonneg_left log_two_bounds.1 (Nat.cast_nonneg (k.choose 2))
    nlinarith only [hchoose, hA, hB]
  have hK : 1 ≤ k := hk'
  have hp : (4:ℝ) ≤ (n:ℝ)^k := hn'.trans (by
    simpa only [pow_one] using pow_le_pow_right₀ (show (1:ℝ) ≤ n by linarith) hK)
  have hc : (n.choose k:ℝ) ≤ (n:ℝ)^k := by exact_mod_cast Nat.choose_le_pow n k
  have he : (n:ℝ)^k/((2:ℝ)^(k.choose 2)) ≤ 1/4 := by
    apply (div_le_iff₀ (show 0 < (2:ℝ)^(k.choose 2) by positivity)).mpr
    have h := (mul_le_mul_of_nonneg_right hp (show 0 ≤ (n:ℝ)^k by positivity)).trans hprod
    linarith
  calc
    _ ≤ 2 * ((2:ℝ)^(k.choose 2))⁻¹ * ((n:ℝ)^k) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = 2*((n:ℝ)^k/(2:ℝ)^(k.choose 2)) := by rw [div_eq_mul_inv]; ring
    _ ≤ 1/2 := by linarith

private theorem deviation_weight_bound {n : ℕ} (hn : 4 ≤ n) :
    2 * exp (-2*(n:ℝ)) * (2:ℝ)^n ≤ 1/8 := by
  have ht : (2:ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1:ℝ)]
  have ht' : (2:ℝ)^n ≤ exp (n:ℝ) := by
    rw [show (n:ℝ) = (n:ℝ)*1 by ring, exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) ht _
  have hp : (16:ℝ) ≤ exp (n:ℝ) := by
    have hn' := (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn).trans ht'
    norm_num at hn'
    exact hn'
  calc
    _ ≤ 2*exp (-2*(n:ℝ))*exp (n:ℝ) := mul_le_mul_of_nonneg_left ht' (by positivity)
    _ = 2*exp (-(n:ℝ)) := by rw [mul_assoc, ← exp_add]; congr 2; ring
    _ ≤ 1/8 := by
      rw [exp_neg]
      have h := inv_anti₀ (by norm_num : (0:ℝ) < 16) hp
      linarith

private theorem positive_weight {ι : Type*} (S : Finset ι) (f : ι → Bool) (c : Bool)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1/2) :
    0 < weight S (biased t c) f := by
  apply prod_pos
  intro i hi
  unfold biased
  split_ifs <;> linarith

private theorem score_for_large_deviation {n : ℕ} (hn : 4 ≤ n) (f : Labels n)
    (S : Finset (Fin n)) (c : Bool)
    (hd : 4*(n:ℝ)*√(n:ℝ) ≤ (2:ℝ)*(((pairs S).filter (fun e => f e=c)).card:ℝ) -
      ((pairs S).card:ℝ)) :
    1 ≤ exp (-2*(n:ℝ)) * weight (pairs S) (biased (√(n:ℝ))⁻¹ c) f := by
  have hn' : (4:ℝ) ≤ n := by exact_mod_cast hn
  have hnr : (0:ℝ) < n := by positivity
  have hs : 0 < √(n:ℝ) := sqrt_pos.mpr hnr
  have hs' : (2:ℝ) ≤ √(n:ℝ) := (le_sqrt (by norm_num) hnr.le).mpr (by exact_mod_cast hn)
  let t := (√(n:ℝ))⁻¹
  have ht0 : 0 < t := inv_pos.mpr hs
  have ht : t ≤ 1/2 := by rw [one_div]; exact inv_anti₀ (by norm_num) hs'
  have hcard : ((pairs S).card:ℝ) ≤ (n:ℝ)^2 := by
    rw [pairs_card]
    have hc : S.card ≤ n := by simpa using (card_le_univ S)
    exact_mod_cast (Nat.choose_le_pow S.card 2).trans (Nat.pow_le_pow_left hc _)
  have hpen : t^2*((pairs S).card:ℝ) ≤ (n:ℝ) := by
    have hn2 : t^2*(n:ℝ) = 1 := by
      dsimp [t]
      rw [inv_pow, sq_sqrt hnr.le, inv_mul_cancel₀ hnr.ne']
    calc
      _ ≤ t^2*(n:ℝ)^2 := mul_le_mul_of_nonneg_left hcard (sq_nonneg _)
      _ = (t^2*(n:ℝ))*(n:ℝ) := by ring
      _ = _ := by rw [hn2, one_mul]
  have hgood : (2:ℝ)*n ≤ log (weight (pairs S) (biased t c) f) := by
    have hg := mul_le_mul_of_nonneg_left hd ht0.le
    have hh : t*(4*(n:ℝ)*√(n:ℝ)) = 4*(n:ℝ) := by
      dsimp [t]
      field_simp
    rw [hh] at hg
    have := weight_log_bound (pairs S) f c ht0.le ht
    linarith
  have hw := (log_le_log_iff (exp_pos _) (positive_weight (pairs S) f c ht0.le ht)).mp
    (show log (exp (2*(n:ℝ))) ≤ _ by rw [log_exp]; exact hgood)
  have hh := mul_le_mul_of_nonneg_left hw (exp_pos (-2*(n:ℝ))).le
  rw [← exp_add, show -2*(n:ℝ)+2*(n:ℝ)=0 by ring, exp_zero] at hh
  exact hh

private theorem term_le_penalty {ι β : Type*} {T : Finset β} {v : β}
    (hv : v ∈ T) (S : β → Finset ι) (p : Bool → Bool → ℝ)
    (hp : ∀ c b, 0 ≤ p c b) (w : ℝ) (hw : 0 ≤ w) (f : ι → Bool) (c : Bool) :
    w*weight (S v) (p c) f ≤ ∑ a ∈ T, ∑ b : Bool, w*weight (S a) (p b) f := by
  have hn (a : β) (b : Bool) : 0 ≤ w * weight (S a) (p b) f :=
    mul_nonneg hw (prod_nonneg (fun i hi => hp b (f i)))
  exact (single_le_sum (fun b hb => hn v b) (mem_univ c)).trans
    (single_le_sum (fun a ha => sum_nonneg (fun b hb => hn a b)) hv)

private theorem exists_labels {n k : ℕ} (hn : 4 ≤ n) (hk : 8*log (n:ℝ)+1 ≤ (k:ℝ)) :
    ∃ f : Labels n,
      (∀ S : Finset (Fin n),
        |(2:ℝ)*(edgeCount f S:ℝ)-((pairs S).card:ℝ)| < 4*(n:ℝ)*√(n:ℝ)) ∧
      (∀ (S : Finset (Fin n)), S.card = k → ∀ c : Bool, ¬ ∀ e ∈ pairs S, f e = c) := by
  classical
  let t := (√(n:ℝ))⁻¹
  let X : Finset (Finset (Fin n)) := univ.powerset
  let Y : Finset (Finset (Fin n)) := univ.powersetCard k
  let w := exp (-2*(n:ℝ))
  let u := ((2:ℝ)^(k.choose 2))⁻¹
  let dev (f : Labels n) := ∑ S ∈ X, ∑ c : Bool, w*weight (pairs S) (biased t c) f
  let hom (f : Labels n) := ∑ S ∈ Y, ∑ c : Bool, u*weight (pairs S) (homogeneous c) f
  have ht0 : 0 ≤ t := by unfold t; positivity
  have hn' : (4:ℝ) ≤ n := by exact_mod_cast hn
  have hs : (2:ℝ) ≤ √(n:ℝ) := (le_sqrt (by norm_num) (by positivity)).mpr (by exact_mod_cast hn)
  have ht : t ≤ 1/2 := by rw [one_div]; exact inv_anti₀ (by norm_num) hs
  have hp (c b : Bool) : 0 ≤ biased t c b := by unfold biased; split_ifs <;> linarith
  have hq (c b : Bool) : 0 ≤ homogeneous c b := by cases c <;> cases b <;> norm_num [homogeneous]
  have hw : 0 ≤ w := (exp_pos _).le
  have hu : 0 ≤ u := by unfold u; positivity
  have hd0 (f : Labels n) : 0 ≤ dev f := sum_nonneg (fun S hS =>
    sum_nonneg (fun c hc => mul_nonneg hw (prod_nonneg (fun i hi => hp c (f i)))))
  have hh0 (f : Labels n) : 0 ≤ hom f := sum_nonneg (fun S hS =>
    sum_nonneg (fun c hc => mul_nonneg hu (prod_nonneg (fun i hi => hq c (f i)))))
  have hp' (c : Bool) : biased t c false + biased t c true = 2 := by
    cases c <;> simp [biased] <;> ring
  have hq' (c : Bool) : homogeneous c false + homogeneous c true = 2 := by
    cases c <;> norm_num [homogeneous]
  have hsum :
      (∑ f : Labels n, (dev f + hom f)) =
        (2:ℝ)^(Fintype.card (Sym2 (Fin n))) * (2*w*(2:ℝ)^n + 2*u*(n.choose k:ℝ)) := by
    rw [sum_add_distrib]
    unfold dev hom
    rw [total_weight X pairs _ hp', total_weight Y pairs _ hq']
    simp [X, Y, card_powersetCard, Nat.cast_pow]
    ring
  have hwlt : 2*w*(2:ℝ)^n + 2*u*(n.choose k:ℝ) < 1 := by
    have ha : 2*w*(2:ℝ)^n ≤ 1/8 := deviation_weight_bound hn
    have hb : 2*u*(n.choose k:ℝ) ≤ 1/2 := homogeneous_weight_bound hn hk
    linarith
  have hsmall : ∃ f : Labels n, dev f + hom f < 1 := by
    by_contra! h
    have hsum' := sum_le_sum (s := (univ : Finset (Labels n))) (fun f _ => h f)
    rw [hsum] at hsum'
    have he : (∑ _ : Labels n, (1:ℝ)) = (2:ℝ)^(Fintype.card (Sym2 (Fin n))) := by
      simp [Fintype.card_bool, Nat.cast_pow]
    rw [he] at hsum'
    have hlt := mul_lt_mul_of_pos_left hwlt (show 0 < (2:ℝ)^(Fintype.card (Sym2 (Fin n))) by positivity)
    rw [mul_one] at hlt
    exact hlt.not_ge hsum'
  obtain ⟨f, hf⟩ := hsmall
  refine ⟨f, ?_, ?_⟩
  · intro S
    have hS : S ∈ X := mem_powerset.mpr (subset_univ _)
    have hall (c : Bool) : (2:ℝ)*(((pairs S).filter (fun e => f e=c)).card:ℝ) -
        ((pairs S).card:ℝ) < 4*(n:ℝ)*√(n:ℝ) := by
      by_contra! hbad
      have hge : 1 ≤ w*weight (pairs S) (biased t c) f := score_for_large_deviation hn f S c hbad
      have hdom := term_le_penalty hS pairs (biased t) hp w hw f c
      change w*weight (pairs S) (biased t c) f ≤ dev f at hdom
      linarith [hh0 f]
    have hop : (((pairs S).filter (fun e => f e=false)).card:ℝ) + (edgeCount f S:ℝ) =
        ((pairs S).card:ℝ) := by
      have he : ∀ e, (¬ f e = false) ↔ f e = true := by intro e; cases f e <;> simp
      exact_mod_cast (by simpa [he, edgeCount] using
        card_filter_add_card_filter_not (s := pairs S) (fun e => f e = false))
    exact abs_lt.mpr ⟨by linarith [hall false], hall true⟩
  · intro S hS c hconst
    have hS' : S ∈ Y := mem_powersetCard.mpr ⟨subset_univ _, hS⟩
    have hcarrier : weight (pairs S) (homogeneous c) f = (2:ℝ)^(k.choose 2) := by
      unfold weight
      calc
        _ = ∏ _e ∈ pairs S, (2:ℝ) := prod_congr rfl (fun e he => by simp [homogeneous,hconst e he])
        _ = _ := by simp [pairs_card, hS]
    have hle := term_le_penalty hS' pairs homogeneous hq u hu f c
    change u*weight (pairs S) (homogeneous c) f ≤ hom f at hle
    rw [hcarrier, inv_mul_cancel₀ (by positivity : (2:ℝ)^(k.choose 2) ≠ 0)] at hle
    linarith [hd0 f]

private theorem clique_indep_bound {n k : ℕ} {f : Labels n}
    (h : ∀ (S : Finset (Fin n)), S.card = k → ∀ c : Bool, ¬ ∀ e ∈ pairs S, f e = c) :
    (graph f).cliqueNum < k ∧ (graph f).indepNum < k := by
  classical
  constructor
  · by_contra! hbad
    obtain ⟨U, hU⟩ := (graph f).exists_isNClique_cliqueNum
    obtain ⟨S,hSU,hS⟩ := exists_subset_card_eq (hU.card_eq ▸ hbad)
    apply h S hS true
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      obtain ⟨hab, hne⟩ := mem_filter.mp he
      obtain ⟨ha,hb⟩ := mk_mem_sym2_iff.mp hab
      have hne' : a ≠ b := fun h => hne (Sym2.mk_isDiag_iff.mpr h)
      have hh := hU.isClique (mem_coe.mpr (hSU ha)) (mem_coe.mpr (hSU hb)) hne'
      exact hh.1
  · by_contra! hbad
    obtain ⟨U, hU⟩ := (graph f).exists_isNIndepSet_indepNum
    obtain ⟨S,hSU,hS⟩ := exists_subset_card_eq (hU.card_eq ▸ hbad)
    apply h S hS false
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      obtain ⟨hab, hne⟩ := mem_filter.mp he
      obtain ⟨ha,hb⟩ := mk_mem_sym2_iff.mp hab
      have hne' : a ≠ b := fun h => hne (Sym2.mk_isDiag_iff.mpr h)
      have hh := hU.isIndepSet (mem_coe.mpr (hSU ha)) (mem_coe.mpr (hSU hb)) hne'
      cases hh' : f s(a,b)
      · rfl
      · exact False.elim (hh ⟨hh', hne'⟩)

private theorem subgraphs_upper {n : ℕ} (hn : 4 ≤ n) {f : Labels n}
    (hf : ∀ S : Finset (Fin n),
      |(2:ℝ)*(edgeCount f S:ℝ)-((pairs S).card:ℝ)| < 4*(n:ℝ)*√(n:ℝ)) :
    ¬ Erdos636.HasManyDistinctInducedSubgraphs (graph f) (20*(n:ℝ)^(5/2:ℝ)) := by
  classical
  let M := ⌈4*(n:ℝ)*√(n:ℝ)⌉₊
  let D := (Finset.range (n+1)) ×ˢ Icc (-(M:ℤ)) (M:ℤ)
  let tag (s : Set (Fin n)) : ℕ × ℤ :=
    (s.ncard, (2:ℤ)*(((graph f).induce s).edgeSet.ncard:ℤ) - (s.ncard.choose 2:ℤ))
  rintro ⟨𝒮,hpair,hsize⟩
  have hInto s (hs : s ∈ 𝒮) : tag s ∈ (D : Set (ℕ × ℤ)) := by
    let S := s.toFinset
    have he : (S : Set (Fin n)) = s := by ext i; simp [S]
    have hc : S.card = s.ncard := by rw [← he, Set.ncard_coe_finset]
    have hE : ((graph f).induce s).edgeSet.ncard = edgeCount f S := he ▸ edgeCount_eq f S
    have hd : |(((tag s).2 : ℤ):ℝ)| ≤ (M:ℝ) := by
      have hdev := hf S
      rw [pairs_card, hc, ← hE] at hdev
      have hm : 4*(n:ℝ)*√(n:ℝ) ≤ (M:ℝ) := Nat.le_ceil _
      apply le_trans _ hm
      simpa [tag] using hdev.le
    have habs : |(tag s).2| ≤ (M:ℤ) := by exact_mod_cast hd
    have hle : s.ncard ≤ n := by
      rw [← hc]
      simpa using card_le_univ S
    exact mem_coe.mpr (mem_product.mpr ⟨mem_range.mpr (by show s.ncard < n+1; omega),
      mem_Icc.mpr (abs_le.mp habs)⟩)
  have hInj : 𝒮.InjOn tag := by
    intro s hs t ht he
    by_contra hne
    have hc : s.ncard = t.ncard := congrArg Prod.fst he
    have he' := congrArg Prod.snd he
    dsimp [tag] at he'
    rw [hc] at he'
    have hE : ((graph f).induce s).edgeSet.ncard = ((graph f).induce t).edgeSet.ncard := by omega
    exact (hpair hs ht hne).elim (fun h => h hc) (fun h => h hE)
  have hbound : 𝒮.ncard ≤ D.card := by
    simpa using Set.ncard_le_ncard_of_injOn tag hInto hInj D.finite_toSet
  have hD : D.card = (n+1)*(2*M+1) := by
    dsimp [D]
    rw [card_product, card_range, Int.card_Icc]
    congr 1
    omega
  have hnr : (4:ℝ) ≤ n := by exact_mod_cast hn
  have hroot : (2:ℝ) ≤ √(n:ℝ) := (le_sqrt (by norm_num) (by positivity)).mpr (by exact_mod_cast hn)
  have hM : (M:ℝ) ≤ 4*(n:ℝ)*√(n:ℝ)+1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hMs : 2*(M:ℝ)+1 ≤ 9*(n:ℝ)*√(n:ℝ) := by
    have h := mul_le_mul hnr hroot (by norm_num : (0:ℝ) ≤ 2) (by positivity : (0:ℝ) ≤ n)
    nlinarith
  have hfinal : (𝒮.ncard:ℝ) < 20*((n:ℝ)^2*√(n:ℝ)) := by
    calc
      _ ≤ (D.card:ℝ) := by exact_mod_cast hbound
      _ = ((n:ℝ)+1)*(2*(M:ℝ)+1) := by simp [hD]
      _ ≤ (2*(n:ℝ))*(9*(n:ℝ)*√(n:ℝ)) :=
        mul_le_mul (by linarith) hMs (by positivity) (by positivity)
      _ < _ := by
        have hpos : 0 < (n:ℝ)^2*√(n:ℝ) := by positivity
        nlinarith
  have hrpow : (n:ℝ)^(5/2:ℝ) = (n:ℝ)^2*√(n:ℝ) := by
    rw [show (5/2:ℝ) = (↑(2:ℕ):ℝ)+1/2 by norm_num,
      rpow_add (by positivity), rpow_natCast, ← sqrt_eq_rpow]
  exact hfinal.not_ge (hrpow ▸ hsize)

private theorem best_possible :
    ∃ C > (0 : ℝ), ∃ K : ℝ, ∀ᶠ n : ℕ in atTop, ∃ G : SimpleGraph (Fin n),
      (G.cliqueNum : ℝ) < C * Real.log n ∧ (G.indepNum : ℝ) < C * Real.log n ∧
        ¬ Erdos636.HasManyDistinctInducedSubgraphs G (K * (n : ℝ) ^ (5 / 2 : ℝ)) := by
  refine ⟨10, by norm_num, 20, ?_⟩
  filter_upwards [eventually_ge_atTop (4:ℕ)] with n hn
  let k := ⌈8*log (n:ℝ)⌉₊+1
  have hl : 1 ≤ log (n:ℝ) := by
    have hn' : (4:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have h := log_le_log (by norm_num : 0 < (4:ℝ)) hn'
    have he : log (4:ℝ) = 2*log 2 := by rw [show (4:ℝ) = 2^2 by norm_num, log_pow]; norm_num
    linarith [log_two_bounds.1]
  have hk : 8*log (n:ℝ)+1 ≤ (k:ℝ) := by
    dsimp [k]
    rw [Nat.cast_add, Nat.cast_one]
    linarith [Nat.le_ceil (8*log (n:ℝ))]
  have hku : (k:ℝ) ≤ 10*log (n:ℝ) := by
    dsimp [k]
    rw [Nat.cast_add, Nat.cast_one]
    have h := Nat.ceil_lt_add_one (show 0 ≤ 8*log (n:ℝ) by linarith)
    linarith
  obtain ⟨f, hdev, hhom⟩ := exists_labels hn hk
  obtain ⟨hc,hi⟩ := clique_indep_bound hhom
  exact ⟨graph f, (by exact_mod_cast hc : ((graph f).cliqueNum:ℝ) < k).trans_le hku,
    (by exact_mod_cast hi : ((graph f).indepNum:ℝ) < k).trans_le hku, subgraphs_upper hn hdev⟩

end OMA

theorem OMA.solution : type_of% @Erdos636.erdos_636.variants.best_possible :=
  OMA.best_possible