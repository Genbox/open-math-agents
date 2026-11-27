import FormalConjectures.ErdosProblems.«1042»
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fin.Rev
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Analysis.Complex.OpenMapping

/-! Finite truncated-distance estimates for the number of lemniscate components. -/

open scoped BigOperators ENNReal
open Finset

namespace LemniscateSampling

/-- Uniformly truncate all factors away from zero while preserving a product bound.
If truncation changes a factor, that factor is small enough to bound the whole product. -/
private theorem truncated_prod_bound {ι : Type*} (J : Finset ι)
    {B Q : ℝ} (hB : 1 ≤ B) (hQ : 0 < Q) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ (a : ι → ℝ), (∀ i ∈ J, 0 ≤ a i) → (∀ i ∈ J, a i ≤ B) →
      (∏ i ∈ J, a i) ≤ Q → (∏ i ∈ J, max δ (a i)) ≤ Q := by
  classical
  have hBp : 0 < B := zero_lt_one.trans_le hB
  let δ := min 1 (Q / B ^ J.card)
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos hQ (pow_pos hBp _))
  refine ⟨δ, hδ, min_le_left _ _, ?_⟩
  intro a _ ha hprod
  by_cases hall : ∀ i ∈ J, δ ≤ a i
  · exact (prod_congr rfl (fun i hi => max_eq_right (hall i hi))).le.trans hprod
  · push Not at hall
    obtain ⟨i, hi, hai⟩ := hall
    have hfactor : ∀ j ∈ J.erase i, max δ (a j) ≤ B := by
      intro j hj
      exact max_le ((min_le_left _ _).trans hB) (ha j (mem_of_mem_erase hj))
    have hremain : (∏ j ∈ J.erase i, max δ (a j)) ≤ B ^ J.card := by
      calc
        _ ≤ ∏ _ ∈ J.erase i, B :=
          prod_le_prod (fun _ _ => hδ.le.trans (le_max_left _ _)) hfactor
        _ = B ^ (J.erase i).card := prod_const B
        _ ≤ B ^ J.card := pow_le_pow_right₀ hB (card_le_card (erase_subset _ _))
    rw [← mul_prod_erase J (fun j => max δ (a j)) hi, max_eq_left hai.le]
    calc
      _ ≤ δ * B ^ J.card := mul_le_mul_of_nonneg_left hremain hδ.le
      _ ≤ Q := (le_div_iff₀ (pow_pos hBp _)).1 (min_le_right _ _)

end LemniscateSampling

namespace LemniscateSampling

private def indexPairs (N : ℕ) : Finset (Σ _ : Fin N, Fin N) :=
  Finset.univ.sigma fun i => Finset.Ioi i

private theorem mem_indexPairs {N : ℕ} (p : Σ _ : Fin N, Fin N) :
    p ∈ indexPairs N ↔ p.1 < p.2 := by
  simp [indexPairs]

private theorem capacity_gives_product_bound (F : Set ℂ)
    (hpos : 0 < Erdos1042.transfiniteDiameter F)
    (hcap : Erdos1042.transfiniteDiameter F < 1) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∃ N : ℕ, 2 ≤ N ∧
      ∀ x : Fin N → ℂ, (∀ i, x i ∈ F) →
        (∏ p ∈ indexPairs N, dist (x p.1) (x p.2)) ≤ q ^ (N.choose 2) := by
  obtain ⟨b, hb, hb1⟩ := exists_between hcap
  have hbtop : b ≠ ⊤ := (hb1.trans_le le_top).ne
  let q := b.toReal
  have hqpos : 0 < q := ENNReal.toReal_pos (hpos.trans hb).ne' hbtop
  have hq1 : q < 1 := by
    simpa [q] using (ENNReal.toReal_lt_toReal hbtop ENNReal.one_ne_top).2 hb1
  have he : ∀ᶠ N : ℕ in Filter.atTop, Erdos1042.nthDiameter F N < b :=
    Filter.eventually_lt_of_limsup_lt hb
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (he.and (Filter.eventually_ge_atTop (2 : ℕ)))
  refine ⟨q, hqpos, hq1, N, (hN N le_rfl).2, ?_⟩
  intro x hx
  have hm : 0 < N.choose 2 := Nat.choose_pos (hN N le_rfl).2
  have hmR : (N.choose 2 : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  let P := ∏ p ∈ indexPairs N, dist (x p.1) (x p.2)
  have hP : ENNReal.ofReal P =
      ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, edist (x i) (x j) := by
    dsimp only [P, indexPairs]
    rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => dist_nonneg), Finset.prod_sigma]
    simp only [edist_dist]
  have hle : ENNReal.ofReal P ^ (1 / (N.choose 2 : ℝ)) ≤ b := by
    rw [hP]
    refine le_trans ?_ (hN N le_rfl).1.le
    exact le_iSup_of_le x (le_iSup_of_le hx le_rfl)
  have hpow := pow_le_pow_left' hle (N.choose 2)
  rw [← ENNReal.rpow_mul_natCast, div_mul_cancel₀ _ hmR, ENNReal.rpow_one] at hpow
  rw [show b = ENNReal.ofReal q from (ENNReal.ofReal_toReal hbtop).symm,
    ← ENNReal.ofReal_pow hqpos.le] at hpow
  exact (ENNReal.ofReal_le_ofReal_iff (pow_nonneg hqpos.le _)).1 hpow

end LemniscateSampling

namespace LemniscateSampling

private theorem bounded_of_product_bound {F : Set ℂ} {N : ℕ} (hN : 2 ≤ N)
    {Q : ℝ} (hQ : 0 < Q)
    (hprod : ∀ x : Fin N → ℂ, (∀ i, x i ∈ F) →
      (∏ p ∈ indexPairs N, dist (x p.1) (x p.2)) ≤ Q) :
    Bornology.IsBounded F := by
  classical
  by_contra hbounded
  have hinfinite : F.Infinite := fun h => hbounded h.isCompact.isBounded
  let e := Set.Infinite.natEmbedding F hinfinite
  let a (i : Fin N) : ℂ := (e i : F)
  have ha : Function.Injective a := fun i j hij =>
    Fin.ext (e.injective (Subtype.ext hij))
  let u : Fin N := ⟨0, by omega⟩
  let v : Fin N := ⟨1, by omega⟩
  let p : Σ _ : Fin N, Fin N := ⟨u, v⟩
  have hu : u ≠ v := by simp [u, v, Fin.ext_iff]
  have hp : p ∈ indexPairs N := (mem_indexPairs p).2 (by norm_num [p, u, v, Fin.lt_def])
  let P := ∏ j ∈ (indexPairs N).erase p, dist (a j.1) (a j.2)
  have hP : 0 < P := by
    apply Finset.prod_pos
    intro j hj
    exact dist_pos.mpr (ha.ne ((mem_indexPairs j).1 (Finset.mem_of_mem_erase hj)).ne)
  let D := ∑ i : Fin N, ‖a i‖
  have hD (i : Fin N) : ‖a i‖ ≤ D :=
    Finset.single_le_sum (fun j _ => norm_nonneg (a j)) (Finset.mem_univ i)
  have hDpos : 0 ≤ D := (norm_nonneg (a u)).trans (hD u)
  have hQp : 0 < Q / P := div_pos hQ hP
  apply hbounded
  refine (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).2 ⟨Q/P + 3*D, ?_⟩
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! hzlarge
  let x (i : Fin N) : ℂ := if i = u then z else a i
  have hx (i : Fin N) : x i ∈ F := by
    by_cases hi : i = u
    · simpa only [x, if_pos hi] using hz
    · simpa only [x, if_neg hi] using (e i).property
  have hlong (i : Fin N) : Q/P + 2*D < dist z (a i) := by
    have ht : ‖z‖ ≤ dist z (a i) + ‖a i‖ := by
      rw [dist_eq_norm]
      simpa only [sub_add_cancel] using norm_add_le (z-a i) (a i)
    linarith only [hzlarge, ht, hD i]
  have hshort (i j : Fin N) : dist (a i) (a j) ≤ 2*D := by
    have ht := dist_triangle (a i) 0 (a j)
    rw [dist_zero_right, dist_zero_left] at ht
    linarith only [ht, hD i, hD j]
  have hremain : P ≤ ∏ j ∈ (indexPairs N).erase p, dist (x j.1) (x j.2) := by
    refine Finset.prod_le_prod (fun _ _ => dist_nonneg) ?_
    intro j hj
    have hne := ((mem_indexPairs j).1 (mem_of_mem_erase hj)).ne
    by_cases hi : j.1 = u
    · have hj' : j.2 ≠ u := fun h => hne (hi.trans h.symm)
      simp only [x, if_pos hi, if_neg hj']
      linarith only [hshort j.1 j.2, hlong j.2, hQp]
    · by_cases hj' : j.2 = u
      · simp only [x, if_neg hi, if_pos hj']
        rw [dist_comm (a j.1) z]
        linarith only [hshort j.1 j.2, hlong j.1, hQp]
      · simp only [x, if_neg hi, if_neg hj', le_refl]
  have hpdist : dist (x p.1) (x p.2) = dist z (a v) := by
    simp only [p, x, if_pos rfl, if_neg hu.symm]
  have hprod' := hprod x hx
  rw [← Finset.mul_prod_erase (indexPairs N) (fun j => dist (x j.1) (x j.2)) hp,
    hpdist] at hprod'
  have hqp : Q < dist z (a v) * P :=
    (div_lt_iff₀ hP).1 (by linarith only [hlong v, hDpos])
  exact (not_lt_of_ge hprod') (hqp.trans_le (mul_le_mul_of_nonneg_left hremain dist_nonneg))

end LemniscateSampling

namespace LemniscateSampling

private theorem ball_of_negative_row {n : ℕ} (hn : 0 < n) (a : Fin n → ℂ)
    {δ ε t : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hsmall : Real.log (1 + ε/δ) + t < 0)
    {i : Fin n} (hrow : (∑ j, Real.log (max δ (dist (a i) (a j)))) ≤ (n : ℝ) * t) :
    Metric.ball (a i) ε ⊆ {z | ‖∏ j, (z - a j)‖ < 1} := by
  let m (j : Fin n) := max δ (dist (a i) (a j))
  let B := 1 + ε/δ
  have hB : 0 < B := by dsimp [B]; positivity
  have hm (j : Fin n) : 0 < m j := hδ.trans_le (le_max_left _ _)
  have hprodPos : 0 < ∏ j, B * m j :=
    Finset.prod_pos fun j _ => mul_pos hB (hm j)
  have hprodSmall : (∏ j, B * m j) < 1 := by
    apply (Real.log_lt_log_iff hprodPos zero_lt_one).1
    rw [Real.log_prod (fun j _ => (mul_pos hB (hm j)).ne'), Real.log_one]
    simp_rw [Real.log_mul hB.ne' (hm _).ne', Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have h := mul_neg_of_pos_of_neg hnR hsmall
    change (n : ℝ) * Real.log B + (∑ j, Real.log (m j)) < 0
    change (n : ℝ) * (Real.log B + t) < 0 at h
    linarith only [h, hrow]
  intro z hz
  change ‖∏ j, (z - a j)‖ < 1
  rw [norm_prod]
  apply lt_of_le_of_lt _ hprodSmall
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) ?_
  intro j _
  have hd : dist z (a i) < ε := Metric.mem_ball.mp hz
  have hmδ : δ ≤ m j := le_max_left _ _
  have hdist : dist (a i) (a j) ≤ m j := le_max_right _ _
  have hdiv : ε ≤ (ε/δ) * m j := by
    calc
      ε = (ε/δ) * δ := (div_mul_cancel₀ ε hδ.ne').symm
      _ ≤ (ε/δ) * m j := mul_le_mul_of_nonneg_left hmδ (div_nonneg hε.le hδ.le)
  rw [← dist_eq_norm]
  calc
    dist z (a j) ≤ dist z (a i) + dist (a i) (a j) := dist_triangle _ _ _
    _ ≤ ε + m j := add_le_add hd.le hdist
    _ ≤ B * m j := by dsimp [B]; linarith only [hdiv]

end LemniscateSampling

open Set Polynomial

namespace LemniscateSampling

-- Fixing the image at two distinct coordinates leaves the other coordinates free.
private def splitPair {T A : Type*} [DecidableEq T] {i j : T} (hij : i ≠ j) :
    (T → A) ≃ (A × A) × ({k : T // k ≠ i ∧ k ≠ j} → A) where
  toFun f := ((f i, f j), fun k => f k)
  invFun p k := if hi : k = i then p.1.1 else if hj : k = j then p.1.2 else p.2 ⟨k,hi,hj⟩
  left_inv f := by
    funext k
    by_cases hi : k = i
    · subst k
      simp
    by_cases hj : k = j
    · subst k
      simp [hij.symm]
    · simp [hi,hj]
  right_inv := by
    rintro ⟨⟨a,b⟩, f⟩
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · simp
    · simp [hij.symm]
    · funext k
      simp [k.property.1,k.property.2]

private lemma pair_marginal {T A : Type*} [Fintype T] [DecidableEq T] [Fintype A] (b : A → A → ℝ)
    {i j : T} (hij : i ≠ j) :
    (Fintype.card A : ℝ)^2 * (∑ s : T → A, b (s i) (s j)) =
      (Fintype.card (T → A) : ℝ) * ∑ a : A, ∑ a' : A, b a a' := by
  classical
  let W := {k : T // k ≠ i ∧ k ≠ j} → A
  let e : (T → A) ≃ (A × A) × W := splitPair hij
  have hc := Fintype.card_congr e
  rw [Fintype.card_prod, Fintype.card_prod, ← pow_two] at hc
  have hcR : (Fintype.card (T → A) : ℝ) = (Fintype.card A : ℝ)^2 * Fintype.card W := by
    exact_mod_cast hc
  have hs : (∑ s : T → A, b (s i) (s j)) =
      (Fintype.card W : ℝ) * ∑ a : A, ∑ a' : A, b a a' := by
    calc
      _ = ∑ p : (A × A) × W, b p.1.1 p.1.2 :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = _ := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
        rw [Fintype.sum_prod_type]
  rw [hs,hcR]
  ring

private lemma count_increasing_pairs (N : ℕ) :
    (∑ i : Fin N, (Finset.Ioi i).card) = N.choose 2 := by
  have h (i : Fin N) : (Finset.Ioi i).card = (Fin.revPerm i).val := by
    rw [Fin.card_Ioi, Fin.revPerm_apply, Fin.val_rev]
    omega
  simp_rw [h]
  rw [Equiv.sum_comp Fin.revPerm (fun i : Fin N => i.val)]
  change (∑ i : Fin N, id i.val) = _
  rw [Fin.sum_univ_eq_sum_range]
  simp only [id_eq]
  rw [Finset.sum_range_id, Nat.choose_two_right]

-- The hypothesis bounds each tuple by the same constant times its number of pairs.
private theorem pair_mean_le {N n : ℕ} (hN : 2 ≤ N) (b : Fin n → Fin n → ℝ) (L : ℝ)
    (h : ∀ s : Fin N → Fin n,
      (∑ i : Fin N, ∑ j ∈ Finset.Ioi i, b (s i) (s j)) ≤ (N.choose 2 : ℝ) * L) :
    (∑ i : Fin n, ∑ j : Fin n, b i j) ≤ (n : ℝ)^2 * L := by
  classical
  by_cases hn : n = 0
  · subst n
    simp
  let K : ℝ := Fintype.card (Fin N → Fin n)
  have hK : 0 < K := by
    have hne : Nonempty (Fin N → Fin n) := ⟨fun _ => ⟨0, Nat.pos_of_ne_zero hn⟩⟩
    dsimp [K]
    exact_mod_cast Fintype.card_pos_iff.mpr hne
  have hC : (0 : ℝ) < N.choose 2 := by exact_mod_cast Nat.choose_pos hN
  have hsum :
      (∑ s : Fin N → Fin n, ∑ i : Fin N, ∑ j ∈ Finset.Ioi i, b (s i) (s j)) ≤
        K * ((N.choose 2 : ℝ) * L) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, K] using
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N → Fin n))) (fun s _ => h s)
  have hswap :
      (∑ s : Fin N → Fin n, ∑ i : Fin N, ∑ j ∈ Finset.Ioi i, b (s i) (s j)) =
        ∑ i : Fin N, ∑ j ∈ Finset.Ioi i, ∑ s : Fin N → Fin n, b (s i) (s j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
  have hcount :
      (n : ℝ)^2 * (∑ s : Fin N → Fin n, ∑ i : Fin N, ∑ j ∈ Finset.Ioi i, b (s i) (s j)) =
        (K * (N.choose 2 : ℝ)) * (∑ a : Fin n, ∑ a' : Fin n, b a a') := by
    conv_lhs =>
      rw [hswap]
      simp only [Finset.mul_sum]
    calc
      _ = ∑ i : Fin N, ∑ j ∈ Finset.Ioi i, K * ∑ a : Fin n, ∑ a' : Fin n, b a a' := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
        rw [← Finset.mul_sum]
        simpa only [Fintype.card_fin, K] using pair_marginal b (Finset.mem_Ioi.mp hj).ne
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul, ← Nat.cast_sum,
          count_increasing_pairs]
        ring
  apply le_of_mul_le_mul_left _ (mul_pos hK hC)
  calc
    _ = (n : ℝ)^2 * (∑ s : Fin N → Fin n, ∑ i : Fin N, ∑ j ∈ Finset.Ioi i, b (s i) (s j)) :=
      hcount.symm
    _ ≤ (n : ℝ)^2 * (K * ((N.choose 2 : ℝ) * L)) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end LemniscateSampling

private theorem OMA.counting_prod_index {R M : Type*} [CommMonoid M] (s : Multiset R)
    (g : R → M) : (s.map g).prod = ∏ i : Fin s.toList.length, g (s.toList.get i) := by
  rw [← List.prod_ofFn]
  change _ = (List.ofFn (g ∘ s.toList.get)).prod
  rw [← List.map_ofFn, List.ofFn_get]
  simp

private theorem OMA.counting_sublevel_compact (p : ℂ[X]) (hp : p.Monic)
    (hdeg : 0 < p.natDegree) (c : ℝ) (hc : 0 ≤ c) :
    IsCompact {z : ℂ | ‖p.eval z‖ ≤ c} := by
  classical
  have hclosed : IsClosed {z : ℂ | ‖p.eval z‖ ≤ c} := isClosed_le p.continuous.norm continuous_const
  have hfin : (p.rootSet ℂ).Finite := p.rootSet_finite _
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (0 : ℂ)).mp hfin.isBounded
  have hroot (r : ℂ) (hr : r ∈ p.roots) : ‖r‖ < R := by
    have he : p.eval r = 0 := (mem_roots hp.ne_zero).1 hr
    have hrC : r ∈ p.rootSet ℂ := hp.mem_rootSet.mpr (by simpa using he)
    simpa [Metric.mem_ball, dist_zero_right] using hR hrC
  refine Metric.isCompact_of_isClosed_isBounded hclosed
    (Metric.isBounded_ball.subset (t := Metric.ball (0 : ℂ) (R + c + 1)) ?_)
  intro z hz
  rw [Metric.mem_ball, dist_zero_right]
  by_contra! h
  have hbound (i : Fin p.roots.toList.length) : c + 1 ≤ ‖z - p.roots.toList.get i‖ := by
    have hr := hroot (p.roots.toList.get i) (Multiset.mem_toList.mp (List.get_mem _ i))
    have ht := norm_add_le (z - p.roots.toList.get i) (p.roots.toList.get i)
    rw [sub_add_cancel] at ht
    linarith
  have hL : p.roots.toList.length = p.natDegree := by
    simpa using (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
  have hprod : (c + 1) ^ p.natDegree ≤ ‖p.eval z‖ := by
    rw [(IsAlgClosed.splits p).eval_eq_prod_roots_of_monic hp, counting_prod_index, norm_prod]
    have hprod : (∏ _ : Fin p.roots.toList.length, (c + 1)) ≤
        ∏ i, ‖z - p.roots.toList.get i‖ :=
      Finset.prod_le_prod (s := Finset.univ) (fun _ _ => by positivity) (fun i _ => hbound i)
    simpa [hL] using hprod
  have hpow : c + 1 ≤ (c + 1) ^ p.natDegree := by
    simpa only [pow_one] using pow_le_pow_right₀ (show 1 ≤ c + 1 by linarith) (by omega : 1 ≤ p.natDegree)
  change ‖p.eval z‖ ≤ c at hz
  linarith [hpow.trans hprod]

private theorem OMA.counting_strict_component_root (p : ℂ[X]) (hdeg : 0 < p.natDegree)
    {c : ℝ} (hc : 0 < c) (hbounded : Bornology.IsBounded {z : ℂ | ‖p.eval z‖ < c})
    {z : ℂ} (hz : ‖p.eval z‖ < c) :
    ∃ r ∈ connectedComponentIn {q : ℂ | ‖p.eval q‖ < c} z, p.eval r = 0 := by
  let S := {q : ℂ | ‖p.eval q‖ < c}
  let D := Metric.ball (0 : ℂ) c
  let U := connectedComponentIn S z
  have hzS : z ∈ S := hz
  have hUS : U ⊆ S := connectedComponentIn_subset S z
  have hzU : z ∈ U := mem_connectedComponentIn hzS
  have hU : IsConnected U := isConnected_connectedComponentIn_iff.mpr hzS
  have hD : IsPreconnected D := (convex_ball (0 : ℂ) c).isPreconnected
  have hSopen : IsOpen S := isOpen_lt p.continuous.norm continuous_const
  have hmap : IsOpenMap p.eval := by
    have han : AnalyticOnNhd ℂ p.eval univ := fun v _ => p.differentiable.analyticAt v
    rcases han.is_constant_or_isOpenMap with ⟨w, heq⟩ | hopen
    · have hpconst : p = C w := Polynomial.funext (fun x => by simpa using heq x)
      rw [hpconst, natDegree_C] at hdeg
      omega
    · exact hopen
  have hzD : p.eval z ∈ D := by simpa [D, Metric.mem_ball, dist_zero_right] using hz
  have hpart : closure U ∩ S ⊆ U := by
    have hpre : IsPreconnected (closure U ∩ S) :=
      hU.isPreconnected.subset_closure
        (fun q hq => ⟨subset_closure hq, hUS hq⟩) inter_subset_left
    exact hpre.subset_connectedComponentIn ⟨subset_closure hzU, hzS⟩ inter_subset_right
  have hcl : IsClosed (p.eval '' closure U) :=
    (((hbounded.subset hUS).isCompact_closure).image p.continuous).isClosed
  have hclSub : closure (p.eval '' U) ⊆ p.eval '' closure U :=
    closure_minimal (image_mono subset_closure) hcl
  have hsurj := hD.subset_of_closure_inter_subset (hmap _ hSopen.connectedComponentIn)
    ⟨p.eval z, hzD, ⟨z, hzU, rfl⟩⟩ (by
      intro w hw
      obtain ⟨q, hq, rfl⟩ := hclSub hw.1
      have hqS : q ∈ S := by
        simpa [S, D, Metric.mem_ball, dist_zero_right] using hw.2
      exact ⟨q, hpart ⟨hq, hqS⟩, rfl⟩)
  exact hsurj (Metric.mem_ball_self hc)

open scoped Classical in
private theorem OMA.numComponents_add_le_natDegree_add_one (f : ℂ[X]) (hf : f.Monic)
    {T : Set ℂ} (hTconn : IsPreconnected T) (hTsub : T ⊆ Erdos1047.strictSublevelSet f 1)
    {k : ℕ} (hk : 1 ≤ k) (hcount : k ≤ (f.roots.filter (· ∈ T)).card) :
    Erdos1042.numComponents f + k ≤ f.natDegree + 1 := by
  classical
  have hdeg := f.card_roots'
  have hfilter := Multiset.card_le_card (Multiset.filter_le (· ∈ T) f.roots)
  have hn : 0 < f.natDegree := by omega
  let S := Erdos1047.strictSublevelSet f 1
  have hclosedCompact := counting_sublevel_compact f hf hn 1 zero_le_one
  have hbounded : Bornology.IsBounded S :=
    hclosedCompact.isBounded.subset (fun z hz => (show ‖f.eval z‖ < 1 from hz).le)
  obtain ⟨t, ht⟩ := Multiset.card_pos_iff_exists_mem.mp
    (show 0 < (f.roots.filter (· ∈ T)).card by omega)
  have htT := (Multiset.mem_filter.mp ht).2
  let K := connectedComponentIn S t
  have hTK : T ⊆ K := hTconn.subset_connectedComponentIn htT hTsub
  let W := Erdos1047.componentsIn S
  let outside : Multiset ℂ := f.roots.filter (· ∉ T)
  let R : Set ℂ := ↑outside.toFinset
  let comp (r : ℂ) := connectedComponentIn S r
  have hR : R.Finite := Finset.finite_toSet _
  have hW : W ⊆ insert K (comp '' R) := by
    rintro U ⟨z, hz, rfl⟩
    obtain ⟨r, hrU, hr0⟩ := counting_strict_component_root f hn zero_lt_one hbounded hz
    change r ∈ connectedComponentIn S z at hrU
    have hr : r ∈ f.roots := (mem_roots hf.ne_zero).2 hr0
    by_cases hrT : r ∈ T
    · apply Set.mem_insert_iff.mpr
      left
      exact (connectedComponentIn_eq hrU).trans (connectedComponentIn_eq (hTK hrT)).symm
    · apply Set.mem_insert_iff.mpr
      right
      refine ⟨r, ?_, (connectedComponentIn_eq hrU).symm⟩
      exact Multiset.mem_toFinset.mpr (Multiset.mem_filter.mpr ⟨hr, hrT⟩)
  have hbound : W.ncard ≤ outside.card + 1 := by
    calc
      W.ncard ≤ (insert K (comp '' R)).ncard :=
        Set.ncard_le_ncard hW ((hR.image comp).insert K)
      _ ≤ (comp '' R).ncard + 1 := Set.ncard_insert_le _ _
      _ ≤ R.ncard + 1 := Nat.add_le_add_right (Set.ncard_image_le hR) _
      _ ≤ outside.card + 1 := by
        rw [show R.ncard = outside.toFinset.card from Set.ncard_coe_finset _]
        exact Nat.add_le_add_right outside.toFinset_card_le _
  have hsum : (f.roots.filter (· ∈ T)).card + outside.card = f.roots.card := by
    have he := congrArg Multiset.card (Multiset.filter_add_not (· ∈ T) f.roots)
    simpa only [Multiset.card_add] using he
  change W.ncard + k ≤ f.natDegree + 1
  omega

open scoped Classical in
private theorem OMA.compact_root_ball_pigeonhole
    {F : Set ℂ} (hF : IsCompact F) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, 0 < B ∧ ∀ {n : ℕ} (a : Fin n → ℂ), (∀ i, a i ∈ F) →
      ∀ G : Finset (Fin n), G.Nonempty →
        ∃ i ∈ G, G.card ≤ B * (Finset.univ.filter
          (fun j => a j ∈ Metric.ball (a i) ε)).card := by
  classical
  obtain ⟨D, _, hDf, hDcover⟩ := hF.finite_cover_balls (show 0 < ε / 3 by positivity)
  let centers := hDf.toFinset
  refine ⟨centers.card + 1, by omega, ?_⟩
  intro n a ha G hG
  let rootBall (i : Fin n) := Finset.univ.filter (fun j => a j ∈ Metric.ball (a i) ε)
  let nearCenter (x : ℂ) := G.filter (fun j => a j ∈ Metric.ball x (ε / 3))
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image G (fun i => (rootBall i).card) hG
  refine ⟨i, hi, ?_⟩
  change G.card ≤ (centers.card + 1) * (rootBall i).card
  have hGsub : G ⊆ centers.biUnion nearCenter := by
    intro j hj
    obtain ⟨x, hx⟩ := mem_iUnion.mp (hDcover (ha j))
    obtain ⟨hxD, hxball⟩ := mem_iUnion.mp hx
    exact Finset.mem_biUnion.mpr
      ⟨x, hDf.mem_toFinset.mpr hxD, Finset.mem_filter.mpr ⟨hj, hxball⟩⟩
  have hlocal (x : ℂ) : (nearCenter x).card ≤ (rootBall i).card := by
    by_cases hx : (nearCenter x).Nonempty
    · obtain ⟨j, hj⟩ := hx
      obtain ⟨hjG, hjball⟩ := Finset.mem_filter.mp hj
      have hsub : nearCenter x ⊆ rootBall j := by
        intro k hk
        have hkball := (Finset.mem_filter.mp hk).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Metric.mem_ball.mpr ?_⟩
        have ht := dist_triangle (a k) x (a j)
        rw [dist_comm x (a j)] at ht
        linarith [Metric.mem_ball.mp hkball, Metric.mem_ball.mp hjball]
      exact (Finset.card_le_card hsub).trans (hmax j hjG)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hx, Finset.card_empty]
      exact Nat.zero_le _
  calc
    G.card ≤ (centers.biUnion nearCenter).card := Finset.card_le_card hGsub
    _ ≤ ∑ x ∈ centers, (nearCenter x).card := Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ centers, (rootBall i).card := Finset.sum_le_sum (fun x _ => hlocal x)
    _ = centers.card * (rootBall i).card := by simp
    _ ≤ (centers.card + 1) * (rootBall i).card := Nat.mul_le_mul_right _ (by omega)

namespace LemniscateGoodRows

private theorem good_row_proportion (m L : ℝ) (hL : L < 0) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {n : ℕ}, 0 < n → ∀ R : Fin n → ℝ,
        (∀ i, m ≤ R i) → (∑ i, R i) ≤ (n : ℝ) * L →
        (n : ℝ) * c ≤ ((Finset.univ.filter (fun i => R i ≤ L / 2)).card : ℝ) := by
  classical
  let D : ℝ := 1 + |m| + |L / 2|
  let c : ℝ := (L / 2 - L) / D
  have hD : 0 < D := by
    dsimp [D]
    linarith only [abs_nonneg m, abs_nonneg (L / 2)]
  have hc : 0 < c := div_pos (by linarith only [hL]) hD
  have hcD : c * D = L / 2 - L := div_mul_cancel₀ _ hD.ne'
  have hDm : L / 2 - D ≤ m := by
    dsimp [D]
    linarith only [le_abs_self (L / 2), neg_abs_le m]
  refine ⟨c, hc, ?_⟩
  intro n _ R hR hmean
  have hweight : (∑ i : Fin n, if R i ≤ L / 2 then D else 0) =
      ((Finset.univ.filter (fun i => R i ≤ L / 2)).card : ℝ) * D := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hpoint (i : Fin n) : L / 2 - (if R i ≤ L / 2 then D else 0) ≤ R i := by
    split_ifs with hi
    · exact hDm.trans (hR i)
    · simpa only [sub_zero] using (le_of_not_ge hi)
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun i _ => hpoint i)
  have hs' : (n : ℝ) * (L / 2) -
      ((Finset.univ.filter (fun i => R i ≤ L / 2)).card : ℝ) * D ≤ ∑ i, R i := by
    simpa only [Finset.sum_sub_distrib, hweight, Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ, Fintype.card_fin] using hs
  apply le_of_mul_le_mul_right _ hD
  rw [mul_assoc, hcD]
  linarith only [hs', hmean]

end LemniscateGoodRows

namespace LemniscateSampling

private theorem uniform_truncated_average (F : Set ℂ) (hclosed : IsClosed F)
    (hpos : 0 < Erdos1042.transfiniteDiameter F) (hcap : Erdos1042.transfiniteDiameter F < 1) :
    IsCompact F ∧ ∃ (δ L : ℝ), 0 < δ ∧ L < 0 ∧
    ∀ {n : ℕ} (a : Fin n → ℂ), (∀ i, a i ∈ F) →
      (∑ i, ∑ j, Real.log (max δ (dist (a i) (a j)))) ≤ (n : ℝ)^2 * L := by
  obtain ⟨q, hq, hq1, N, hN, hprod⟩ := capacity_gives_product_bound F hpos hcap
  have hQ := pow_pos hq (N.choose 2)
  have hbounded := bounded_of_product_bound hN hQ hprod
  have hcompact := hbounded.isCompact_closure
  rw [hclosed.closure_eq] at hcompact
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hbounded
  let B : ℝ := max 1 (2*R)
  have hB : 1 ≤ B := le_max_left _ _
  have hdist (x y : ℂ) (hx : x ∈ F) (hy : y ∈ F) : dist x y ≤ B := by
    have hxR : dist x 0 ≤ R := Metric.mem_closedBall.1 (hR hx)
    have hyR : dist 0 y ≤ R := by rw [dist_comm]; exact Metric.mem_closedBall.1 (hR hy)
    apply le_trans (dist_triangle x 0 y)
    have hrB : 2*R ≤ B := le_max_right 1 (2*R)
    linarith only [hxR, hyR, hrB]
  obtain ⟨δ, hδ, _, htrunc⟩ := truncated_prod_bound (indexPairs N) hB hQ
  refine ⟨hcompact, δ, Real.log q, hδ, Real.log_neg hq hq1, ?_⟩
  intro n a ha
  apply pair_mean_le hN
  intro s
  let w (p : Σ _ : Fin N, Fin N) := dist (a (s p.1)) (a (s p.2))
  have hW := htrunc w (fun _ _ => dist_nonneg)
    (fun _ _ => hdist _ _ (ha _) (ha _)) (hprod (a ∘ s) (fun i => ha (s i)))
  have hWp (p : Σ _ : Fin N, Fin N) : 0 < max δ (w p) := hδ.trans_le (le_max_left _ _)
  have hlog := Real.log_le_log (Finset.prod_pos (fun p _ => hWp p)) hW
  rw [Real.log_prod (fun p _ => (hWp p).ne'), Real.log_pow, indexPairs, Finset.sum_sigma] at hlog
  exact hlog

private theorem choose_cluster_radius {δ L : ℝ} (hδ : 0 < δ) (hL : L < 0) :
    ∃ ε : ℝ, 0 < ε ∧ Real.log (1 + ε/δ) + L/2 < 0 := by
  have he : 1 < Real.exp (-(L/2)) := by
    rw [← Real.exp_zero, Real.exp_lt_exp]
    linarith
  let ε := δ * (Real.exp (-(L/2)) - 1) / 2
  have hε : 0 < ε := div_pos (mul_pos hδ (sub_pos.2 he)) (by norm_num)
  refine ⟨ε, hε, ?_⟩
  have heq : ε/δ = (Real.exp (-(L/2)) - 1) / 2 := by
    dsimp [ε]
    field_simp
  have hlt : 1 + ε/δ < Real.exp (-(L/2)) := by rw [heq]; linarith
  have hp : 0 < 1 + ε/δ := by positivity
  have hlog := Real.log_lt_log hp hlt
  rw [Real.log_exp] at hlog
  linarith

private theorem list_filter_card_eq_index_card {α : Type*} (P : α → Prop) [DecidablePred P]
    (l : List α) :
    (l.filter (fun x => decide (P x))).length =
      (Finset.univ.filter (fun i : Fin l.length => P (l.get i))).card := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [Finset.card_filter]
    change _ = ∑ i : Fin (l.length + 1), if P ((x :: l).get i) then 1 else 0
    rw [Fin.sum_univ_succ]
    by_cases hx : P x <;> simp [hx, Nat.add_comm] <;> exact ih

end LemniscateSampling

theorem OMA.solution : type_of% @Erdos1042.erdos_1042.parts.ii := by
  intro F hF hpos hcap
  classical
  obtain ⟨hcompact, δ, L, hδ, hL, haverage⟩ :=
    LemniscateSampling.uniform_truncated_average F hF hpos hcap
  obtain ⟨ε, hε, hsmall⟩ := LemniscateSampling.choose_cluster_radius hδ hL
  obtain ⟨c₀, hc₀, hgood⟩ := LemniscateGoodRows.good_row_proportion (Real.log δ) L hL
  obtain ⟨B, hB, hcover⟩ := OMA.compact_root_ball_pigeonhole hcompact hε
  have hBR : 0 < (B : ℝ) := by exact_mod_cast hB
  let c := c₀ / (2 * (B : ℝ))
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  obtain ⟨M, hM⟩ := exists_nat_ge c⁻¹
  filter_upwards [Filter.eventually_ge_atTop M] with n hnM
  intro f hf
  obtain ⟨hmonic, hdegree, hroots⟩ := hf
  have hnC : c⁻¹ ≤ (n : ℝ) := hM.trans (by exact_mod_cast hnM)
  have hcN := mul_le_mul_of_nonneg_right hnC hc.le
  rw [inv_mul_cancel₀ hc.ne'] at hcN
  have hn : 0 < n := by
    by_contra! hn
    have hn0 : n = 0 := by omega
    norm_num [hn0] at hcN
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let W := f.roots.toList
  let a : Fin W.length → ℂ := W.get
  have hlength : W.length = n := by
    calc
      W.length = f.natDegree := by
        simpa [W] using (IsAlgClosed.splits f).natDegree_eq_card_roots.symm
      _ = n := hdegree
  have hlen : 0 < W.length := hlength.symm ▸ hn
  have hlenR : 0 < (W.length : ℝ) := by exact_mod_cast hlen
  have ha (i : Fin W.length) : a i ∈ F :=
    hroots (a i) (Multiset.mem_toList.mp (List.get_mem W i))
  let R (i : Fin W.length) :=
    (∑ j, Real.log (max δ (dist (a i) (a j)))) / (W.length : ℝ)
  have hRlower (i : Fin W.length) : Real.log δ ≤ R i := by
    apply (le_div_iff₀ hlenR).2
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin W.length)))
      (fun j _ => Real.log_le_log hδ (le_max_left δ (dist (a i) (a j))))
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm] using hsum
  have hRmean : (∑ i, R i) ≤ (W.length : ℝ) * L := by
    dsimp [R]
    rw [← Finset.sum_div, div_le_iff₀ hlenR]
    nlinarith only [haverage a ha]
  let G := Finset.univ.filter (fun i : Fin W.length => R i ≤ L/2)
  have hG : (W.length : ℝ) * c₀ ≤ (G.card : ℝ) := hgood hlen R hRlower hRmean
  have hGpos : (0 : ℝ) < G.card := (mul_pos hlenR hc₀).trans_le hG
  have hGne : G.Nonempty := Finset.card_pos.1 (by exact_mod_cast hGpos)
  obtain ⟨i, hi, hcluster⟩ := hcover a ha G hGne
  have hiR : R i ≤ L/2 := (Finset.mem_filter.mp hi).2
  have hirow : (∑ j, Real.log (max δ (dist (a i) (a j)))) ≤ (W.length : ℝ) * (L/2) := by
    have hh := (div_le_iff₀ hlenR).1 hiR
    simpa only [mul_comm] using hh
  let T := Metric.ball (a i) ε
  have hTconn : IsPreconnected T := (convex_ball _ _).isPreconnected
  have hTsub : T ⊆ Erdos1047.strictSublevelSet f 1 := by
    have hball := LemniscateSampling.ball_of_negative_row hlen a hδ hε hsmall hirow
    have hfFact : f = ∏ j, (X - C (a j)) :=
      ((IsAlgClosed.splits f).eq_prod_roots_of_monic hmonic).trans (OMA.counting_prod_index _ _)
    intro z hz
    have hzeval : f.eval z = ∏ j, (z - a j) := by
      conv_lhs => rw [hfFact]
      simp [eval_prod]
    change ‖f.eval z‖ < 1
    rw [hzeval]
    exact hball hz
  let k := (f.roots.filter (· ∈ T)).card
  have hk : (Finset.univ.filter (fun j : Fin W.length => a j ∈ T)).card = k := by
    rw [← LemniscateSampling.list_filter_card_eq_index_card (fun z => z ∈ T) W]
    rw [← Multiset.coe_card, ← Multiset.filter_coe, Multiset.coe_toList]
  have hclusterR : (G.card : ℝ) ≤ (B : ℝ) * (k : ℝ) := by
    rw [hk] at hcluster
    exact_mod_cast hcluster
  have hratio : (n : ℝ) * c₀ ≤ (B : ℝ) * (k : ℝ) := by
    calc
      _ = (W.length : ℝ) * c₀ := by rw [hlength]
      _ ≤ _ := hG.trans hclusterR
  have hkpos : 1 ≤ k := by
    by_contra! hk0
    have hzero : k = 0 := by omega
    simp [hzero] at hratio
    exact (not_lt_of_ge hratio) (mul_pos hnR hc₀)
  have hcount := OMA.numComponents_add_le_natDegree_add_one f hmonic hTconn hTsub
    hkpos (show k ≤ (f.roots.filter (· ∈ T)).card from le_rfl)
  rw [hdegree] at hcount
  have hcountR : (Erdos1042.numComponents f : ℝ) + (k : ℝ) ≤ (n : ℝ) + 1 := by
    exact_mod_cast hcount
  have hcEq : 2*c = c₀ / (B : ℝ) := by dsimp [c]; field_simp
  have hclusterFinal : (n : ℝ) * (2*c) ≤ (k : ℝ) := by
    rw [hcEq, ← mul_div_assoc, div_le_iff₀ hBR]
    simpa only [mul_comm] using hratio
  nlinarith only [hcountR, hclusterFinal, hcN]