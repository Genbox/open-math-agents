import FormalConjectures.ErdosProblems.«1119»

-- Problem: Erdős Problem 1119 — erdos wetzel ch
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1119.lean:118 (declaration Erdos1119.erdos_1119.variants.erdos_wetzel_ch)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA1119

open Complex Finset
open scoped Cardinal

/-- Gaussian rationals: a countable dense set. -/
def D : Set ℂ := Set.range (fun q : ℚ × ℚ => ((q.1 : ℂ) + (q.2 : ℂ) * I))

lemma D_countable : D.Countable := Set.countable_range _

lemma D_dense (c : ℂ) (ε : ℝ) (hε : 0 < ε) : ∃ d ∈ D, ‖d - c‖ < ε := by
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show c.re - ε / 2 < c.re + ε / 2 by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show c.im - ε / 2 < c.im + ε / 2 by linarith)
  refine ⟨(a : ℂ) + (b : ℂ) * I, ⟨(a, b), rfl⟩, ?_⟩
  calc ‖(a : ℂ) + (b : ℂ) * I - c‖
      ≤ |((a : ℂ) + (b : ℂ) * I - c).re| + |((a : ℂ) + (b : ℂ) * I - c).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ < ε / 2 + ε / 2 := by
        simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero, sub_im, add_im, mul_im, zero_add]
        simp only [Complex.ratCast_re, Complex.ratCast_im, mul_zero, mul_one, sub_zero, zero_add,
          add_zero]
        have h1 : |(a : ℝ) - c.re| < ε / 2 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
        have h2 : |(b : ℝ) - c.im| < ε / 2 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
        linarith
    _ = ε := by ring

lemma exists_t : ∃ t : ℂ, t ∉ D := by
  by_contra h
  push Not at h
  exact not_countable_complex (D_countable.mono (fun x _ => h x))

lemma choose_delta (c q : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℂ, ‖δ‖ ≤ ε ∧ (q = 0 → δ = 0) ∧ (q ≠ 0 → c + δ * q ∈ D) := by
  by_cases hq : q = 0
  · exact ⟨0, by simp; linarith, fun _ => rfl, fun h => absurd hq h⟩
  · obtain ⟨d, hd, hdc⟩ := D_dense c (ε * ‖q‖) (by positivity)
    refine ⟨(d - c) / q, ?_, fun h => absurd h hq, fun _ => ?_⟩
    · rw [norm_div, div_le_iff₀ (norm_pos_iff.2 hq)]
      linarith
    · rw [div_mul_cancel₀ _ hq]
      simpa using hd

noncomputable def P (z : ℂ) (w : ℕ → ℂ) (m : ℕ) (x : ℂ) : ℂ :=
  (x - z) * ∏ k ∈ range m, (x - w k)

noncomputable def M (z : ℂ) (w : ℕ → ℂ) (n : ℕ) : ℝ :=
  ((n : ℝ) + ‖z‖) * ∏ k ∈ range n, ((n : ℝ) + ‖w k‖)

lemma M_nonneg (z : ℂ) (w : ℕ → ℂ) (n : ℕ) : 0 ≤ M z w n := by
  unfold M; positivity

noncomputable def eps (z : ℂ) (w : ℕ → ℂ) (n : ℕ) : ℝ := (1 / 2) ^ n / (1 + M z w n)

lemma eps_pos (z : ℂ) (w : ℕ → ℂ) (n : ℕ) : 0 < eps z w n := by
  have := M_nonneg z w n
  unfold eps; positivity

noncomputable def step (z : ℂ) (w : ℕ → ℂ) (t : ℂ) (n : ℕ) (δs : ℕ → ℂ) : ℂ :=
  Classical.choose (choose_delta (t + ∑ m ∈ range n, δs m * P z w m (w n)) (P z w n (w n))
    (eps z w n) (eps_pos z w n))

noncomputable def Dn (z : ℂ) (w : ℕ → ℂ) (t : ℂ) : ℕ → ℕ → ℂ
  | 0 => fun _ => 0
  | n + 1 => Function.update (Dn z w t n) n (step z w t n (Dn z w t n))

noncomputable def δ (z : ℂ) (w : ℕ → ℂ) (t : ℂ) (m : ℕ) : ℂ := Dn z w t (m + 1) m

lemma Dn_stable (z : ℂ) (w : ℕ → ℂ) (t : ℂ) : ∀ n m, m < n → Dn z w t n m = δ z w t m := by
  intro n
  induction n with
  | zero => intro m hm; omega
  | succ n ih =>
    intro m hm
    rcases Nat.lt_succ_iff_lt_or_eq.1 hm with h | h
    · rw [Dn, Function.update_of_ne (by omega), ih m h]
    · subst h; rfl

lemma δ_spec (z : ℂ) (w : ℕ → ℂ) (t : ℂ) (n : ℕ) :
    ‖δ z w t n‖ ≤ eps z w n ∧ (P z w n (w n) = 0 → δ z w t n = 0) ∧
      (P z w n (w n) ≠ 0 →
        t + ∑ m ∈ range n, δ z w t m * P z w m (w n) + δ z w t n * P z w n (w n) ∈ D) := by
  have h1 : δ z w t n = step z w t n (Dn z w t n) := by
    simp [δ, Dn]
  have h2 : ∑ m ∈ range n, Dn z w t n m * P z w m (w n) =
      ∑ m ∈ range n, δ z w t m * P z w m (w n) :=
    sum_congr rfl fun m hm => by rw [Dn_stable z w t n m (mem_range.1 hm)]
  rw [h1]
  have hspec : ‖step z w t n (Dn z w t n)‖ ≤ eps z w n ∧
      (P z w n (w n) = 0 → step z w t n (Dn z w t n) = 0) ∧
      (P z w n (w n) ≠ 0 → t + ∑ m ∈ range n, Dn z w t n m * P z w m (w n) +
        step z w t n (Dn z w t n) * P z w n (w n) ∈ D) :=
    Classical.choose_spec (choose_delta _ _ _ (eps_pos z w n))
  generalize step z w t n (Dn z w t n) = d at hspec ⊢
  rw [h2] at hspec
  exact hspec

lemma P_bound (z : ℂ) (w : ℕ → ℂ) (n : ℕ) (R : ℝ) (x : ℂ) (hx : ‖x‖ ≤ R) :
    ‖P z w n x‖ ≤ (R + ‖z‖) * ∏ k ∈ range n, (R + ‖w k‖) := by
  unfold P
  rw [norm_mul, norm_prod]
  have hR : 0 ≤ R := le_trans (norm_nonneg _) hx
  have h1 : ‖x - z‖ ≤ R + ‖z‖ := (norm_sub_le x z).trans (by linarith)
  have h2 : ∀ k, ‖x - w k‖ ≤ R + ‖w k‖ := fun k => (norm_sub_le x (w k)).trans (by linarith)
  exact mul_le_mul h1 (prod_le_prod (fun k _ => norm_nonneg _) (fun k _ => h2 k))
    (prod_nonneg fun k _ => norm_nonneg _) (by positivity)

lemma P_zero_of_lt (z : ℂ) (w : ℕ → ℂ) {n m : ℕ} (h : n < m) : P z w m (w n) = 0 := by
  unfold P
  rw [prod_eq_zero (mem_range.2 h) (sub_self _), mul_zero]

lemma key (S : Set ℂ) (hS : S.Countable) (z : ℂ) (hz : z ∉ S) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ (∀ w ∈ S, f w ∈ D) ∧ f z ∉ D := by
  obtain ⟨t, ht⟩ := exists_t
  rcases S.eq_empty_or_nonempty with hS0 | hSne
  · exact ⟨fun _ => t, differentiable_const t, by simp [hS0], ht⟩
  obtain ⟨w, rfl⟩ := hS.exists_eq_range hSne
  set f : ℂ → ℂ := fun x => t + ∑' n, δ z w t n * P z w n x with hf
  -- differentiability
  have hdiff : Differentiable ℂ f := by
    intro x
    set R : ℝ := ‖x‖ + 1 with hR
    set u : ℕ → ℝ := fun n => (1 / 2) ^ n +
      (if (n : ℝ) < R then ‖δ z w t n‖ * ((R + ‖z‖) * ∏ k ∈ range n, (R + ‖w k‖)) else 0)
      with hu
    have hsum : Summable u := by
      refine (summable_geometric_of_lt_one (by norm_num) (by norm_num)).add ?_
      refine summable_of_ne_finset_zero (s := range (⌈R⌉₊ + 1)) fun n hn => ?_
      rw [if_neg]
      intro hlt
      apply hn
      rw [mem_range]
      have := Nat.le_ceil R
      have : (n : ℝ) < ⌈R⌉₊ + 1 := by linarith
      exact_mod_cast this
    have hon : DifferentiableOn ℂ (fun y => ∑' n, δ z w t n * P z w n y) (Metric.ball 0 R) := by
      refine differentiableOn_tsum_of_summable_norm hsum (fun n => ?_) Metric.isOpen_ball
        (fun n y hy => ?_)
      · unfold P
        fun_prop
      · rw [mem_ball_zero_iff] at hy
        rw [norm_mul]
        by_cases hn : (n : ℝ) < R
        · have hb := P_bound z w n R y hy.le
          have : ‖δ z w t n‖ * ‖P z w n y‖ ≤
              ‖δ z w t n‖ * ((R + ‖z‖) * ∏ k ∈ range n, (R + ‖w k‖)) :=
            mul_le_mul_of_nonneg_left hb (norm_nonneg _)
          simp only [hu, if_pos hn]
          have : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
          linarith
        · push Not at hn
          have hb := P_bound z w n n y (by linarith)
          have he := (δ_spec z w t n).1
          have hM := M_nonneg z w n
          have h3 : ‖δ z w t n‖ * ‖P z w n y‖ ≤ eps z w n * M z w n :=
            mul_le_mul he hb (norm_nonneg _) (eps_pos z w n).le
          have h4 : eps z w n * M z w n ≤ (1 / 2) ^ n := by
            unfold eps
            rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
            have : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
            nlinarith
          simp only [hu, if_neg (not_lt.2 hn), add_zero]
          linarith
    have hx : x ∈ Metric.ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; linarith
    exact (hon.differentiableAt (Metric.isOpen_ball.mem_nhds hx)).const_add t
  -- values
  have hval : ∀ n, f (w n) = t + ∑ m ∈ range n, δ z w t m * P z w m (w n) +
      δ z w t n * P z w n (w n) := by
    intro n
    simp only [hf]
    rw [tsum_eq_sum (s := range (n + 1)), sum_range_succ, add_assoc]
    intro m hm
    rw [mem_range, not_lt] at hm
    rw [P_zero_of_lt z w (by omega), mul_zero]
  have hfz : f z = t := by
    simp only [hf]
    have : ∀ n, δ z w t n * P z w n z = 0 := fun n => by simp [P]
    simp [this]
  refine ⟨f, hdiff, ?_, by rw [hfz]; exact ht⟩
  rintro _ ⟨n, rfl⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hq : P z w n (w n) = 0
    · unfold P at hq
      rcases mul_eq_zero.1 hq with h | h
      · exact absurd ⟨n, sub_eq_zero.1 h⟩ hz
      · obtain ⟨k, hk, hk0⟩ := prod_eq_zero_iff.1 h
        rw [sub_eq_zero.1 hk0]
        exact ih k (mem_range.1 hk)
    · rw [hval]
      exact (δ_spec z w t n).2.2 hq

end OMA1119

open scoped Cardinal in
theorem OMA.solution : type_of% @Erdos1119.erdos_1119.variants.erdos_wetzel_ch := by
  intro h'
  have h : (𝔠 : Cardinal.{0}) = Cardinal.aleph 1 := by
    have h2 := h'
    rw [← Cardinal.lift_continuum.{_, 0}] at h2
    have h3 : Cardinal.aleph 1 = Cardinal.lift (Cardinal.aleph (1 : Ordinal.{0})) := by
      rw [Cardinal.lift_aleph]; simp
    rw [h3] at h2
    exact Cardinal.lift_inj.1 h2
  obtain ⟨e⟩ : Nonempty (ℂ ≃ (Cardinal.aleph 1).ord.ToType) := by
    apply Cardinal.eq.1
    rw [Cardinal.mk_complex, Cardinal.mk_toType, Cardinal.card_ord]
    exact h
  have hS : ∀ z, {w : ℂ | e w < e z}.Countable := by
    intro z
    have hc : (Set.Iio (e z)).Countable :=
      (Cardinal.countable_iff_lt_aleph_one _).2 (Cardinal.mk_Iio_toType_ord_lt _)
    exact hc.preimage e.injective
  have hk : ∀ z, ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ (∀ w ∈ {w : ℂ | e w < e z}, f w ∈ OMA1119.D) ∧
      f z ∉ OMA1119.D := fun z => OMA1119.key _ (hS z) z (by simp)
  choose g hgd hgS hgz using hk
  have hinj : Function.Injective g := by
    intro y z hyz
    by_contra hne
    rcases lt_trichotomy (e y) (e z) with hlt | heq | hgt
    · exact hgz y (hyz ▸ hgS z y hlt)
    · exact hne (e.injective heq)
    · exact hgz z (hyz.symm ▸ hgS y z hgt)
  refine ⟨Set.range g, ?_, ?_, ?_⟩
  · rintro _ ⟨z, rfl⟩; exact hgd z
  · intro z₀
    have hsub : {y : ℂ | ∃ f ∈ Set.range g, f z₀ = y} ⊆
        OMA1119.D ∪ (fun z => g z z₀) '' ({w : ℂ | e w < e z₀} ∪ {z₀}) := by
      rintro y ⟨_, ⟨z, rfl⟩, rfl⟩
      by_cases hz : e z₀ < e z
      · exact Or.inl (hgS z z₀ hz)
      · right
        refine ⟨z, ?_, rfl⟩
        rcases lt_or_eq_of_le (not_lt.1 hz) with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (e.injective h1)
    exact (OMA1119.D_countable.union (((hS z₀).union (Set.countable_singleton z₀)).image _)).mono
      hsub
  · intro hc
    apply not_countable_complex
    have : (Set.univ : Set ℂ) = g ⁻¹' Set.range g := by simp
    rw [this]
    exact hc.preimage hinj
