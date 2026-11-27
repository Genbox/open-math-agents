import FormalConjectures.ErdosProblems.«1087»

-- Problem: Erdős Problem 1087 — lower
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1087.lean:87 (declaration Erdos1087.erdos_1087.variants.lower)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.


namespace OMA1087L
open Finset

def C (K : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 K ×ˢ Icc 1 K).filter (fun zy => zy.2 ≤ zy.1 ∧ Nat.Coprime zy.1 zy.2)

def Pr (K : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 K ×ˢ Icc 1 K).filter (fun zy => zy.2 ≤ zy.1)

lemma harm_le (K : ℕ) : Real.log K ≤ ∑ z ∈ Icc 1 K, ((z:ℝ))⁻¹ := by
  have h := log_add_one_le_harmonic K
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp
  · calc Real.log K ≤ Real.log (K+1) :=
          Real.log_le_log (by exact_mod_cast hK) (by linarith)
      _ ≤ _ := h

lemma Pr_sum (K : ℕ) : ∑ zy ∈ Pr K, ((zy.1 : ℝ) ^ 2)⁻¹ = ∑ z ∈ Icc 1 K, ((z:ℝ))⁻¹ := by
  unfold Pr
  rw [sum_filter, sum_product]
  refine sum_congr rfl fun z hz => ?_
  rw [← sum_filter]; dsimp only; rw [sum_const, nsmul_eq_mul]
  have : (Icc 1 K).filter (fun y => y ≤ z) = Icc 1 z := by
    ext y; simp at hz ⊢; omega
  rw [this, Nat.card_Icc, Nat.add_sub_cancel]
  simp only [mem_Icc] at hz
  have hz0 : (z:ℝ) ≠ 0 := by have := hz.1; positivity
  rw [pow_two, mul_inv, ← mul_assoc, mul_inv_cancel₀ hz0, one_mul]

lemma inv_sq_le (K : ℕ) : ∑ g ∈ Icc 1 K, ((g:ℝ)^2)⁻¹ ≤ 2 := by
  have : Icc 1 K = Ioo 0 (K+1) := by ext; simp; omega
  rw [this]
  have := sum_Ioo_inv_sq_le (α := ℝ) 0 (K+1)
  simpa using this

lemma Pr_le_C (K : ℕ) :
    ∑ zy ∈ Pr K, ((zy.1 : ℝ) ^ 2)⁻¹ ≤ 2 * ∑ zy ∈ C K, ((zy.1 : ℝ) ^ 2)⁻¹ := by
  set ψ : ℕ × ℕ → ℕ × (ℕ × ℕ) := fun zy =>
    (Nat.gcd zy.1 zy.2, (zy.1 / Nat.gcd zy.1 zy.2, zy.2 / Nat.gcd zy.1 zy.2)) with hψ
  set h : ℕ × (ℕ × ℕ) → ℝ := fun t => ((t.1:ℝ)^2)⁻¹ * ((t.2.1 : ℝ)^2)⁻¹ with hh
  have hinj : ∀ a ∈ Pr K, ∀ b ∈ Pr K, ψ a = ψ b → a = b := by
    rintro ⟨z, y⟩ - ⟨z', y'⟩ - he
    simp only [ψ, Prod.mk.injEq] at he
    obtain ⟨hg, h1, h2⟩ := he
    have e1 := Nat.div_mul_cancel (Nat.gcd_dvd_left z y)
    have e2 := Nat.div_mul_cancel (Nat.gcd_dvd_right z y)
    have e3 := Nat.div_mul_cancel (Nat.gcd_dvd_left z' y')
    have e4 := Nat.div_mul_cancel (Nat.gcd_dvd_right z' y')
    rw [h1, hg, e3] at e1
    rw [h2, hg, e4] at e2
    rw [← e1, ← e2]
  have hmaps : ∀ a ∈ Pr K, ψ a ∈ Icc 1 K ×ˢ C K := by
    rintro ⟨z, y⟩ ha
    simp only [Pr, mem_filter, mem_product, mem_Icc] at ha
    obtain ⟨⟨⟨hz1, hzK⟩, hy1, hyK⟩, hyz⟩ := ha
    have gpos : 0 < Nat.gcd z y := Nat.gcd_pos_of_pos_left _ hz1
    have gz : Nat.gcd z y ≤ z := Nat.gcd_le_left y hz1
    have gy : Nat.gcd z y ≤ y := Nat.gcd_le_right _ hy1
    simp only [ψ, C, mem_product, mem_filter, mem_Icc]
    refine ⟨⟨gpos, gz.trans hzK⟩, ⟨⟨Nat.div_pos gz gpos, (Nat.div_le_self _ _).trans hzK⟩,
      Nat.div_pos gy gpos, ((Nat.div_le_self _ _).trans hyK)⟩,
      Nat.div_le_div_right hyz, Nat.coprime_div_gcd_div_gcd gpos⟩
  have hw : ∀ a ∈ Pr K, ((a.1 : ℝ) ^ 2)⁻¹ = h (ψ a) := by
    rintro ⟨z, y⟩ -
    simp only [h, ψ]
    have e : z = Nat.gcd z y * (z / Nat.gcd z y) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left z y)).symm
    conv_lhs => rw [e]
    push_cast
    rw [mul_pow, mul_inv]
  calc ∑ zy ∈ Pr K, ((zy.1 : ℝ) ^ 2)⁻¹ = ∑ zy ∈ Pr K, h (ψ zy) := sum_congr rfl hw
    _ = ∑ t ∈ (Pr K).image ψ, h t := (sum_image hinj).symm
    _ ≤ ∑ t ∈ Icc 1 K ×ˢ C K, h t :=
        sum_le_sum_of_subset_of_nonneg (image_subset_iff.2 hmaps) (fun _ _ _ => by positivity)
    _ = (∑ g ∈ Icc 1 K, ((g:ℝ)^2)⁻¹) * ∑ zy ∈ C K, ((zy.1 : ℝ) ^ 2)⁻¹ := by
        rw [sum_product, sum_mul]
        refine sum_congr rfl fun g _ => ?_
        rw [mul_sum]
    _ ≤ 2 * ∑ zy ∈ C K, ((zy.1 : ℝ) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right (inv_sq_le K) (sum_nonneg fun _ _ => by positivity)

def D (K : ℕ) : Finset (Σ _ : ℕ × ℕ, ℕ × ℕ) :=
  (C K).sigma (fun zy => Icc 1 (K / zy.1) ×ˢ Icc 1 (K / zy.1))

lemma D_card (K : ℕ) : (K:ℝ)^2 / 8 * Real.log K ≤ ((D K).card : ℝ) := by
  have hc : (D K).card = ∑ zy ∈ C K, (K / zy.1) ^ 2 := by
    unfold D; rw [card_sigma]; refine sum_congr rfl fun zy _ => ?_
    rw [card_product, Nat.card_Icc, Nat.add_sub_cancel, sq]
  have hterm : ∀ zy ∈ C K, (K:ℝ)^2 / 4 * ((zy.1:ℝ)^2)⁻¹ ≤ (((K / zy.1) ^ 2 : ℕ) : ℝ) := by
    intro zy hzy
    simp only [C, mem_filter, mem_product, mem_Icc] at hzy
    obtain ⟨⟨⟨hz1, hzK⟩, -⟩, -⟩ := hzy
    have hq : 1 ≤ K / zy.1 := Nat.div_pos hzK hz1
    have hlt : K < K / zy.1 * zy.1 + zy.1 := Nat.lt_div_mul_add hz1
    have key : K ≤ 2 * (K / zy.1) * zy.1 := by nlinarith
    have key' : (K:ℝ) ≤ 2 * ((K / zy.1 : ℕ) : ℝ) * zy.1 := by exact_mod_cast key
    have hz' : (0:ℝ) < zy.1 := by exact_mod_cast hz1
    have hK0 : (0:ℝ) ≤ K := by positivity
    push_cast
    calc (K:ℝ)^2 / 4 * ((zy.1:ℝ)^2)⁻¹ = (K:ℝ)^2 / (4 * (zy.1:ℝ)^2) := by
          field_simp
      _ ≤ ((K / zy.1 : ℕ) : ℝ) ^ 2 := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith
  have h1 := Pr_le_C K
  rw [Pr_sum] at h1
  have h2 := harm_le K
  have h3 : (K:ℝ)^2 / 4 * ∑ zy ∈ C K, ((zy.1 : ℝ) ^ 2)⁻¹ ≤ ((D K).card : ℝ) := by
    rw [hc, mul_sum]; push_cast
    refine sum_le_sum fun zy hzy => ?_
    have := hterm zy hzy
    push_cast at this
    exact this
  have hK0 : (0:ℝ) ≤ (K:ℝ)^2 / 8 := by positivity
  nlinarith

open scoped EuclideanGeometry Classical

noncomputable def ι (a : ℤ × ℤ) : ℝ² := !₂[(a.1 : ℝ), (a.2 : ℝ)]

lemma ι_inj : Function.Injective ι := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h0 := congrArg (fun v : ℝ² => v 0) h
  have h1 := congrArg (fun v : ℝ² => v 1) h
  simp [ι] at h0 h1
  rw [h0, h1]

lemma dist_ι (a b : ℤ × ℤ) :
    dist (ι a) (ι b) = Real.sqrt ((((a.1 - b.1)^2 + (a.2 - b.2)^2 : ℤ)) : ℝ) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp [ι, Real.dist_eq, sq_abs]

example : Infinite ℝ² := inferInstance

lemma rep (a b c d : ℝ²) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (h : dist a b = dist a c) :
    ({a, b, c, d} : Finset ℝ²).card = 4 ∧ Erdos1087.HasRepeatedDistance {a, b, c, d} := by
  have h4 : ({a, b, c, d} : Finset ℝ²).card = 4 := by
    rw [card_insert_of_notMem, card_insert_of_notMem, card_pair hcd] <;> simp [*]
  refine ⟨h4, ?_⟩
  unfold Erdos1087.HasRepeatedDistance distinctDistances distanceSet
  rw [h4, show Nat.choose 4 2 = 6 by rfl]
  have hsub : ({a, b, c, d} : Finset ℝ²).offDiag.image (fun pair => dist pair.1 pair.2) ⊆
      {dist a b, dist a d, dist b c, dist b d, dist c d} := by
    intro r hr
    simp only [mem_image, mem_offDiag, mem_insert, mem_singleton] at hr
    obtain ⟨⟨x, y⟩, ⟨hx, hy, hxy⟩, rfl⟩ := hr
    dsimp only at hx hy hxy ⊢
    simp only [mem_insert, mem_singleton]
    rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;>
      subst hx hy <;> simp_all [dist_comm]
  have := card_le_card hsub
  have h5 : ({dist a b, dist a d, dist b c, dist b d, dist c d} : Finset ℝ).card ≤ 5 :=
    (card_insert_le _ _).trans (Nat.succ_le_succ ((card_insert_le _ _).trans
      (Nat.succ_le_succ ((card_insert_le _ _).trans (Nat.succ_le_succ
        ((card_insert_le _ _).trans (Nat.succ_le_succ (card_singleton _).le)))))))
  omega


/-- `(zw + xy, yw - xz)` for `s = ⟨(z, y), (x, w)⟩`. -/
def v1 (s : Σ _ : ℕ × ℕ, ℕ × ℕ) : ℤ × ℤ :=
  ((s.1.1 : ℤ) * s.2.2 + (s.2.1 : ℤ) * s.1.2, (s.1.2 : ℤ) * s.2.2 - (s.2.1 : ℤ) * s.1.1)

/-- `(zw - xy, yw + xz)` for `s = ⟨(z, y), (x, w)⟩`. -/
def v2 (s : Σ _ : ℕ × ℕ, ℕ × ℕ) : ℤ × ℤ :=
  ((s.1.1 : ℤ) * s.2.2 - (s.2.1 : ℤ) * s.1.2, (s.1.2 : ℤ) * s.2.2 + (s.2.1 : ℤ) * s.1.1)

def A (K : ℕ) : Finset (ℤ × ℤ) := Ico (2 * K : ℤ) (4 * K) ×ˢ Ico (2 * K : ℤ) (4 * K)
def B (K : ℕ) : Finset (ℤ × ℤ) := Ico (6 * K : ℤ) (8 * K) ×ˢ Ico (6 * K : ℤ) (8 * K)
noncomputable def G (K : ℕ) : Finset ℝ² := (Ico (0 : ℤ) (8 * K) ×ˢ Ico (0 : ℤ) (8 * K)).image ι
def T (K : ℕ) : Finset ((ℤ × ℤ) × (Σ _ : ℕ × ℕ, ℕ × ℕ) × (ℤ × ℤ)) := A K ×ˢ D K ×ˢ B K

noncomputable def Φ (t : (ℤ × ℤ) × (Σ _ : ℕ × ℕ, ℕ × ℕ) × (ℤ × ℤ)) : ℝ² × ℝ² × ℝ² × ℝ² :=
  (ι t.1, ι (t.1 + v1 t.2.1), ι (t.1 + v2 t.2.1), ι t.2.2)

noncomputable def F (t : (ℤ × ℤ) × (Σ _ : ℕ × ℕ, ℕ × ℕ) × (ℤ × ℤ)) : Finset ℝ² :=
  {(Φ t).1, (Φ t).2.1, (Φ t).2.2.1, (Φ t).2.2.2}

lemma memD {K : ℕ} {s : Σ _ : ℕ × ℕ, ℕ × ℕ} (hs : s ∈ D K) :
    1 ≤ s.1.2 ∧ s.1.2 ≤ s.1.1 ∧ Nat.Coprime s.1.1 s.1.2 ∧ 1 ≤ s.2.1 ∧ 1 ≤ s.2.2 ∧
    s.2.1 * s.1.1 ≤ K ∧ s.2.2 * s.1.1 ≤ K ∧ s.2.1 * s.1.2 ≤ K ∧ s.1.2 * s.2.2 ≤ K := by
  obtain ⟨⟨z, y⟩, ⟨x, w⟩⟩ := s
  simp only [D, C, mem_sigma, mem_filter, mem_product, mem_Icc] at hs
  obtain ⟨⟨⟨⟨hz1, hzK⟩, hy1, hyK⟩, hyz, hcop⟩, ⟨hx1, hxK⟩, hw1, hwK⟩ := hs
  have e1 : x * z ≤ K := (Nat.mul_le_mul_right z hxK).trans (Nat.div_mul_le_self K z)
  have e2 : w * z ≤ K := (Nat.mul_le_mul_right z hwK).trans (Nat.div_mul_le_self K z)
  refine ⟨hy1, hyz, hcop, hx1, hw1, e1, e2, ?_, ?_⟩
  · exact (Nat.mul_le_mul_left x hyz).trans e1
  · calc y * w ≤ z * w := Nat.mul_le_mul_right w hyz
      _ = w * z := mul_comm _ _
      _ ≤ K := e2

lemma F_mem {K : ℕ} {t : (ℤ × ℤ) × (Σ _ : ℕ × ℕ, ℕ × ℕ) × (ℤ × ℤ)} (ht : t ∈ T K) :
    F t ∈ ((G K).powersetCard 4).filter Erdos1087.HasRepeatedDistance := by
  obtain ⟨⟨p1, p2⟩, s, ⟨q1, q2⟩⟩ := t
  simp only [T, A, B, mem_product, mem_Ico] at ht
  obtain ⟨⟨⟨hp1, hp1'⟩, hp2, hp2'⟩, hs, ⟨hq1, hq1'⟩, hq2, hq2'⟩ := ht
  obtain ⟨hy1, hyz, -, hx1, hw1, e1, e2, e3, e4⟩ := memD hs
  obtain ⟨⟨z, y⟩, ⟨x, w⟩⟩ := s
  dsimp only at *
  have i1 : (1:ℤ) ≤ y := by exact_mod_cast hy1
  have i2 : (y:ℤ) ≤ z := by exact_mod_cast hyz
  have i3 : (1:ℤ) ≤ x := by exact_mod_cast hx1
  have i4 : (1:ℤ) ≤ w := by exact_mod_cast hw1
  have j1 : (x:ℤ) * z ≤ K := by exact_mod_cast e1
  have j2 : (z:ℤ) * w ≤ K := by rw [mul_comm]; exact_mod_cast e2
  have j3 : (x:ℤ) * y ≤ K := by exact_mod_cast e3
  have j4 : (y:ℤ) * w ≤ K := by exact_mod_cast e4
  have k1 : (1:ℤ) ≤ x * z := by nlinarith
  have k2 : (1:ℤ) ≤ z * w := by nlinarith
  have k3 : (1:ℤ) ≤ x * y := by nlinarith
  have k4 : (1:ℤ) ≤ y * w := by nlinarith
  have hne : ∀ a b : ℤ × ℤ, a ≠ b → ι a ≠ ι b := fun a b h => ι_inj.ne h
  have hd : dist (ι (p1, p2)) (ι ((p1, p2) + v1 ⟨(z, y), (x, w)⟩)) =
      dist (ι (p1, p2)) (ι ((p1, p2) + v2 ⟨(z, y), (x, w)⟩)) := by
    rw [dist_ι, dist_ι]
    congr 2
    simp only [v1, v2, Prod.mk_add_mk]
    ring
  obtain ⟨h4, hrep⟩ := rep (ι (p1, p2)) (ι ((p1, p2) + v1 ⟨(z, y), (x, w)⟩))
    (ι ((p1, p2) + v2 ⟨(z, y), (x, w)⟩)) (ι (q1, q2))
    (hne _ _ (by intro h; have := congrArg Prod.fst h; simp [v1] at this; linarith))
    (hne _ _ (by intro h; have := congrArg Prod.snd h; simp [v2] at this; linarith))
    (hne _ _ (by intro h; have := congrArg Prod.fst h; simp at this; omega))
    (hne _ _ (by intro h; have := congrArg Prod.fst h; simp [v1, v2] at this; linarith))
    (hne _ _ (by intro h; have := congrArg Prod.fst h; simp [v1] at this; linarith))
    (hne _ _ (by intro h; have := congrArg Prod.fst h; simp [v2] at this; linarith)) hd
  simp only [mem_filter, mem_powersetCard]
  refine ⟨⟨?_, h4⟩, hrep⟩
  have box : ∀ a : ℤ × ℤ, 0 ≤ a.1 → a.1 < 8 * K → 0 ≤ a.2 → a.2 < 8 * K → ι a ∈ G K :=
    fun a h1 h2 h3 h4 => mem_image_of_mem _ (by simp only [mem_product, mem_Ico]; omega)
  simp only [F, Φ, insert_subset_iff, singleton_subset_iff]
  refine ⟨box _ ?_ ?_ ?_ ?_, box _ ?_ ?_ ?_ ?_, box _ ?_ ?_ ?_ ?_, box _ ?_ ?_ ?_ ?_⟩ <;>
    simp only [v1, v2, Prod.fst_add, Prod.snd_add] <;> linarith

lemma Φ_inj (K : ℕ) : Set.InjOn Φ (T K) := by
  rintro ⟨p, ⟨⟨z, y⟩, ⟨x, w⟩⟩, q⟩ ht ⟨p', ⟨⟨z', y'⟩, ⟨x', w'⟩⟩, q'⟩ ht' he
  simp only [Φ, Prod.mk.injEq] at he
  obtain ⟨h1, h2, h3, h4⟩ := he
  have hp := ι_inj h1
  have hq := ι_inj h4
  subst hp hq
  have h2' := add_left_cancel (ι_inj h2)
  have h3' := add_left_cancel (ι_inj h3)
  simp only [v1, v2, Prod.mk.injEq] at h2' h3'
  simp only [T, mem_coe, mem_product] at ht ht'
  obtain ⟨hy1, hyz, hcop, hx1, -, -, -, -, -⟩ := memD ht.2.1
  obtain ⟨hy1', -, hcop', hx1', -, -, -, -, -⟩ := memD ht'.2.1
  dsimp only at *
  have a1 : x * y = x' * y' := by
    have : (x:ℤ) * y = x' * y' := by linarith
    exact_mod_cast this
  have a2 : z * w = z' * w' := by
    have : (z:ℤ) * w = z' * w' := by linarith
    exact_mod_cast this
  have a3 : x * z = x' * z' := by
    have : (x:ℤ) * z = x' * z' := by linarith
    exact_mod_cast this
  have hx : x = x' := by
    have g1 : Nat.gcd (x * y) (x * z) = x := by
      rw [Nat.gcd_mul_left, Nat.Coprime.gcd_eq_one hcop.symm, mul_one]
    have g2 : Nat.gcd (x' * y') (x' * z') = x' := by
      rw [Nat.gcd_mul_left, Nat.Coprime.gcd_eq_one hcop'.symm, mul_one]
    rw [← g1, ← g2, a1, a3]
  subst hx
  have hy : y = y' := Nat.eq_of_mul_eq_mul_left hx1 a1
  have hz : z = z' := Nat.eq_of_mul_eq_mul_left hx1 a3
  subst hy hz
  have hw : w = w' := Nat.eq_of_mul_eq_mul_left (lt_of_lt_of_le hy1 hyz) a2
  subst hw
  rfl

lemma T_le (K : ℕ) : (T K).card ≤ 256 * Erdos1087.degenerateCount (G K) := by
  have h := card_le_mul_card_image (T K) (f := F) 256 ?_
  · refine h.trans (Nat.mul_le_mul_left _ ?_)
    unfold Erdos1087.degenerateCount
    exact card_le_card (fun S hS => by obtain ⟨t, ht, rfl⟩ := mem_image.1 hS; exact F_mem ht)
  · intro S hS
    obtain ⟨t0, -, rfl⟩ := mem_image.1 hS
    have hc : (F t0).card ≤ 4 := card_le_four
    calc #{a ∈ T K | F a = F t0} ≤ (F t0 ×ˢ F t0 ×ˢ F t0 ×ˢ F t0).card := by
          refine card_le_card_of_injOn Φ (fun t ht => ?_) ((Φ_inj K).mono ?_)
          · rw [mem_coe, mem_filter] at ht
            rw [mem_coe, ← ht.2]
            simp [F, mem_product]
          · intro t ht
            rw [mem_coe, mem_filter] at ht
            exact ht.1
      _ ≤ 256 := by
          rw [card_product, card_product, card_product]
          calc (F t0).card * ((F t0).card * ((F t0).card * (F t0).card)) ≤ 4 * (4 * (4 * 4)) := by
                gcongr
            _ = 256 := by norm_num

lemma T_card (K : ℕ) : (T K).card = 16 * K ^ 4 * (D K).card := by
  simp only [T, A, B, card_product, Int.card_Ico]
  have e1 : (4 * (K:ℤ) - 2 * K).toNat = 2 * K := by omega
  have e2 : (8 * (K:ℤ) - 6 * K).toNat = 2 * K := by omega
  rw [e1, e2]
  ring

lemma G_card (K : ℕ) : (G K).card ≤ 64 * K ^ 2 := by
  refine card_image_le.trans ?_
  simp only [card_product, Int.card_Ico]
  have e1 : (8 * (K:ℤ) - 0).toNat = 8 * K := by omega
  rw [e1]
  nlinarith

lemma main (K : ℕ) :
    (K:ℝ) ^ 6 * Real.log K ≤ 128 * (Erdos1087.degenerateCount (G K) : ℝ) := by
  have h1 := T_le K
  rw [T_card] at h1
  have h1' : 16 * (K:ℝ) ^ 4 * (D K).card ≤ 256 * (Erdos1087.degenerateCount (G K) : ℝ) := by
    exact_mod_cast h1
  have h2 := D_card K
  have h3 : 16 * (K:ℝ) ^ 4 * ((K:ℝ)^2 / 8 * Real.log K) ≤ 16 * (K:ℝ) ^ 4 * (D K).card :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  nlinarith

end OMA1087L

open scoped EuclideanGeometry Classical in
theorem OMA.solution : type_of% @Erdos1087.erdos_1087.variants.lower := by
  show (fun n : ℕ ↦ (n : ℝ) ^ 3 * Real.log n) =O[Filter.atTop] fun n : ℕ ↦ (Erdos1087.f n : ℝ)
  refine Asymptotics.isBigO_iff.2 ⟨2 ^ 33, Filter.eventually_atTop.2 ⟨65536, fun n hn => ?_⟩⟩
  have hn1 : (65536 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  set K := Nat.sqrt (n / 64) with hK
  have hK1 : K ^ 2 ≤ n / 64 := Nat.sqrt_le' _
  have hK2 : n / 64 < (K + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have hK3 : 32 ≤ K := Nat.le_sqrt'.2 (by omega)
  have hn64 : n < n / 64 * 64 + 64 := Nat.lt_div_mul_add (by norm_num)
  have hGn : (OMA1087L.G K).card ≤ n := by
    have := OMA1087L.G_card K
    have : n / 64 * 64 ≤ n := Nat.div_mul_le_self n 64
    nlinarith
  obtain ⟨Q, hGQ, hQ⟩ := Infinite.exists_superset_card_eq (OMA1087L.G K) n hGn
  have hdc : Erdos1087.degenerateCount (OMA1087L.G K) ≤ Erdos1087.f n := by
    have h1 : Erdos1087.degenerateCount (OMA1087L.G K) ≤ Erdos1087.degenerateCount Q := by
      unfold Erdos1087.degenerateCount
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.powersetCard_mono hGQ))
    have h2 := Erdos1087.degenerateCount_le_f Q
    rw [hQ] at h2
    omega
  have hdc' : (Erdos1087.degenerateCount (OMA1087L.G K) : ℝ) ≤ Erdos1087.f n := by
    exact_mod_cast hdc
  have hm := OMA1087L.main K
  have hk : (32 : ℝ) ≤ K := by exact_mod_cast hK3
  have hk2n : n ≤ 256 * K ^ 2 := by nlinarith
  have hk2 : (n : ℝ) ≤ 256 * (K : ℝ) ^ 2 := by exact_mod_cast hk2n
  have hlog : Real.log n ≤ 4 * Real.log K := by
    have l1 : Real.log n ≤ Real.log (256 * (K : ℝ) ^ 2) :=
      Real.log_le_log (by linarith) hk2
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at l1
    have l2 : 2 * Real.log 256 ≤ Real.log n := by
      rw [← Real.log_rpow (by norm_num)]
      exact Real.log_le_log (by positivity) (by norm_num; linarith)
    push_cast at l1
    linarith
  have hpow : (n : ℝ) ^ 3 ≤ 256 ^ 3 * (K : ℝ) ^ 6 := by
    calc (n : ℝ) ^ 3 ≤ (256 * (K : ℝ) ^ 2) ^ 3 := pow_le_pow_left₀ (by positivity) hk2 3
      _ = 256 ^ 3 * (K : ℝ) ^ 6 := by ring
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by linarith)
  calc (n : ℝ) ^ 3 * Real.log n ≤ (256 ^ 3 * (K : ℝ) ^ 6) * (4 * Real.log K) :=
        mul_le_mul hpow hlog hlogn (by positivity)
    _ = 256 ^ 3 * 4 * ((K : ℝ) ^ 6 * Real.log K) := by ring
    _ ≤ 256 ^ 3 * 4 * (128 * (Erdos1087.degenerateCount (OMA1087L.G K) : ℝ)) := by
        gcongr
    _ ≤ 2 ^ 33 * (Erdos1087.f n : ℝ) := by nlinarith
