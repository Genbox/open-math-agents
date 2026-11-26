import FormalConjectures.Arxiv.«2602.05192».FirstProof4

-- Problem: First Proof, Theorem 4 — four 3
-- Upstream: formal-conjectures FormalConjectures/Arxiv/2602.05192/FirstProof4.lean:176 (declaration Arxiv.«2602.05192».four_3)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.


open Polynomial Finset Arxiv.«2602.05192»

namespace OMA.Four3

noncomputable def Aco (p : ℝ[X]) : ℝ := p.coeff 1 - p.coeff 2 ^ 2 / 3
noncomputable def Bco (p : ℝ[X]) : ℝ := p.coeff 0 - p.coeff 1 * p.coeff 2 / 3 + 2 * p.coeff 2 ^ 3 / 27
noncomputable def Vf (a b : ℝ) : ℝ := if a = 0 then 0 else (-4 * a ^ 3 - 27 * b ^ 2) / (18 * a ^ 2)

lemma cubic_expand (x y z : ℝ) : (X - C x) * (X - C y) * (X - C z) =
    X ^ 3 + C (-(x + y + z)) * X ^ 2 + C (x * y + y * z + z * x) * X + C (-(x * y * z)) := by
  simp only [map_neg, map_add, map_mul]; ring

lemma key (p : ℝ[X]) (hm : p.Monic) (hd : p.natDegree = 3) (hc : p.roots.card = 3) :
    1 / Φ p = ENNReal.ofReal (Vf (Aco p) (Bco p)) ∧ Aco p ≤ 0 ∧ (Aco p = 0 → Bco p = 0) ∧
      0 ≤ -4 * Aco p ^ 3 - 27 * Bco p ^ 2 := by
  obtain ⟨x, y, z, hr⟩ := Multiset.card_eq_three.mp hc
  have hp : p = (X - C x) * (X - C y) * (X - C z) := by
    have := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm (by rw [hc, hd])
    rw [← this, hr]; simp [mul_assoc]
  have hcf : p.coeff 2 = -(x + y + z) ∧ p.coeff 1 = x * y + y * z + z * x ∧
      p.coeff 0 = -(x * y * z) := by
    rw [hp, cubic_expand]
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
    norm_num
  obtain ⟨h2, h1, h0⟩ := hcf
  have hA : Aco p = -((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) / 6 := by
    rw [Aco, h2, h1]; ring
  have hB : Bco p = -(x * y * z) - (x * y + y * z + z * x) * (-(x + y + z)) / 3
      + 2 * (-(x + y + z)) ^ 3 / 27 := by
    rw [Bco, h2, h1, h0]
  have hD : -4 * Aco p ^ 3 - 27 * Bco p ^ 2 = ((x - y) * (y - z) * (z - x)) ^ 2 := by
    rw [hA, hB]; ring
  refine ⟨?_, ?_, ?_, by rw [hD]; positivity⟩
  rotate_left
  · rw [hA]; have : 0 ≤ (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 := by positivity
    linarith
  · intro h0'
    rw [hA] at h0'
    have hxy : x = y := by nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    have hyz : y = z := by nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    rw [hB, hxy, hyz]; ring
  unfold Φ
  rw [hr]
  by_cases hnd : ({x, y, z} : Multiset ℝ).Nodup
  · have hxy : x ≠ y := by simp at hnd; tauto
    have hxz : x ≠ z := by simp at hnd; tauto
    have hyz : y ≠ z := by simp at hnd; tauto
    rw [if_pos hnd]
    have hts : ({x, y, z} : Multiset ℝ).toFinset = {x, y, z} := by
      ext t; simp
    rw [hts]
    dsimp only
    have hinner : ∀ i ∈ ({x, y, z} : Finset ℝ),
        (∑ j ∈ ({x, y, z} : Finset ℝ).erase i, 1 / (i - j)) =
          ∑ j ∈ ({x, y, z} : Finset ℝ), 1 / (i - j) := by
      intro i hi
      exact Finset.sum_erase _ (by simp)
    rw [Finset.sum_congr rfl (fun i hi => congrArg (· ^ 2) (hinner i hi))]
    have hxy' : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hxz' : x - z ≠ 0 := sub_ne_zero.mpr hxz
    have hyz' : y - z ≠ 0 := sub_ne_zero.mpr hyz
    have hS : (∑ i ∈ ({x, y, z} : Finset ℝ), (∑ j ∈ ({x, y, z} : Finset ℝ), 1 / (i - j)) ^ 2)
        = 18 * (Aco p) ^ 2 / ((x - y) * (y - z) * (z - x)) ^ 2 := by
      have nx : x ∉ ({y, z} : Finset ℝ) := by simp [hxy, hxz]
      have ny : y ∉ ({z} : Finset ℝ) := by simp [hyz]
      simp only [Finset.sum_insert nx, Finset.sum_insert ny, Finset.sum_singleton, sub_self,
        div_zero, add_zero, zero_add]
      rw [hA]
      have hzx' : z - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxz)
      have hyx' : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
      have hzy' : z - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hyz)
      field_simp
      ring
    rw [hS]
    have hA0 : Aco p ≠ 0 := by
      rw [hA]
      have : 0 < (x - y) ^ 2 := by positivity
      have : 0 ≤ (y - z) ^ 2 + (z - x) ^ 2 := by positivity
      intro h; linarith
    have hpos : 0 < 18 * (Aco p) ^ 2 / ((x - y) * (y - z) * (z - x)) ^ 2 := by
      have : (z - x) ≠ 0 := sub_ne_zero.mpr (Ne.symm hxz)
      positivity
    change 1 / ENNReal.ofReal _ = _
    rw [one_div, ← ENNReal.ofReal_inv_of_pos hpos]
    congr 1
    rw [Vf, if_neg hA0, hD]
    have : (z - x) ≠ 0 := sub_ne_zero.mpr (Ne.symm hxz)
    field_simp
  · rw [if_neg hnd]
    simp only [ENNReal.div_top]
    have hD0 : ((x - y) * (y - z) * (z - x)) ^ 2 = 0 := by
      by_contra hne
      apply hnd
      have h1 : x ≠ y := by intro h; apply hne; rw [h]; ring
      have h2 : y ≠ z := by intro h; apply hne; rw [h]; ring
      have h3 : x ≠ z := by intro h; apply hne; rw [h]; ring
      simp [h1, h2, h3]
    rw [Vf]
    split_ifs
    · simp
    · rw [hD, hD0]; simp


lemma conv3_eq (p q : ℝ[X]) : finiteAdditiveConvolution 3 p q =
    C (p.coeff 3 * q.coeff 3) * X ^ 3
    + C (p.coeff 2 * q.coeff 3 + p.coeff 3 * q.coeff 2) * X ^ 2
    + C (p.coeff 1 * q.coeff 3 + 2/3 * p.coeff 2 * q.coeff 2 + p.coeff 3 * q.coeff 1) * X
    + C (p.coeff 0 * q.coeff 3 + 1/3 * p.coeff 1 * q.coeff 2 + 1/3 * p.coeff 2 * q.coeff 1
        + p.coeff 3 * q.coeff 0) := by
  unfold finiteAdditiveConvolution
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.Nat.antidiagonal_succ,
    Finset.Nat.antidiagonal_zero, Finset.sum_cons, Finset.sum_map, Finset.sum_singleton]
  simp [Nat.factorial, smul_eq_C_mul]
  norm_num
  ring

lemma Vf_nonneg (a b : ℝ) (h : 0 ≤ -4 * a ^ 3 - 27 * b ^ 2) : 0 ≤ Vf a b := by
  unfold Vf; split_ifs
  · exact le_rfl
  · positivity

lemma Vf_super (a b a' b' : ℝ) (ha : a ≤ 0) (ha' : a' ≤ 0) (hb : a = 0 → b = 0)
    (hb' : a' = 0 → b' = 0) : Vf a b + Vf a' b' ≤ Vf (a + a') (b + b') := by
  rcases eq_or_lt_of_le ha with h0 | hlt
  · rw [h0, hb h0]; simp [Vf]
  rcases eq_or_lt_of_le ha' with h0' | hlt'
  · rw [h0', hb' h0']; simp [Vf]
  have hs : a + a' < 0 := by linarith
  have hne : a ≠ 0 := hlt.ne
  have hne' : a' ≠ 0 := hlt'.ne
  have hsne : a + a' ≠ 0 := hs.ne
  have e : ∀ c d : ℝ, c ≠ 0 → Vf c d = -2 * c / 9 - 3 / 2 * (d / c) ^ 2 := by
    intro c d hc; rw [Vf, if_neg hc]; field_simp; ring
  rw [e _ _ hne, e _ _ hne', e _ _ hsne]
  set u := b / a
  set v := b' / a'
  set l := a / (a + a')
  have hw : (b + b') / (a + a') = l * u + (1 - l) * v := by
    simp only [u, v, l]; field_simp; ring
  have hl0 : 0 ≤ l := div_nonneg_of_nonpos ha hs.le
  have hl1 : 0 ≤ 1 - l := by
    have : 1 - l = a' / (a + a') := by simp only [l]; field_simp; ring
    rw [this]; exact div_nonneg_of_nonpos ha' hs.le
  rw [hw]
  nlinarith [mul_nonneg (mul_nonneg hl0 hl1) (sq_nonneg (u - v)), sq_nonneg u, sq_nonneg v,
    mul_nonneg hl0 (sq_nonneg u), mul_nonneg hl1 (sq_nonneg v)]

lemma small_roots (r : ℝ[X]) (hd : r.natDegree = 3) (hc : r.roots.card ≠ 3) : 1 / Φ r = ⊤ := by
  obtain ⟨g, hg, hdeg, hg0⟩ := exists_prod_multiset_X_sub_C_mul r
  have hle : r.roots.card ≤ 1 := by
    by_contra hcon
    have h2 : r.roots.card = 2 := by omega
    have hg1 : g.natDegree = 1 := by omega
    have hgne : g ≠ 0 := by intro h; rw [h] at hg1; simp at hg1
    obtain ⟨x, hx⟩ := exists_root_of_degree_eq_one ((degree_eq_iff_natDegree_eq hgne).mpr hg1)
    have : x ∈ g.roots := (mem_roots hgne).mpr hx
    rw [hg0] at this; simp at this
  unfold Φ
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h | h
  · rw [Multiset.card_eq_zero.mp h]; simp
  · obtain ⟨x, hx⟩ := Multiset.card_eq_one.mp h
    rw [hx]; simp


theorem main3 : ∀ (p q : ℝ[X]), FourProp p q 3 := by
  intro p q hpd hpc hqd hqc hpm hqm
  have hpn : p.natDegree = 3 := natDegree_eq_of_degree_eq_some hpd
  have hqn : q.natDegree = 3 := natDegree_eq_of_degree_eq_some hqd
  have hp3 : p.coeff 3 = 1 := by rw [← hpn]; exact hpm
  have hq3 : q.coeff 3 = 1 := by rw [← hqn]; exact hqm
  obtain ⟨kp, ap, bp, dp⟩ := key p hpm hpn hpc
  obtain ⟨kq, aq, bq, dq⟩ := key q hqm hqn hqc
  have hrm : (finiteAdditiveConvolution 3 p q).Monic :=
    finiteAdditiveConvolution_monic' 3 p q (by norm_num) hpd hqd hpm hqm
  have hE := conv3_eq p q
  rw [hp3, hq3] at hE
  set r := finiteAdditiveConvolution 3 p q with hrdef
  have hc : ∀ k, r.coeff k = (C (1 * 1) * X ^ 3
    + C (p.coeff 2 * 1 + 1 * q.coeff 2) * X ^ 2
    + C (p.coeff 1 * 1 + 2/3 * p.coeff 2 * q.coeff 2 + 1 * q.coeff 1) * X
    + C (p.coeff 0 * 1 + 1/3 * p.coeff 1 * q.coeff 2 + 1/3 * p.coeff 2 * q.coeff 1
        + 1 * q.coeff 0) : ℝ[X]).coeff k := by
    intro k; rw [hE]
  have c0 := hc 0
  have c1 := hc 1
  have c2 := hc 2
  have c3 := hc 3
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] at c0 c1 c2 c3
  norm_num at c0 c1 c2 c3
  have hrn : r.natDegree = 3 := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · rw [hE]; compute_degree
    · rw [c3]; norm_num
  by_cases hrc : r.roots.card = 3
  · obtain ⟨kr, -, -, -⟩ := key r hrm hrn hrc
    have hA : Aco r = Aco p + Aco q := by
      unfold Aco; rw [c1, c2]; ring
    have hB : Bco r = Bco p + Bco q := by
      unfold Bco; rw [c0, c1, c2]; ring
    rw [kp, kq, kr, hA, hB, ← ENNReal.ofReal_add (Vf_nonneg _ _ dp) (Vf_nonneg _ _ dq)]
    exact ENNReal.ofReal_le_ofReal (Vf_super _ _ _ _ ap aq bp bq)
  · rw [small_roots r hrn hrc]; exact le_top

end OMA.Four3

theorem OMA.solution : type_of% @Arxiv.«2602.05192».four_3 := OMA.Four3.main3
