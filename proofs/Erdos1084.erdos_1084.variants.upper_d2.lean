import FormalConjectures.ErdosProblems.«1084»

/-! A deficit estimate for planar contact graphs. -/

open scoped BigOperators EuclideanGeometry

namespace PackingDeficit

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (p : V → ℂ)

private theorem terminal (hp : Function.Injective p)
    (opposite : ∀ x y, G.degree y = 6 → G.Adj x y →
      ∃ z, G.Adj y z ∧ p z - p y = p y - p x)
    {a b : V} (hab : G.Adj a b) :
    ∃ x y : V, G.degree y ≠ 6 ∧ G.Adj y x ∧
      p y - p x = p b - p a ∧
      ∃ k : ℕ, p y = p a + (k : ℂ) * (p b - p a) := by
  classical
  by_contra! H
  let d := p b - p a
  have hd : d ≠ 0 := sub_ne_zero.mpr (fun h => hab.ne (hp h).symm)
  have hex (k : ℕ) : ∃ x y : V, G.Adj x y ∧ p x = p a + (k : ℂ) * d ∧
      p y = p x + d := by
    induction k with
    | zero => exact ⟨a, b, hab, by simp, by dsimp [d]; ring⟩
    | succ k ih =>
      obtain ⟨x, y, hxy, hx, hy⟩ := ih
      have hy' : p y = p a + ((k + 1 : ℕ) : ℂ) * d := by push_cast; rw [hy, hx]; ring
      have hxy' : p y - p x = d := by rw [hy]; ring
      have hfull : G.degree y = 6 := by
        by_contra h
        exact H x y h hxy.symm hxy' (k + 1) hy'
      obtain ⟨z, hyz, hz⟩ := opposite x y hfull hxy
      exact ⟨y, z, hyz, hy', sub_eq_iff_eq_add.mp (hz.trans hxy') |>.trans (add_comm _ _)⟩
  choose x y _ hx _ using hex
  let f : Fin (Fintype.card V + 1) → V := fun i => x i.val
  have hfin : Function.Injective f := by
    intro i j h
    apply Fin.ext
    have hh := congrArg p h
    change p (x i.val) = p (x j.val) at hh
    rw [hx, hx] at hh
    have hmul := add_left_cancel hh
    exact_mod_cast (mul_right_cancel₀ hd hmul)
  have := Fintype.card_le_of_injective f hfin
  simp only [Fintype.card_fin] at this
  omega

private def cross (x y : ℂ) : ℝ := x.re * y.im - x.im * y.re

private theorem coordinates_unique {u v : ℂ} {a b c d : ℕ}
    (huv : cross u v ≠ 0)
    (h : ((a : ℂ) - (b : ℂ)) * u = ((c : ℂ) - (d : ℂ)) * v) :
    a = b := by
  have hcross := congrArg (fun z => cross z v) h
  simp only [cross, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.natCast_re, Complex.natCast_im, sub_self, zero_mul, sub_zero, add_zero] at hcross
  have hz : ((a : ℝ) - (b : ℝ)) * cross u v = 0 := by
    unfold cross
    linarith only [show ((a : ℝ) - (b : ℝ)) * (u.re * v.im - u.im * v.re) =
        ((a : ℝ) - (b : ℝ)) * u.re * v.im - ((a : ℝ) - (b : ℝ)) * u.im * v.re by ring,
      hcross, show ((c : ℝ) - (d : ℝ)) * v.re * v.im -
        ((c : ℝ) - (d : ℝ)) * v.im * v.re = 0 by ring]
  exact_mod_cast sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right huv)

private theorem size_bound (hp : Function.Injective p)
    (degree_le : ∀ x, G.degree x ≤ 6)
    (opposite : ∀ x y, G.degree y = 6 → G.Adj x y →
      ∃ z, G.Adj y z ∧ p z - p y = p y - p x)
    (independent : ∀ a, G.degree a = 6 → ∃ b c, G.Adj a b ∧ G.Adj a c ∧
      cross (p b - p a) (p c - p a) ≠ 0) :
    Fintype.card V ≤ (Finset.univ.filter fun x => G.degree x ≠ 6).card +
      (6 * (Finset.univ.filter fun x => G.degree x ≠ 6).card)^2 := by
  classical
  let Bad := {x : V // G.degree x ≠ 6}
  let Full := {x : V // G.degree x = 6}
  let Terminal := Σ b : Bad, {x : V // x ∈ G.neighborFinset b.val}
  have hT : Fintype.card Terminal ≤ 6 * Fintype.card Bad := by
    rw [Fintype.card_sigma]
    calc
      ∑ b : Bad, Fintype.card {x : V // x ∈ G.neighborFinset b.val}
          ≤ ∑ _ : Bad, (6 : ℕ) := by
            apply Finset.sum_le_sum
            intro b _
            rw [Fintype.card_coe, SimpleGraph.card_neighborFinset_eq_degree]
            exact degree_le b.val
      _ = 6 * Fintype.card Bad := by simp [mul_comm]
  have ht (a : Full) : ∃ u v : Terminal, ∃ k l : ℕ,
      p u.1.val = p a.val + (k : ℂ) * (p u.1.val - p u.2.val) ∧
      p v.1.val = p a.val + (l : ℂ) * (p v.1.val - p v.2.val) ∧
      cross (p u.1.val - p u.2.val) (p v.1.val - p v.2.val) ≠ 0 := by
    obtain ⟨b, c, hab, hac, hcross⟩ := independent a.val a.property
    obtain ⟨x, y, hy, hxy, huv, k, hk⟩ := terminal G p hp opposite hab
    obtain ⟨x', y', hy', hxy', huv', l, hl⟩ := terminal G p hp opposite hac
    exact ⟨⟨⟨y, hy⟩, ⟨x, (G.mem_neighborFinset _ _).mpr hxy⟩⟩,
      ⟨⟨y', hy'⟩, ⟨x', (G.mem_neighborFinset _ _).mpr hxy'⟩⟩, k, l,
      by dsimp; rw [huv]; exact hk, by dsimp; rw [huv']; exact hl,
      by dsimp; rw [huv, huv']; exact hcross⟩
  choose u v k l hu hv hcross using ht
  let f : Full → Terminal × Terminal := fun a => (u a, v a)
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : u a = u b := congrArg Prod.fst hab
    have h2 : v a = v b := congrArg Prod.snd hab
    have h₁ := hu b
    have h₂ := hv b
    rw [← h1] at h₁
    rw [← h2] at h₂
    have ha := hu a
    have hb := hv a
    have hdir :
        ((k a : ℂ) - (k b : ℂ)) * (p (u a).1.val - p (u a).2.val) =
        ((l a : ℂ) - (l b : ℂ)) * (p (v a).1.val - p (v a).2.val) := by
      calc
        _ = p b.val - p a.val := by linear_combination h₁ - ha
        _ = _ := by linear_combination hb - h₂
    have hk := coordinates_unique (hcross a) hdir
    rw [hk] at ha
    exact Subtype.ext (hp (add_right_cancel (ha.symm.trans h₁)))
  have hF : Fintype.card Full ≤ (6 * Fintype.card Bad)^2 :=
    (Fintype.card_le_of_injective f hf).trans
      (by rw [Fintype.card_prod]; simpa [pow_two] using Nat.mul_le_mul hT hT)
  have hsplit : Fintype.card V = Fintype.card Bad + Fintype.card Full := by
    have h := Fintype.card_congr (Equiv.sumCompl fun x : V => G.degree x ≠ 6)
    simpa [Bad, Full] using h.symm
  have hB : Fintype.card Bad = (Finset.univ.filter fun x => G.degree x ≠ 6).card := by
    exact Fintype.card_subtype _
  rw [hB] at hF hsplit
  omega

private theorem chord_gap {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hd : 1 ≤ ‖x - y‖) (harg : x.arg ≤ y.arg) :
    Real.pi / 3 ≤ y.arg - x.arg ∧ y.arg - x.arg ≤ 5 * Real.pi / 3 := by
  have hxr : x.re = Real.cos x.arg := by
    rw [← Complex.norm_mul_cos_arg, hx, one_mul]
  have hxi : x.im = Real.sin x.arg := by
    rw [← Complex.norm_mul_sin_arg, hx, one_mul]
  have hyr : y.re = Real.cos y.arg := by
    rw [← Complex.norm_mul_cos_arg, hy, one_mul]
  have hyi : y.im = Real.sin y.arg := by
    rw [← Complex.norm_mul_sin_arg, hy, one_mul]
  have hcos : Real.cos (y.arg - x.arg) ≤ 1 / 2 := by
    have hsq : 1 ≤ ‖x - y‖ ^ 2 := by nlinarith
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      hxr, hxi, hyr, hyi] at hsq
    rw [Real.cos_sub]
    nlinarith only [hsq, Real.sin_sq_add_cos_sq x.arg, Real.sin_sq_add_cos_sq y.arg]
  have hπ := Real.pi_pos
  have hid : Real.cos (2 * Real.pi - (y.arg - x.arg)) = Real.cos (y.arg - x.arg) := by
    rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]
    ring
  constructor
  · by_contra! H
    have hlt := Real.strictAntiOn_cos
      (show y.arg - x.arg ∈ Set.Icc 0 Real.pi from ⟨by linarith, by linarith⟩)
      (show Real.pi / 3 ∈ Set.Icc 0 Real.pi from ⟨by linarith, by linarith⟩) H
    rw [Real.cos_pi_div_three] at hlt
    linarith
  · by_contra! H
    have hlt := Real.strictAntiOn_cos
      (show 2 * Real.pi - (y.arg - x.arg) ∈ Set.Icc 0 Real.pi from
        ⟨by linarith [Complex.arg_le_pi y, Complex.neg_pi_lt_arg x], by linarith⟩)
      (show Real.pi / 3 ∈ Set.Icc 0 Real.pi from ⟨by linarith, by linarith⟩)
      (show 2 * Real.pi - (y.arg - x.arg) < Real.pi / 3 by linarith)
    rw [Real.cos_pi_div_three, hid] at hlt
    linarith

private theorem angles {A : Type*} (S : Finset A) (u : A → ℂ)
    (hnorm : ∀ a ∈ S, ‖u a‖ = 1)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → 1 ≤ ‖u a - u b‖) :
    S.card ≤ 6 ∧ (S.card = 6 →
      (∀ a ∈ S, ∃ b ∈ S, u b = -u a) ∧
      ∃ a ∈ S, ∃ b ∈ S, cross (u a) (u b) ≠ 0) := by
  classical
  let s := S.image fun a => (u a).arg
  have hinj : Set.InjOn (fun a => (u a).arg) ↑S := by
    intro a ha b hb hab
    change (u a).arg = (u b).arg at hab
    by_contra H
    apply not_le_of_gt (by norm_num : (0 : ℝ) < 1) 
    have heq : u a = u b :=
      Complex.ext (by rw [← Complex.norm_mul_cos_arg, ← Complex.norm_mul_cos_arg, hnorm _ ha,
        hnorm _ hb, hab]) (by rw [← Complex.norm_mul_sin_arg, ← Complex.norm_mul_sin_arg,
        hnorm _ ha, hnorm _ hb, hab])
    simpa [heq] using hsep a ha b hb H
  have hcard : s.card = S.card := Finset.card_image_of_injOn hinj
  have gap {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y) :
      Real.pi / 3 ≤ y - x ∧ y - x ≤ 5 * Real.pi / 3 := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact chord_gap (hnorm _ ha) (hnorm _ hb)
      (hsep a ha b hb (fun h => hxy.ne (congrArg (fun z => (u z).arg) h))) hxy.le
  have hsix : s.card ≤ 6 := by
    by_contra! H
    obtain ⟨t, ht, htcard⟩ := Finset.exists_subset_card_eq (show 7 ≤ s.card by omega)
    let g := t.orderEmbOfFin htcard
    have gg (i j : Fin 7) (h : i < j) :=
      gap (ht (t.orderEmbOfFin_mem htcard i)) (ht (t.orderEmbOfFin_mem htcard j)) (g.strictMono h)
    linarith only [(gg 0 1 (by decide)).1, (gg 1 2 (by decide)).1, (gg 2 3 (by decide)).1,
      (gg 3 4 (by decide)).1, (gg 4 5 (by decide)).1, (gg 5 6 (by decide)).1,
      (gg 0 6 (by decide)).2, Real.pi_pos]
  refine ⟨hcard ▸ hsix, fun h => ?_⟩
  let hc := hcard.trans h
  let g := s.orderEmbOfFin hc
  have gm (i : Fin 6) : g i ∈ s := s.orderEmbOfFin_mem hc i
  have gg (i j : Fin 6) (h : i < j) := gap (gm i) (gm j) (g.strictMono h)
  have step (i : Fin 6) :
      g i = g 0 + (i.val : ℝ) * (Real.pi / 3) := by
    have numeral {k : ℕ} (hk : k < 6) : (⟨k, hk⟩ : Fin 6) = OfNat.ofNat (α := Fin 6) k := by
      ext
      exact (Nat.mod_eq_of_lt hk).symm
    fin_cases i <;> simp only [numeral] <;> norm_num <;>
      linarith only [(gg 0 1 (by decide)).1, (gg 1 2 (by decide)).1, (gg 2 3 (by decide)).1,
        (gg 3 4 (by decide)).1, (gg 4 5 (by decide)).1, (gg 0 5 (by decide)).2]
  have represented (i : Fin 6) : ∃ a ∈ S, (u a).arg = g i := Finset.mem_image.mp (gm i)
  refine ⟨?_, ?_⟩
  · intro a ha
    have hm : (u a).arg ∈ s := Finset.mem_image_of_mem _ ha
    obtain ⟨i, hi⟩ : ∃ i : Fin 6, g i = (u a).arg :=
      Set.mem_range.mp (by rw [Finset.range_orderEmbOfFin]; exact hm)
    let j := i + (3 : Fin 6)
    obtain ⟨b, hb, hbj⟩ := represented j
    refine ⟨b, hb, ?_⟩
    have hd : (u b).arg = (u a).arg + Real.pi ∨ (u b).arg = (u a).arg - Real.pi := by
      rw [← hi, hbj, step i, step j]
      fin_cases i <;> norm_num [j, Fin.add_def] <;> ring_nf <;> tauto
    apply Complex.ext
    · rw [Complex.neg_re]
      simp only [← Complex.norm_mul_cos_arg, hnorm _ ha, hnorm _ hb, one_mul]
      rcases hd with hd | hd <;> rw [hd]
      · exact Real.cos_add_pi _
      · exact Real.cos_sub_pi _
    · rw [Complex.neg_im]
      simp only [← Complex.norm_mul_sin_arg, hnorm _ ha, hnorm _ hb, one_mul]
      rcases hd with hd | hd <;> rw [hd]
      · exact Real.sin_add_pi _
      · exact Real.sin_sub_pi _
  · obtain ⟨a, ha, hia⟩ := represented 0
    obtain ⟨b, hb, hib⟩ := represented 1
    refine ⟨a, ha, b, hb, ?_⟩
    simp only [cross, ← Complex.norm_mul_cos_arg, ← Complex.norm_mul_sin_arg,
      hnorm _ ha, hnorm _ hb, one_mul]
    rw [mul_comm (Real.cos (u a).arg), mul_comm (Real.sin (u a).arg), ← Real.sin_sub,
      hia, hib, step (1 : Fin 6)]
    have hdelta : g 0 + ((1 : Fin 6).val : ℝ) * (Real.pi / 3) - g 0 = Real.pi / 3 := by
      norm_num
    rw [hdelta]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos]))

private theorem bound_finset (S : Finset ℝ²)
    (hsep : Metric.IsSeparated' 1 (S : Set ℝ²)) :
    (unitDistNum S : ℝ) ≤ 3 * S.card - Real.sqrt S.card / 14 := by
  classical
  let V := {v // v ∈ S}
  let G : SimpleGraph V :=
    { Adj := fun x y => dist (x : ℝ²) y = 1
      symm := ⟨fun x y h => (dist_comm _ _).trans h⟩
      loopless := ⟨fun x h => by simp at h⟩ }
  let e : ℝ² ≃ₗᵢ[ℝ] ℂ :=
    (Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)).symm
  let p : V → ℂ := fun a => e a.val
  have hp : Function.Injective p := fun _ _ h => Subtype.ext (e.injective h)
  have neigh (a : V) := angles (G.neighborFinset a) (fun b => p b - p a)
    (fun b hb => by
      have h := (G.mem_neighborFinset _ _).mp hb
      change dist a.val b.val = 1 at h
      simp [p, ← dist_eq_norm, dist_comm b.val a.val, h])
    (fun b _ c _ hbc => by
      have hd := hsep b.property c.property (fun h => hbc (Subtype.ext h))
      dsimp [p]
      rw [sub_sub_sub_cancel_right, ← dist_eq_norm, e.dist_map]
      exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp
        (by simpa only [ENNReal.ofReal_one, ← edist_dist] using hd))
  have hdeg (a : V) : G.degree a ≤ 6 := by
    have h := (neigh a).1
    rwa [SimpleGraph.card_neighborFinset_eq_degree] at h
  have hop (x y : V) (hy : G.degree y = 6) (hxy : G.Adj x y) :
      ∃ z, G.Adj y z ∧ p z - p y = p y - p x := by
    have hn := (neigh y).2 (by rwa [SimpleGraph.card_neighborFinset_eq_degree])
    obtain ⟨z, hz, ho⟩ := hn.1 x ((G.mem_neighborFinset _ _).mpr hxy.symm)
    exact ⟨z, (G.mem_neighborFinset _ _).mp hz, ho.trans (neg_sub _ _)⟩
  have hind (a : V) (ha : G.degree a = 6) :
      ∃ b c, G.Adj a b ∧ G.Adj a c ∧ cross (p b - p a) (p c - p a) ≠ 0 := by
    obtain ⟨b, hb, c, hc, h⟩ := ((neigh a).2 (by rwa [SimpleGraph.card_neighborFinset_eq_degree])).2
    exact ⟨b, c, (G.mem_neighborFinset _ _).mp hb, (G.mem_neighborFinset _ _).mp hc, h⟩
  let D := (Finset.univ.filter fun x : V => G.degree x ≠ 6).card
  have hV : Fintype.card V = S.card := Fintype.card_coe _
  have hsize := size_bound G p hp hdeg hop hind
  rw [hV] at hsize
  change S.card ≤ D + (6 * D)^2 at hsize
  have hsqrt : Real.sqrt S.card ≤ 7 * (D : ℝ) := by
    have hd : (D : ℝ) ≤ (D : ℝ)^2 := by
      by_cases hd : D = 0
      · simp [hd]
      · have hh : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
        nlinarith only [mul_le_mul_of_nonneg_right hh (show (0 : ℝ) ≤ (D : ℝ) by positivity)]
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    have h : (S.card : ℝ) ≤ (D : ℝ) + (6 * (D : ℝ))^2 := by exact_mod_cast hsize
    nlinarith only [h, hd, sq_nonneg (D : ℝ)]
  have hedge : unitDistNum S ≤ G.edgeFinset.card := by
    let eV : V ↪ ℝ² := ⟨Subtype.val, Subtype.val_injective⟩
    let eE := eV.sym2Map
    apply (Finset.card_le_card (t := G.edgeFinset.map eE) ?_).trans (Finset.card_map eE).le
    intro k hk
    obtain ⟨hm, hd⟩ := Finset.mem_filter.mp hk
    let a := k.out.1
    let b := k.out.2
    have ha : a ∈ S := (Finset.mem_sym2_iff.mp hm) a (Sym2.out_fst_mem k)
    have hb : b ∈ S := (Finset.mem_sym2_iff.mp hm) b (Sym2.out_snd_mem k)
    refine Finset.mem_map.mpr ⟨s(⟨a, ha⟩, ⟨b, hb⟩), G.mem_edgeFinset.mpr hd, ?_⟩
    change s(a, b) = k
    exact Quot.out_eq k
  have hsum : (∑ a : V, G.degree a) + D ≤ 6 * S.card := by
    dsimp [D]
    rw [Finset.card_filter, ← Finset.sum_add_distrib, ← hV]
    calc
      ∑ a : V, (G.degree a + if G.degree a ≠ 6 then 1 else 0)
          ≤ ∑ _ : V, (6 : ℕ) := by
            apply Finset.sum_le_sum
            intro a _
            have := hdeg a
            split <;> omega
      _ = 6 * Fintype.card V := by simp [mul_comm]
  rw [G.sum_degrees_eq_twice_card_edges] at hsum
  have hfin : 2 * unitDistNum S + D ≤ 6 * S.card := by omega
  have hcast : (2 : ℝ) * unitDistNum S + D ≤ 6 * S.card := by exact_mod_cast hfin
  linarith only [hcast, hsqrt]

end PackingDeficit

theorem OMA.solution : type_of% @Erdos1084.erdos_1084.variants.upper_d2 := by
  refine ⟨1 / 28, by norm_num, ?_⟩
  intro n hn
  let b := 3 * (n : ℝ) - Real.sqrt n / 14
  have hbound (s : Finset ℝ²) (hs : s.card = n)
      (hsep : Metric.IsSeparated' 1 (s : Set ℝ²)) : (unitDistNum s : ℝ) ≤ b := by
    simpa only [b, hs] using PackingDeficit.bound_finset s hsep
  have hb : 0 ≤ b := by
    have hs : Real.sqrt n ≤ (n : ℝ) := by
      refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith only [mul_le_mul_of_nonneg_right h1 (show (0 : ℝ) ≤ (n : ℝ) by positivity)]
    dsimp [b]
    linarith only [hs, show (0 : ℝ) ≤ (n : ℝ) by positivity]
  have hNat : Erdos1084.f 2 n ≤ ⌊b⌋₊ := by
    unfold Erdos1084.f
    exact ciSup_le' fun s => ciSup_le' fun hs => ciSup_le' fun hsep => Nat.le_floor (hbound s hs hsep)
  have hReal : (Erdos1084.f 2 n : ℝ) ≤ b :=
    (Nat.cast_le.mpr hNat).trans (Nat.floor_le hb)
  dsimp [b] at hReal
  have : 0 < Real.sqrt n := Real.sqrt_pos_of_pos (by exact_mod_cast hn)
  linarith only [hReal, this]