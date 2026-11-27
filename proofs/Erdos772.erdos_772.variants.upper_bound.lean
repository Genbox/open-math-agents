import FormalConjectures.ErdosProblems.«772»

/-! A mixed-radix additive grid gives the upper bound for the largest guaranteed Sidon subset. -/

-- Credit: @Genbox

open Filter AdditiveCombinatorics

namespace SidonGrid

private def radix (a b : ℕ) : ℕ := 2 * (a + b) ^ 2 + 2 * (a + b) + 1

private def encode {a b : ℕ} (p : Fin a × Fin b) : ℕ :=
  p.1.val ^ 2 + radix a b * (p.1.val + radix a b * (p.2.val ^ 2 + radix a b * p.2.val))

private theorem split_digit {B l r s t : ℕ} (hl : l < B) (hr : r < B)
    (he : l + B * s = r + B * t) : l = r ∧ s = t := by
  have hmod := congrArg (fun x : ℕ => x % B) he
  have heq : l = r := by
    simpa only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hr] using hmod
  refine ⟨heq, Nat.mul_left_cancel (show 0 < B by omega) ?_⟩
  exact Nat.add_left_cancel (heq ▸ he)

private theorem same_pair {i j k l : ℕ} (hs : i + j = k + l)
    (hq : i ^ 2 + j ^ 2 = k ^ 2 + l ^ 2) :
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  have hprod : i * j = k * l := by nlinarith [congrArg (fun x : ℕ => x ^ 2) hs]
  have hsz : (i : ℤ) + (j : ℤ) = (k : ℤ) + (l : ℤ) := by exact_mod_cast hs
  have hpz : (i : ℤ) * (j : ℤ) = (k : ℤ) * (l : ℤ) := by exact_mod_cast hprod
  have hzero : ((i : ℤ) - k) * ((i : ℤ) - l) = 0 := calc
    _ = (i : ℤ) ^ 2 - ((k : ℤ) + l) * i + k * l := by ring
    _ = 0 := by rw [← hsz, ← hpz]; ring
  rcases mul_eq_zero.mp hzero with he | he
  · have h : i = k := by exact_mod_cast sub_eq_zero.mp he
    exact Or.inl ⟨h, by omega⟩
  · have h : i = l := by exact_mod_cast sub_eq_zero.mp he
    exact Or.inr ⟨h, by omega⟩

private theorem recover {a b : ℕ} {p q u v : Fin a × Fin b}
    (he : encode p + encode q = encode u + encode v) :
    ((p.1 = u.1 ∧ q.1 = v.1) ∨ (p.1 = v.1 ∧ q.1 = u.1)) ∧
    ((p.2 = u.2 ∧ q.2 = v.2) ∨ (p.2 = v.2 ∧ q.2 = u.2)) := by
  let B := radix a b
  have hlin {c d : ℕ} (hc : c ≤ a+b) (hd : d ≤ a+b) : c+d < B := by
    have hb : 2*(a+b) < B := by dsimp [B, radix]; omega
    omega
  have hsq {c d : ℕ} (hc : c ≤ a+b) (hd : d ≤ a+b) : c^2+d^2 < B := by
    have hc' := Nat.pow_le_pow_left hc 2
    have hd' := Nat.pow_le_pow_left hd 2
    dsimp [B, radix]
    omega
  have hb (f : Fin a) : f.val ≤ a+b := by have := f.isLt; omega
  have hc (f : Fin b) : f.val ≤ a+b := by have := f.isLt; omega
  have h' : p.1.val^2 + q.1.val^2 + B *
        (p.1.val + q.1.val + B * (p.2.val^2 + q.2.val^2 + B * (p.2.val + q.2.val))) =
      u.1.val^2 + v.1.val^2 + B *
        (u.1.val + v.1.val + B * (u.2.val^2 + v.2.val^2 + B * (u.2.val + v.2.val))) := by
    convert he using 1 <;> unfold encode <;> dsimp only [B] <;> ring
  obtain ⟨hrowSq, h'⟩ := split_digit (hsq (hb p.1) (hb q.1)) (hsq (hb u.1) (hb v.1)) h'
  obtain ⟨hrowSum, h'⟩ := split_digit (hlin (hb p.1) (hb q.1)) (hlin (hb u.1) (hb v.1)) h'
  obtain ⟨hcolSq, hcolSum⟩ := split_digit (hsq (hc p.2) (hc q.2)) (hsq (hc u.2) (hc v.2)) h'
  simp only [Fin.ext_iff]
  exact ⟨same_pair hrowSum hrowSq, same_pair hcolSum hcolSq⟩

private theorem encode_injective (a b : ℕ) :
    Function.Injective (encode : Fin a × Fin b → ℕ) := by
  intro p q he
  obtain ⟨hi, hj⟩ := recover (p := p) (q := p) (u := q) (v := q) (by rw [he])
  exact Prod.ext (hi.elim And.left And.left) (hj.elim And.left And.left)

private def grid (a b : ℕ) : Finset ℕ :=
  Finset.univ.image (encode : Fin a × Fin b → ℕ)

private theorem grid_card (a b : ℕ) : (grid a b).card = a * b := by
  unfold grid
  rw [Finset.card_image_of_injective _ (encode_injective a b)]
  simp

open scoped Classical in
private noncomputable def reprs (A : Set ℕ) (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.HasAntidiagonal.antidiagonal m).filter (fun p => p.1 ∈ A ∧ p.2 ∈ A)

private theorem sumRep_eq_reprs (A : Set ℕ) (m : ℕ) : sumRep A m = (reprs A m).card :=
  sumRep_def A m

private theorem mem_reprs {A : Set ℕ} {m : ℕ} {p : ℕ × ℕ} :
    p ∈ reprs A m ↔ p.1 + p.2 = m ∧ p.1 ∈ A ∧ p.2 ∈ A := by
  classical
  simp only [reprs, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal]

private theorem sumRep_grid_le (a b m : ℕ) : sumRep (grid a b : Set ℕ) m ≤ 4 := by
  classical
  let R := reprs (grid a b : Set ℕ) m
  have hR : sumRep (grid a b : Set ℕ) m = R.card := sumRep_eq_reprs _ _
  rw [hR]
  by_cases h : R.Nonempty
  · obtain ⟨w, hw⟩ := h
    obtain ⟨hwm, hw₁, hw₂⟩ := mem_reprs.mp hw
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hw₁
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hw₂
    let rows : Finset (Fin a) := {u.1, v.1}
    let cols : Finset (Fin b) := {u.2, v.2}
    let targets := (rows.product cols).image (encode : Fin a × Fin b → ℕ)
    have htarget : ∀ w ∈ R, w.1 ∈ targets := by
      intro z hz
      obtain ⟨hzm, hz₁, hz₂⟩ := mem_reprs.mp hz
      obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hz₁
      obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hz₂
      obtain ⟨hrows, hcols⟩ := recover (p := p) (q := q) (u := u) (v := v)
        (by rw [hp, hq, hu, hv, hwm, hzm])
      exact Finset.mem_image.mpr ⟨p, Finset.mem_product.mpr
        ⟨by simpa [rows] using hrows.imp And.left And.left,
          by simpa [cols] using hcols.imp And.left And.left⟩, hp⟩
    have hinj : Set.InjOn Prod.fst (↑R : Set (ℕ × ℕ)) := by
      intro x hx y hy he
      have hx' := (mem_reprs.mp (Finset.mem_coe.mp hx)).1
      have hy' := (mem_reprs.mp (Finset.mem_coe.mp hy)).1
      exact Prod.ext he (by omega)
    have hr : rows.card ≤ 2 := by
      simpa only [rows, Finset.card_singleton] using Finset.card_insert_le u.1 ({v.1} : Finset (Fin a))
    have hc : cols.card ≤ 2 := by
      simpa only [cols, Finset.card_singleton] using Finset.card_insert_le u.2 ({v.2} : Finset (Fin b))
    calc
      R.card ≤ targets.card := Finset.card_le_card_of_injOn Prod.fst
        (fun w hw => htarget w (Finset.mem_coe.mp hw)) hinj
      _ ≤ (rows.product cols).card := Finset.card_image_le
      _ = rows.card * cols.card := by rw [Finset.product_eq_sprod, Finset.card_product]
      _ ≤ 4 := Nat.mul_le_mul hr hc
  · rw [Finset.not_nonempty_iff_eq_empty.mp h]
    decide

private theorem grid_sidon_le {a b : ℕ} (ha : 0 < a) {S : Finset ℕ}
    (hS : S ⊆ grid a b) (hsid : IsSidon (S : Set ℕ)) : S.card ≤ b + a^2 := by
  classical
  let T : Finset (Fin a × Fin b) := Finset.univ.filter (fun p => encode p ∈ S)
  have hT (p : Fin a × Fin b) : p ∈ T ↔ encode p ∈ S := by simp [T]
  have hST : T.image encode = S := by
    ext m
    constructor
    · intro hm
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
      exact (hT p).mp hp
    · intro hm
      obtain ⟨p, _, he⟩ := Finset.mem_image.mp (hS hm)
      exact Finset.mem_image.mpr ⟨p, (hT p).mpr (he.symm ▸ hm), he⟩
  let pick (j : Fin b) : Fin a :=
    if h : ∃ i : Fin a, (i, j) ∈ T then h.choose else ⟨0, ha⟩
  have hpick {p : Fin a × Fin b} (hp : p ∈ T) : (pick p.2, p.2) ∈ T := by
    obtain ⟨i, j⟩ := p
    have h : ∃ i : Fin a, (i, j) ∈ T := ⟨i, hp⟩
    simpa [pick, dif_pos h] using h.choose_spec
  let f (p : Fin a × Fin b) : Fin b ⊕ (Fin a × Fin a) :=
    if p.1 = pick p.2 then .inl p.2 else .inr (pick p.2, p.1)
  have hf : Set.InjOn f (↑T : Set (Fin a × Fin b)) := by
    intro p hp q hq he
    change p ∈ T at hp
    change q ∈ T at hq
    by_cases hpr : p.1 = pick p.2 <;> by_cases hqr : q.1 = pick q.2
    · have hcol : p.2 = q.2 := Sum.inl.inj (by simpa only [f, if_pos hpr, if_pos hqr] using he)
      exact Prod.ext (hpr.trans (congrArg pick hcol |>.trans hqr.symm)) hcol
    · simp [f, hpr, hqr] at he
    · simp [f, hpr, hqr] at he
    · have hrows := Sum.inr.inj (by simpa only [f, if_neg hpr, if_neg hqr] using he)
      have hr : pick p.2 = pick q.2 := congrArg Prod.fst hrows
      have hrow : p.1 = q.1 := congrArg Prod.snd hrows
      let p' : Fin a × Fin b := (pick p.2, p.2)
      let q' : Fin a × Fin b := (pick q.2, q.2)
      have hrect : encode p + encode q' = encode q + encode p' := by
        unfold encode
        dsimp [p', q']
        rw [hr, hrow]
        ring
      have hsid' := hsid (encode p) ((hT p).mp hp) (encode q) ((hT q).mp hq)
        (encode q') ((hT q').mp (hpick hq)) (encode p') ((hT p').mp (hpick hp)) hrect
      have hinj := encode_injective a b
      rcases hsid' with h | h
      · exact hinj h.1
      · exact False.elim (hpr (congrArg Prod.fst (hinj h.1)))
  rw [← hST, Finset.card_image_of_injective _ (encode_injective a b)]
  have hcard := Finset.card_le_card_of_injOn (t := (Finset.univ : Finset (Fin b ⊕ (Fin a × Fin a))))
    f (fun _ _ => Finset.mem_univ _) hf
  simpa [pow_two] using hcard

private theorem initial_segment_bound {k n a : ℕ} (ha : 0 < a) (hsize : n ≤ a^3) (hk : 4 ≤ k) :
    Erdos772.H k n ≤ 2*a^2 := by
  classical
  let A := grid a (a^2)
  have hn : n ≤ A.card := by
    simpa only [A, grid_card, pow_succ, Nat.mul_comm] using hsize
  obtain ⟨A', hA', hA'card⟩ := Finset.exists_subset_card_eq hn
  have hRep (m : ℕ) : sumRep (A' : Set ℕ) m ≤ k := by
    have hmon : sumRep (A' : Set ℕ) m ≤ sumRep (A : Set ℕ) m := by
      rw [sumRep_eq_reprs, sumRep_eq_reprs]
      apply Finset.card_le_card
      intro p hp
      obtain ⟨hm, h₁, h₂⟩ := mem_reprs.mp hp
      exact mem_reprs.mpr ⟨hm, hA' h₁, hA' h₂⟩
    exact hmon.trans ((sumRep_grid_le a (a^2) m).trans hk)
  let bounds : Set ℕ := {r | r ≤ n ∧ ∀ X : Finset ℕ, X.card = n → (∀ m, sumRep X m ≤ k) →
    ∃ S ⊆ X, IsSidon (S : Set ℕ) ∧ r ≤ S.card}
  change sSup bounds ≤ _
  by_cases hne : bounds.Nonempty
  · apply csSup_le hne
    rintro r ⟨_, hr⟩
    obtain ⟨S, hS, hsid, hle⟩ := hr A' hA'card hRep
    have hcard := grid_sidon_le ha (hS.trans hA') hsid
    exact hle.trans (by simpa [two_mul] using hcard)
  · simp [Set.not_nonempty_iff_eq_empty.mp hne]

end SidonGrid

theorem OMA.solution : type_of% @Erdos772.erdos_772.variants.upper_bound := by
  refine ⟨8, ?_⟩
  intro k hk
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  let x : ℝ := (n : ℝ) ^ (1 / 3 : ℝ)
  let a : ℕ := ⌈x⌉₊
  have hnx : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hx₁ : 1 ≤ x := Real.one_le_rpow hnx (by norm_num)
  have hx₀ : 0 ≤ x := by linarith
  have ha₁ : x ≤ (a : ℝ) := Nat.le_ceil x
  have ha : 0 < a := Nat.ceil_pos.mpr (by linarith)
  have ha₂ : (a : ℝ) ≤ 2 * x := (Nat.ceil_lt_add_one hx₀).le.trans (by linarith)
  have hcube : x ^ 3 = (n : ℝ) := by
    dsimp [x]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n), show (1 / 3 : ℝ) * (3 : ℕ) = 1 by norm_num,
      Real.rpow_one]
  have hsize : n ≤ a^3 := by
    have h : x ^ 3 ≤ (a : ℝ)^3 := by gcongr
    rw [hcube] at h
    exact_mod_cast h
  have hsquare : x ^ 2 = (n : ℝ) ^ (2 / 3 : ℝ) := by
    dsimp [x]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n), show (1 / 3 : ℝ) * (2 : ℕ) = 2 / 3 by norm_num]
  calc
    (Erdos772.H k n : ℝ) ≤ 2 * (a : ℝ)^2 := by exact_mod_cast SidonGrid.initial_segment_bound ha hsize hk
    _ ≤ 2 * (2*x)^2 := by gcongr
    _ = 8 * (n : ℝ) ^ (2 / 3 : ℝ) := by rw [← hsquare]; ring