import FormalConjectures.ErdosProblems.«596»
import Mathlib.NumberTheory.Bertrand
import Mathlib.Algebra.Field.ZMod

/-! An affine incidence graph and a length-three path count. -/

open Finset SimpleGraph

namespace OMA.Erdos596Finite

private noncomputable def degree {A B : Type*} (R : A → B → Prop)
    (T : Finset B) (a : A) : ℕ := by
  classical
  exact (T.filter (R a)).card

private noncomputable def count {A B : Type*} (R : A → B → Prop)
    (S : Finset A) (T : Finset B) : ℕ :=
  ∑ a ∈ S, degree R T a

private theorem count_swap {A B : Type*} (R : A → B → Prop)
    (S : Finset A) (T : Finset B) :
    count R S T = count (fun b a => R a b) T S := by
  classical
  simp only [count, degree, card_filter]
  exact sum_comm

private theorem dense_core {A B : Type*} (R : A → B → Prop) (d : ℕ)
    (S : Finset A) (T : Finset B) (h : d * (S.card + T.card) < count R S T) :
    ∃ U : Finset A, ∃ V : Finset B, U.Nonempty ∧
      (∀ a ∈ U, d < degree R V a) ∧
      (∀ b ∈ V, d < degree (fun b a => R a b) U b) := by
  classical
  let P (k : ℕ) := ∃ U : Finset A, ∃ V : Finset B,
    U.card + V.card = k ∧ d * k < count R U V
  have hex : ∃ k, P k := ⟨S.card + T.card, S, T, rfl, h⟩
  obtain ⟨U, V, hk, hd⟩ := Nat.find_spec hex
  have hmin (X : Finset A) (Y : Finset B) (hxy : X.card + Y.card < Nat.find hex) :
      count R X Y ≤ d * (X.card + Y.card) := by
    by_contra! hc
    exact Nat.find_min hex hxy ⟨X, Y, rfl, hc⟩
  refine ⟨U, V, ?_, ?_, ?_⟩
  · by_contra hu
    have hU : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hu
    simp [hU, count] at hd
  · intro a ha
    have hn := Finset.card_erase_add_one ha
    have hb := hmin (U.erase a) V (by omega)
    have he : count R (U.erase a) V + degree R V a = count R U V :=
      Finset.sum_erase_add _ _ ha
    rw [← hk, ← he] at hd
    rw [← hn] at hd
    rw [show (U.erase a).card + 1 + V.card = ((U.erase a).card + V.card) + 1 by omega,
      Nat.mul_add, Nat.mul_one] at hd
    omega
  · intro b hb
    have hn := Finset.card_erase_add_one hb
    have hh := hmin U (V.erase b) (by omega)
    rw [count_swap] at hh hd
    have he : count (fun b a => R a b) (V.erase b) U +
        degree (fun b a => R a b) U b = count (fun b a => R a b) V U :=
      Finset.sum_erase_add _ _ hb
    rw [← hk, ← he, ← hn, ← Nat.add_assoc, Nat.mul_add, Nat.mul_one] at hd
    omega

private theorem embed_neighbors {A B : Type*} (R : A → B → Prop) (T : Finset B)
    (a : A) (d : ℕ) (h : d ≤ degree R T a) :
    ∃ f : Fin d ↪ B, ∀ i, f i ∈ T ∧ R a (f i) := by
  classical
  let N := T.filter (R a)
  have hN : Fintype.card (Fin d) ≤ Fintype.card (↥N) := by
    simpa [N, degree] using h
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hN
  exact ⟨f.trans (Function.Embedding.subtype _), fun i => Finset.mem_filter.mp (f i).2⟩

private theorem erase_degree {A B : Type*} [DecidableEq B] (R : A → B → Prop) (T : Finset B)
    (a : A) (b : B) (d : ℕ) (h : d < degree R T a) :
    d ≤ degree R (T.erase b) a := by
  classical
  have he : (T.erase b).filter (R a) = (T.filter (R a)).erase b := by ext x; simp [and_comm, and_left_comm]
  simp only [degree, he]
  have := Finset.pred_card_le_card_erase (s := T.filter (R a)) (a := b)
  simp only [degree] at h
  omega

private theorem sextuple {A B : Type*} [Fintype B] (R : A → B → Prop) (d : ℕ)
    (U : Finset A) (V : Finset B) (hU : U.Nonempty)
    (hleft : ∀ a ∈ U, d < degree R V a)
    (hright : ∀ b ∈ V, d < degree (fun b a => R a b) U b)
    (hcard : Fintype.card B < d ^ 3)
    (hnorect : ∀ a a' b b', R a b → R a' b → R a b' → R a' b' →
      a = a' ∨ b = b') :
    ∃ a a' a'' b b' b'', a ≠ a' ∧ a ≠ a'' ∧ a' ≠ a'' ∧
      b ≠ b' ∧ b ≠ b'' ∧ b' ≠ b'' ∧
      R a b ∧ R a' b ∧ R a' b' ∧ R a'' b' ∧ R a'' b'' ∧ R a b'' := by
  classical
  obtain ⟨a, ha⟩ := hU
  obtain ⟨f, hf⟩ := embed_neighbors R V a d (hleft a ha).le
  have hsecond (i : Fin d) := embed_neighbors (fun b a => R a b) (U.erase a) (f i) d
    (erase_degree (fun b a => R a b) U (f i) a d (hright _ (hf i).1))
  choose g hg using hsecond
  have hthird (i j : Fin d) := embed_neighbors R (V.erase (f i)) (g i j) d
    (erase_degree R V (g i j) (f i) d (hleft _ (mem_erase.mp (hg i j).1).2))
  choose t ht using hthird
  let endpoint : Fin d × Fin d × Fin d → B := fun w => t w.1 w.2.1 w.2.2
  have hnot : ¬ Function.Injective endpoint := by
    intro hinj
    have hc := Fintype.card_le_of_injective endpoint hinj
    simp only [Fintype.card_prod, Fintype.card_fin] at hc
    exact (not_le_of_gt hcard) (by simpa [pow_succ, Nat.mul_assoc] using hc)
  obtain ⟨⟨i, j, k⟩, ⟨i', j', k'⟩, heq, hw⟩ := Function.not_injective_iff.mp hnot
  change t i j k = t i' j' k' at heq
  have hba := (hf i).2
  have hba' := (hf i').2
  have hbg := (hg i j).2
  have hbg' := (hg i' j').2
  have htg := (ht i j k).2
  have htg' := (ht i' j' k').2
  rw [← heq] at htg'
  have hag := (mem_erase.mp (hg i j).1).1
  have hag' := (mem_erase.mp (hg i' j').1).1
  have htb := (mem_erase.mp (ht i j k).1).1
  have htb' : t i j k ≠ f i' := heq.symm ▸ (mem_erase.mp (ht i' j' k').1).1
  have hi : i ≠ i' := by
    intro hi
    subst i'
    have hgg := (hnorect _ _ _ _ hbg hbg' htg htg').resolve_right htb.symm
    have hj := (g i).injective hgg
    subst j'
    have hk := (t i j).injective heq
    subst k'
    exact hw rfl
  have hbb : f i ≠ f i' := fun h => hi (f.injective h)
  have hgg : g i j ≠ g i' j' := by
    intro h
    rw [← h] at hbg'
    exact hag ((hnorect _ _ _ _ hbg hba hbg' hba').resolve_right hbb)
  exact ⟨a, g i j, g i' j', f i, t i j k, f i',
    hag.symm, hag'.symm, hgg, htb.symm, hbb, htb', hba, hbg, htg, htg', hbg', hba'⟩

private def bipartite {A B : Type*} (R : A → B → Prop) : SimpleGraph (A ⊕ B) where
  Adj
    | .inl a, .inr b => R a b
    | .inr b, .inl a => R a b
    | _, _ => False
  symm := by constructor; intro x y h; cases x <;> cases y <;> exact h
  loopless := by constructor; intro x; cases x <;> exact id

private theorem free_four {A B : Type*} (R : A → B → Prop)
    (hrect : ∀ a a' b b', R a b → R a' b → R a b' → R a' b' →
      a = a' ∨ b = b') :
    (cycleGraph 4).Free (bipartite R) := by
  rintro ⟨f⟩
  have h01 : (bipartite R).Adj (f 0) (f 1) :=
    f.toHom.map_adj (show (cycleGraph 4).Adj 0 1 by decide)
  have h12 : (bipartite R).Adj (f 1) (f 2) :=
    f.toHom.map_adj (show (cycleGraph 4).Adj 1 2 by decide)
  have h23 : (bipartite R).Adj (f 2) (f 3) :=
    f.toHom.map_adj (show (cycleGraph 4).Adj 2 3 by decide)
  have h30 : (bipartite R).Adj (f 3) (f 0) :=
    f.toHom.map_adj (show (cycleGraph 4).Adj 3 0 by decide)
  have h02 : f 0 ≠ f 2 := f.injective.ne (by decide)
  have h13 : f 1 ≠ f 3 := f.injective.ne (by decide)
  cases e0 : f 0 <;> cases e1 : f 1 <;> rw [e0, e1] at h01 <;>
    simp only [bipartite] at h01
  all_goals
    cases e2 : f 2 <;> rw [e1, e2] at h12 <;> simp only [bipartite] at h12
  all_goals
    cases e3 : f 3 <;> rw [e2, e3] at h23 <;> simp only [bipartite] at h23
  all_goals
    rw [e3, e0] at h30
    simp only [bipartite] at h30
    simp only [e0, e2, e1, e3] at h02 h13
  · exact (hrect _ _ _ _ h01 h12 h30 h23).elim (fun h => h02 (congrArg Sum.inl h)) (fun h => h13 (congrArg Sum.inr h))
  · exact (hrect _ _ _ _ h01 h30 h12 h23).elim (fun h => h13 (congrArg Sum.inl h)) (fun h => h02 (congrArg Sum.inr h))

private theorem copy_six {A B : Type*} (H : SimpleGraph (A ⊕ B))
    (a a' a'' : A) (b b' b'' : B)
    (ha₁ : a ≠ a') (ha₂ : a ≠ a'') (ha₃ : a' ≠ a'')
    (hb₁ : b ≠ b') (hb₂ : b ≠ b'') (hb₃ : b' ≠ b'')
    (h₀ : H.Adj (.inl a) (.inr b)) (h₁ : H.Adj (.inl a') (.inr b))
    (h₂ : H.Adj (.inl a') (.inr b')) (h₃ : H.Adj (.inl a'') (.inr b'))
    (h₄ : H.Adj (.inl a'') (.inr b'')) (h₅ : H.Adj (.inl a) (.inr b'')) :
    cycleGraph 6 ⊑ H := by
  let f : Fin 6 → A ⊕ B := ![.inl a, .inr b, .inl a', .inr b', .inl a'', .inr b'']
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals
      first
      | exact h₀
      | exact h₀.symm
      | exact h₁
      | exact h₁.symm
      | exact h₂
      | exact h₂.symm
      | exact h₃
      | exact h₃.symm
      | exact h₄
      | exact h₄.symm
      | exact h₅
      | exact h₅.symm
      | exact False.elim ((by decide : ¬ (cycleGraph 6).Adj _ _) hij)
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals simp [f, ha₁, ha₂, ha₃, hb₁, hb₂, hb₃, Ne.symm ha₁, Ne.symm ha₂, Ne.symm ha₃,
      Ne.symm hb₁, Ne.symm hb₂, Ne.symm hb₃] at hij ⊢

private def incidence {F : Type*} [Field F] (a b : F × F) : Prop :=
  a.2 = b.1 * a.1 + b.2

private theorem incidence_rect {F : Type*} [Field F]
    (a a' b b' : F × F)
    (hab : incidence a b) (ha'b : incidence a' b)
    (hab' : incidence a b') (ha'b' : incidence a' b') :
    a = a' ∨ b = b' := by
  unfold incidence at hab ha'b hab' ha'b'
  by_cases hx : a.1 = a'.1
  · left
    exact Prod.ext hx (by rw [hab, ha'b, hx])
  · right
    have hz : (b.1 - b'.1) * (a.1 - a'.1) = 0 := by linear_combination -hab + hab' + ha'b - ha'b'
    have hs := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hx))
    exact Prod.ext hs (by rw [hs] at hab; exact add_left_cancel (hab.symm.trans hab'))

private theorem degree_incidence {F : Type*} [Field F] [Fintype F] (a : F × F) :
    degree incidence (univ : Finset (F × F)) a = Fintype.card F := by
  classical
  simp only [degree]
  refine Finset.card_bij' (fun b _ => b.1) (fun s _ => (s, a.2 - s * a.1))
    (fun _ _ => mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro s hs
    simp [incidence, add_sub_cancel]
  · intro b hb
    have h := (mem_filter.mp hb).2
    exact Prod.ext rfl (by dsimp; rw [incidence] at h; rw [h, add_sub_cancel_left])

private theorem color_cover_count {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
    (R : A → B → Prop) (Q : I → A → B → Prop)
    (hcover : ∀ a b, R a b → ∃ i, Q i a b) :
    count R univ univ ≤ ∑ i, count (Q i) univ univ := by
  classical
  simp only [count, degree, card_filter]
  conv_rhs => rw [sum_comm]
  refine sum_le_sum fun a _ => ?_
  conv_rhs => rw [sum_comm]
  refine sum_le_sum fun b _ => ?_
  split_ifs with h
  · obtain ⟨i, hi⟩ := hcover a b h
    simpa only [if_pos hi] using
      (single_le_sum (f := fun j : I => if Q j a b then (1 : ℕ) else 0)
        (fun j _ => Nat.zero_le _) (mem_univ i))
  · exact Nat.zero_le _

end OMA.Erdos596Finite

open OMA.Erdos596Finite in
theorem OMA.solution : type_of% @Erdos596.erdos_596.variants.C4_C6_finite_ramsey := by
  classical
  intro r hr
  let d := (16 * r) ^ 2
  obtain ⟨p, hp, hp₁, hp₂⟩ := Nat.exists_prime_lt_and_le_two_mul (4 * r * d) (by
    dsimp [d]
    positivity)
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  let F := ZMod p
  let A := F × F
  let H : SimpleGraph (A ⊕ A) := bipartite incidence
  have hc : Fintype.card A = p * p := by simp [A, F, ZMod.card]
  have hd : p * p < d ^ 3 := by
    have hsq := Nat.mul_le_mul hp₂ hp₂
    have hdpos : 0 < d := by dsimp [d]; positivity
    have hs : (8 * r * d) * (8 * r * d) = (8 * r) ^ 2 * d ^ 2 := by ring
    have ht : (8 * r) ^ 2 < d := by
      dsimp [d]
      nlinarith
    calc
      p * p ≤ (8 * r * d) * (8 * r * d) := by convert hsq using 1; ring
      _ = (8 * r) ^ 2 * d ^ 2 := hs
      _ < d * d ^ 2 := Nat.mul_lt_mul_of_pos_right ht (pow_pos hdpos 2)
      _ = d ^ 3 := by ring
  refine ⟨A ⊕ A, H, free_four incidence incidence_rect, ?_⟩
  intro C hC
  let Q (i : Fin r) (a b : A) := (C i).Adj (.inl a) (.inr b)
  have hcover (a b : A) (hab : incidence a b) : ∃ i, Q i a b := by
    have hh : H.Adj (.inl a) (.inr b) := hab
    rwa [hC.1, iSup_adj] at hh
  have hsub (i : Fin r) : C i ≤ H := hC.1.symm ▸ le_iSup C i
  have htotal : count (A := A) incidence univ univ = p * p * p := by
    rw [count]
    simp_rw [fun a : A => degree_incidence (F := F) a]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
    rw [show Fintype.card F = p by exact ZMod.card p]
    rfl
  have hlarge : ∃ i, d * ((univ : Finset A).card + (univ : Finset A).card) <
      count (Q i) univ univ := by
    by_contra! h
    have hall := color_cover_count incidence Q hcover
    rw [htotal] at hall
    have hsum := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin r))) => h i)
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hc] at hsum
    have hbound : r * (d * (p * p + p * p)) < p * p * p := by
      have hp0 := hp.pos
      have hh := Nat.mul_lt_mul_of_pos_right hp₁ (Nat.mul_pos hp0 hp0)
      calc
        r * (d * (p * p + p * p)) ≤ (4 * r * d) * (p * p) := by
          calc
            r * (d * (p * p + p * p)) = (2 * r * d) * (p * p) := by ring
            _ ≤ (4 * r * d) * (p * p) := by gcongr; omega
        _ < p * (p * p) := hh
        _ = p * p * p := by ring
    exact (not_le_of_gt hbound) (hall.trans hsum)
  obtain ⟨i, hi⟩ := hlarge
  obtain ⟨U, V, hU, hl, hr'⟩ := dense_core (Q i) d univ univ hi
  have hrect a a' b b' (hab : Q i a b) (ha'b : Q i a' b) (hab' : Q i a b')
      (ha'b' : Q i a' b') := incidence_rect a a' b b'
    (hsub i hab) (hsub i ha'b) (hsub i hab') (hsub i ha'b')
  obtain ⟨a, a', a'', b, b', b'', h⟩ := sextuple (Q i) d U V hU hl hr' (hc ▸ hd) hrect
  rcases h with ⟨ha₁, ha₂, ha₃, hb₁, hb₂, hb₃, h₀, h₁, h₂, h₃, h₄, h₅⟩
  exact ⟨i, copy_six (C i) a a' a'' b b' b'' ha₁ ha₂ ha₃ hb₁ hb₂ hb₃ h₀ h₁ h₂ h₃ h₄ h₅⟩