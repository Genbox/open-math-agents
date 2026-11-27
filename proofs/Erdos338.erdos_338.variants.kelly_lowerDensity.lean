import FormalConjectures.ErdosProblems.«338»
import Mathlib.Combinatorics.Additive.Corner.Roth

/-! Kelly’s positive-density bound, via Roth’s theorem. -/

open Finset Filter Erdos338

namespace KellyDensity

private def Represented (A : Set ℕ) (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧ S.card ≤ 3 ∧ ∑ x ∈ S, x = n

private theorem represented_pair {A : Set ℕ} {a b : ℕ}
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) : Represented A (a + b) := by
  refine ⟨{a, b}, ?_, ?_, ?_⟩
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  · simp [hab]
  · simp [hab]

private theorem represented_triple {A : Set ℕ} {a b c : ℕ}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Represented A (a + b + c) := by
  have ha' : a ∉ ({b, c} : Finset ℕ) := by simp [hab, hac]
  refine ⟨{a, b, c}, ?_, ?_, ?_⟩
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · rw [card_insert_of_notMem ha']
    simp [hbc]
  · rw [sum_insert ha']
    simp [hbc, add_assoc]

private theorem dense_segment (A : Set ℕ) (hd : 0 < A.lowerDensity) :
    ∃ m : ℕ, ∃ S : Finset ℕ, (∀ a ∈ S, a < m ∧ a ∈ A) ∧ 2 * rothNumberNat m < S.card := by
  classical
  have hδ : 0 < A.lowerDensity / 4 := by positivity
  have hdens : ∀ᶠ m : ℕ in atTop, A.lowerDensity / 2 < A.partialDensity Set.univ m := by
    apply eventually_lt_of_lt_liminf
    · change A.lowerDensity / 2 < A.lowerDensity
      linarith
    · exact isBoundedUnder_of_eventually_ge (Eventually.of_forall fun _ => by positivity)
  have hroth : ∀ᶠ m : ℕ in atTop, (rothNumberNat m : ℝ) ≤ A.lowerDensity / 4 * m := by
    simpa only [Real.norm_natCast] using rothNumberNat_isLittleO_id.def hδ
  obtain ⟨m, hm, hdm, hrm⟩ := ((eventually_gt_atTop (0 : ℕ)).and (hdens.and hroth)).exists
  let S := (range m).filter (· ∈ A)
  have hset : (S : Set ℕ) = A ∩ Set.Iio m := by
    ext a
    simp [S, and_comm]
  have hcard : (A ∩ Set.Iio m).ncard = S.card := by
    rw [← hset, Set.ncard_coe_finset]
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio, hcard] at hdm
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hdm' := (lt_div_iff₀ hm').mp hdm
  refine ⟨m, S, fun a ha => ?_, ?_⟩
  · simpa [S] using ha
  · exact_mod_cast (show (2 : ℝ) * (rothNumberNat m : ℝ) < (S.card : ℝ) by linarith)

private theorem collision {A : Set ℕ} {n m a : ℕ} (hm : 3 * m < n)
    (ha : a ∈ A) (ham : a < m)
    (h : ∃ S : Multiset ℕ, (∀ x ∈ S, x ∈ A) ∧ S.card ≤ 2 ∧ S.sum = n - a)
    (hn : ¬ Represented A n) :
    n - 2 * a ∈ A ∨ ∃ x ∈ A, x + x = n - a := by
  obtain ⟨S, hS, hcard, hsum⟩ := h
  have hcases : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
  rcases hcases with hz | ho | ht
  · have hzero := Multiset.card_eq_zero.mp hz
    simp [hzero] at hsum
    omega
  · obtain ⟨b, rfl⟩ := Multiset.card_eq_one.mp ho
    simp at hS hsum
    exact (hn (by
      have h : a + b = n := by omega
      rw [← h]
      exact represented_pair ha hS (by omega))).elim
  · obtain ⟨b, c, rfl⟩ := Multiset.card_eq_two.mp ht
    have hb := hS b (by simp)
    have hc := hS c (by simp)
    have hbc : b + c = n - a := by simpa using hsum
    by_cases hab : a = b
    · left
      rwa [show n - 2 * a = c by omega]
    by_cases hac : a = c
    · left
      rwa [show n - 2 * a = b by omega]
    by_cases heq : b = c
    · right
      exact ⟨b, hb, by simpa [← heq] using hbc⟩
    · exact (hn (by
        have h : a + b + c = n := by omega
        rw [← h]
        exact represented_triple ha hb hc hab hac heq)).elim

end KellyDensity

open KellyDensity in
theorem OMA.solution : type_of% @Erdos338.erdos_338.variants.kelly_lowerDensity := by
  classical
  intro A hA hd
  obtain ⟨m, S, hS, hdense⟩ := dense_segment A hd
  obtain ⟨M, hM⟩ := eventually_atTop.mp hA
  refine eventually_atTop.mpr ⟨3 * m + M + 1, fun n hn => ?_⟩
  change Represented A n
  by_contra hbad
  let P := (fun a : ℕ => n - 2 * a ∈ A)
  let X := S.filter P
  let Y := S.filter (fun a => ¬ P a)
  have hX (a : ℕ) (ha : a ∈ X) : a < m ∧ a ∈ A ∧ n - 2 * a ∈ A := by
    have hmem : a ∈ S ∧ P a := mem_filter.mp ha
    exact ⟨(hS a hmem.1).1, (hS a hmem.1).2, hmem.2⟩
  have hY (a : ℕ) (ha : a ∈ Y) : a < m ∧ a ∈ A ∧ ∃ b ∈ A, b + b = n - a := by
    have hmem : a ∈ S ∧ ¬ P a := mem_filter.mp ha
    obtain ⟨ham, haA⟩ := hS a hmem.1
    have h := collision (by omega) haA ham (hM (n - a) (by omega)) hbad
    exact ⟨ham, haA, h.resolve_left hmem.2⟩
  have hXfree : ThreeAPFree (X : Set ℕ) := by
    intro a ha b hb c hc habc
    by_contra hab
    obtain ⟨ham, haA, _⟩ := hX a ha
    obtain ⟨hbm, _, hxA⟩ := hX b hb
    obtain ⟨hcm, hcA, _⟩ := hX c hc
    have hs : a + c + (n - 2 * b) = n := by omega
    exact hbad (hs ▸ represented_triple haA hcA hxA (by omega) (by omega) (by omega))
  have hYfree : ThreeAPFree (Y : Set ℕ) := by
    intro a ha b hb c hc habc
    by_contra hab
    obtain ⟨ham, _, x, hxA, hx⟩ := hY a ha
    obtain ⟨hbm, hbA, _⟩ := hY b hb
    obtain ⟨hcm, _, y, hyA, hy⟩ := hY c hc
    have hs : b + x + y = n := by omega
    exact hbad (hs ▸ represented_triple hbA hxA hyA (by omega) (by omega) (by omega))
  have hx := hXfree.le_rothNumberNat X (fun a ha => (hX a ha).1) rfl
  have hy := hYfree.le_rothNumberNat Y (fun a ha => (hY a ha).1) rfl
  have hcard : X.card + Y.card = S.card := by
    exact card_filter_add_card_filter_not (s := S) P
  omega