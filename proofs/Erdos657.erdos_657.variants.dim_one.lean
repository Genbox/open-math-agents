import FormalConjectures.ErdosProblems.«657»
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Combinatorics.SimpleGraph.Triangle.Tripartite
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal

/-! The line case follows from the Ruzsa–Szemerédi construction on a finite difference set. -/

open Finset Filter SimpleGraph TripartiteFromTriangles
open scoped Pointwise

namespace LinearDistances

private theorem threeAPFree_of_isoscelesFree {A : Finset ℝ}
    (hA : (A : Set ℝ).IsIsoscelesFree) : ThreeAPFree (A : Set ℝ) := by
  intro a ha b hb c hc habc
  by_contra hab
  have hac : a ≠ c := by intro he; apply hab; linarith
  have hbc : b ≠ c := by intro he; apply hab; linarith
  exact (hA ha hb hc hab hbc hac) (Or.inl (by
    rw [Real.dist_eq, Real.dist_eq, show a - b = b - c by linarith]))

private def indices (A : Finset ℝ) [DecidableEq ℝ] :
    Finset (↥(A - A) × ↥A × ↥(A + A)) :=
  univ.map
    { toFun := fun ab : ↥A × ↥A =>
        (⟨ab.1.val - ab.2.val, mem_sub.mpr ⟨_, ab.1.property, _, ab.2.property, rfl⟩⟩, ab.1,
          ⟨ab.1.val + ab.2.val, mem_add.mpr ⟨_, ab.1.property, _, ab.2.property, rfl⟩⟩)
      inj' := by
        intro x y h
        have h₁ : x.1 = y.1 := congrArg (fun v => v.2.1) h
        have h₂ : (x.1.val + x.2.val) = (y.1.val + y.2.val) :=
          congrArg (fun v => v.2.2.val) h
        exact Prod.ext h₁ (Subtype.ext (by rw [h₁] at h₂; linarith)) }

private theorem mem_indices {A : Finset ℝ} [DecidableEq ℝ]
    {l : ↥(A - A)} {m : ↥A} {r : ↥(A + A)} :
    (l, m, r) ∈ indices A ↔ m.val - l.val ∈ A ∧ r.val = m.val + (m.val - l.val) := by
  constructor
  · intro ht
    rw [indices, Finset.mem_map] at ht
    obtain ⟨⟨a, b⟩, _, h⟩ := ht
    have hl : a.val - b.val = l.val := congrArg (fun x => x.1.val) h
    have hm : a = m := congrArg (fun x => x.2.1) h
    have hr : a.val + b.val = r.val := congrArg (fun x => x.2.2.val) h
    subst a
    have hsub : m.val - l.val = b.val := by linarith
    rw [hsub, hr]
    exact ⟨b.property, rfl⟩
  · rintro ⟨hb, hr⟩
    rw [indices, Finset.mem_map]
    refine ⟨(m, ⟨m.val - l.val, hb⟩), mem_univ _, ?_⟩
    refine Prod.ext ?_ (Prod.ext rfl ?_)
    · apply Subtype.ext
      change m.val - (m.val - l.val) = l.val
      ring
    · exact Subtype.ext hr.symm

private theorem card_indices (A : Finset ℝ) [DecidableEq ℝ] : (indices A).card = A.card ^ 2 := by
  simp [indices, Fintype.card_prod, pow_two]

private instance indices_disjoint (A : Finset ℝ) [DecidableEq ℝ] :
    ExplicitDisjoint (indices A) := by
  constructor
  · intro a b c a' h h'
    apply Subtype.ext
    have h₁ := (mem_indices.mp h).2
    have h₂ := (mem_indices.mp h').2
    linarith
  · intro a b c b' h h'
    apply Subtype.ext
    have h₁ := (mem_indices.mp h).2
    have h₂ := (mem_indices.mp h').2
    linarith
  · intro a b c c' h h'
    apply Subtype.ext
    exact (mem_indices.mp h).2.trans (mem_indices.mp h').2.symm

private theorem no_accidental (A : Finset ℝ) [DecidableEq ℝ]
    (hA : ThreeAPFree (A : Set ℝ)) : NoAccidental (indices A) := by
  constructor
  intro a a' b b' c c' ha hb hc
  obtain ⟨h₁, ha'⟩ := mem_indices.mp ha
  obtain ⟨h₂, hb'⟩ := mem_indices.mp hb
  obtain ⟨h₃, _⟩ := mem_indices.mp hc
  have heq := hA h₁ h₂ h₃ (by linarith)
  left
  apply Subtype.ext
  linarith

private theorem difference_bound (A : Finset ℝ) :
    (A - A).card ≤ 2 * distinctDistances A + 1 := by
  classical
  let D := distanceSet A
  have hs : A - A ⊆ insert 0 (D ∪ -D) := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sub.mp hx
    by_cases h : a = b
    · simp [h]
    have hd : dist a b ∈ D :=
      mem_image.mpr ⟨(a, b), mem_offDiag.mpr ⟨ha, hb, h⟩, rfl⟩
    rcases le_total 0 (a - b) with hpos | hneg
    · apply mem_insert_of_mem
      exact mem_union_left _ (by simpa [Real.dist_eq, abs_of_nonneg hpos] using hd)
    · apply mem_insert_of_mem
      apply mem_union_right
      simpa [Real.dist_eq, abs_of_nonpos hneg] using hd
  calc
    _ ≤ (insert 0 (D ∪ -D)).card := card_le_card hs
    _ ≤ (D ∪ -D).card + 1 := card_insert_le _ _
    _ ≤ 2 * distinctDistances A + 1 := by
      have h := card_union_le D (-D)
      rw [card_neg] at h
      dsimp [distinctDistances]
      change (D ∪ -D).card + 1 ≤ 2 * D.card + 1
      omega

private theorem sum_bound (A : Finset ℝ) (hA : A.Nonempty) :
    ((A + A).card : ℝ) ≤ (((A - A).card : ℝ) / A.card) ^ 2 * A.card := by
  have h := pluennecke_ruzsa_inequality_nsmul_sub hA A 2
  have h' : ((2 • A : Finset ℝ).card : ℝ) ≤
      (((A - A).card : ℝ) / A.card) ^ 2 * A.card := by
    have hR := NNRat.cast_le (K := ℝ).mpr h
    simpa only [NNRat.cast_natCast, NNRat.cast_div, NNRat.cast_pow, NNRat.cast_mul] using hR
  simpa [two_nsmul] using h'

private theorem bounded_size (C : ℝ) (hC : 0 ≤ C) :
    ∃ B : ℕ, ∀ A : Finset ℝ, B ≤ A.card → (A : Set ℝ).IsIsoscelesFree →
      C * A.card ≤ distinctDistances A := by
  classical
  let K := 2 * C + 1
  let M := K ^ 2 + K + 1
  let ε := 1 / M ^ 2
  have hK : 0 < K := by dsimp [K]; linarith
  have hM : 0 < M := by dsimp [M]; positivity
  have he : 0 < ε := by dsimp [ε]; positivity
  let δ := triangleRemovalBound ε
  have hd : 0 < δ := triangleRemovalBound_pos he
  obtain ⟨B, hB⟩ := exists_nat_gt (max 0 (1 / δ))
  refine ⟨B, fun A hcard hfree => ?_⟩
  by_contra! hsmall
  have hN : (0 : ℝ) < A.card := by
    exact (lt_of_le_of_lt (le_max_left 0 (1 / δ)) hB).trans_le (by exact_mod_cast hcard)
  have hN1 : (1 : ℝ) ≤ A.card := by
    exact_mod_cast Nat.succ_le_of_lt (show 0 < A.card by exact_mod_cast hN)
  have hDiff : ((A - A).card : ℝ) ≤ K * A.card := by
    have hb : ((A - A).card : ℝ) ≤ 2 * (distinctDistances A : ℝ) + 1 := by
      exact_mod_cast difference_bound A
    dsimp [K]
    nlinarith
  have hSum : ((A + A).card : ℝ) ≤ K ^ 2 * A.card := by
    refine (sum_bound A (card_pos.mp (by exact_mod_cast hN))).trans ?_
    gcongr
    exact (div_le_iff₀ hN).mpr hDiff
  let t := indices A
  let : NoAccidental t := no_accidental A (threeAPFree_of_isoscelesFree hfree)
  let v := (A - A).card + A.card + (A + A).card
  have hvupper : (v : ℝ) ≤ M * A.card := by
    dsimp [v, M]
    push_cast
    nlinarith
  have hvlower : (A.card : ℝ) ≤ v := by
    exact_mod_cast (show A.card ≤ v by dsimp [v]; omega)
  have hcount : ε * ((v ^ 2 : ℕ) : ℝ) ≤ t.card := by
    rw [show t.card = A.card ^ 2 from card_indices A]
    push_cast
    calc
      ε * (v : ℝ) ^ 2 ≤ ε * (M * A.card) ^ 2 := by gcongr
      _ = (A.card : ℝ) ^ 2 := by
        dsimp [ε]
        field_simp
  have hfar : (graph t).FarFromTriangleFree ε := by
    apply farFromTriangleFree t
    simpa [v] using hcount
  have htri := hfar.le_card_cliqueFinset
  rw [card_triangles, show t.card = A.card ^ 2 from card_indices A] at htri
  have htri' : δ * (v : ℝ) ^ 3 ≤ (A.card : ℝ) ^ 2 := by
    simpa [δ, v, Fintype.card_sum, Nat.cast_add, add_assoc] using htri
  have htri'' : ((A.card : ℝ) * δ) * (A.card : ℝ) ^ 2 ≤ (A.card : ℝ) ^ 2 := calc
    _ = δ * (A.card : ℝ) ^ 3 := by ring
    _ ≤ δ * (v : ℝ) ^ 3 := by gcongr
    _ ≤ _ := htri'
  have hcancel : (A.card : ℝ) * δ ≤ 1 := by
    refine le_of_mul_le_mul_right ?_ (pow_pos hN 2)
    rwa [one_mul]
  have hbound : (A.card : ℝ) ≤ 1 / δ := (le_div_iff₀ hd).mpr hcancel
  exact (not_lt_of_ge hbound) <| (lt_of_le_of_lt (le_max_right 0 (1 / δ)) hB).trans_le
    (by exact_mod_cast hcard)

end LinearDistances

open LinearDistances in
theorem OMA.solution : type_of% @Erdos657.erdos_657.variants.dim_one := by
  classical
  let S (n : ℕ) : Set ℕ :=
    {d | ∃ A : Finset ℝ, A.card = n ∧ (A : Set ℝ).IsIsoscelesFree ∧ distinctDistances A = d}
  let f (n : ℕ) : ℝ := if (S n).Nonempty then ((sInf (S n) : ℕ) : ℝ) / n else n
  refine ⟨f, ?_, ?_⟩
  · apply tendsto_atTop.2
    intro C
    obtain ⟨B, hB⟩ := bounded_size (max C 0) (le_max_right _ _)
    obtain ⟨B', hB'⟩ := exists_nat_gt (max C 0)
    filter_upwards [eventually_ge_atTop (max B B')] with n hn
    have hnB : B ≤ n := (le_max_left _ _).trans hn
    have hnB' : B' ≤ n := (le_max_right _ _).trans hn
    have hCn : max C 0 < (n : ℝ) := hB'.trans_le (by exact_mod_cast hnB')
    have hnpos : (0 : ℝ) < n := (le_max_right C 0).trans_lt hCn
    by_cases h : (S n).Nonempty
    · obtain ⟨A, hcard, hA, hdist⟩ := Nat.sInf_mem h
      simp only [f, if_pos h]
      rw [← hdist, le_div_iff₀ hnpos, ← hcard]
      exact (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans
        (hB A (by rw [hcard]; exact hnB) hA)
    · simp only [f, if_neg h]
      exact (le_max_left C 0).trans hCn.le
  · intro n A hn hA
    have hmem : distinctDistances A ∈ S n := ⟨A, hn, hA, rfl⟩
    simp only [f, if_pos (show (S n).Nonempty from ⟨_, hmem⟩)]
    by_cases hn0 : n = 0
    · simp [hn0]
    · rw [div_mul_cancel₀ _ (by exact_mod_cast hn0 : (n : ℝ) ≠ 0)]
      exact_mod_cast Nat.sInf_le hmem