import OMAReductions.R_Green37_green_37_lower_bound_R1_H1_R1
import Mathlib.NumberTheory.Bertrand
/-! Compressing finite covers of arithmetic progressions by counting the points
in the union of intervals starting at each element. -/
open Finset Green37
namespace CoverRanks

private theorem ap_iff {A : Set ℕ} {k d : ℕ} (hd : 0 < d) :
    A.ContainsAP k d ↔ ∃ a, ∀ i < k, a + i*d ∈ A := by
  constructor
  · rintro ⟨a, s, hs, _, rfl⟩
    refine ⟨a, fun i hi => hs ?_⟩
    exact ⟨i, by exact_mod_cast hi, by simp⟩
  · rintro ⟨a, ha⟩
    let f (i : ℕ) := a+i*d
    have inj : Function.Injective f := by
      intro i j h
      exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel h)
    refine ⟨a, ((Finset.range k).image f : Set ℕ), ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact ha i (Finset.mem_range.mp hi)
    · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ inj,
          Finset.card_range]
    · ext x
      simp [f]

private lemma attained (N k : ℕ) : ∃ A : Finset ℕ,
    A.card = m N k ∧ IsAPCover (A : Set ℕ) N k := by
  apply Nat.sInf_mem (s := {z : ℕ | ∃ A : Finset ℕ, A.card = z ∧ IsAPCover (A : Set ℕ) N k})
  refine ⟨_, Finset.range (k*N+1), rfl, ?_⟩
  intro d hd
  apply (ap_iff hd.1).mpr
  refine ⟨0, fun i hi => ?_⟩
  simpa using Nat.lt_succ_of_le (Nat.mul_le_mul hi.le hd.2)

private def U (A : Finset ℕ) (N : ℕ) : Finset ℕ :=
  A.biUnion (fun a => Finset.Ico a (a+N))

private def rank (A : Finset ℕ) (N x : ℕ) : ℕ :=
  ((U A N).filter (fun i => i < x)).card

private theorem step (A : Finset ℕ) (N x d : ℕ) (hx : x ∈ A) (hd : d ≤ N) :
    rank A N (x+d) = rank A N x + d := by
  let u := U A N
  have he : u.filter (fun i => i < x+d) = u.filter (fun i => i < x) ∪ Finset.Ico x (x+d) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_Ico]
    constructor
    · rintro ⟨hu, hi⟩
      by_cases hix : i < x
      · exact Or.inl ⟨hu,hix⟩
      · exact Or.inr ⟨by omega,hi⟩
    · rintro (⟨hu,hi⟩|⟨hi,hix⟩)
      · exact ⟨hu,by omega⟩
      · refine ⟨Finset.mem_biUnion.mpr ⟨x,hx,Finset.mem_Ico.mpr ⟨hi,by omega⟩⟩,hix⟩
  have dis : Disjoint (u.filter (fun i => i<x)) (Finset.Ico x (x+d)) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    exact (Finset.mem_filter.mp hi).2.not_ge (Finset.mem_Ico.mp hi').1
  change (u.filter _).card = (u.filter _).card + d
  rw [he, Finset.card_union_of_disjoint dis, Nat.card_Ico]
  omega

private theorem compressed (N k : ℕ) (hN : 1≤N) (_hk : 1≤k) :
    ∃ B : Finset ℕ, B.card=m N k ∧ IsAPCover (B : Set ℕ) N k ∧
      ∀ x ∈ B, x ≤ m N k*N := by
  obtain ⟨A,hA,cover⟩ := attained N k
  let f := rank A N
  let B := A.image f
  have mono : Monotone f := by
    intro x y hxy
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2.trans_le hxy⟩
  have strict {x y : ℕ} (hx : x∈A) (hxy : x<y) : f x<f y := by
    have e := step A N x 1 hx hN
    have mxy := mono (show x+1≤y by omega)
    change f (x+1) = f x+1 at e
    omega
  have inj : Set.InjOn f (A : Set ℕ) := by
    intro x hx y hy h
    rcases lt_trichotomy x y with hh|hh|hh
    · exact False.elim ((strict hx hh).ne h)
    · exact hh
    · exact False.elim ((strict hy hh).ne h.symm)
  refine ⟨B, (Finset.card_image_of_injOn inj).trans hA, ?_, ?_⟩
  · intro d hd
    obtain ⟨a,ha⟩ := (ap_iff hd.1).mp (cover d hd)
    apply (ap_iff hd.1).mpr
    refine ⟨f a, ?_⟩
    have pathStep (i : ℕ) (hi : i<k) : f (a+i*d) = f a+i*d := by
      induction i with
      | zero => simp
      | succ i ih =>
        rw [Nat.succ_mul, ← Nat.add_assoc, ←Nat.add_assoc]
        exact (step A N (a+i*d) d (ha i (by omega)) hd.2).trans (by rw [← ih (by omega)])
    intro i hi
    exact Finset.mem_image.mpr ⟨_,ha i hi,pathStep i hi⟩
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    have co := Finset.card_biUnion_le_card_mul A (fun a => Finset.Ico a (a+N)) N
      (fun a _ => by simp)
    exact (Finset.card_filter_le _ _).trans (co.trans_eq (by rw [hA]))

end CoverRanks

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1_H1_R1.H2 := CoverRanks.compressed