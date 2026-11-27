import FormalConjectures.GreensOpenProblems.«14»
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Logic.Function.DependsOn
import Mathlib.Combinatorics.HalesJewett
import Mathlib.Tactic

/-!
We color each position independently, with red probability proportional to log(r)/r.
Let Z(S) be the probability that S contains no monochromatic forbidden progression.
When inserting a point, charge every new bad progression to its support. Removing that
support restores independence, which gives a lower bound on Z(S) by induction.
There are at most k(n+1) progressions of length k through any specified point.
-/

section
open Set

namespace WaerdenBridge

private theorem ap_set_eq {n k : ℕ} {s : Finset (Icc 1 n)} {a d : ℕ}
    (h : ({x : ℕ | ∃ y ∈ s, (y : ℕ) = x}).IsAPOfLengthWith k a d) :
    {x : ℕ | ∃ y ∈ s, (y : ℕ) = x} = {x : ℕ | ∃ j < k, a + j * d = x} := by
  ext x
  rw [h.eq]
  simp

private theorem ap_step_pos {n k : ℕ} (hk : 2 ≤ k) {s : Finset (Icc 1 n)} {a d : ℕ}
    (h : ({x : ℕ | ∃ y ∈ s, (y : ℕ) = x}).IsAPOfLengthWith k a d) : 0 < d := by
  by_contra! hd
  obtain rfl : d = 0 := Nat.eq_zero_of_le_zero hd
  have hset : {x : ℕ | ∃ y ∈ s, (y : ℕ) = x} = {a} := by
    rw [ap_set_eq h]
    ext x
    simp only [Nat.mul_zero, Nat.add_zero, mem_ofPred_eq, mem_singleton_iff]
    exact ⟨fun ⟨_, _, he⟩ => he.symm, fun he => ⟨0, by omega, he.symm⟩⟩
  have hc := h.card
  rw [hset] at hc
  have hkc : (1 : ℕ∞) = k := by simpa using hc
  have : (1 : ℕ) = k := ENat.natCast_inj.mp hkc
  omega

private theorem monoAP_iff_indices {n k : ℕ} (hk : 2 ≤ k)
    (coloring : Icc 1 n → Fin 2) (v : ℕ → Bool) (c : Fin 2) (b : Bool)
    (encode : ∀ x : Icc 1 n, coloring x = c ↔ v (x.val - 1) = b) :
    (∃ s : Finset (Icc 1 n),
      ({(x : ℕ) | x ∈ s}).IsAPOfLength k ∧ ∀ x ∈ s, coloring x = c) ↔
    ∃ a d : ℕ, 0 < d ∧ a + (k - 1) * d < n ∧ ∀ j < k, v (a + j * d) = b := by
  classical
  constructor
  · rintro ⟨s, ⟨a, d, hap⟩, hcolor⟩
    have hset := ap_set_eq hap
    have mem (j : ℕ) (hj : j < k) :
        ∃ y ∈ s, (y : ℕ) = a + j * d := by
      change a + j * d ∈ {x : ℕ | ∃ y ∈ s, (y : ℕ) = x}
      rw [hset]
      exact ⟨j, hj, rfl⟩
    obtain ⟨y, _, hy⟩ := mem 0 (by omega)
    have ha : 1 ≤ a := by simpa [hy] using y.property.1
    obtain ⟨z, _, hz⟩ := mem (k - 1) (by omega)
    have hlast : a + (k - 1) * d ≤ n := hz ▸ z.property.2
    refine ⟨a - 1, d, ap_step_pos hk hap, by omega, ?_⟩
    intro j hj
    obtain ⟨x, hx, he⟩ := mem j hj
    have hb := (encode x).mp (hcolor x hx)
    have hidx : x.val - 1 = a - 1 + j * d := by omega
    simpa only [hidx] using hb
  · rintro ⟨a, d, hd, hlast, hcolor⟩
    let f (j : Fin k) : Icc 1 n :=
      ⟨a + 1 + j.val * d, by
        have hle : j.val * d ≤ (k - 1) * d :=
          Nat.mul_le_mul_right d (by have := j.isLt; omega)
        exact ⟨by omega, by omega⟩⟩
    let s := Finset.univ.image f
    let g (j : Fin k) : ℕ := (f j).val
    have hg : Function.Injective g := by
      intro i j hij
      change a + 1 + i.val * d = a + 1 + j.val * d at hij
      apply Fin.ext
      exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hij)
    have hset : {x : ℕ | ∃ y ∈ s, (y : ℕ) = x} = range g := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
        exact ⟨j, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨f j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, rfl⟩
    refine ⟨s, ⟨a + 1, d, ?_, ?_⟩, ?_⟩
    · change ENat.card {x : ℕ | ∃ y ∈ s, (y : ℕ) = x} = k
      rw [hset, ← ENat.card_congr (Equiv.ofInjective g hg)]
      simp
    · change {x : ℕ | ∃ y ∈ s, (y : ℕ) = x} = _
      rw [hset]
      ext x
      simp only [mem_range, mem_ofPred_eq, ENat.natCast_lt_natCast, nsmul_eq_mul]
      exact ⟨fun ⟨j, he⟩ => ⟨j.val, j.isLt, he⟩,
        fun ⟨j, hj, he⟩ => ⟨⟨j, hj⟩, he⟩⟩
    · intro x hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      apply (encode (f j)).mpr
      have hidx : (f j).val - 1 = a + j.val * d := by
        change a + 1 + j.val * d - 1 = _
        omega
      rw [hidx]
      exact hcolor j.val j.isLt

private theorem not_mono_iff {n k : ℕ} (v : ℕ → Bool) (b : Bool) :
    (¬ ∃ a d : ℕ, 0 < d ∧ a + (k - 1) * d < n ∧ ∀ j < k, v (a + j * d) = b) ↔
    ∀ a d : ℕ, 0 < d → a + (k - 1) * d < n → ∃ j < k, v (a + j * d) = !b := by
  classical
  cases b <;> simp

private theorem fin_two_eq_one_iff_ne_zero (c : Fin 2) : c = 1 ↔ c ≠ 0 := by
  fin_cases c <;> decide

theorem not_mem_iff {n k : ℕ} (hk : 2 ≤ k) :
    ¬ n ∈ Green14.mixedMonoAPGuaranteeSet 3 k ↔
    ∃ v : ℕ → Bool,
      (∀ a d : ℕ, 0 < d → a + 2 * d < n → ∃ j < 3, v (a + j * d) = false) ∧
      (∀ a d : ℕ, 0 < d → a + (k - 1) * d < n → ∃ j < k, v (a + j * d) = true) := by
  classical
  simp only [Green14.mixedMonoAPGuaranteeSet, mem_ofPred_eq, not_forall, not_or]
  constructor
  · rintro ⟨coloring, hred, hblue⟩
    let v (i : ℕ) : Bool :=
      if hi : i + 1 ≤ n then decide (coloring ⟨i + 1, by omega, hi⟩ = 0) else false
    have hzero (x : Icc 1 n) : coloring x = 0 ↔ v (x.val - 1) = true := by
      obtain ⟨x, hx₁, hx₂⟩ := x
      have hi : x - 1 + 1 = x := by omega
      have hle : x - 1 + 1 ≤ n := hi.symm ▸ hx₂
      simp only [v, dif_pos hle, decide_eq_true_eq]
      have he : (⟨x - 1 + 1, by omega, hle⟩ : Icc 1 n) = ⟨x, hx₁, hx₂⟩ :=
        Subtype.ext hi
      rw [he]
    have hone (x : Icc 1 n) : coloring x = 1 ↔ v (x.val - 1) = false := by
      rw [fin_two_eq_one_iff_ne_zero]
      change (¬ coloring x = 0) ↔ _
      rw [hzero x]
      cases v (x.val - 1) <;> decide
    exact ⟨v, (not_mono_iff v true).mp (fun h => hred
      ((monoAP_iff_indices (by omega) coloring v 0 true hzero).mpr h)),
      (not_mono_iff v false).mp (fun h => hblue
        ((monoAP_iff_indices hk coloring v 1 false hone).mpr h))⟩
  · rintro ⟨v, hred, hblue⟩
    let coloring (x : Icc 1 n) : Fin 2 := if v (x.val - 1) then 0 else 1
    have hzero (x : Icc 1 n) : coloring x = 0 ↔ v (x.val - 1) = true := by
      cases hx : v (x.val - 1) <;> simp [coloring, hx]
    have hone (x : Icc 1 n) : coloring x = 1 ↔ v (x.val - 1) = false := by
      cases hx : v (x.val - 1) <;> simp [coloring, hx]
    exact ⟨coloring, fun h => (not_mono_iff v true).mpr hred
      ((monoAP_iff_indices (by omega) coloring v 0 true hzero).mp h),
      fun h => (not_mono_iff v false).mpr hblue
        ((monoAP_iff_indices hk coloring v 1 false hone).mp h)⟩

theorem guarantee_mono {k r m n : ℕ} (hmn : m ≤ n)
    (hm : m ∈ Green14.mixedMonoAPGuaranteeSet k r) :
    n ∈ Green14.mixedMonoAPGuaranteeSet k r := by
  classical
  intro coloring
  let f : Icc 1 m ↪ Icc 1 n :=
    ⟨fun x => ⟨x.val, x.property.1, x.property.2.trans hmn⟩,
      fun _ _ h => Subtype.ext (congrArg (fun x : Icc 1 n => (x : ℕ)) h)⟩
  have lift (l : ℕ) (c : Fin 2) (s : Finset (Icc 1 m))
      (hap : ({(x : ℕ) | x ∈ s}).IsAPOfLength l)
      (hc : ∀ x ∈ s, coloring (f x) = c) :
      ∃ t : Finset (Icc 1 n), ({(x : ℕ) | x ∈ t}).IsAPOfLength l ∧
        ∀ x ∈ t, coloring x = c := by
    refine ⟨s.map f, ?_, ?_⟩
    · convert hap using 1
      ext x
      change (∃ y ∈ s.map f, (y : ℕ) = x) ↔ (∃ y ∈ s, (y : ℕ) = x)
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hy
        exact ⟨z, hz, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨f y, Finset.mem_map.mpr ⟨y, hy, rfl⟩, rfl⟩
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
      exact hc x hx
  rcases hm (coloring ∘ f) with ⟨s, hap, hc⟩ | ⟨s, hap, hc⟩
  · exact Or.inl (lift k 0 s hap hc)
  · exact Or.inr (lift r 1 s hap hc)

theorem W_gt_of_not_mem {k r n : ℕ} (hn : n ∉ Green14.mixedMonoAPGuaranteeSet k r)
    (hne : (Green14.mixedMonoAPGuaranteeSet k r).Nonempty) : n < Green14.W k r := by
  exact lt_of_not_ge (fun h => hn (guarantee_mono h (csInf_mem hne)))


end WaerdenBridge

end
open Finset MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped BigOperators

namespace ProgressionColoring

private def bad {V : Type} (e : Finset V) (b : Bool) : Set (V → Bool) :=
  {f | ∀ v ∈ e, f v = b}

private def good {V I : Type} (A : Finset I) (edges : I → Finset V)
    (color : I → Bool) (S : Finset V) : Set (V → Bool) :=
  {f | ∀ i ∈ A, edges i ⊆ S → f ∉ bad (edges i) (color i)}

private lemma good_dep {V I : Type} (A : Finset I) (edges : I → Finset V)
    (color : I → Bool) (S : Finset V) :
    DependsOn (good A edges color S) (S : Set V) := by
  intro f g hfg
  apply propext
  constructor <;> intro h i hi hs hb
  · exact h i hi hs (fun v hv ↦ (hfg v (hs hv)).trans (hb v hv))
  · exact h i hi hs (fun v hv ↦ (hfg v (hs hv)).symm.trans (hb v hv))

private lemma bad_dep {V : Type} (S : Finset V) (b : Bool) :
    DependsOn (bad S b) (S : Set V) := by
  intro f g hfg
  apply propext
  exact ⟨fun h i hi ↦ (hfg i hi).symm.trans (h i hi),
    fun h i hi ↦ (hfg i hi).trans (h i hi)⟩

private lemma inter_prob {V : Type} [Fintype V] (ν : Measure Bool) [IsProbabilityMeasure ν]
    {s t : Finset V} (hd : Disjoint s t) {E F : Set (V → Bool)}
    (hE : DependsOn E (s : Set V)) (hF : DependsOn F (t : Set V)) :
    (Measure.pi (fun _ : V ↦ ν)).real (E ∩ F) =
      (Measure.pi (fun _ : V ↦ ν)).real E * (Measure.pi (fun _ : V ↦ ν)).real F := by
  classical
  obtain ⟨e, he⟩ := dependsOn_iff_exists_comp.mp hE
  obtain ⟨f, hf⟩ := dependsOn_iff_exists_comp.mp hF
  have hind : iIndepFun (fun (i : V) (w : V → Bool) ↦ w i) (Measure.pi (fun _ : V ↦ ν)) :=
    iIndepFun_pi (X := fun _ : V ↦ id) (fun _ ↦ aemeasurable_id)
  have hi := hind.indepFun_finset s t hd (fun i ↦ measurable_pi_apply i)
  have hh := hi.measure_inter_preimage_eq_mul {x | e x} {y | f y}
    (Set.to_countable _).measurableSet (Set.to_countable _).measurableSet
  have h₁ : (fun (w : V → Bool) (i : s) ↦ w i) ⁻¹' {x | e x} = E := by
    ext w
    exact (congrFun he w).symm.to_iff
  have h₂ : (fun (w : V → Bool) (i : t) ↦ w i) ⁻¹' {x | f x} = F := by
    ext w
    exact (congrFun hf w).symm.to_iff
  rw [h₁, h₂] at hh
  exact (congrArg ENNReal.toReal hh).trans ENNReal.toReal_mul

private lemma bad_prob {V : Type} [Fintype V] (ν : Measure Bool) [IsProbabilityMeasure ν]
    (e : Finset V) (b : Bool) :
    (Measure.pi (fun _ : V ↦ ν)).real (bad e b) = (ν.real {b}) ^ e.card := by
  classical
  have he : bad e b = (e : Set V).pi (fun _ ↦ ({b} : Set Bool)) := by ext w; rfl
  simp [Measure.real, he, Measure.pi_pi_finset, ENNReal.toReal_pow]

private lemma prob_step {V I : Type} [Fintype V] [DecidableEq V] [DecidableEq I]
    (ν : Measure Bool) [IsProbabilityMeasure ν] (A : Finset I)
    (edges : I → Finset V) (color : I → Bool) (S : Finset V) (v : V) :
    let μ := Measure.pi (fun _ : V ↦ ν)
    let Z := fun T ↦ μ.real (good A edges color T)
    Z (S.erase v) ≤ Z S +
      ∑ i ∈ A.filter (fun i ↦ v ∈ edges i ∧ edges i ⊆ S),
        (ν.real {color i})^(edges i).card * Z (S \ edges i) := by
  classical
  dsimp only
  let I₀ := A.filter (fun i ↦ v ∈ edges i ∧ edges i ⊆ S)
  let hit := fun i ↦ bad (edges i) (color i) ∩ good A edges color (S \ edges i)
  have hs : good A edges color (S.erase v) ⊆ good A edges color S ∪ ⋃ i ∈ I₀, hit i := by
    intro w hw
    by_cases hw' : w ∈ good A edges color S
    · exact Or.inl hw'
    · right
      change ¬ ∀ i ∈ A, edges i ⊆ S → w ∉ bad (edges i) (color i) at hw'
      push Not at hw'
      obtain ⟨i, hi, he, hb⟩ := hw'
      have hv : v ∈ edges i := by
        by_contra hn
        exact hw i hi (fun x hx ↦ mem_erase.mpr ⟨fun hxv ↦ hn (hxv ▸ hx), he hx⟩) hb
      refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨mem_filter.mpr ⟨hi,hv,he⟩, hb, ?_⟩⟩
      intro j hj hjs
      exact hw j hj (fun x hx ↦ mem_erase.mpr
        ⟨fun h ↦ (mem_sdiff.mp (hjs hx)).2 (h ▸ hv), (mem_sdiff.mp (hjs hx)).1⟩)
  let μ := Measure.pi (fun _ : V ↦ ν)
  calc
    _ ≤ μ.real (good A edges color S ∪ ⋃ i ∈ I₀, hit i) := measureReal_mono hs
    _ ≤ μ.real (good A edges color S) + μ.real (⋃ i ∈ I₀, hit i) := measureReal_union_le _ _
    _ ≤ _ + ∑ i ∈ I₀, μ.real (hit i) :=
      add_le_add_right (measureReal_biUnion_finset_le _ _) _
    _ = _ := by
      congr 1
      apply sum_congr rfl
      intro i hi
      rw [show μ.real (hit i) = μ.real (bad (edges i) (color i)) *
        μ.real (good A edges color (S \ edges i)) from
          inter_prob ν (by exact disjoint_sdiff_self_right)
            (bad_dep ..) (good_dep ..), bad_prob]

private lemma avoid {V I : Type} [Fintype V] [DecidableEq I] [DecidableEq V]
    (ν : Measure Bool) [IsProbabilityMeasure ν] (A : Finset I)
    (edges : I → Finset V) (color : I → Bool) (ne : ∀ i ∈ A, (edges i).Nonempty)
    (q : ℝ) (hq : 0 < q)
    (cost : ∀ v : V, ∑ i ∈ A.filter (fun i ↦ v ∈ edges i),
      (ν.real {color i})^(edges i).card / q^((edges i).card-1) ≤ 1-q) :
    (good A edges color Finset.univ).Nonempty := by
  classical
  let μ := Measure.pi (fun _ : V ↦ ν)
  let Z := fun S ↦ μ.real (good A edges color S)
  let F := fun S ↦ Z S / q^S.card
  have pos (S : Finset V) : 0 ≤ F S := div_nonneg measureReal_nonneg (pow_pos hq _).le
  have mono (S T : Finset V) (hTS : T ⊆ S) : F T ≤ F S := by
    induction S using Finset.strongInduction generalizing T with
    | H S ih =>
      by_cases heq : T = S
      · rw [heq]
      obtain ⟨v, hv, hvT⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hTS, heq⟩)
      let R := S.erase v
      have hRS : R ⊂ S := erase_ssubset hv
      have hTR : T ⊆ R := fun x hx ↦ mem_erase.mpr ⟨fun hh ↦ hvT (hh ▸ hx), hTS hx⟩
      apply (ih R hRS T hTR).trans
      let B := A.filter (fun i ↦ v ∈ edges i ∧ edges i ⊆ S)
      let price := fun i ↦ (ν.real {color i})^(edges i).card / q^((edges i).card-1)
      have hp (i) : 0 ≤ price i :=
        div_nonneg (pow_nonneg measureReal_nonneg _) (pow_pos hq _).le
      have hc : ∑ i ∈ B, price i ≤ 1-q :=
        (sum_le_sum_of_subset_of_nonneg (fun i hi ↦ by
          obtain ⟨hi,hv',_⟩ := mem_filter.mp hi
          exact mem_filter.mpr ⟨hi,hv'⟩) (fun i _ _ ↦ hp i)).trans (cost v)
      have hz (K : Finset V) : Z K = F K * q^K.card := (div_mul_cancel₀ _ (pow_ne_zero _ hq.ne')).symm
      have hcard : R.card+1 = S.card := card_erase_add_one hv
      have hsum : ∑ i ∈ B, (ν.real {color i})^(edges i).card * Z (S \ edges i) ≤
          (∑ i ∈ B, price i) * (q^R.card * F R) := by
        rw [sum_mul]
        apply sum_le_sum
        intro i hi
        obtain ⟨_, hv', hs'⟩ := mem_filter.mp hi
        have hsub : S \ edges i ⊆ R := by
          intro x hx
          exact mem_erase.mpr ⟨fun h ↦ (mem_sdiff.mp hx).2 (h ▸ hv'), (mem_sdiff.mp hx).1⟩
        have hec : (edges i).card ≤ S.card := card_le_card hs'
        have hep : 0 < (edges i).card := card_pos.mpr ⟨v,hv'⟩
        have heq : (S \ edges i).card + ((edges i).card - 1) = R.card := by
          rw [card_sdiff_of_subset hs']; omega
        rw [hz, ← heq, pow_add]
        dsimp only [price]
        calc
          _ ≤ (ν.real {color i})^(edges i).card * (F R * q^(S \ edges i).card) := by
            gcongr
            exact ih R hRS _ hsub
          _ = _ := by field_simp
      have hh : Z R ≤ Z S + (∑ i ∈ B, price i) * (q^R.card * F R) :=
        (prob_step ν A edges color S v).trans (add_le_add_right hsum _)
      have hh' := hh.trans (add_le_add_right (mul_le_mul_of_nonneg_right hc
        (mul_nonneg (pow_pos hq _).le (pos R))) _)
      rw [hz R, hz S, ← hcard, pow_succ] at hh'
      have hh'' : F R * (q^R.card*q) ≤ F S * (q^R.card*q) := by linarith only [hh']
      exact le_of_mul_le_mul_right hh'' (by positivity)
  have hempty : good A edges color ∅ = Set.univ := by
    ext w
    simp only [Set.mem_univ, iff_true]
    intro i hi hs
    exact False.elim ((ne i hi).ne_empty (Finset.subset_empty.mp hs))
  have hbase : F ∅ = 1 := by simp [F, Z, hempty, μ]
  have hnon := mono Finset.univ ∅ (empty_subset _)
  rw [hbase] at hnon
  by_contra hn
  have he := Set.not_nonempty_iff_eq_empty.mp hn
  simp [F, Z, he] at hnon
  linarith

private def parameters (n k : ℕ) : Finset (ℕ × ℕ) :=
  ((range n) ×ˢ (range (n+1))).filter (fun z ↦ 0 < z.2 ∧ z.1 + (k-1)*z.2 < n)

private def edge (n k : ℕ) (z : ℕ × ℕ) : Finset (Fin (n+1)) :=
  (range k).image fun j ↦ (Fin.ofNat (n+1) (z.1+j*z.2))

private lemma edge_index {n k : ℕ} {z : ℕ × ℕ} (hz : z ∈ parameters n k)
    {j : ℕ} (hj : j < k) :
    ((Fin.ofNat (n+1) (z.1+j*z.2)) : ℕ) = z.1+j*z.2 := by
  have h := (mem_filter.mp hz).2.2
  have := Nat.mul_le_mul_right z.2 (show j ≤ k-1 by omega)
  exact Nat.mod_eq_of_lt (by omega)

private lemma edge_card {n k : ℕ} {z : ℕ × ℕ} (hz : z ∈ parameters n k) :
    (edge n k z).card = k := by
  rw [edge, card_image_of_injOn, card_range]
  intro i hi j hj he
  have he' := congrArg Fin.val he
  rw [edge_index hz (mem_range.mp hi), edge_index hz (mem_range.mp hj)] at he'
  exact Nat.eq_of_mul_eq_mul_right (mem_filter.mp hz).2.1 (Nat.add_left_cancel he')

private lemma incidence {n k : ℕ} (v : Fin (n+1)) :
    ((parameters n k).filter (fun z ↦ v ∈ edge n k z)).card ≤ k*(n+1) := by
  let index := (range k) ×ˢ (range (n+1))
  let recover := fun z : ℕ × ℕ ↦ (v.val-z.1*z.2,z.2)
  have hs : (parameters n k).filter (fun z ↦ v ∈ edge n k z) ⊆ index.image recover := by
    intro z hz
    obtain ⟨hz,hv⟩ := mem_filter.mp hz
    obtain ⟨j,hj,hjv⟩ := mem_image.mp hv
    have he := congrArg Fin.val hjv
    rw [edge_index hz (mem_range.mp hj)] at he
    refine mem_image.mpr ⟨(j,z.2),mem_product.mpr ⟨hj,(mem_product.mp (mem_filter.mp hz).1).2⟩, ?_⟩
    apply Prod.ext
    · change v.val - j*z.2 = z.1
      omega
    · rfl
  exact (card_le_card hs).trans (card_image_le.trans (by simp [index]))

private def tags (n r : ℕ) : Finset (Bool × ℕ × ℕ) :=
  ((parameters n 3).image (Prod.mk true)) ∪ ((parameters n r).image (Prod.mk false))

private def apEdge (n r : ℕ) (i : Bool × ℕ × ℕ) := edge n (if i.1 then 3 else r) i.2

private lemma tagSum (n r : ℕ) (v : Fin (n+1)) (f : Bool → ℕ → ℝ) :
    ∑ i ∈ (tags n r).filter (fun i ↦ v ∈ apEdge n r i), f i.1 (apEdge n r i).card =
      ((parameters n 3).filter (fun z ↦ v ∈ edge n 3 z)).card * f true 3 +
      ((parameters n r).filter (fun z ↦ v ∈ edge n r z)).card * f false r := by
  classical
  have one (b : Bool) (k : ℕ) (hk : (if b then 3 else r) = k) :
      ∑ i ∈ ((parameters n k).image (Prod.mk b)).filter (fun i ↦ v ∈ apEdge n r i),
        f i.1 (apEdge n r i).card =
        ((parameters n k).filter (fun z ↦ v ∈ edge n k z)).card * f b k := by
    rw [filter_image, sum_image]
    · have eqf : ∀ z ∈ (parameters n k).filter (fun z ↦ v ∈ apEdge n r (b,z)),
          f b (apEdge n r (b,z)).card = f b k := by
        intro z hz
        simp [apEdge, hk, edge_card (mem_filter.mp hz).1]
      convert sum_congr rfl eqf using 1
      simp [apEdge, hk]
    · intro a ha c hc h; exact Prod.mk.inj h |>.2
  rw [tags, filter_union, sum_union, one true 3 rfl, one false r rfl]
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨_,_,he⟩ := mem_image.mp (mem_filter.mp hz).1
  obtain ⟨_,_,he'⟩ := mem_image.mp (mem_filter.mp hz').1
  exact Bool.noConfusion (congrArg Prod.fst (he.trans he'.symm))

private lemma coloring (n r : ℕ) (hr : 3 ≤ r) (p q : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hq : 0 < q) (hbudget : 3*(n+1)*(p^3/q^2) + (r:ℝ)*(n+1)*((1-p)^r/q^(r-1)) ≤ 1-q) :
    ∃ w : ℕ → Bool,
      (∀ a d : ℕ, 0 < d → a+2*d < n → ∃ j < 3, w (a+j*d) = false) ∧
      (∀ a d : ℕ, 0 < d → a+(r-1)*d < n → ∃ j < r, w (a+j*d) = true) := by
  classical
  let ν := bernoulliMeasure true false ⟨p,hp,hp'⟩
  have h₁ : ν.real {true} = p := by simp [ν]
  have h₀ : ν.real {false} = 1-p := by simp [ν]
  have hn (i) (hi : i ∈ tags n r) : (apEdge n r i).Nonempty := by
    rcases mem_union.mp hi with hi|hi
    · obtain ⟨z,hz,rfl⟩ := mem_image.mp hi
      apply card_pos.mp
      simp [apEdge, edge_card hz]
    · obtain ⟨z,hz,rfl⟩ := mem_image.mp hi
      apply card_pos.mp
      simpa [apEdge, edge_card hz] using (show 0 < r by omega)
  obtain ⟨g,hg⟩ := avoid ν (tags n r) (apEdge n r) Prod.fst hn q hq (by
    intro v
    rw [tagSum n r v (fun b k ↦ (ν.real {b}) ^ k / q^(k-1))]
    rw [h₁,h₀]
    have h3 : (((parameters n 3).filter (fun z ↦ v ∈ edge n 3 z)).card : ℝ) ≤ 3*(n+1) := by
      exact_mod_cast incidence (k:=3) v
    have hk : (((parameters n r).filter (fun z ↦ v ∈ edge n r z)).card : ℝ) ≤ (r:ℝ)*(n+1) := by
      exact_mod_cast incidence (k:=r) v
    exact (add_le_add (mul_le_mul_of_nonneg_right h3 (by positivity))
      (mul_le_mul_of_nonneg_right hk (by exact div_nonneg (pow_nonneg (sub_nonneg.mpr hp') _) (pow_pos hq _).le))).trans hbudget)
  refine ⟨fun x ↦ g (Fin.ofNat (n+1) x), ?_, ?_⟩
  · intro a d hd h
    by_contra! hn
    have hz : (a,d) ∈ parameters n 3 := mem_filter.mpr
      ⟨mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩,hd,h⟩
    apply hg (true,a,d) (mem_union_left _ (mem_image.mpr ⟨_,hz,rfl⟩)) (subset_univ _)
    intro x hx
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hx
    simpa using hn j (mem_range.mp hj)
  · intro a d hd h
    by_contra! hn
    have he := Nat.mul_le_mul_right d (show 1 ≤ r-1 by omega)
    simp only [one_mul] at he
    have hz : (a,d) ∈ parameters n r := mem_filter.mpr
      ⟨mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩,hd,h⟩
    apply hg (false,a,d) (mem_union_right _ (mem_image.mpr ⟨_,hz,rfl⟩)) (subset_univ _)
    intro x hx
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hx
    simpa using hn j (mem_range.mp hj)

private lemma budget {n r : ℕ} (hr : 3 ≤ r) (hl : 1 ≤ Real.log (r:ℝ))
    (p : ℝ) (hp : p*(r:ℝ) = 16 * Real.log r) (hsm : p ≤ 1/10)
    (hn : (n:ℝ)+1 ≤ 1/(50*p^2)) :
    3*((n:ℝ)+1)*(p^3/(1-p/2)^2) +
      (r:ℝ)*(n+1)*((1-p)^r/(1-p/2)^(r-1)) ≤ 1-(1-p/2) := by
  have hrp : 0 < (r:ℝ) := by positivity
  have hp0 : 0 < p := by nlinarith [mul_nonpos_of_nonpos_of_nonneg (a:=p) (b:=(r:ℝ))]
  have hq : 0 < 1-p/2 := by linarith
  have hq' : 1-p/2 ≤ 1 := by linarith
  have hred : 3*((n:ℝ)+1)*(p^3/(1-p/2)^2) ≤ p/4 := by
    calc
      _ ≤ 3*(1/(50*p^2))*(p^3/(1-p/2)^2) := by gcongr
      _ ≤ p/4 := by
        have hq2 : 1/2 ≤ (1-p/2)^2 := by nlinarith [sq_nonneg p]
        calc
          _ = (3*p/50)/(1-p/2)^2 := by field_simp
          _ ≤ p/4 := (div_le_iff₀ (sq_pos_of_pos hq)).mpr (by nlinarith [mul_le_mul_of_nonneg_left hq2 hp0.le])
  have hratio : (1-p)^r/(1-p/2)^(r-1) ≤ (Real.exp (-(p/2)))^r := by
    have h1 : 1-p ≤ (1-p/2)^2 := by nlinarith [sq_nonneg p]
    have he : 1-p/2 ≤ Real.exp (-(p/2)) := by linarith [Real.add_one_le_exp (-(p/2))]
    calc
      _ ≤ ((1-p/2)^2)^r/(1-p/2)^(r-1) := by gcongr; linarith
      _ = (1-p/2)^r*(1-p/2) := by
        apply (div_eq_iff (pow_ne_zero _ hq.ne')).2
        rw [← pow_mul, mul_assoc, ← pow_succ', ← pow_add]
        congr 1
        omega
      _ ≤ (1-p/2)^r*1 := by gcongr
      _ ≤ _ := by rw [mul_one]; gcongr
  have hpow : (Real.exp (-(p/2)))^r = 1/(r:ℝ)^8 := by
    rw [← Real.exp_nat_mul, show (r:ℝ) * -(p/2) = -(8*Real.log r) by linarith only [hp],
      Real.exp_neg, show (8:ℝ)*Real.log r = (8:ℕ)*Real.log r by norm_num,
      Real.exp_nat_mul, Real.exp_log hrp, one_div]
  have hn' : (n:ℝ)+1 ≤ (r:ℝ)^2 := by
    apply hn.trans
    apply (div_le_iff₀ (by positivity)).2
    have hpr : 1 ≤ p*(r:ℝ) := by linarith
    nlinarith [sq_nonneg (p*r-1), mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1) hpr]
  have hblue : (r:ℝ)*(n+1)*((1-p)^r/(1-p/2)^(r-1)) ≤ p/4 := by
    rw [hpow] at hratio
    calc
      _ ≤ (r:ℝ)*(r:ℝ)^2*(1/(r:ℝ)^8) := by gcongr; exact div_nonneg (pow_nonneg (by linarith) _) (pow_pos hq _).le
      _ ≤ 1/(r:ℝ) := by
        field_simp
        exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ r by omega))
      _ ≤ p/4 := by apply (div_le_iff₀ hrp).2; linarith
  linarith

private lemma scale : ∀ᶠ r : ℕ in atTop,
    ∃ (p : ℝ) (n : ℕ), 3 ≤ r ∧ 1 ≤ Real.log (r:ℝ) ∧ 0 < p ∧
      p * r = 16*Real.log r ∧ p ≤ 1/10 ∧ (n:ℝ)+1 ≤ 1/(50*p^2) ∧
      ((r:ℝ)/Real.log r)^2 < 25600*((n:ℝ)+1) := by
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := (Real.isLittleO_log_id_atTop.def (show (0:ℝ) < 1/160 by norm_num)).filter_mono
    (show Filter.map (fun n:ℕ ↦ (n:ℝ)) atTop ≤ atTop from tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_ge_atTop 3, hlog.eventually_ge_atTop 1, hsmall] with r hr hl hs
  change 1 ≤ Real.log (r:ℝ) at hl
  have hrp : 0 < (r:ℝ) := by positivity
  change ‖Real.log (r:ℝ)‖ ≤ 1/160*‖id (r:ℝ)‖ at hs
  rw [Real.norm_eq_abs, abs_of_pos (by linarith : 0 < Real.log (r:ℝ)),
    Real.norm_eq_abs, id_eq, abs_of_pos hrp] at hs
  let p := 16*Real.log (r:ℝ)/(r:ℝ)
  have hp : p*(r:ℝ) = 16*Real.log r := div_mul_cancel₀ _ hrp.ne'
  have hp0 : 0 < p := by dsimp [p]; positivity
  have hsm : p ≤ 1/10 := (div_le_iff₀ hrp).mpr (by linarith)
  let n := ⌊1/(100*p^2)⌋₊
  have hlower : (n:ℝ) ≤ 1/(100*p^2) := Nat.floor_le (by positivity)
  have hupper : 1/(100*p^2) < (n:ℝ)+1 := Nat.lt_floor_add_one _
  refine ⟨p,n,hr,hl,hp0,hp,hsm,?_,?_⟩
  · have hs1 : 1 ≤ 1/(100*p^2) := (le_div_iff₀ (by positivity)).mpr (by
      nlinarith [mul_self_le_mul_self hp0.le hsm])
    have : 1/(50*p^2) = 2*(1/(100*p^2)) := by ring
    linarith
  · have hlog0 : Real.log (r:ℝ) ≠ 0 := by linarith
    have he : ((r:ℝ)/Real.log r)^2 = 25600*(1/(100*p^2)) := by
      dsimp only [p]
      field_simp
      ring
    rw [he]
    linarith

private lemma guarantee_exists (r : ℕ) (hr : 3 ≤ r) :
    (Green14.mixedMonoAPGuaranteeSet 3 r).Nonempty := by
  classical
  obtain ⟨ι, inst, H⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin r) Bool
  let n := Fintype.card ι * r + 1
  refine ⟨n, ?_⟩
  by_contra hn
  obtain ⟨w,red,blue⟩ := (WaerdenBridge.not_mem_iff (by omega) ).mp hn
  let total := fun z : ι → Fin r ↦ ∑ i, (z i : ℕ)
  obtain ⟨l,b,hl⟩ := H (fun z ↦ w (total z))
  let V := Finset.univ.filter (fun i ↦ l.idxFun i = none)
  let d := V.card
  let a := ∑ i, ((l.idxFun i).map Fin.val).getD 0
  have hd : 0 < d := Finset.card_pos.mpr
    ⟨l.proper.choose, mem_filter.mpr ⟨mem_univ _,l.proper.choose_spec⟩⟩
  have formula (j : Fin r) : total (l j) = a + j.val*d := by
    change ∑ i, ((l j i).val) = _ + _ * V.card
    have expand (i : ι) : (l j i).val =
        ((l.idxFun i).map Fin.val).getD 0 + (if i ∈ V then j.val else 0) := by
      cases he : l.idxFun i with
      | none => simp [V, he]
      | some x => simp [V, he]
    simp_rw [expand]
    simp [sum_add_distrib, a, mul_comm]
  have upper (j : Fin r) : a + j.val*d < n := by
    rw [← formula]
    have hu : total (l j) ≤ ∑ _i : ι, r :=
      sum_le_sum (fun i _ ↦ (l j i).isLt.le)
    simpa [n] using Nat.lt_succ_of_le hu
  have monochrome (j : ℕ) (hj : j < r) : w (a+j*d) = b := by
    simpa only [formula] using hl (⟨j,hj⟩ : Fin r)
  cases b with
  | false =>
    have hi : r-1 < r := by omega
    obtain ⟨j,hj,hc⟩ := blue a d hd (upper ⟨r-1,hi⟩)
    have := monochrome j hj
    simp_all
  | true =>
    obtain ⟨j,hj,hc⟩ := red a d hd (upper ⟨2,by omega⟩)
    have := monochrome j (by omega)
    simp_all

private lemma lower_bound : (fun r : ℕ ↦ ((r:ℝ)/Real.log r)^2) =O[atTop]
    fun r : ℕ ↦ (Green14.W 3 r : ℝ) := by
  refine isBigO_iff.mpr ⟨25600,?_⟩
  filter_upwards [scale] with r h
  obtain ⟨p,n,hr,hl,hp,heq,hs,hn,hsize⟩ := h
  have hw := coloring n r hr p (1-p/2) hp.le (by linarith) (by linarith)
    (budget hr hl p heq hs hn)
  have hW := WaerdenBridge.W_gt_of_not_mem ((WaerdenBridge.not_mem_iff (by omega)).mpr hw)
    (guarantee_exists r hr)
  have hW' : (n:ℝ)+1 ≤ (Green14.W 3 r : ℝ) := by exact_mod_cast hW
  simpa [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ Real.log (r:ℝ) by linarith)] using
    hsize.le.trans (mul_le_mul_of_nonneg_left hW' (by norm_num : (0:ℝ) ≤ 25600))

private lemma log_comparison :
    (fun r : ℕ ↦ (r:ℝ)^(2-1/Real.log (Real.log (r:ℝ)))) =O[atTop]
    fun r : ℕ ↦ ((r:ℝ)/Real.log r)^2 := by
  have hl := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll := Real.tendsto_log_atTop.comp hl
  apply isBigO_iff.mpr
  refine ⟨1,?_⟩
  filter_upwards [eventually_ge_atTop 2, hl.eventually_ge_atTop 1, hll.eventually_ge_atTop 12]
    with r hr hlog hu
  change 1 ≤ Real.log (r:ℝ) at hlog
  change 12 ≤ Real.log (Real.log (r:ℝ)) at hu
  let u := Real.log (Real.log (r:ℝ))
  have hu' : 12 ≤ u := hu
  have hr' : 0 < (r:ℝ) := by positivity
  have hlog' : 0 < Real.log (r:ℝ) := by linarith
  have hbound := Real.pow_div_factorial_le_exp u (show 0 ≤ u by linarith) 3
  have heu : Real.exp u = Real.log (r:ℝ) := Real.exp_log hlog'
  rw [heu] at hbound
  norm_num at hbound
  have hsq : 2*u^2 ≤ Real.log (r:ℝ) := by nlinarith [mul_le_mul_of_nonneg_right hu' (sq_nonneg u)]
  have hu0 : 0 < u := by linarith
  have hexp : Real.log (r:ℝ) * (2-1/u) ≤ 2*(Real.log (r:ℝ)-u) := by
    have := (le_div_iff₀ hu0).2 (show 2*u*u ≤ Real.log (r:ℝ) by linarith only [hsq])
    calc
      _ = 2*Real.log (r:ℝ) - Real.log (r:ℝ)/u := by ring
      _ ≤ _ := by linarith
  have hratio : Real.exp (2*(Real.log (r:ℝ)-u)) = ((r:ℝ)/Real.log r)^2 := by
    rw [two_mul, Real.exp_add, Real.exp_sub, Real.exp_log hr', heu]
    ring
  have h := (Real.exp_le_exp.mpr hexp).trans_eq hratio
  rw [← Real.rpow_def_of_pos hr'] at h
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hr'.le _),
    abs_of_nonneg (sq_nonneg ((r:ℝ)/Real.log r)), one_mul] using h

end ProgressionColoring

theorem OMA.solution : type_of% @Green14.green_14_lower_bound_brown_landman_robertson :=
  ProgressionColoring.log_comparison.trans ProgressionColoring.lower_bound