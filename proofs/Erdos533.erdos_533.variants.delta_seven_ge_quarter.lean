import FormalConjectures.ErdosProblems.«533»
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Logic.Function.DependsOn
import Mathlib.Tactic

/-! A sparse triple system with an edge in every large set and no Berge triangle. -/

open Finset MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped BigOperators

namespace TripleSystem

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

private def sides {V : Type} [DecidableEq V] (x : Fin 6 → V) : Finset (Finset V) :=
  {{x 0,x 1,x 3},{x 1,x 2,x 4},{x 2,x 0,x 5}}

private def cycles (n : ℕ) : Finset (Fin 6 → Fin n) :=
  univ.filter fun x ↦ (sides x).card = 3 ∧ ∀ t ∈ sides x, t.card = 3

private lemma cycle_count (n : ℕ) (t : Finset (Fin n)) :
    ((cycles n).filter (fun x ↦ t ∈ sides x)).card ≤ 81 * n^3 := by
  classical
  by_cases ht : t.card = 3
  swap
  · have : (cycles n).filter (fun x ↦ t ∈ sides x) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨h,h'⟩ := mem_filter.mp hx
      exact ht ((mem_filter.mp h).2.2 t h')
    simp [this]
  let box := fun a b c : Fin 6 ↦ Fintype.piFinset
    (fun i : Fin 6 ↦ if i=a ∨ i=b ∨ i=c then t else univ)
  have cardbox (a b c : Fin 6) (ha : a ≠ b) (hb : b ≠ c) (hc : c ≠ a) :
      (box a b c).card = 27 * n^3 := by
    rw [Fintype.card_piFinset]
    simp only [apply_ite Finset.card,ht,card_univ,Fintype.card_fin]
    have he (i : Fin 6) : (i=a ∨ i=b ∨ i=c) ↔ i ∈ ({a,b,c} : Finset (Fin 6)) := by simp
    simp_rw [he]
    rw [prod_ite]
    have hf : (univ.filter (fun i : Fin 6 ↦ i ∈ ({a,b,c} : Finset _))) = {a,b,c} := by ext; simp
    have hf' : (univ.filter (fun i : Fin 6 ↦ i ∉ ({a,b,c} : Finset _))) = ({a,b,c} : Finset _)ᶜ := by ext; simp
    rw [hf,hf']
    simp [ha,hb,hc.symm, Finset.card_compl]
  have inbox (a b c : Fin 6) (x : Fin 6 → Fin n) (h : t = {x a,x b,x c}) :
      x ∈ box a b c := by
    apply Fintype.mem_piFinset.mpr
    intro i
    split_ifs with hi
    · rcases hi with rfl | rfl | rfl <;> simp [h]
    · simp
  have hs : (cycles n).filter (fun x ↦ t ∈ sides x) ⊆
      (box 0 1 3 ∪ box 1 2 4) ∪ box 2 0 5 := by
    intro x hx
    have h := (mem_filter.mp hx).2
    simp only [sides,mem_insert,mem_singleton] at h
    rcases h with h|h|h
    · exact mem_union_left _ (mem_union_left _ (inbox 0 1 3 x h))
    · exact mem_union_left _ (mem_union_right _ (inbox 1 2 4 x h))
    · exact mem_union_right _ (inbox 2 0 5 x h)
  have h := (card_le_card hs).trans ((card_union_le ..).trans
    (Nat.add_le_add_right (card_union_le ..) _))
  rw [cardbox 0 1 3 (by decide) (by decide) (by decide),
    cardbox 1 2 4 (by decide) (by decide) (by decide),
    cardbox 2 0 5 (by decide) (by decide) (by decide)] at h
  omega

private abbrev Index (n : ℕ) := (Fin 6 → Fin n) ⊕ Finset (Fin n)

private def events (n m : ℕ) : Finset (Index n) :=
  (cycles n).disjSum (univ.powersetCard m)

private def support {n : ℕ} : Index n → Finset (Finset (Fin n))
  | .inl x => sides x
  | .inr S => S.powersetCard 3

private def shade {n : ℕ} : Index n → Bool := Sum.elim (fun _ ↦ true) (fun _ ↦ false)

private lemma select (n m : ℕ) (hm : 3 ≤ m) (p q : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hq : 0 < q) (hb : 81*(n:ℝ)^3*(p^3/q^2) +
       (2:ℝ)^n*((1-p)^(m.choose 3)/q^(m.choose 3-1)) ≤ 1-q) :
    ∃ f : Finset (Fin n) → Bool,
      (∀ x ∈ cycles n, ¬ ∀ t ∈ sides x, f t = true) ∧
      (∀ S : Finset (Fin n), S.card = m → ∃ t ⊆ S, t.card = 3 ∧ f t = true) := by
  classical
  let ν := bernoulliMeasure true false ⟨p,hp,hp'⟩
  have h₁ : ν.real {true} = p := by simp [ν]
  have h₀ : ν.real {false} = 1-p := by simp [ν]
  have nn (i) (hi : i ∈ events n m) : (support i).Nonempty := by
    cases i with
    | inl x =>
      exact ⟨_, mem_insert_self ..⟩
    | inr S =>
      have hs : S.card = m := (mem_powersetCard.mp (inr_mem_disjSum.mp hi)).2
      exact Finset.powersetCard_nonempty.mpr (hs ▸ hm)
  obtain ⟨f,hf⟩ := avoid ν (events n m) support shade nn q hq (by
    intro t
    have redcost : ∑ x ∈ (cycles n).filter (fun x ↦ t ∈ sides x),
        (ν.real {true})^(sides x).card/q^((sides x).card-1) =
        (((cycles n).filter (fun x ↦ t ∈ sides x)).card : ℝ) * (p^3/q^2) := by
      rw [← nsmul_eq_mul, ← sum_const]
      apply sum_congr rfl
      intro x hx
      rw [(mem_filter.mp (mem_filter.mp hx).1).2.1,h₁]
    let blue := (univ.powersetCard m : Finset (Finset (Fin n))).filter (fun S ↦ t ∈ S.powersetCard 3)
    have bluecost : ∑ S ∈ blue, (ν.real {false})^(S.powersetCard 3).card/
        q^((S.powersetCard 3).card-1) = (blue.card:ℝ) * ((1-p)^(m.choose 3)/q^(m.choose 3-1)) := by
      rw [← nsmul_eq_mul, ← sum_const]
      apply sum_congr rfl
      intro S hS
      rw [h₀, card_powersetCard, (mem_powersetCard.mp (mem_filter.mp hS).1).2]
    have split : (events n m).filter (fun i ↦ t ∈ support i) =
        ((cycles n).filter (fun x ↦ t ∈ sides x)).disjSum blue := by
      ext i
      rw [Finset.mem_filter]
      cases i <;> simp only [events,inl_mem_disjSum,inr_mem_disjSum,support,blue,Finset.mem_filter]
    rw [split,sum_disjSum]
    dsimp only [support,shade,Sum.elim_inl,Sum.elim_inr]
    rw [redcost,bluecost]
    have redle : (((cycles n).filter (fun x ↦ t ∈ sides x)).card:ℝ) ≤ 81*(n:ℝ)^3 := by
      exact_mod_cast cycle_count n t
    have bluele : (blue.card:ℝ) ≤ (2:ℝ)^n := by
      exact_mod_cast (show blue.card ≤ 2^n by simpa using blue.card_le_univ)
    exact (add_le_add (mul_le_mul_of_nonneg_right redle (by positivity))
      (mul_le_mul_of_nonneg_right bluele
        (div_nonneg (pow_nonneg (sub_nonneg.mpr hp') _) (pow_pos hq _).le))).trans hb)
  refine ⟨f, fun x hx ↦ hf (.inl x) (inl_mem_disjSum.mpr hx) (subset_univ _), ?_⟩
  intro S hS
  have h := hf (.inr S) (inr_mem_disjSum.mpr (mem_powersetCard.mpr ⟨subset_univ _, hS⟩)) (subset_univ _)
  change ¬ ∀ t ∈ S.powersetCard 3, f t = false at h
  push Not at h
  obtain ⟨t,ht,hf⟩ := h
  obtain ⟨hs,hc⟩ := mem_powersetCard.mp ht
  exact ⟨t,hs,hc,by simpa using hf⟩

private def shadow {n : ℕ} (f : Finset (Fin n) → Bool) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ ∃ u, x ≠ u ∧ y ≠ u ∧ f {x,y,u} = true
  symm.symm := by
    rintro x y ⟨h,u,hx,hy,hf⟩
    exact ⟨h.symm,u,hy,hx,by simpa [insert_comm] using hf⟩
  loopless := ⟨fun x h ↦ h.1 rfl⟩

private lemma forbidden {n : ℕ} {f : Finset (Fin n) → Bool}
    (avoidance : ∀ x ∈ cycles n, ¬ ∀ t ∈ sides x, f t = true)
    {x y z a b c : Fin n} (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
    (hxa : x ≠ a) (hya : y ≠ a) (hyb : y ≠ b) (hzb : z ≠ b)
    (hzc : z ≠ c) (hxc : x ≠ c) (hza : z ≠ a) (hxb : x ≠ b) (hyc : y ≠ c)
    (f₁ : f {x,y,a} = true) (f₂ : f {y,z,b} = true) (f₃ : f {z,x,c} = true) : False := by
  let u : Fin 6 → Fin n := ![x,y,z,a,b,c]
  let t₁ : Finset (Fin n) := {x,y,a}
  let t₂ : Finset (Fin n) := {y,z,b}
  let t₃ : Finset (Fin n) := {z,x,c}
  have h₁₂ : t₁ ≠ t₂ := fun he ↦ (show z ∉ t₁ by simp [t₁,hzx,hyz.symm,hza]) (he ▸ by simp [t₂])
  have h₂₃ : t₂ ≠ t₃ := fun he ↦ (show x ∉ t₂ by simp [t₂,hxy,hzx.symm,hxb]) (he ▸ by simp [t₃])
  have h₃₁ : t₃ ≠ t₁ := fun he ↦ (show y ∉ t₃ by simp [t₃,hyz,hxy.symm,hyc]) (he ▸ by simp [t₁])
  have he : sides u = {t₁,t₂,t₃} := rfl
  have hu : u ∈ cycles n := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_, ?_⟩
    · simp [he,h₁₂,h₂₃,h₃₁.symm]
    · intro t ht
      rw [he] at ht
      simp only [mem_insert,mem_singleton] at ht
      rcases ht with rfl|rfl|rfl
      · simp [t₁,hxy,hxa,hya]
      · simp [t₂,hyz,hyb,hzb]
      · simp [t₃,hzx,hzc,hxc]
  apply avoidance u hu
  intro t ht
  rw [he] at ht
  simp only [mem_insert,mem_singleton] at ht
  rcases ht with rfl|rfl|rfl <;> assumption

private lemma triangle {n : ℕ} {f : Finset (Fin n) → Bool}
    (avoidance : ∀ x ∈ cycles n, ¬ ∀ t ∈ sides x, f t = true)
    {x y z : Fin n} (h₁ : (shadow f).Adj x y) (h₂ : (shadow f).Adj y z)
    (h₃ : (shadow f).Adj z x) : f {x,y,z} = true := by
  obtain ⟨hxy,a,hxa,hya,f₁⟩ := h₁
  obtain ⟨hyz,b,hyb,hzb,f₂⟩ := h₂
  obtain ⟨hzx,c,hzc,hxc,f₃⟩ := h₃
  by_contra hf
  have za : z ≠ a := fun he ↦ hf (he ▸ f₁)
  have xb : x ≠ b := by rintro rfl; apply hf; rwa [show ({y,z,x} : Finset _) = {x,y,z} by ext; simp; tauto] at f₂
  have yc : y ≠ c := by rintro rfl; apply hf; rwa [show ({z,x,y} : Finset _) = {x,y,z} by ext; simp; tauto] at f₃
  exact forbidden avoidance hxy hyz hzx hxa hya hyb hzb hzc hxc za xb yc f₁ f₂ f₃

private lemma no_four {n : ℕ} {f : Finset (Fin n) → Bool}
    (avoidance : ∀ x ∈ cycles n, ¬ ∀ t ∈ sides x, f t = true)
    {T : Finset (Fin n)} (hc : (shadow f).IsClique T) : T.card ≤ 3 := by
  by_contra! h
  obtain ⟨x,y,z,u,xt,yt,zt,ut,xy,xz,xu,yz,yu,zu⟩ := three_lt_card_iff.mp h
  have hx := triangle avoidance (hc xt yt xy) (hc yt ut yu) (hc ut xt xu.symm)
  have hy := triangle avoidance (hc yt zt yz) (hc zt ut zu) (hc ut yt yu.symm)
  have hz := triangle avoidance (hc zt xt xz.symm) (hc xt ut xu) (hc ut zt zu.symm)
  exact forbidden avoidance xy yz xz.symm xu yu yu zu zu xu zu xu yu hx hy hz

private lemma selected_clique {n : ℕ} {f : Finset (Fin n) → Bool} {t : Finset (Fin n)}
    (hc : t.card = 3) (ht : f t = true) : (shadow f).IsNClique 3 t := by
  apply (shadow f).isNClique_iff.mpr
  refine ⟨?_,hc⟩
  intro i hi j hj hij
  have hz : ∃ z ∈ t, i ≠ z ∧ j ≠ z := by
    by_contra! hn
    have sub : t ⊆ {i,j} := by
      intro z hz
      by_cases hi : i = z
      · simp [hi]
      · simp [hn z hz hi]
    have hc' := card_le_card sub
    simp [hij,hc] at hc'
  obtain ⟨z,hz,iz,jz⟩ := hz
  have he : ({i,j,z} : Finset _) = t := by
    apply eq_of_subset_of_card_le (by simpa [insert_subset_iff] using And.intro hi (And.intro hj hz))
    simp [hc,hij,iz,jz]
  exact ⟨hij,z,iz,jz,he ▸ ht⟩

private lemma triple_scale (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∃ (m : ℕ) (p q : ℝ), 3 ≤ m ∧
      (∀ a : ℕ, δ*n < a → m ≤ a) ∧ 0 ≤ p ∧ p ≤ 1 ∧ 0 < q ∧
      81*(n:ℝ)^3*(p^3/q^2) + (2:ℝ)^n*((1-p)^(m.choose 3)/q^(m.choose 3-1)) ≤ 1-q := by
  let K := 1+192/δ^3
  have hK : 1 ≤ K := by dsimp [K]; linarith [show 0 ≤ 192/δ^3 by positivity]
  have hKδ : 192 ≤ K*δ^3 := by dsimp [K]; rw [add_mul,div_mul_cancel₀ _ (by positivity)]; linarith [show 0 ≤ δ^3 by positivity]
  have large (x : ℝ) : ∀ᶠ n : ℕ in atTop, x ≤ (n:ℝ) := tendsto_natCast_atTop_atTop.eventually_ge_atTop x
  filter_upwards [large (2000*K^2),large (8/δ),large 24] with n hn hnδ hn24
  have hn0 : 0 < (n:ℝ) := by linarith
  have hbig : 8 ≤ δ*(n:ℝ) := by have := (div_le_iff₀ hδ).mp hnδ; linarith
  let m := ⌊δ*(n:ℝ)⌋₊ + 1
  have hm : δ*(n:ℝ) < (m:ℝ) := by simpa [m] using Nat.lt_floor_add_one (δ*(n:ℝ))
  have hm3 : 3 ≤ m := by exact_mod_cast (show (3:ℝ) ≤ (m:ℝ) by linarith)
  let p := K/(n:ℝ)^2
  have hp : 0 < p := div_pos (by linarith) (by positivity)
  have hKn : K ≤ (n:ℝ) := by nlinarith [sq_nonneg (K-1)]
  have hp1 : p ≤ 1 := (div_le_one₀ (by positivity)).mpr (by nlinarith [sq_nonneg ((n:ℝ)-1)])
  let q := 1-p/2
  have hq : 1/2 ≤ q := by dsimp [q]; linarith
  have hq0 : 0 < q := by linarith
  have hq1 : q ≤ 1 := by dsimp [q]; linarith
  refine ⟨m,p,q,hm3,fun a ha ↦ Nat.succ_le_of_lt (Nat.floor_lt (by positivity) |>.mpr ha),
    hp.le,hp1,hq0,?_⟩
  have red : 81*(n:ℝ)^3*(p^3/q^2) ≤ p/4 := by
    have hq2 : 1/4 ≤ q^2 := by nlinarith [sq_nonneg (q-1/2)]
    have he : 81*(n:ℝ)^3*(p^3/q^2) = (81*K^2/(n:ℝ)) * (p/q^2) := by dsimp [p]; field_simp
    have h1 : 81*K^2/(n:ℝ) ≤ 1/16 := (div_le_iff₀ hn0).mpr (by nlinarith [sq_nonneg K])
    rw [he]
    calc
      _ ≤ (1/16)*(p/q^2) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ p/4 := by
        rw [show (1/16)*(p/q^2) = (p/16)/q^2 by ring]
        apply (div_le_iff₀ (by positivity)).mpr
        nlinarith [mul_le_mul_of_nonneg_left hq2 hp.le]
  let k := m.choose 3
  have hk : 0 < k := Nat.choose_pos hm3
  have hchoose : 6*(k:ℝ) = (m:ℝ)*(m-1)*(m-2) := by
    have hh := Nat.descFactorial_eq_factorial_mul_choose m 3
    simp only [Nat.descFactorial_succ,Nat.descFactorial_zero,mul_one,Nat.sub_zero] at hh
    have hh' : ((m-2 : ℕ):ℝ)*((m-1:ℕ):ℝ)*(m:ℝ) = 6*(k:ℝ) := by
      exact_mod_cast (by simpa [k,Nat.factorial,mul_assoc] using hh : (m-2)*(m-1)*m = 6*k)
    rw [Nat.cast_sub (by omega : 2 ≤ m), Nat.cast_sub (by omega : 1 ≤ m)] at hh'
    push_cast at hh'
    linarith
  have hc : (δ*n/2)^3 ≤ 6*(k:ℝ) := by
    rw [hchoose, pow_succ, pow_two]
    gcongr <;> first | positivity | exact mul_nonneg (by positivity) (by linarith) | linarith
  have rate : 2*(n:ℝ) ≤ p*(k:ℝ)/2 := by
    have hc' := mul_le_mul_of_nonneg_left hc (show 0 ≤ K by linarith)
    have hnum := mul_le_mul_of_nonneg_right hKδ (show 0 ≤ (n:ℝ)^3 by positivity)
    dsimp [p]
    rw [div_mul_eq_mul_div, div_div]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [hc',hnum]
  have bounded : (1-p)^k/q^(k-1) ≤ Real.exp (-2*(n:ℝ)) := by
    have h' : 1-p ≤ q^2 := by dsimp [q]; nlinarith [sq_nonneg p]
    have expq : q ≤ Real.exp (-(p/2)) := by dsimp [q]; linarith [Real.add_one_le_exp (-(p/2))]
    calc
      _ ≤ (q^2)^k/q^(k-1) := by gcongr
      _ = q^k*q := by
        apply (div_eq_iff (pow_ne_zero _ hq0.ne')).mpr
        rw [← pow_mul,mul_assoc,← pow_succ',← pow_add]; congr 1; omega
      _ ≤ q^k*1 := by gcongr
      _ ≤ (Real.exp (-(p/2)))^k := by rw [mul_one]; gcongr
      _ ≤ _ := by rw [← Real.exp_nat_mul]; apply Real.exp_le_exp.mpr; linarith
  have blue : (2:ℝ)^n*((1-p)^k/q^(k-1)) ≤ p/4 := by
    calc
      _ ≤ (Real.exp 1)^n * Real.exp (-2*(n:ℝ)) := by
        apply mul_le_mul (pow_le_pow_left₀ (by norm_num) (show (2:ℝ) ≤ Real.exp 1 by linarith [Real.add_one_le_exp (1:ℝ)]) n) bounded
        · exact div_nonneg (pow_nonneg (sub_nonneg.mpr hp1) _) (pow_pos hq0 _).le
        · positivity
      _ = 1 / Real.exp (n:ℝ) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, show (n:ℝ)*1 + -2*n = -(n:ℝ) by ring, Real.exp_neg,one_div]
      _ ≤ 6/(n:ℝ)^3 := by
        have h := Real.pow_div_factorial_le_exp (n:ℝ) hn0.le 3
        norm_num at h
        apply (div_le_div_iff₀ (Real.exp_pos _) (by positivity)).mpr
        linarith
      _ ≤ p/4 := by
        dsimp [p]
        field_simp
        nlinarith [mul_le_mul_of_nonneg_right hK hn0.le]
  dsimp only [q]
  linarith

private def completed {n : ℕ} (f : Finset (Fin n) → Bool) : SimpleGraph (Fin n) where
  Adj x y := (shadow f).Adj x y ∨ (x.val<n/2 ∧ n/2≤y.val) ∨ (y.val<n/2 ∧ n/2≤x.val)
  symm.symm x y h := by
    rcases h with h|h|h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  loopless := ⟨fun x h ↦ by rcases h with h|h|h; exact (shadow f).loopless.irrefl _ h; omega; omega⟩

private lemma no_seven {n : ℕ} {f : Finset (Fin n) → Bool}
    (avoidance : ∀ x ∈ cycles n, ¬ ∀ t ∈ sides x, f t = true) :
    (completed f).CliqueFree 7 := by
  intro S hS
  have split (P : Fin n → Prop) [DecidablePred P]
      (hP : ∀ x y, P x → P y → ((x.val<n/2) ↔ (y.val<n/2))) :
      (S.filter P).card ≤ 3 := by
    apply no_four avoidance
    intro x hx y hy hxy
    obtain ⟨hx,px⟩ := mem_filter.mp hx
    obtain ⟨hy,py⟩ := mem_filter.mp hy
    have h := hS.isClique hx hy hxy
    have hi := hP x y px py
    rcases h with h|h|h
    · exact h
    · omega
    · omega
  have h₁ := split (fun i ↦ i.val<n/2) (by intros; tauto)
  have h₂ := split (fun i ↦ ¬i.val<n/2) (by intros; tauto)
  have both := S.card_filter_add_card_filter_not (fun i ↦ i.val<n/2)
  have hc := hS.card_eq
  omega

open scoped Classical in
private lemma cross_edges {n : ℕ} (f : Finset (Fin n) → Bool) :
    n/2 * (n-n/2) ≤ (completed f).edgeFinset.card := by
  classical
  let left (x : Fin (n/2)) : Fin n := ⟨x.val, lt_of_lt_of_le x.isLt (Nat.div_le_self ..)⟩
  let right (x : Fin (n-n/2)) : Fin n := ⟨n/2 + x.val,by have := x.isLt; omega⟩
  let edge (z : Fin (n/2) × Fin (n-n/2)) := Sym2.mk (left z.1) (right z.2)
  have hmem (z) : edge z ∈ (completed f).edgeFinset := by
    apply SimpleGraph.mem_edgeFinset.mpr
    exact Or.inr (Or.inl ⟨z.1.isLt, Nat.le_add_right ..⟩)
  have hinj : Function.Injective edge := by
    intro x y h
    rcases Sym2.eq_iff.mp h with ⟨ha,hb⟩|⟨ha,_⟩
    · apply Prod.ext
      · exact Fin.ext (congrArg (fun v : Fin n ↦ v.val) ha)
      · exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val hb))
    · have h' : x.1.val = n/2 + y.2.val := congrArg Fin.val ha
      have := x.1.isLt
      omega
  have h := card_le_card_of_injOn (s:=univ) (t:=(completed f).edgeFinset) edge (fun x _ ↦ hmem x) hinj.injOn
  simpa using h

private lemma enough_edges (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (1/4-ε)*(n:ℝ)^2 ≤ (n/2:ℕ)*(↑(n-n/2:ℕ):ℝ) := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (1/ε),eventually_ge_atTop 2] with n hn hn2
  have hn0 : 0 < (n:ℝ) := by positivity
  have hn' : 1 ≤ (n:ℝ)*ε := (div_le_iff₀ hε).mp hn
  have hq : n ≤ 2*(n/2)+1 := by omega
  have hq' : 2*(n/2) ≤ n := by omega
  have hL : (n:ℝ) ≤ 2*((n/2:ℕ):ℝ)+1 := by exact_mod_cast hq
  have hR : 2*((n/2:ℕ):ℝ) ≤ n := by exact_mod_cast hq'
  rw [Nat.cast_sub (Nat.div_le_self n 2)]
  nlinarith [mul_le_mul_of_nonneg_left hn' hn0.le,
    mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hR), sq_nonneg ((n:ℝ)-2*(n/2:ℕ)-1)]

end TripleSystem

theorem OMA.solution : type_of% @Erdos533.erdos_533.variants.delta_seven_ge_quarter := by
  classical
  intro ε δ hε hδ
  filter_upwards [TripleSystem.triple_scale δ hδ, TripleSystem.enough_edges ε hε] with n hn he
  obtain ⟨m,p,q,hm,hsize,hp,hp',hq,hb⟩ := hn
  obtain ⟨f,hcycle,hlarge⟩ := TripleSystem.select n m hm p q hp hp' hq hb
  refine ⟨TripleSystem.completed f, TripleSystem.no_seven hcycle, ?_,
    he.trans (by exact_mod_cast TripleSystem.cross_edges f)⟩
  intro S hS
  by_contra! hS'
  obtain ⟨s,hs,hsc⟩ := Finset.le_card_iff_exists_subset_card.mp (hsize S.card hS')
  obtain ⟨t,ht,htc,hf⟩ := hlarge s hsc
  have hle : TripleSystem.shadow f ≤ TripleSystem.completed f := fun _ _ h ↦ Or.inl h
  exact hS (Finset.coe_subset.mpr (ht.trans hs))
    ((TripleSystem.selected_clique htc hf).mono hle)