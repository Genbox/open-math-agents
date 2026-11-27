import FormalConjectures.Paper.HallRatioConjecture
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Logic.Function.DependsOn
import Mathlib.Tactic

/-! Join successively larger high-girth graphs. Each critical layer admits an independent
set of at least a fixed fraction of every vertex subset, and sufficiently small subsets induce forests.
A fractional colouring of the join pays separately for each layer. -/

open Finset MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped BigOperators

namespace SparseGraph

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

private def step {l : ℕ} (i : Fin (l+3)) := i+1

private lemma step_ne {l : ℕ} (i : Fin (l+3)) : step i ≠ i := by
  intro he
  have h : (1 : Fin (l+3)) = 0 := add_left_cancel (show i+1=i+0 by rw [add_zero]; exact he)
  have := congrArg Fin.val h
  simp at this

private lemma two_steps_ne {l : ℕ} (i : Fin (l+3)) : step (step i) ≠ i := by
  intro he
  have h : (1+1 : Fin (l+3)) = 0 := add_left_cancel (show i+(1+1)=i+0 by simpa [step,add_assoc] using he)
  have hh := congrArg Fin.val h
  change (1%(l+3)+1%(l+3))%(l+3)=0 at hh
  simp only [Nat.mod_eq_of_lt (show 1 < l+3 by omega),Nat.reduceAdd,
    Nat.mod_eq_of_lt (show 2 < l+3 by omega)] at hh
  omega

private def sides {n l : ℕ} (x : Fin (l+3) → Fin n) : Finset (Finset (Fin n)) :=
  univ.image fun i ↦ {x i,x (step i)}

private lemma cycle_card {n l : ℕ} (x : Fin (l+3) → Fin n) (hx : Function.Injective x) :
    (sides x).card = l+3 := by
  rw [sides,card_image_of_injective,card_univ,Fintype.card_fin]
  intro i j hij
  change ({x i,x (step i)} : Finset _) = {x j,x (step j)} at hij
  have hi : x i ∈ ({x j,x (step j)} : Finset _) := by rw [← hij]; simp
  have hj : x j ∈ ({x i,x (step i)} : Finset _) := by rw [hij]; simp
  simp only [mem_insert,mem_singleton,hx.eq_iff] at hi hj
  rcases hi with h|h
  · exact h
  rcases hj with h'|h'
  · exact h'.symm
  exact ((two_steps_ne i) ((congrArg step h').symm.trans h.symm)).elim

private def tuples (n l : ℕ) : Finset (Fin (l+3) → Fin n) :=
  univ.filter Function.Injective

private lemma per_edge (n l : ℕ) (t : Finset (Fin n)) :
    ((tuples n l).filter (fun x ↦ t ∈ sides x)).card ≤ 4*(l+3)*n^(l+1) := by
  classical
  let box (i : Fin (l+3)) := Fintype.piFinset
    (fun j : Fin (l+3) ↦ if j=i ∨ j=step i then t else univ)
  by_cases ht : t.card=2
  swap
  · have hem : (tuples n l).filter (fun x ↦ t ∈ sides x) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨hx,hm⟩ := mem_filter.mp hx
      have hx' : Function.Injective x := (mem_filter.mp hx).2
      obtain ⟨i,_,rfl⟩ := mem_image.mp hm
      have hi : x i ≠ x (step i) := fun he ↦ step_ne i (hx' he).symm
      exact ht (by simp [hi])
    simp [hem]
  have hbox (i) : (box i).card = 4*n^(l+1) := by
    rw [Fintype.card_piFinset]
    simp only [apply_ite Finset.card,ht,card_univ,Fintype.card_fin]
    have he (j) : (j=i ∨ j=step i) ↔ j ∈ ({i,step i} : Finset _) := by simp
    simp_rw [he]
    rw [prod_ite]
    have hf : (univ.filter (fun j ↦ j ∈ ({i,step i} : Finset _))) = {i,step i} := by ext; simp
    have hf' : (univ.filter (fun j ↦ j ∉ ({i,step i} : Finset _))) = ({i,step i} : Finset _)ᶜ := by ext; simp
    rw [hf,hf']
    simp [Finset.card_compl,Ne.symm (step_ne i)]
  have sub : (tuples n l).filter (fun x ↦ t ∈ sides x) ⊆ univ.biUnion box := by
    intro x hx
    obtain ⟨i,_,hi⟩ := mem_image.mp (mem_filter.mp hx).2
    refine mem_biUnion.mpr ⟨i,mem_univ _, Fintype.mem_piFinset.mpr ?_⟩
    intro j
    split_ifs with hj
    · rcases hj with rfl|rfl <;> simp [← hi]
    · simp
  have h := (card_le_card sub).trans (card_biUnion_le)
  simpa [hbox,mul_left_comm,mul_assoc,mul_comm] using h

private def graph {n : ℕ} (f : Finset (Fin n) → Bool) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ f {x,y} = true
  symm.symm x y h := ⟨h.1.symm, by simpa [Finset.pair_comm] using h.2⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

private lemma girth {n m : ℕ} {f : Finset (Fin n) → Bool}
    (h : ∀ l < m-2, ∀ x ∈ tuples n l, ¬ ∀ e ∈ sides x, f e = true) :
    (m:ℕ∞) < (graph f).egirth := by
  apply ENat.natCast_add_one_le_iff.mp
  apply SimpleGraph.le_egirth.mpr
  intro a w hw
  by_contra! hlen
  have hwlen : w.length ≤ m := by
    have hh : w.length < m+1 := by exact_mod_cast hlen
    omega
  have hw3 : 3 ≤ w.length := hw.three_le_length
  let l := w.length-3
  have hl : l+3=w.length := by dsimp [l]; omega
  let x := fun i : Fin (l+3) ↦ w.getVert i.val
  have hx : Function.Injective x := by
    intro i j h
    exact Fin.ext (hw.getVert_injOn' (by change i.val ≤ w.length-1; omega)
      (by change j.val ≤ w.length-1; omega) h)
  apply h l (by dsimp [l]; omega) x (mem_filter.mpr ⟨mem_univ _,hx⟩)
  intro e he
  obtain ⟨i,_,rfl⟩ := mem_image.mp he
  have adj := w.adj_getVert_succ (show i.val < w.length by omega)
  have stepvert : x (step i) = w.getVert (i.val+1) := by
    change w.getVert ((i.val+1)%(l+3)) = _
    by_cases hi : i.val+1 < l+3
    · rw [Nat.mod_eq_of_lt hi]
    · have eq : i.val+1 = l+3 := by omega
      rw [eq,Nat.mod_self,hl]
      simp
  change f {x i,x (step i)} = true
  rw [stepvert]
  exact adj.2

private abbrev Cycles (n : ℕ) := Σ l : ℕ, Fin (l+3) → Fin n
private abbrev Index (n : ℕ) := Cycles n ⊕ Finset (Fin n)

private def events (n m a : ℕ) : Finset (Index n) :=
  ((range (m-2)).sigma (tuples n)).disjSum (univ.powersetCard a)

private def support {n : ℕ} : Index n → Finset (Finset (Fin n))
  | .inl z => sides z.2
  | .inr S => S.powersetCard 2

private def shade {n : ℕ} : Index n → Bool := Sum.elim (fun _ ↦ true) (fun _ ↦ false)

private noncomputable def redTotal (n m : ℕ) (p q : ℝ) :=
  ∑ l ∈ range (m-2), (4:ℝ)*(l+3)*(n:ℝ)^(l+1)* (p^(l+3)/q^(l+2))

private lemma construct (n m a : ℕ) (ha : 2 ≤ a) (p q : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hq : 0 < q) (budget : redTotal n m p q +
      (2:ℝ)^n*((1-p)^(a.choose 2)/q^(a.choose 2-1)) ≤ 1-q) :
    ∃ G : SimpleGraph (Fin n), (m:ℕ∞) < G.egirth ∧
      ∀ S : Finset (Fin n), G.IsIndepSet S → S.card < a := by
  classical
  let ν := bernoulliMeasure true false ⟨p,hp,hp'⟩
  have h₁ : ν.real {true} = p := by simp [ν]
  have h₀ : ν.real {false} = 1-p := by simp [ν]
  have nn (i) (hi : i ∈ events n m a) : (support i).Nonempty := by
    cases i with
    | inl z => exact Finset.image_nonempty.mpr univ_nonempty
    | inr S =>
      have hs : S.card = a := (mem_powersetCard.mp (inr_mem_disjSum.mp hi)).2
      exact Finset.powersetCard_nonempty.mpr (hs ▸ ha)
  obtain ⟨f,hf⟩ := avoid ν (events n m a) support shade nn q hq (by
    intro t
    let red := fun l ↦ (tuples n l).filter (fun x ↦ t ∈ sides x)
    let blue := (univ.powersetCard a : Finset (Finset (Fin n))).filter (fun S ↦ t ∈ S.powersetCard 2)
    have split : (events n m a).filter (fun i ↦ t ∈ support i) =
        ((range (m-2)).sigma red).disjSum blue := by
      ext i
      rw [Finset.mem_filter]
      cases i <;> simp only [events,inl_mem_disjSum,inr_mem_disjSum,support,blue,red,mem_sigma,Finset.mem_filter,and_assoc]
    rw [split,sum_disjSum,sum_sigma]
    dsimp only [support,shade,Sum.elim_inl,Sum.elim_inr]
    rw [h₀,h₁]
    have hr : ∀ l, ∑ x ∈ red l, p^(sides x).card/q^((sides x).card-1) ≤
        (4:ℝ)*(l+3)*(n:ℝ)^(l+1)*(p^(l+3)/q^(l+2)) := by
      intro l
      have hfix (x) (hx : x ∈ red l) : (sides x).card = l+3 :=
        cycle_card x (mem_filter.mp (mem_filter.mp hx).1).2
      calc
        _ = ∑ _x ∈ red l, p^(l+3)/q^(l+2) := by
          apply sum_congr rfl; intro x hx; rw [hfix x hx]; rfl
        _ = ((red l).card:ℝ) * _ := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast per_edge n l t) (by positivity)
    have hb : ∑ S ∈ blue, (1-p)^(S.powersetCard 2).card/q^((S.powersetCard 2).card-1) ≤
        (2:ℝ)^n*((1-p)^(a.choose 2)/q^(a.choose 2-1)) := by
      calc
        _ = ∑ _S ∈ blue, (1-p)^(a.choose 2)/q^(a.choose 2-1) := by
          apply sum_congr rfl
          intro S hS
          rw [card_powersetCard,(mem_powersetCard.mp (mem_filter.mp hS).1).2]
        _ = (blue.card:ℝ) * _ := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (show blue.card ≤ 2^n by
          simpa using blue.card_le_univ)) (div_nonneg (pow_nonneg (sub_nonneg.mpr hp') _) (pow_pos hq _).le)
    exact (add_le_add (sum_le_sum (fun l _ ↦ hr l)) hb).trans budget)
  refine ⟨graph f,girth (fun l hl x hx ↦ hf (.inl ⟨l,x⟩)
    (inl_mem_disjSum.mpr (mem_sigma.mpr ⟨mem_range.mpr hl,hx⟩)) (subset_univ _)),?_⟩
  intro S hS
  by_contra! h
  obtain ⟨s,hs,hsc⟩ := le_card_iff_exists_subset_card.mp h
  have hh := hf (.inr s) (inr_mem_disjSum.mpr (mem_powersetCard.mpr ⟨subset_univ _,hsc⟩)) (subset_univ _)
  change ¬ ∀ t ∈ s.powersetCard 2, f t = false at hh
  push Not at hh
  obtain ⟨t,ht,hf⟩ := hh
  obtain ⟨ht,hc⟩ := mem_powersetCard.mp ht
  obtain ⟨x,y,hxy,rfl⟩ := card_eq_two.mp hc
  exact hS (hs (ht (by simp))) (hs (ht (by simp))) hxy ⟨hxy,by simpa using hf⟩

private lemma feasible {n m k : ℕ} (hk : 1 ≤ k)
    (hn : 16*(k:ℝ)^2 ≤ n)
    (room : 16*(m:ℝ)^2*(16*(k:ℝ)^2)^m ≤ n) :
    ∃ G : SimpleGraph (Fin n), (m:ℕ∞) < G.egirth ∧
      ∀ S : Finset (Fin n), G.IsIndepSet S → S.card < n/k + 1 := by
  have hk' : 1 ≤ (k:ℝ) := by exact_mod_cast hk
  have hk0 : 0 < (k:ℝ) := by linarith
  have hn0 : 0 < (n:ℝ) := by nlinarith [sq_nonneg ((k:ℝ)-1)]
  let D := 8*(k:ℝ)^2
  let p := D/n
  let q := 1-p/2
  have hD : 8 ≤ D := by dsimp [D]; nlinarith [sq_nonneg ((k:ℝ)-1)]
  have hp : 0 < p := div_pos (by linarith) hn0
  have hp1 : p ≤ 1/2 := (div_le_iff₀ hn0).mpr (by dsimp [D]; linarith)
  have hq : 1/2 ≤ q := by dsimp [q]; linarith
  have hq0 : 0 < q := by linarith
  have hq1 : q ≤ 1 := by dsimp [q]; linarith
  have red : redTotal n m p q ≤ p/4 := by
    have term (l : ℕ) (hl : l ∈ range (m-2)) :
        (4:ℝ)*(l+3)*(n:ℝ)^(l+1)*(p^(l+3)/q^(l+2)) ≤
          (4:ℝ)*m*(2*D)^m/(n:ℝ)^2 := by
      have hl' := mem_range.mp hl
      have hlm : l+3 ≤ m := by omega
      have h2 : 1/q ≤ 2 := (div_le_iff₀ hq0).mpr (by linarith)
      have ht : (n:ℝ)^(l+1)*p^(l+3) = D^(l+3)/(n:ℝ)^2 := by
        dsimp [p]
        rw [div_pow]
        rw [show l+3=(l+1)+2 by omega, pow_add D, pow_add (n:ℝ)]
        field_simp
        rw [← pow_add]
      have hpow : D^(l+3)*(1/q)^(l+2) ≤ (2*D)^m := by
        calc
          _ ≤ D^(l+3)*2^(l+2) := by gcongr
          _ ≤ D^(l+3)*2^(l+3) := by gcongr <;> norm_num
          _ = (2*D)^(l+3) := by rw [mul_pow (2:ℝ) D]; exact mul_comm ..
          _ ≤ _ := pow_le_pow_right₀ (by linarith) hlm
      calc
        _ = 4*(l+3)*(D^(l+3)*(1/q)^(l+2))/(n:ℝ)^2 := by
          calc
            _ = 4*(l+3)*((n:ℝ)^(l+1)*p^(l+3))*(1/q)^(l+2) := by rw [one_div,inv_pow]; ring
            _ = _ := by rw [ht]; ring
        _ ≤ _ := by gcongr; exact_mod_cast hlm
    have hsum := sum_le_sum (fun l h ↦ term l h)
    simp only [sum_const,card_range,nsmul_eq_mul] at hsum
    calc
      _ ≤ _ := hsum
      _ ≤ (m:ℝ)*(4*m*(2*D)^m/(n:ℝ)^2) := by
        apply mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le m 2) (by positivity)
      _ ≤ p/4 := by
        have hbase : 2*D = 16*(k:ℝ)^2 := by dsimp [D]; ring
        rw [hbase]; dsimp [p]
        field_simp
        nlinarith [mul_le_mul_of_nonneg_right (show 1 ≤ D by linarith) hn0.le]
  let a := n/k+1
  let b := n/k
  have hb : (b:ℝ)*k ≤ n := by exact_mod_cast Nat.div_mul_le_self n k
  have hb' : (n:ℝ) < ((b:ℝ)+1)*k := by
    have hh := Nat.lt_mul_div_succ n (show 0 < k by omega)
    exact_mod_cast (by simpa [b,mul_comm] using hh : n < (b+1)*k)
  have hnk : 16*(k:ℝ) ≤ n := by nlinarith [sq_nonneg ((k:ℝ)-1)]
  have hb9 : 7*(n:ℝ)/8 ≤ (b:ℝ)*k := by linarith
  have ha : 2 ≤ a := by
    have hbk : 1 ≤ b := (Nat.one_le_div_iff (by omega)).mpr (by exact_mod_cast (show (k:ℝ) ≤ n by linarith))
    dsimp [a,b] at *; omega
  let c := a.choose 2
  have hc : 0 < c := Nat.choose_pos ha
  have hchoose : 2*(c:ℝ) = (b:ℝ)*((b:ℝ)+1) := by
    have hh := Nat.descFactorial_eq_factorial_mul_choose (b+1) 2
    simp only [Nat.descFactorial_succ,Nat.descFactorial_zero,Nat.sub_zero,Nat.add_sub_cancel,mul_one] at hh
    exact_mod_cast (by simpa [a,b,c,Nat.factorial] using hh.symm : 2*c = b*(b+1))
  have rate : 3*(n:ℝ)/2 ≤ p*c/2 := by
    have hs := mul_self_le_mul_self (by positivity) hb9
    have hs' := congrArg (fun z : ℝ ↦ z*(k:ℝ)^2) hchoose
    dsimp [p,D]
    rw [div_mul_eq_mul_div,div_div]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg (show 0 ≤ (b:ℝ) by positivity) (sq_nonneg (k:ℝ))]
  have bounded : (1-p)^c/q^(c-1) ≤ Real.exp (-3*(n:ℝ)/2) := by
    have h' : 1-p ≤ q^2 := by dsimp [q]; nlinarith [sq_nonneg p]
    have expq : q ≤ Real.exp (-(p/2)) := by dsimp [q]; linarith [Real.add_one_le_exp (-(p/2))]
    calc
      _ ≤ (q^2)^c/q^(c-1) := by gcongr; linarith
      _ = q^c*q := by
        apply (div_eq_iff (pow_ne_zero _ hq0.ne')).mpr
        rw [← pow_mul,mul_assoc,← pow_succ',← pow_add]; congr 1; omega
      _ ≤ q^c*1 := by gcongr
      _ ≤ (Real.exp (-(p/2)))^c := by rw [mul_one]; gcongr
      _ ≤ _ := by rw [← Real.exp_nat_mul]; apply Real.exp_le_exp.mpr; linarith
  have blue : (2:ℝ)^n*((1-p)^c/q^(c-1)) ≤ p/4 := by
    calc
      _ ≤ (Real.exp 1)^n * Real.exp (-3*(n:ℝ)/2) := by
        apply mul_le_mul (pow_le_pow_left₀ (by norm_num) (show (2:ℝ) ≤ Real.exp 1 by linarith [Real.add_one_le_exp (1:ℝ)]) n) bounded
        · exact div_nonneg (pow_nonneg (by linarith) _) (pow_pos hq0 _).le
        · positivity
      _ = 1 / Real.exp ((n:ℝ)/2) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, show (n:ℝ)*1 + -3*n/2 = -(n/2:ℝ) by ring, Real.exp_neg,one_div]
      _ ≤ 2/(n:ℝ) := by
        apply (div_le_div_iff₀ (Real.exp_pos _) hn0).mpr
        linarith [Real.add_one_le_exp ((n:ℝ)/2)]
      _ ≤ p/4 := by dsimp [p]; field_simp; linarith
  apply construct n m a ha p q hp.le (by linarith) hq0
  dsimp only [q]
  linarith

open SimpleGraph
open scoped Classical

private def goodSet {V : Type} (G : SimpleGraph V) (s : Finset V) (k : ℕ) : Prop :=
  ∃ I ⊆ s, G.IsIndepSet (I : Set V) ∧ s.card ≤ k*I.card

private lemma lift_good {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (T : Finset V) (S : Finset T)
    (k : ℕ) (h : goodSet G (S.image Subtype.val) k) : goodSet (G.induce (T:Set V)) S k := by
  classical
  obtain ⟨I,hi,ind,hs⟩ := h
  let J := S.filter (fun x ↦ x.val ∈ I)
  have himage : J.image Subtype.val = I := by
    ext v
    constructor
    · intro hv
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hv
      exact (mem_filter.mp hx).2
    · intro hv
      obtain ⟨x,hx,rfl⟩ := mem_image.mp (hi hv)
      exact mem_image.mpr ⟨x,mem_filter.mpr ⟨hx,hv⟩,rfl⟩
  have hc := congrArg Finset.card himage
  rw [card_image_of_injective _ Subtype.val_injective] at hc hs
  refine ⟨J,filter_subset _ _,?_,by simpa [hc] using hs⟩
  intro x hx y hy hxy
  exact ind (mem_filter.mp hx).2 (mem_filter.mp hy).2 (fun he ↦ hxy (Subtype.ext he))

private lemma image_indep {V : Type} [DecidableEq V] (G : SimpleGraph V) (T : Finset V) {S : Finset T}
    (hi : (G.induce (T : Set V)).IsIndepSet (S : Set T)) :
    G.IsIndepSet (↑(S.image Subtype.val) : Set V) := by
  rintro x hx y hy hxy
  obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
  obtain ⟨v,hv,rfl⟩ := mem_image.mp hy
  exact hi hu hv (fun he ↦ hxy (congrArg Subtype.val he))

private lemma of_coloring {V : Type} [Fintype V] (G : SimpleGraph V) (T : Finset V)
    (c : (G.induce (T : Set V)).Coloring (Fin 2)) : goodSet G T 2 := by
  classical
  let f := fun i : Fin 2 ↦ univ.filter (fun x : T ↦ c x=i)
  obtain ⟨a,ha,hm⟩ := Finset.exists_max_image (univ : Finset (Fin 2)) (fun i ↦ (f i).card) univ_nonempty
  have hc : Fintype.card T = ∑ i, (f i).card := by
    simpa only [card_univ] using (card_eq_sum_card_fiberwise
      (s:=univ) (t:=univ) (f:=fun x : T ↦ c x) (fun _ _ ↦ mem_univ _))
  have hh : (G.induce (T:Set V)).IsIndepSet (f a : Set T) := by
    intro x hx y hy hxy hadj
    exact c.valid hadj ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm)
  refine ⟨(f a).image Subtype.val,?_,image_indep G T hh,?_⟩
  · rintro x hx
    obtain ⟨v,_,rfl⟩ := mem_image.mp hx
    exact v.2
  · rw [card_image_of_injective _ Subtype.val_injective]
    have he := sum_le_sum (s:=(univ : Finset (Fin 2))) (fun i hi ↦ hm i hi)
    simpa only [Fintype.card_coe] using (show Fintype.card T ≤ 2*(f a).card by
      rw [hc]; simpa [Nat.mul_comm] using he)

private lemma forest_pieces {V : Type} [Fintype V] (G : SimpleGraph V) (T : Finset V)
    {m : ℕ} (hg : (m:ℕ∞)<G.egirth) (hs : T.card ≤ m) : goodSet G T 2 := by
  classical
  apply of_coloring
  apply Nonempty.some
  apply SimpleGraph.IsAcyclic.colorable_two
  intro a w hcyc
  have hw := hcyc.support_nodup.length_le_card
  have hlen : w.length ≤ T.card := by simpa [List.length_tail] using hw
  have hsub : (G.induce (T:Set V)) ⊑ G := ⟨SimpleGraph.Copy.induce G _⟩
  have hh := hg.trans_le (hsub.egirth_le.trans (SimpleGraph.egirth_le_length hcyc))
  exact (not_lt_of_ge (hlen.trans hs)) (ENat.natCast_lt_natCast.mp hh)

private lemma small_critical {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (bad : ¬goodSet G univ k) :
    ∃ T : Finset V, ¬goodSet G T k ∧ ∀ s ⊆ T, goodSet G s (k+1) := by
  classical
  let D := univ.filter (fun s : Finset V ↦ ¬goodSet G s k)
  obtain ⟨T,hT,hmin⟩ := exists_min_image D Finset.card ⟨univ,mem_filter.mpr ⟨mem_univ _,bad⟩⟩
  have hproper (s : Finset V) (hs : s.card < T.card) : goodSet G s k := by
    by_contra h
    exact (not_le_of_gt hs) (hmin s (mem_filter.mpr ⟨mem_univ _,h⟩))
  refine ⟨T,(mem_filter.mp hT).2,?_⟩
  intro s hs
  by_cases he : s.card<T.card
  · obtain ⟨I,hI,hi,hc⟩ := hproper s he
    exact ⟨I,hI,hi,hc.trans (Nat.mul_le_mul_right _ (by omega))⟩
  · have hh := card_le_card hs
    have hne : s.Nonempty := by
      by_contra hn
      have hem : s=∅ := not_nonempty_iff_eq_empty.mp hn
      have : T=∅ := card_eq_zero.mp (by rw [hem,card_empty] at he; omega)
      exact (mem_filter.mp hT).2 (by rw [this]; exact ⟨∅,by simp,by simp,by simp⟩)
    obtain ⟨x,hx⟩ := hne
    obtain ⟨I,hI,hi,hc⟩ := hproper (s.erase x) (by rw [card_erase_of_mem hx]; have := card_pos.mpr ⟨x,hx⟩; omega)
    by_cases hn : I.Nonempty
    · refine ⟨I,hI.trans (erase_subset _ _),hi,?_⟩
      rw [card_erase_of_mem hx] at hc
      rw [Nat.add_mul,one_mul]
      have := card_pos.mpr hn
      omega
    · have hi0 : I.card=0 := by simp [not_nonempty_iff_eq_empty.mp hn]
      rw [card_erase_of_mem hx,hi0,mul_zero] at hc
      exact ⟨{x},singleton_subset_iff.mpr hx,by simp,by simp; omega⟩

private def dual {V : Type} [Fintype V] (G : SimpleGraph V) (w : V → ℝ) : Prop :=
  (∀ v, 0 ≤ w v) ∧ ∀ s : Finset V, G.IsIndepSet (s:Set V) → ∑ v ∈ s, w v ≤ 1

private lemma dual_le {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {w : V → ℝ}
    (hw : dual G w) : ∑ v, w v ≤ G.fractionalChromaticNumber := by
  classical
  apply le_csInf G.fractionalColoringWeights_nonempty
  rintro t ⟨f,hf,rfl⟩
  have scaled (s : Finset V) : (∑ v ∈ s,w v)*f s ≤ f s := by
    by_cases hz : f s=0
    · simp [hz]
    · simpa using mul_le_mul_of_nonneg_right (hw.2 s (hf.indep s hz)) (hf.nonneg s)
  calc
    _ ≤ ∑ v, w v * ∑ s ∈ univ.filter (fun s : Finset V ↦ v ∈ s), f s :=
      sum_le_sum fun v _ ↦ by simpa using mul_le_mul_of_nonneg_left (hf.cover v) (hw.1 v)
    _ = ∑ s, (∑ v ∈ s,w v)*f s := by
      simp_rw [Finset.sum_filter,mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro s _
      rw [sum_mul]
      simp_rw [mul_ite,mul_zero]
      rw [←Finset.sum_filter]
      simp
    _ ≤ _ := sum_le_sum fun s _ ↦ scaled s

private lemma layer (k m : ℕ) (hk : 1 ≤ k) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (w : V → ℝ), dual G w ∧ k ≤ ∑ v,w v ∧
      (∀ s, goodSet G s (k+1)) ∧ ∀ s : Finset V, s.card ≤ m → goodSet G s 2 := by
  classical
  let n := 16*(k+1)^2 + 16*m^2*(16*(k+1)^2)^m + 1
  have hn : 0<n := by dsimp [n]; omega
  obtain ⟨G,hg,hi⟩ := feasible (n:=n) (m:=m) (k:=k+1) (by omega)
    (by exact_mod_cast (show 16*(k+1)^2 ≤ n by dsimp [n]; omega))
    (by exact_mod_cast (show 16*m^2*(16*(k+1)^2)^m ≤ n by dsimp [n]; omega))
  have bad : ¬goodSet G univ k := by
    rintro ⟨I,_,hI,hc⟩
    simp only [card_univ,Fintype.card_fin] at hc
    have h := (Nat.mul_le_mul_right (k+1) (Nat.le_of_lt_succ (hi I hI))).trans (Nat.div_mul_le_self _ _)
    rw [Nat.mul_add_one,Nat.mul_comm I.card k] at h
    have hz : I.card=0 := by omega
    simp [hz] at hc
  obtain ⟨T,ht,hcover⟩ := small_critical G k bad
  let F := G.induce (T:Set (Fin n))
  have hpos : 0<T.card := by
    by_contra! hz
    have h0 : T=∅ := card_eq_zero.mp (by omega)
    apply ht
    rw [h0]
    exact ⟨∅,by simp,by simp,by simp⟩
  have hr : 0 < (T.card:ℝ) := by exact_mod_cast hpos
  refine ⟨T,inferInstance,F,(fun _ ↦ (k:ℝ)/T.card),⟨fun _ ↦ by positivity,?_⟩,?_,?_,?_⟩
  · intro s hs
    have him : s.image Subtype.val ⊆ T := by
      intro v hv
      obtain ⟨u,_,rfl⟩ := mem_image.mp hv
      exact u.2
    have hsmall : k*(s.image Subtype.val).card < T.card := by
      by_contra! h
      exact ht ⟨_,him,image_indep G T hs,h⟩
    rw [card_image_of_injective _ Subtype.val_injective] at hsmall
    have hreal : (k:ℝ)*s.card < T.card := by exact_mod_cast hsmall
    simp only [sum_const,nsmul_eq_mul]
    rw [←mul_div_assoc,div_le_iff₀ hr]
    linarith
  · simp [hr.ne',mul_div_cancel₀]
  · intro s
    apply lift_good
    apply hcover
    intro v hv
    obtain ⟨u,_,rfl⟩ := mem_image.mp hv
    exact u.2
  · intro s hs
    apply forest_pieces F s (hg.trans_le ((show F ⊑ G from ⟨SimpleGraph.Copy.induce G _⟩).egirth_le)) hs

private def joined {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V ⊕ W) :=
  (Gᶜ.sum Hᶜ)ᶜ

private lemma join_indep {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W} (s : Finset (V⊕W))
    (hs : (joined G H).IsIndepSet (s:Set (V⊕W))) :
    G.IsIndepSet (s.toLeft:Set V) ∧ H.IsIndepSet (s.toRight:Set W) ∧
      (s.toLeft=∅ ∨ s.toRight=∅) := by
  classical
  have leftAdj {u v : V} (h : G.Adj u v) : (joined G H).Adj (Sum.inl u) (Sum.inl v) := by
    simpa [joined,SimpleGraph.compl_adj,h.ne] using h
  have rightAdj {u v : W} (h : H.Adj u v) : (joined G H).Adj (Sum.inr u) (Sum.inr v) := by
    simpa [joined,SimpleGraph.compl_adj,h.ne] using h
  refine ⟨?_,?_,?_⟩
  · intro u hu v hv huv ha
    exact hs (mem_toLeft.mp hu) (mem_toLeft.mp hv) (fun he ↦ huv (Sum.inl.inj he)) (leftAdj ha)
  · intro u hu v hv huv ha
    exact hs (mem_toRight.mp hu) (mem_toRight.mp hv) (fun he ↦ huv (Sum.inr.inj he)) (rightAdj ha)
  · by_contra! he
    obtain ⟨u,hu⟩ := he.1
    obtain ⟨v,hv⟩ := he.2
    exact hs (mem_toLeft.mp hu) (mem_toRight.mp hv) (by simp) (by simp [joined,SimpleGraph.compl_adj])

private lemma joined_dual {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    {p : V → ℝ} {q : W → ℝ} (hp : dual G p) (hq : dual H q) : dual (joined G H) (Sum.elim p q) := by
  constructor
  · rintro (v|v)
    · exact hp.1 v
    · exact hq.1 v
  · intro s hs
    obtain ⟨hl,hr,hh⟩ := join_indep s hs
    rw [sum_sum_eq_sum_toLeft_add_sum_toRight]
    rcases hh with he|he
    · simpa [he] using hq.2 _ hr
    · simpa [he] using hp.2 _ hl

private lemma join_left {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W} {I : Finset V}
    (hI : G.IsIndepSet (I:Set V)) : (joined G H).IsIndepSet (↑(I.disjSum (∅ : Finset W)) : Set (V ⊕ W)) := by
  classical
  rintro (x|x) hx (y|y) hy hxy hadj <;> simp_all [joined,SimpleGraph.compl_adj]
  exact hI hx hy hxy hadj

private lemma join_right {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W} {I : Finset W}
    (hI : H.IsIndepSet (I:Set W)) : (joined G H).IsIndepSet (↑((∅ : Finset V).disjSum I) : Set (V ⊕ W)) := by
  classical
  rintro (x|x) hx (y|y) hy hxy hadj <;> simp_all [joined,SimpleGraph.compl_adj]
  exact hI hx hy hxy hadj

private lemma add_parts {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W} (s : Finset (V ⊕ W))
    {a b : ℕ} (hl : goodSet G s.toLeft a) (hr : goodSet H s.toRight b) :
    goodSet (joined G H) s (a+b) := by
  classical
  obtain ⟨I,hi,hI,ci⟩ := hl
  obtain ⟨J,hj,hJ,cj⟩ := hr
  have hcs := card_toLeft_add_card_toRight (u:=s)
  by_cases he : I.card ≤ J.card
  · refine ⟨(∅ : Finset V).disjSum J,disjSum_subset.mpr ⟨empty_subset _,hj⟩,join_right hJ,?_⟩
    simp only [card_disjSum,card_empty,zero_add,add_mul]
    have hle := ci.trans (Nat.mul_le_mul_left a he)
    omega
  · refine ⟨I.disjSum (∅ : Finset W),disjSum_subset.mpr ⟨hi,empty_subset _⟩,join_left hI,?_⟩
    simp only [card_disjSum,card_empty,add_zero,add_mul]
    have hle := cj.trans (Nat.mul_le_mul_left b (by omega : J.card≤I.card))
    omega

private lemma assemble (k r : ℕ) (hk : 1≤k) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (w : V → ℝ), dual G w ∧
      (r:ℝ)*k ≤ ∑ v,w v ∧ ∀ s, goodSet G s (2*(k+1)+2*r) := by
  classical
  induction r with
  | zero =>
    refine ⟨Fin 0,inferInstance,⊥,(fun _ ↦ 0),⟨by simp,by simp⟩,by simp,?_⟩
    intro s
    have hz : s=∅ := eq_empty_iff_forall_notMem.mpr fun v ↦ Fin.elim0 v
    exact ⟨∅,empty_subset _,by simp,by simp [hz]⟩
  | succ r ih =>
    obtain ⟨V,instV,G,w,hw,ht,hs⟩ := ih
    obtain ⟨W,instW,H,p,hp,hu,ha,hb⟩ := layer k (Fintype.card V) hk
    refine ⟨V⊕W,inferInstance,joined G H,Sum.elim w p,joined_dual hw hp,?_,?_⟩
    · rw [Fintype.sum_sum_type,Nat.cast_add_one,add_mul,one_mul]
      exact add_le_add ht hu
    · intro s
      by_cases hsize : s.toRight.card ≤ Fintype.card V
      · have h := add_parts s (hs s.toLeft) (hb s.toRight hsize)
        rw [show 2*(k+1)+2*(r+1)=2*(k+1)+2*r+2 by omega]
        exact h
      · obtain ⟨J,hJ,hi,hc⟩ := ha s.toRight
        refine ⟨(∅:Finset V).disjSum J,disjSum_subset.mpr ⟨empty_subset _,hJ⟩,join_right hi,?_⟩
        simp only [card_disjSum,card_empty,zero_add]
        have hleft := card_le_univ s.toLeft
        have hs' : s.card ≤ (2*(k+1))*J.card := by
          rw [←card_toLeft_add_card_toRight,Nat.mul_assoc]
          omega
        exact hs'.trans (Nat.mul_le_mul_right _ (by omega))

private lemma ratio_bound {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {k : ℕ} (hk : ∀ s, goodSet G s k) : HallRatioConjecture.hallRatio G ≤ k := by
  classical
  apply Real.sSup_le
  · rintro y ⟨s,hs,rfl⟩
    obtain ⟨I,hI,hi,hc⟩ := hk s
    let J : Finset s := univ.filter (fun x ↦ x.val ∈ I)
    have him : J.image Subtype.val = I := by
      ext x
      constructor
      · intro hx
        obtain ⟨v,hv,rfl⟩ := mem_image.mp hx
        exact (mem_filter.mp hv).2
      · intro hx
        exact mem_image.mpr ⟨⟨x,hI hx⟩,mem_filter.mpr ⟨mem_univ _,hx⟩,rfl⟩
    have hj : (G.induce (s:Set V)).IsIndepSet (J:Set s) := by
      intro x hx y hy hxy
      exact hi (mem_filter.mp hx).2 (mem_filter.mp hy).2 (fun he ↦ hxy (Subtype.ext he))
    have he := congrArg Finset.card him
    rw [card_image_of_injective _ Subtype.val_injective] at he
    have hb := hj.card_le_indepNum
    rw [he] at hb
    have hn := hc.trans (Nat.mul_le_mul_left k hb)
    apply div_le_of_le_mul₀ (by positivity) (by positivity)
    exact_mod_cast hn
  · positivity

theorem separation (C : ℝ) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      C * HallRatioConjecture.hallRatio G < G.fractionalChromaticNumber := by
  classical
  obtain ⟨k,hk⟩ := exists_nat_gt (6*(max C 1))
  have hk1 : 1≤k := by
    have hr := le_max_right C 1
    by_contra! he
    have : k=0 := by omega
    rw [this] at hk
    norm_num at hk
    linarith
  obtain ⟨V,instV,G,w,hw,hh,ha⟩ := assemble k k hk1
  refine ⟨V,instV,inferInstance,G,?_⟩
  have upper := ratio_bound G ha
  have lower := hh.trans (dual_le G hw)
  have hu : HallRatioConjecture.hallRatio G ≤ 6*(k:ℝ) := upper.trans (by
    push_cast
    have hh' : (1:ℝ) ≤ k := by exact_mod_cast hk1
    linarith)
  by_cases hc : C < 0
  · have nn : 0 ≤ HallRatioConjecture.hallRatio G := by
      apply Real.sSup_nonneg
      rintro _ ⟨s,_,rfl⟩
      positivity
    have hnn := mul_nonpos_of_nonpos_of_nonneg hc.le nn
    have hk' : (0:ℝ) < k := by exact_mod_cast hk1
    nlinarith
  · have hC := le_max_left C 1
    have hr : C*6 < k := by linarith
    have hk' : (0:ℝ) < k := by exact_mod_cast hk1
    calc
      _ ≤ C*(6*k) := mul_le_mul_of_nonneg_left hu (by linarith)
      _ = (C*6)*k := by ring
      _ < (k:ℝ)*k := mul_lt_mul_of_pos_right hr hk'
      _ ≤ _ := lower

end SparseGraph

theorem OMA.solution : type_of% @HallRatioConjecture.hall_ratio_conjecture.variants.unbounded := SparseGraph.separation