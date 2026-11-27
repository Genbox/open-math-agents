import FormalConjectures.ErdosProblems.«827»
import Mathlib.Data.Nat.Choose.Bounds

/-! A finite counting bound for subsets with distinct circumradii. -/

open Erdos827 EuclideanGeometry Finset Asymptotics Filter

namespace OMA.Erdos827Counting

private theorem two_distances {a b c d e : ℝ²} {r s : ℝ}
    (hab : a ≠ b) (hcd : c ≠ d)
    (ha : dist c a = r) (hb : dist d a = r) (he : dist e a = r)
    (ha' : dist c b = s) (hb' : dist d b = s) (he' : dist e b = s) :
    e = c ∨ e = d :=
  eq_of_dist_eq_of_dist_eq_of_finrank_eq_two (by simp) hab hcd ha hb he ha' hb' he'

private theorem radius_unique_at_insert {E : Finset ℝ²} (hE : E.card = 2)
    {x : ℝ²} (hx : x ∉ E) {r s : ℝ}
    (h₁ : OnCircleOfRadius (insert x E) r) (h₂ : OnCircleOfRadius (insert x E) s) :
    r = s := by
  classical
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hE
  obtain ⟨c, hc⟩ := h₁
  obtain ⟨d, hd⟩ := h₂
  have hax : a ∈ (insert x {a, b} : Finset ℝ²) := by simp
  have hbx : b ∈ (insert x {a, b} : Finset ℝ²) := by simp
  have hxx : x ∈ (insert x {a, b} : Finset ℝ²) := by simp
  by_cases he : c = d
  · exact (hc x hxx).symm.trans (he ▸ hd x hxx)
  · exact False.elim (hx (by
      rcases two_distances he hab (hc a hax) (hc b hbx) (hc x hxx)
        (hd a hax) (hd b hbx) (hd x hxx) with h | h <;> simp [h]))

private theorem three_insert_impossible {X E : Finset ℝ²}
    (hX : NoFourConcyclic (X : Set ℝ²)) (hEX : E ⊆ X) (hE : E.card = 2)
    {x y z : ℝ²} (hxX : x ∈ X) (hyX : y ∈ X) (hzX : z ∈ X)
    (hx : x ∉ E) (hy : y ∉ E) (hz : z ∉ E)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {r : ℝ}
    (h₁ : OnCircleOfRadius (insert x E) r) (h₂ : OnCircleOfRadius (insert y E) r)
    (h₃ : OnCircleOfRadius (insert z E) r) : False := by
  classical
  have centers_ne {u v c : ℝ²} (huX : u ∈ X) (hvX : v ∈ X)
      (hu : u ∉ E) (hv : v ∉ E) (huv : u ≠ v)
      (huc : ∀ w ∈ insert u E, dist w c = r)
      (hvc : ∀ w ∈ insert v E, dist w c = r) : False := by
    apply hX (↑(insert u (insert v E)) : Set ℝ²)
    · intro w hw
      obtain rfl | hw := Finset.mem_insert.mp (Finset.mem_coe.mp hw)
      · exact huX
      · obtain rfl | hw := Finset.mem_insert.mp hw
        · exact hvX
        · exact hEX hw
    · rw [Set.ncard_coe_finset, Finset.card_insert_of_notMem (by simp [huv, hu]),
        Finset.card_insert_of_notMem hv, hE]
    · refine ⟨c, r, ?_⟩
      intro w hw
      obtain rfl | hw := Finset.mem_insert.mp (Finset.mem_coe.mp hw)
      · exact huc _ (Finset.mem_insert_self ..)
      · exact hvc w hw
  obtain ⟨c, hc⟩ := h₁
  obtain ⟨d, hd⟩ := h₂
  obtain ⟨e, he⟩ := h₃
  have hcd : c ≠ d := fun hh => centers_ne hxX hyX hx hy hxy hc (hh ▸ hd)
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hE
  have ha (w : ℝ²) : a ∈ (insert w {a, b} : Finset ℝ²) := by simp
  have hb (w : ℝ²) : b ∈ (insert w {a, b} : Finset ℝ²) := by simp
  obtain h | h := two_distances hab hcd
    ((dist_comm _ _).trans (hc a (ha x))) ((dist_comm _ _).trans (hd a (ha y)))
    ((dist_comm _ _).trans (he a (ha z))) ((dist_comm _ _).trans (hc b (hb x)))
    ((dist_comm _ _).trans (hd b (hb y))) ((dist_comm _ _).trans (he b (hb z)))
  · exact centers_ne hxX hzX hx hz hxz hc (h ▸ he)
  · exact centers_ne hyX hzX hy hz hyz hd (h ▸ he)

private theorem radius_unique {T : Finset ℝ²} (hT : T.card = 3) {r s : ℝ}
    (hr : OnCircleOfRadius T r) (hs : OnCircleOfRadius T s) : r = s := by
  classical
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  have hE : (T.erase p).card = 2 := by
    have := Finset.card_erase_add_one hp
    omega
  exact radius_unique_at_insert hE (notMem_erase p T)
    (by simpa [insert_erase hp] using hr) (by simpa [insert_erase hp] using hs)

private theorem card_two_fiber {X : Type*} [Fintype X] {k : ℕ}
    (B : Finset (Fin k → X)) (i : Fin k)
    (h : ∀ f g t, f ∈ B → g ∈ B → t ∈ B →
      (∀ j, j ≠ i → f j = g j) → (∀ j, j ≠ i → f j = t j) →
      f ≠ g → f ≠ t → g ≠ t → False) :
    B.card ≤ 2 * Fintype.card X ^ (k - 1) := by
  classical
  let I := {j : Fin k // j ≠ i}
  let restriction (g : Fin k → X) : I → X := fun j => g j
  let fiber (f : I → X) := B.filter (fun g => restriction g = f)
  have hb : B ⊆ univ.biUnion fiber := by
    intro g hg
    exact mem_biUnion.mpr ⟨restriction g, mem_univ _, by simp [fiber, hg]⟩
  have hs (f : I → X) : (fiber f).card ≤ 2 := by
    by_contra! hcontra
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := two_lt_card_iff.mp hcontra
    have ha' := mem_filter.mp ha
    have hb' := mem_filter.mp hb
    have hc' := mem_filter.mp hc
    exact h a b c ha'.1 hb'.1 hc'.1
      (fun j hj => congrFun (ha'.2.trans hb'.2.symm) ⟨j, hj⟩)
      (fun j hj => congrFun (ha'.2.trans hc'.2.symm) ⟨j, hj⟩) hab hac hbc
  have hI : Fintype.card I = k - 1 := by simp [I, Fintype.card_subtype_compl]
  calc
    B.card ≤ (univ.biUnion fiber).card := card_le_card hb
    _ ≤ ∑ f, (fiber f).card := card_biUnion_le
    _ ≤ ∑ _ : I → X, 2 := sum_le_sum (fun f _ => hs f)
    _ = 2 * Fintype.card X ^ (k - 1) := by
      simp [hI, Nat.mul_comm]

private noncomputable def duplicates {k : ℕ} (X : Finset ℝ²) (i j : Fin k) :
    Finset (Fin k → ↥X) := by
  classical
  exact univ.filter (fun f => i ≠ j ∧ f i = f j)

private theorem card_duplicates {k : ℕ} (X : Finset ℝ²) (i j : Fin k) :
    (duplicates X i j).card ≤ 2 * X.card ^ (k - 1) := by
  classical
  rw [← Fintype.card_coe X]
  apply card_two_fiber (duplicates X i j) i
  intro f g t hf hg ht hfg hft hne _ _
  have hf' := (mem_filter.mp hf).2
  have hg' := (mem_filter.mp hg).2
  apply hne
  funext x
  by_cases hx : x = i
  · subst x
    exact hf'.2.trans ((hfg j hf'.1.symm).trans hg'.2.symm)
  · exact hfg x hx

private noncomputable def repeats {k : ℕ} (X : Finset ℝ²) (T U : Finset (Fin k)) :
    Finset (Fin k → ↥X) := by
  classical
  exact univ.filter (fun f => Function.Injective f ∧ T ≠ U ∧
    ∃ r, OnCircleOfRadius (T.image fun i => (f i : ℝ²)) r ∧
      OnCircleOfRadius (U.image fun i => (f i : ℝ²)) r)

private theorem card_repeats {k : ℕ} (X : Finset ℝ²)
    (hX : NoFourConcyclic (X : Set ℝ²))
    (T U : Finset (Fin k)) (hT : T.card = 3) (hU : U.card = 3) :
    (repeats X T U).card ≤ 2 * X.card ^ (k - 1) := by
  classical
  by_cases heq : T = U
  · subst U
    have h : repeats X T T = ∅ := by ext; simp [repeats]
    simp [h]
  have hns : ¬ T ⊆ U := fun h => heq (eq_of_subset_of_card_le h (by omega))
  obtain ⟨i, hiT, hiU⟩ : ∃ i ∈ T, i ∉ U := Finset.not_subset.mp hns
  rw [← Fintype.card_coe X]
  apply card_two_fiber (repeats X T U) i
  intro f g t hf hg ht hfg hft hnefg hneft hnegt
  obtain ⟨hfinj, _, r, hfr, hfur⟩ := (mem_filter.mp hf).2
  obtain ⟨hginj, _, s, hgs, hgus⟩ := (mem_filter.mp hg).2
  obtain ⟨htinj, _, q, htq, htuq⟩ := (mem_filter.mp ht).2
  let F (v : Fin k) := (f v : ℝ²)
  let G (v : Fin k) := (g v : ℝ²)
  let H (v : Fin k) := (t v : ℝ²)
  have hFinj : Function.Injective F := fun _ _ h => hfinj (Subtype.ext h)
  have hGinj : Function.Injective G := fun _ _ h => hginj (Subtype.ext h)
  have hHinj : Function.Injective H := fun _ _ h => htinj (Subtype.ext h)
  have hUG : U.image F = U.image G :=
    Finset.image_congr (fun j hj => congrArg Subtype.val (hfg j (by simpa [eq_comm] using ne_of_mem_of_not_mem hj hiU)))
  have hUH : U.image F = U.image H :=
    Finset.image_congr (fun j hj => congrArg Subtype.val (hft j (by simpa [eq_comm] using ne_of_mem_of_not_mem hj hiU)))
  have hUc : (U.image F).card = 3 := (card_image_of_injective U hFinj).trans hU
  have hrs : r = s := radius_unique hUc hfur (hUG.symm ▸ hgus)
  have hrq : r = q := radius_unique hUc hfur (hUH.symm ▸ htuq)
  subst s
  subst q
  let E := (T.erase i).image F
  have hEG : E = (T.erase i).image G :=
    Finset.image_congr (fun j hj => congrArg Subtype.val (hfg j (mem_erase.mp hj).1))
  have hEH : E = (T.erase i).image H :=
    Finset.image_congr (fun j hj => congrArg Subtype.val (hft j (mem_erase.mp hj).1))
  have hE : E.card = 2 := by
    have hcard := card_erase_add_one hiT
    rw [show E = (T.erase i).image F by rfl, card_image_of_injective _ hFinj]
    omega
  have hEX : E ⊆ X := by
    intro v hv
    obtain ⟨j, _, rfl⟩ := mem_image.mp hv
    exact (f j).2
  have hnot (K : Fin k → ℝ²) (hK : Function.Injective K) :
      K i ∉ (T.erase i).image K := by
    intro h
    obtain ⟨j, hj, hji⟩ := mem_image.mp h
    exact (mem_erase.mp hj).1 (hK hji)
  have hne {f g : Fin k → ↥X} (he : ∀ j, j ≠ i → f j = g j) (hn : f ≠ g) :
      (f i : ℝ²) ≠ (g i : ℝ²) := by
    intro hi
    apply hn
    funext j
    by_cases hj : j = i
    · subst j
      exact Subtype.ext hi
    · exact he j hj
  have hind (K : Fin k → ℝ²) : insert (K i) ((T.erase i).image K) = T.image K := by
    rw [← image_insert, insert_erase hiT]
  exact three_insert_impossible hX hEX hE (f i).2 (g i).2 (t i).2
    (hnot F hFinj) (hEG.symm ▸ hnot G hGinj) (hEH.symm ▸ hnot H hHinj)
    (hne hfg hnefg) (hne hft hneft) (hne (fun j hj => (hfg j hj).symm.trans (hft j hj)) hnegt)
    ((hind F).symm ▸ hfr) (hEG.symm ▸ (hind G).symm ▸ hgs) (hEH.symm ▸ (hind H).symm ▸ htq)

private theorem exists_good_tuple {k : ℕ} (hk : 1 ≤ k)
    (X : Finset ℝ²) (hX : NoFourConcyclic (X : Set ℝ²))
    (hcard : X.card = 6 * k ^ 6) :
    ∃ f : Fin k → ↥X, Function.Injective f ∧
      HasDistinctCircumradii (univ.image fun i => (f i : ℝ²)) := by
  classical
  let Ts := (univ : Finset (Fin k)).powersetCard 3
  let dup := (univ : Finset (Fin k × Fin k)).biUnion (fun w => duplicates X w.1 w.2)
  let rep := (Ts ×ˢ Ts).biUnion (fun w => repeats X w.1 w.2)
  let ρ := X.card ^ (k - 1)
  have hdup : dup.card ≤ (k * k) * (2 * ρ) := by
    unfold dup
    simpa [Fintype.card_prod] using
      (card_biUnion_le_card_mul (univ : Finset (Fin k × Fin k))
        (fun w => duplicates X w.1 w.2) (2 * ρ)
        (fun w _ => card_duplicates X w.1 w.2))
  have hrep : rep.card ≤ k ^ 6 * (2 * ρ) := by
    have hTs : Ts.card ≤ k ^ 3 := by
      simpa [Ts, card_powersetCard] using Nat.choose_le_pow k 3
    have hTprod : (Ts ×ˢ Ts).card ≤ k ^ 6 := by
      rw [card_product, show k ^ 6 = k ^ 3 * k ^ 3 by ring]
      exact Nat.mul_le_mul hTs hTs
    refine (card_biUnion_le_card_mul (Ts ×ˢ Ts) _ (2 * ρ) ?_).trans
      (Nat.mul_le_mul_right _ hTprod)
    intro w hw
    obtain ⟨h, h'⟩ := mem_product.mp hw
    exact card_repeats X hX w.1 w.2 (mem_powersetCard.mp h).2 (mem_powersetCard.mp h').2
  have hρ : 0 < ρ := by
    have : 0 < X.card := by rw [hcard]; positivity
    dsimp [ρ]
    positivity
  have hk2 : k * k ≤ k ^ 6 := by
    rw [← pow_two]
    exact Nat.pow_le_pow_right hk (by decide)
  have hbad : (dup ∪ rep).card < (univ : Finset (Fin k → ↥X)).card := by
    calc
      (dup ∪ rep).card ≤ dup.card + rep.card := card_union_le _ _
      _ ≤ (k ^ 6) * (2 * ρ) + (k ^ 6) * (2 * ρ) := by
        exact Nat.add_le_add (hdup.trans (Nat.mul_le_mul_right _ hk2)) hrep
      _ = (4 * k ^ 6) * ρ := by ring
      _ < X.card * ρ := by
        rw [hcard]
        exact Nat.mul_lt_mul_of_pos_right (by
          have : 0 < k ^ 6 := by positivity
          omega) hρ
      _ = (univ : Finset (Fin k → ↥X)).card := by
        simp only [card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin, ρ, ← pow_succ']
        congr 1
        omega
  obtain ⟨f, hf, hnot⟩ := exists_mem_notMem_of_card_lt_card hbad
  have hu : Function.Injective f := by
    intro i j hij
    by_contra hne
    apply hnot
    apply mem_union_left
    exact mem_biUnion.mpr ⟨(i, j), mem_univ _, mem_filter.mpr ⟨mem_univ _, hne, hij⟩⟩
  refine ⟨f, hu, ?_⟩
  intro Y hY Z hZ hy hz hyz r hr hs
  obtain ⟨T, rfl⟩ := subset_univ_image_iff.mp hY
  obtain ⟨U, rfl⟩ := subset_univ_image_iff.mp hZ
  let F (v : Fin k) := (f v : ℝ²)
  have hinj : Function.Injective F := fun _ _ h => hu (Subtype.ext h)
  have hcT : T.card = 3 := (card_image_of_injective T hinj).symm.trans hy
  have hcU : U.card = 3 := (card_image_of_injective U hinj).symm.trans hz
  have hTU : T ≠ U := fun h => hyz (h ▸ rfl)
  apply hnot
  apply mem_union_right
  exact mem_biUnion.mpr ⟨(T, U), mem_product.mpr
    ⟨mem_powersetCard.mpr ⟨subset_univ _, hcT⟩, mem_powersetCard.mpr ⟨subset_univ _, hcU⟩⟩,
    mem_filter.mpr ⟨mem_univ _, hu, hTU, r, hr, hs⟩⟩

private theorem polynomial_bound {k : ℕ} (hk : 1 ≤ k) : n k ≤ 6 * k ^ 6 := by
  classical
  refine n_le fun X hcard hgen => ?_
  obtain ⟨f, hf, hgood⟩ := exists_good_tuple hk X hgen.2 hcard
  let Y := univ.image fun i => (f i : ℝ²)
  refine ⟨Y, ?_, ?_, hgood⟩
  · intro p hp
    obtain ⟨i, _, rfl⟩ := mem_image.mp hp
    exact (f i).2
  · rw [show Y = univ.image (fun i => (f i : ℝ²)) by rfl, card_image_of_injective, card_univ,
      Fintype.card_fin]
    exact fun _ _ h => hf (Subtype.ext h)

end OMA.Erdos827Counting

open OMA.Erdos827Counting in
theorem OMA.solution : type_of% @Erdos827.erdos_827.variants.martinez_roldan_pensado := by
  refine IsBigO.of_bound 6 ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity)]
  exact_mod_cast ((polynomial_bound hk).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hk (by decide))))