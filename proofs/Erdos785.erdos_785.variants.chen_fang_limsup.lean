import FormalConjectures.ErdosProblems.«785»

/-!
A bounded excess along an unbounded sequence gives eventual uniqueness of
the additive representations. A finite shifted-pair count then controls
the first moment of one complement before any doubling gap.

The moment argument follows Yang and Zhao, arXiv:2609.13900, using finite
sets of pairs and triples throughout.

Credit: @Genbox.
-/

open Finset Filter Pointwise Erdos785
open scoped Topology

namespace OMA

open scoped Classical in
private noncomputable def trunc (A : Set ℕ) (n : ℕ) : Finset ℕ :=
  (Icc 1 n).filter (fun a => a ∈ A)

private theorem mem_trunc {A : Set ℕ} {a n : ℕ} :
    a ∈ trunc A n ↔ a ∈ A ∧ 1 ≤ a ∧ a ≤ n := by
  classical
  simp only [trunc, mem_filter, mem_Icc]
  tauto

private theorem count_trunc (A : Set ℕ) (n : ℕ) : (trunc A n).card = counting A n := by
  have h : (trunc A n : Set ℕ) = A ∩ Set.Icc 1 n := by ext a; exact mem_trunc
  rw [counting, ← h, Set.ncard_coe_finset]

private theorem trunc_mono (A : Set ℕ) : Monotone (trunc A) := by
  intro x y hxy a ha
  exact mem_trunc.mpr ⟨(mem_trunc.mp ha).1, (mem_trunc.mp ha).2.1, (mem_trunc.mp ha).2.2.trans hxy⟩

private theorem count_mono (A : Set ℕ) : Monotone (counting A) := by
  intro x y hxy
  rw [← count_trunc, ← count_trunc]
  exact card_le_card (trunc_mono A hxy)

private theorem count_atTop {A : Set ℕ} (hA : A.Infinite) (hA0 : 0 ∉ A) :
    Tendsto (counting A) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun m => ?_
  obtain ⟨S, hS, hcard⟩ := hA.exists_subset_card_eq m
  refine ⟨S.sup id, fun n hn => ?_⟩
  rw [← hcard, ← count_trunc]
  apply card_le_card
  intro a ha
  have hAa := hS ha
  exact mem_trunc.mpr ⟨hAa, Nat.pos_of_ne_zero (fun h => hA0 (h ▸ hAa)),
    (le_sup (f := id) ha).trans hn⟩

private theorem aStar_trunc {A : Set ℕ} {n : ℕ} (hne : (trunc A n).Nonempty) :
    aStar A n ∈ trunc A n ∧ trunc A (aStar A n) = trunc A n := by
  classical
  have h : IsGreatest (A ∩ Set.Icc 1 n) ((trunc A n).max' hne) :=
    ⟨mem_trunc.mp (max'_mem _ _), fun _ ha => le_max' _ _ (mem_trunc.mpr ha)⟩
  unfold aStar
  rw [h.csSup_eq]
  refine ⟨mem_trunc.mpr h.1, le_antisymm (trunc_mono A h.1.2.2) ?_⟩
  intro a ha
  exact mem_trunc.mpr ⟨(mem_trunc.mp ha).1, (mem_trunc.mp ha).2.1, h.2 (mem_trunc.mp ha)⟩

private theorem star_atTop {A : Set ℕ} (hA : A.Infinite) (hA0 : 0 ∉ A) :
    Tendsto (aStar A) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun m => ?_
  obtain ⟨a, ha, hm⟩ := hA.exists_notMem_finset (Iio m)
  have hl : m ≤ a := by simpa using hm
  refine ⟨a, fun n hn => hl.trans ?_⟩
  have he : a ∈ trunc A n :=
    mem_trunc.mpr ⟨ha, Nat.pos_of_ne_zero (fun h => hA0 (h ▸ ha)), hn⟩
  have ht := (aStar_trunc ⟨a,he⟩).2
  exact (mem_trunc.mp (ht ▸ he)).2.2

private def sumPair (p : ℕ × ℕ) := p.1 + p.2

private def onsets (A B : Set ℕ) (p : ℕ × ℕ) := p.1 ∈ A ∧ p.2 ∈ B

private noncomputable def pairs (A B : Set ℕ) (x : ℕ) :=
  trunc A x ×ˢ trunc B x

private theorem card_pairs {A B : Set ℕ} {x : ℕ} :
    (pairs A B x).card = counting A x * counting B x := by
  simp [pairs, card_product, count_trunc]

private theorem pairs_mono (A B : Set ℕ) : Monotone (pairs A B) :=
  fun _ _ h => product_subset_product (trunc_mono A h) (trunc_mono B h)

private theorem onsets_mem_pairs {A B : Set ℕ} (hA0 : 0 ∉ A) (hB0 : 0 ∉ B)
    {p : ℕ × ℕ} {x : ℕ} (hp : onsets A B p) (hx : sumPair p ≤ x) :
    p ∈ pairs A B x := by
  have h1 : p.1 ≠ 0 := fun h => hA0 (h ▸ hp.1)
  have h2 : p.2 ≠ 0 := fun h => hB0 (h ▸ hp.2)
  unfold sumPair at hx
  exact mem_product.mpr ⟨mem_trunc.mpr ⟨hp.1,by omega,by omega⟩,
    mem_trunc.mpr ⟨hp.2,by omega,by omega⟩⟩

private theorem rep_card {A B : Set ℕ} (hA0 : 0 ∉ A) (hB0 : 0 ∉ B) {x r : ℕ}
    (hr : ∀ m ≥ r, m ∈ A + B) :
    Icc r x ⊆ ((trunc A x) ×ˢ (trunc B x)).image sumPair := by
  intro n hn
  obtain ⟨hnr,hnx⟩ := mem_Icc.mp hn
  obtain ⟨a, ha, b, hb, hab⟩ := hr n hnr
  change a+b=n at hab
  have ha0 : a ≠ 0 := fun h => hA0 (h ▸ ha)
  have hb0 : b ≠ 0 := fun h => hB0 (h ▸ hb)
  exact mem_image.mpr ⟨(a,b),mem_product.mpr ⟨mem_trunc.mpr ⟨ha,by omega,by omega⟩,
    mem_trunc.mpr ⟨hb,by omega,by omega⟩⟩,hab⟩

open scoped Classical in
private noncomputable def inner (A B : Set ℕ) (x : ℕ) :=
  (pairs A B x).filter (fun p => sumPair p ≤ x)

private theorem inner_lower {A B : Set ℕ} (hA0 : 0 ∉ A) (hB0 : 0 ∉ B) {x r : ℕ}
    (hr : ∀ n ≥ r, n ∈ A+B) (hrx : r ≤ x) :
    (x:ℝ)-r ≤ (inner A B x).card := by
  have hsub : Icc r x ⊆ (inner A B x).image sumPair := by
    intro n hn
    obtain ⟨p,hp,he⟩ := mem_image.mp (rep_card hA0 hB0 hr hn)
    exact mem_image.mpr ⟨p,mem_filter.mpr ⟨hp, he ▸ (mem_Icc.mp hn).2⟩,he⟩
  have hc := (card_le_card hsub).trans card_image_le
  have hd : x-r ≤ (inner A B x).card := by rw [Nat.card_Icc] at hc; omega
  exact_mod_cast (show ((x:ℝ)-r) ≤ (inner A B x).card from by
    rw [← Nat.cast_sub hrx]; exact_mod_cast hd)

open scoped Classical in
private noncomputable def late (A B : Set ℕ) (x : ℕ) :=
  (pairs A B x).filter (fun p => ¬sumPair p ≤ x)

private theorem late_upper {A B : Set ℕ} (hA0 : 0 ∉ A) (hB0 : 0 ∉ B) {x r : ℕ}
    (hr : ∀ n ≥ r, n ∈ A+B) (hrx : r ≤ x) :
    ((late A B x).card:ℝ) ≤ (counting A x:ℝ)*counting B x-(x:ℝ)+r := by
  classical
  have he := card_filter_add_card_filter_not (s := pairs A B x) (fun p => sumPair p ≤ x)
  change (inner A B x).card + (late A B x).card = (pairs A B x).card at he
  rw [card_pairs] at he
  have he' : ((inner A B x).card:ℝ) + (late A B x).card = (counting A x:ℝ)*counting B x := by
    exact_mod_cast he
  linarith [inner_lower hA0 hB0 hr hrx]

private theorem repeats_card {α β : Type*} [DecidableEq β] (S : Finset α) (f : α → β)
    (R : Finset β) (hR : ∀ n ∈ R, 2 ≤ (S.filter (fun p => f p = n)).card) :
    R.card + (S.image f).card ≤ S.card := by
  classical
  have hS : ∀ n ∈ S.image f, 0 < (S.filter (fun p => f p = n)).card := by
    intro n hn
    obtain ⟨a,ha,he⟩ := mem_image.mp hn
    exact card_pos.mpr ⟨a,mem_filter.mpr ⟨ha,he⟩⟩
  have hRS : R ⊆ S.image f := by
    intro n hn
    obtain ⟨p,hp⟩ := card_pos.mp ((by decide : 0 < 2).trans_le (hR n hn))
    exact mem_image.mpr ⟨p,(mem_filter.mp hp).1,(mem_filter.mp hp).2⟩
  have hs := card_eq_sum_card_fiberwise (fun (a : α) ha => mem_image_of_mem f (s := S) ha)
  rw [hs]
  have he : (S.image f).filter (fun n => n ∈ R) = R :=
    by
      ext n
      exact ⟨fun hn => (mem_filter.mp hn).2,
        fun hn => mem_filter.mpr ⟨hRS hn,hn⟩⟩
  have hcard : R.card = ∑ n ∈ S.image f, if n ∈ R then 1 else 0 := by
    rw [← sum_filter, he]
    simp
  have hcard' : (S.image f).card = ∑ _ ∈ S.image f, (1:ℕ) := by simp
  conv_lhs => rw [hcard, hcard', ← sum_add_distrib]
  refine sum_le_sum fun n hn => ?_
  by_cases h : n ∈ R
  · simpa [h] using hR n h
  · simpa [h] using hS n hn

private theorem eventually_unique {A B : Set ℕ} (hA0 : 0 ∉ A) (hB0 : 0 ∉ B)
    {r : ℕ} (hr : ∀ n ≥ r, n ∈ A+B) {C : ℝ}
    (hbad : ∃ᶠ x : ℕ in atTop, (counting A x:ℝ)*counting B x-(x:ℝ) ≤ C) :
    ∃ N : ℕ, ∀ n ≥ N, ∃! p : ℕ × ℕ, onsets A B p ∧ sumPair p = n := by
  classical
  let bad : Set ℕ := {n | ∃ p q : ℕ × ℕ, p ≠ q ∧
    onsets A B p ∧ sumPair p = n ∧ onsets A B q ∧ sumPair q = n}
  have hfin : bad.Finite := by
    by_contra hinf
    obtain ⟨K,hK⟩ := exists_nat_gt (C+(r:ℝ))
    obtain ⟨R,hR,hRc⟩ := (Set.not_finite.mp hinf).exists_subset_card_eq K
    have hev := (hbad.and_eventually (eventually_ge_atTop (max r (R.sup id)))).exists
    obtain ⟨x,hcx,hX⟩ := hev
    have hx : r ≤ x := (le_max_left _ _).trans hX
    have hh : ∀ n ∈ R, 2 ≤ ((pairs A B x).filter (fun p => sumPair p = n)).card := by
      intro n hn
      obtain ⟨p,q,hp,hpa,hpe,hqa,hqe⟩ := hR hn
      have hn' := (le_sup (f := id) hn).trans ((le_max_right _ _).trans hX)
      have hp' : p ∈ pairs A B x := onsets_mem_pairs hA0 hB0 hpa (hpe ▸ hn')
      have hq' : q ∈ pairs A B x := onsets_mem_pairs hA0 hB0 hqa (hqe ▸ hn')
      have hcard := card_le_card (show {p,q} ⊆ (pairs A B x).filter (fun p => sumPair p = n) by
        intro u hu
        rcases mem_insert.mp hu with rfl | hu
        · exact mem_filter.mpr ⟨hp',hpe⟩
        · obtain rfl := mem_singleton.mp hu
          exact mem_filter.mpr ⟨hq',hqe⟩)
      simpa [card_pair hp] using hcard
    have hM := repeats_card (pairs A B x) sumPair R hh
    have hI : x-r ≤ ((pairs A B x).image sumPair).card := by
      have hi := card_le_card (rep_card hA0 hB0 hr (x := x))
      change (Icc r x).card ≤ ((pairs A B x).image sumPair).card at hi
      rw [Nat.card_Icc] at hi
      omega
    rw [hRc,card_pairs] at hM
    have he : ((K:ℝ)+(x:ℝ)-r) ≤ (counting A x:ℝ)*counting B x := by
      have ht : K+(x-r) ≤ counting A x*counting B x := by omega
      have hh' : ((K+(x-r):ℕ):ℝ) ≤ (counting A x:ℝ)*counting B x := by exact_mod_cast ht
      simp only [Nat.cast_add, Nat.cast_sub hx] at hh'
      linarith
    linarith
  let T := hfin.toFinset.sup id
  refine ⟨max r (T+1), fun n hn => ?_⟩
  have hnb : n ∉ bad := by
    intro hb
    have hb' : n ∈ hfin.toFinset := hfin.mem_toFinset.mpr hb
    have hle : n ≤ T := le_sup (f := id) hb'
    have hgt : T+1 ≤ n := (le_max_right _ _).trans hn
    omega
  obtain ⟨a,ha,b,hb,he⟩ := hr n ((le_max_left _ _).trans hn)
  refine ⟨(a,b),⟨⟨ha,hb⟩,he⟩,?_⟩
  intro q hq
  by_contra hne
  exact hnb ⟨q,(a,b),hne,hq.1,hq.2,⟨ha,hb⟩,he⟩

end OMA

namespace OMA

private def shift (t : ℕ) (p : ℕ × ℕ) : ℕ := t-p.1+p.2

private theorem near_repeated_shift {A B : Set ℕ} {t N : ℕ}
    (huniq : ∀ n ≥ N, ∃! p : ℕ × ℕ, onsets A B p ∧ sumPair p = n)
    {p q : ℕ × ℕ}
    (hp : p ∈ trunc A t ×ˢ trunc B (2*t)) (hq : q ∈ trunc A t ×ˢ trunc B (2*t))
    (hne : p ≠ q) (he : shift t p = shift t q) :
    shift t p ∈ Icc (t-N) (t+N) := by
  obtain ⟨hpa, hpb⟩ := mem_product.mp hp
  obtain ⟨hqa, hqb⟩ := mem_product.mp hq
  obtain ⟨hpaA,_,hpat⟩ := mem_trunc.mp hpa
  obtain ⟨hpbB,_,_⟩ := mem_trunc.mp hpb
  obtain ⟨hqaA,_,hqat⟩ := mem_trunc.mp hqa
  obtain ⟨hqbB,_,_⟩ := mem_trunc.mp hqb
  have he' : p.1+q.2 = q.1+p.2 := by dsimp [shift] at he; omega
  have hlt : p.1+q.2 < N := by
    by_contra! hw
    have hh := (huniq (p.1+q.2) hw).unique
      (y₁ := (p.1,q.2)) (y₂ := (q.1,p.2)) ⟨⟨hpaA,hqbB⟩,rfl⟩ ⟨⟨hqaA,hpbB⟩,he'.symm⟩
    obtain ⟨he₁,he₂⟩ := Prod.mk.inj hh
    exact hne (Prod.ext he₁ he₂.symm)
  exact mem_Icc.mpr (by dsimp [shift]; omega)

private theorem lower_representations {A B : Set ℕ} {t N n : ℕ}
    (hA0 : 0 ∉ A) (hB0 : 0 ∉ B)
    (huniq : ∀ n ≥ N, ∃! p : ℕ × ℕ, onsets A B p ∧ sumPair p = n)
    (hgap : trunc A (2*t) = trunc A t) (hn : N ≤ n) (hnt : n ≤ t)
    {a : ℕ} (ha : a ∈ trunc A t) :
    ∃ p ∈ trunc A t ×ˢ trunc B (2*t), sumPair p = n+a := by
  obtain ⟨⟨u,v⟩,⟨⟨hu,hv⟩,hs⟩,_⟩ := huniq (n+a) (by omega)
  have ha' := (mem_trunc.mp ha).2.2
  change u+v=n+a at hs
  refine ⟨(u,v),mem_product.mpr ⟨?_,?_⟩,hs⟩
  · have hu0 : u ≠ 0 := fun e => hA0 (e ▸ hu)
    have hux : u ∈ trunc A (2*t) := mem_trunc.mpr ⟨hu,by omega,by omega⟩
    rwa [hgap] at hux
  · exact mem_trunc.mpr ⟨hv, Nat.pos_of_ne_zero (fun h => hB0 (h ▸ hv)),by omega⟩

open scoped Classical in
private noncomputable def misses (A B : Set ℕ) (t : ℕ) :=
  (Icc 0 t).filter (fun n => n ∉ ((trunc A t ×ˢ trunc B (2*t)).image (shift t)))

private theorem misses_upper {A B : Set ℕ} {t N : ℕ}
    (hA0 : 0 ∉ A) (hB0 : 0 ∉ B)
    (huniq : ∀ n ≥ N, ∃! p : ℕ × ℕ, onsets A B p ∧ sumPair p = n)
    (hgap : trunc A (2*t) = trunc A t) (ht : t ∈ trunc A t) :
    (misses A B t).card ≤ N + (trunc A t).card*(2*N+1) := by
  classical
  let U := trunc A t
  let V := trunc B (2*t)
  let P := U ×ˢ V
  let J := Icc (t-N) (t+N)
  let K := range N ∪ (U ×ˢ J).image (fun p => p.1+p.2-t)
  have hl : misses A B t ⊆ K := by
    intro n hn'
    obtain ⟨hn,hm⟩ := mem_filter.mp hn'
    by_cases hnN : n < N
    · exact mem_union_left _ (mem_range.mpr hnN)
    have hnt := (mem_Icc.mp hn).2
    have hr (a : U) : ∃ p ∈ P, sumPair p = n+(a:ℕ) :=
      lower_representations hA0 hB0 huniq hgap (by omega) hnt a.property
    choose f hf hfe using hr
    let g (a : U) := (f a).1
    have hmaps : ∀ a ∈ (univ : Finset U), g a ∈ U.erase t := by
      intro a _
      have ha := (mem_trunc.mp a.property).2.2
      have hF := (mem_product.mp (hf a)).1
      refine mem_erase.mpr ⟨?_,hF⟩
      intro he
      apply hm
      have hs := hfe a
      have hB := (mem_product.mp (hf a)).2
      have he' : shift t ((a:ℕ),(f a).2) = n := by
        change (f a).1+(f a).2=n+(a:ℕ) at hs
        dsimp [g] at he
        dsimp [shift]
        omega
      exact mem_image.mpr ⟨(a,(f a).2),mem_product.mpr ⟨a.property,hB⟩,he'⟩
    have hcard : (U.erase t).card < (univ : Finset U).card := by
      rw [card_erase_of_mem (show t ∈ U from ht)]
      simp only [card_univ, Fintype.card_coe]
      have := card_pos.mpr (show U.Nonempty from ⟨t,ht⟩)
      omega
    obtain ⟨a,_,b,_,hab,he⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
    have hp := mem_product.mp (hf a)
    have hq := mem_product.mp (hf b)
    let pa : ℕ × ℕ := (a,(f a).2)
    let pb : ℕ × ℕ := (b,(f b).2)
    have hp' : pa ∈ P := mem_product.mpr ⟨a.property,hp.2⟩
    have hq' : pb ∈ P := mem_product.mpr ⟨b.property,hq.2⟩
    have hne : pa ≠ pb := fun h => hab (Subtype.ext (congrArg Prod.fst h))
    have hsa := hfe a
    have hsb := hfe b
    dsimp [sumPair] at hsa hsb
    dsimp [g] at he
    have ha := (mem_trunc.mp a.property).2.2
    have hb := (mem_trunc.mp b.property).2.2
    have he' : shift t pa = shift t pb := by dsimp [shift,pa,pb]; omega
    have hm' : shift t pa ∈ J := near_repeated_shift huniq hp' hq' hne he'
    apply mem_union_right
    refine mem_image.mpr ⟨((f a).1,shift t pa),mem_product.mpr ⟨hp.1,hm'⟩,?_⟩
    dsimp [shift,pa]
    omega
  have hJ : J.card ≤ 2*N+1 := by dsimp [J]; rw [Nat.card_Icc]; omega
  calc
    _ ≤ K.card := card_le_card hl
    _ ≤ (range N).card + (U ×ˢ J).card := (card_union_le _ _).trans (Nat.add_le_add_left card_image_le _)
    _ ≤ _ := by rw [card_range,card_product]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hJ) _

private theorem moment_bound {A B : Set ℕ} {t N : ℕ}
    (hA0 : 0 ∉ A) (hB0 : 0 ∉ B)
    (huniq : ∀ n ≥ N, ∃! p : ℕ × ℕ, onsets A B p ∧ sumPair p = n)
    (hgap : trunc A (2*t) = trunc A t) (ht : t ∈ trunc A t) :
    ((trunc A t).card:ℝ) * ((t:ℝ) - (N + (trunc A t).card*(2*N+1) + N^2:ℕ)) ≤
      2 * ∑ a ∈ trunc A t, (a:ℝ) := by
  classical
  let U := trunc A t
  let V := trunc B (2*t)
  let P := U ×ˢ V
  let M := misses A B t
  let T := (U ×ˢ P).filter (fun z => z.1+z.2.2 ≤ z.2.1)
  let fu (u : ℕ) := T.filter (fun z => z.1=u)
  let fa (a : ℕ) := T.filter (fun z => z.2.1=a)
  have hlu : T.card = ∑ u ∈ U, (fu u).card :=
    card_eq_sum_card_fiberwise (fun z hz => (mem_product.mp (mem_filter.mp hz).1).1)
  have hla : T.card = ∑ a ∈ U, (fa a).card :=
    card_eq_sum_card_fiberwise (fun z hz => (mem_product.mp (mem_product.mp (mem_filter.mp hz).1).2).1)
  have hlower (u : ℕ) (hu : u ∈ U) : (t:ℝ)+1-u ≤ (fu u).card + M.card := by
    have hut := (mem_trunc.mp hu).2.2
    have hi : Icc 0 (t-u) ⊆ (fu u).image (fun z => shift t z.2) ∪ M := by
      intro n hn
      by_cases hnm : n ∈ M
      · exact mem_union_right _ hnm
      have hnt := (mem_Icc.mp hn).2
      have hnI : n ∈ Icc 0 t := mem_Icc.mpr ⟨Nat.zero_le _,by omega⟩
      have hni : n ∈ P.image (shift t) := by
        by_contra hh
        exact hnm (mem_filter.mpr ⟨hnI,hh⟩)
      obtain ⟨⟨a,b⟩,hab,he⟩ := mem_image.mp hni
      have hat := (mem_trunc.mp (mem_product.mp hab).1).2.2
      have hgood : u+b ≤ a := by dsimp [shift] at he; omega
      apply mem_union_left
      exact mem_image.mpr ⟨(u,(a,b)),mem_filter.mpr
        ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hu,hab⟩,hgood⟩,rfl⟩,he⟩
    have hc := (card_le_card hi).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right card_image_le _))
    rw [Nat.card_Icc, Nat.sub_zero] at hc
    have hcc : (((t-u+1:ℕ):ℝ)) ≤ (fu u).card + M.card := by exact_mod_cast hc
    push_cast [Nat.cast_sub hut] at hcc
    linarith
  have hupper (a : ℕ) (ha : a ∈ U) : ((fa a).card:ℝ) ≤ (a:ℝ)+1+(N:ℝ)^2 := by
    let S := fa a
    let S₁ := S.filter (fun z => z.1+z.2.2 < N)
    let S₂ := S.filter (fun z => ¬(z.1+z.2.2 < N))
    have hparts : S₁.card + S₂.card = S.card := card_filter_add_card_filter_not _
    have h₁ : S₁.card ≤ (range N ×ˢ range N).card := by
      refine card_le_card_of_injOn (fun z => (z.1,z.2.2)) ?_ ?_
      · intro z hz
        have he := (mem_filter.mp hz).2
        change (z.1,z.2.2) ∈ _
        exact mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩
      · intro z hz w hw h
        have hz' := (mem_filter.mp (mem_filter.mp hz).1).2
        have hw' := (mem_filter.mp (mem_filter.mp hw).1).2
        obtain ⟨he₁,he₂⟩ := Prod.mk.inj h
        exact Prod.ext he₁ (Prod.ext (hz'.trans hw'.symm) he₂)
    have h₂ : S₂.card ≤ (Icc 0 a).card := by
      refine card_le_card_of_injOn (fun z => z.1+z.2.2) ?_ ?_
      · intro z hz
        have hz' := mem_filter.mp (mem_filter.mp hz).1
        have he := (mem_filter.mp hz'.1).2
        exact mem_Icc.mpr ⟨Nat.zero_le _,he.trans_eq hz'.2⟩
      · intro z hz w hw he
        have hz' := mem_filter.mp (mem_filter.mp hz).1
        have hw' := mem_filter.mp (mem_filter.mp hw).1
        have hz'' := mem_product.mp (mem_filter.mp hz'.1).1
        have hw'' := mem_product.mp (mem_filter.mp hw'.1).1
        have h := (huniq (z.1+z.2.2) (by
          have := (mem_filter.mp hz).2
          omega)).unique (y₁ := (z.1,z.2.2)) (y₂ := (w.1,w.2.2))
          ⟨⟨(mem_trunc.mp hz''.1).1,(mem_trunc.mp (mem_product.mp hz''.2).2).1⟩, rfl⟩
          ⟨⟨(mem_trunc.mp hw''.1).1,(mem_trunc.mp (mem_product.mp hw''.2).2).1⟩, he.symm⟩
        obtain ⟨he₁,he₂⟩ := Prod.mk.inj h
        exact Prod.ext he₁ (Prod.ext (hz'.2.trans hw'.2.symm) he₂)
    rw [card_product,card_range,← pow_two] at h₁
    rw [Nat.card_Icc, Nat.sub_zero] at h₂
    exact_mod_cast (show S.card ≤ a+1+N^2 by omega)
  have hlu' : (T.card:ℝ) = ∑ u ∈ U, ((fu u).card:ℝ) := by exact_mod_cast hlu
  have hla' : (T.card:ℝ) = ∑ a ∈ U, ((fa a).card:ℝ) := by exact_mod_cast hla
  have h1 := sum_le_sum hlower
  have h2 := sum_le_sum hupper
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul, sum_add_distrib, sum_const, nsmul_eq_mul,
    ← hlu'] at h1
  rw [← hla', sum_add_distrib, sum_add_distrib, sum_const, sum_const,
    nsmul_eq_mul, nsmul_eq_mul] at h2
  have hm := misses_upper hA0 hB0 huniq hgap ht
  have hm' : (M.card:ℝ) ≤ ((N+(U.card)*(2*N+1)+N^2:ℕ):ℝ) - (N:ℝ)^2 := by
    have e : (M.card:ℝ) ≤ ((N+U.card*(2*N+1):ℕ):ℝ) := by exact_mod_cast hm
    push_cast at e ⊢
    linarith
  have he := mul_le_mul_of_nonneg_left hm' (show 0 ≤ (U.card:ℝ) by positivity)
  nlinarith

end OMA

namespace OMA

private theorem div_atTop {L : ℕ} (hL : 0 < L) :
    Tendsto (fun n : ℕ => n/L) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun m => ⟨m*L, fun n hn => (Nat.le_div_iff_mul_le hL).2 hn⟩

private theorem slow_count {A B : Set ℕ} (hB : B.Infinite) (hB0 : 0 ∉ B)
    (h : ∀ᶠ x : ℕ in atTop, (counting A x:ℝ)*counting B x ≤ (13/10:ℝ)*x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, (counting A x:ℝ) ≤ ε*(x:ℝ) := by
  obtain ⟨K,hK⟩ := exists_nat_gt ((13/10:ℝ)/ε)
  filter_upwards [h, tendsto_atTop.1 (count_atTop hB hB0) K] with x hA hx
  have hx' : (K:ℝ) ≤ counting B x := by exact_mod_cast hx
  have hx'' : (13/10:ℝ) < ε*counting B x := by
    have := (div_lt_iff₀ hε).mp (hK.trans_le hx')
    simpa [mul_comm] using this
  have hpos : 0 < (counting B x:ℝ) := by
    by_contra! he
    nlinarith
  apply le_of_mul_le_mul_right _ hpos
  exact hA.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hx''.le) (Nat.cast_nonneg (α := ℝ) x)])

private theorem inner_fibers {A B : Set ℕ} (x : ℕ) :
    (inner A B x).card = ∑ a ∈ trunc A x, counting B (x-a) := by
  classical
  have hmaps : ∀ p ∈ inner A B x, p.1 ∈ trunc A x :=
    fun p hp => (mem_product.mp (mem_filter.mp hp).1).1
  rw [card_eq_sum_card_fiberwise hmaps]
  apply sum_congr rfl
  intro a ha
  let f : ℕ ↪ ℕ × ℕ := ⟨fun b => (a,b), fun _ _ h => congrArg Prod.snd h⟩
  have hf : ((inner A B x).filter (fun p => p.1 = a)) = (trunc B (x-a)).map f := by
    ext p
    rcases p with ⟨u,v⟩
    constructor
    · intro hp
      have ht := mem_filter.mp (mem_filter.mp hp).1
      have he := (mem_filter.mp hp).2
      change u=a at he
      subst u
      have hm := mem_trunc.mp (mem_product.mp ht.1).2
      have hs := ht.2
      change a+v≤x at hs
      exact mem_map.mpr ⟨v,mem_trunc.mpr ⟨hm.1,hm.2.1,by omega⟩,rfl⟩
    · intro hp
      obtain ⟨b,hb,he⟩ := mem_map.mp hp
      change (a,b)=(u,v) at he
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      have hbx := mem_trunc.mp hb
      have ha' := (mem_trunc.mp ha).2.2
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr
        ⟨ha,mem_trunc.mpr ⟨hbx.1,hbx.2.1,by omega⟩⟩,
        show a+b≤x by omega⟩,rfl⟩
  rw [hf,card_map,count_trunc]

private theorem no_large_gap {A B : Set ℕ} (hA0 : 0 ∉ A) (hB0 : 0 ∉ B)
    (hB : B.Infinite)
    {r N : ℕ} (hr : ∀ n ≥ r, n ∈ A+B)
    (huniq : ∀ n ≥ N, ∃! p : ℕ × ℕ, onsets A B p ∧ sumPair p = n)
    (hupper : ∀ᶠ x : ℕ in atTop, (counting A x:ℝ)*counting B x ≤ (13/10:ℝ)*x) :
    ∀ᶠ t : ℕ in atTop, t ∈ trunc A t → trunc A (2*t) ≠ trunc A t := by
  obtain ⟨R,hR⟩ := eventually_atTop.1 hupper
  let η := 1/(200*((2*N+1:ℕ):ℝ))
  have hη : 0 < η := by dsimp [η]; positivity
  filter_upwards [eventually_ge_atTop R, eventually_ge_atTop (200*(N+N^2+r+1)),
    slow_count hB hB0 hupper hη] with t hRt htbig hslow ht hgap
  let U := trunc A t
  let m := (U.card:ℝ)
  let S := ∑ a ∈ U, (a:ℝ)
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast (card_pos.mpr (show U.Nonempty from ⟨t,ht⟩))
  have htx : 0 < (t:ℝ) := by exact_mod_cast (mem_trunc.mp ht).2.1
  have ht' : r ≤ 2*t := by omega
  have hMom := moment_bound hA0 hB0 huniq hgap ht
  change m*((t:ℝ)-((N+U.card*(2*N+1)+N^2:ℕ):ℝ)) ≤ 2*S at hMom
  have hErr : ((N+U.card*(2*N+1)+N^2:ℕ):ℝ) ≤ (t:ℝ)/100 := by
    have hC : (U.card:ℝ) ≤ η*(t:ℝ) := by simp [U,count_trunc,hslow]
    have hh := mul_le_mul_of_nonneg_right hC (show 0 ≤ ((2*N+1:ℕ):ℝ) by positivity)
    have he : η*(t:ℝ)*((2*N+1:ℕ):ℝ) = (t:ℝ)/200 := by dsimp [η]; field_simp
    rw [he] at hh
    have hbig : (200:ℝ)*((N:ℝ)+(N:ℝ)^2+(r:ℝ)+1) ≤ t := by exact_mod_cast htbig
    push_cast at hh ⊢
    linarith
  have hrErr : (r:ℝ) ≤ (t:ℝ)/100 := by
    have hbig : (200:ℝ)*((N:ℝ)+(N:ℝ)^2+(r:ℝ)+1) ≤ t := by exact_mod_cast htbig
    nlinarith
  have hMom' : m*((t:ℝ)-(t:ℝ)/100) ≤ 2*S :=
    (mul_le_mul_of_nonneg_left (sub_le_sub_left hErr _) hm.le).trans hMom
  have hLower := inner_lower hA0 hB0 hr ht'
  rw [inner_fibers, hgap, Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] at hLower
  have hUpperTerm (a : ℕ) (ha : a ∈ U) :
      m*(counting B (2*t-a):ℝ) ≤ (13/10:ℝ)*(2*(t:ℝ)-(a:ℝ)) := by
    have ha' := (mem_trunc.mp ha).2.2
    have hl : t ≤ 2*t-a := by omega
    have hu : 2*t-a ≤ 2*t := by omega
    have he : trunc A (2*t-a) = U := by
      change trunc A (2*t-a) = trunc A t
      apply le_antisymm _ (trunc_mono A hl)
      rw [← hgap]
      exact trunc_mono A hu
    have hc : (counting A (2*t-a):ℝ) = m := by rw [← count_trunc,he]
    have h := hR (2*t-a) (hRt.trans hl)
    rw [hc, Nat.cast_sub (by omega : a ≤ 2*t)] at h
    push_cast at h
    exact h
  have hSum := sum_le_sum hUpperTerm
  rw [← mul_sum, ← mul_sum, sum_sub_distrib, sum_const, nsmul_eq_mul] at hSum
  have hlow' := mul_le_mul_of_nonneg_left hLower hm.le
  have herr' := mul_le_mul_of_nonneg_left hrErr hm.le
  have hn : 0 < m*(t:ℝ) := mul_pos hm htx
  change m*(∑ a ∈ U, (counting B (2*t-a):ℝ)) ≤ (13/10:ℝ)*(m*(2*(t:ℝ))-S) at hSum
  linarith

private theorem upper_of_limsup {A B : Set ℕ}
    (hl : limsup (fun x : ℕ => (((counting A x:ℝ)*counting B x/(x:ℝ)):EReal)) atTop <
      ((3-Real.sqrt 3:ℝ):EReal)) :
    ∀ᶠ x : ℕ in atTop, (counting A x:ℝ)*counting B x ≤ (13/10:ℝ)*x := by
  have hS : (17/10:ℝ) < Real.sqrt 3 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hC : ((3-Real.sqrt 3:ℝ):EReal) < ((13/10:ℝ):EReal) := by
    exact_mod_cast (show 3-Real.sqrt 3 < (13/10:ℝ) by linarith)
  have hE := eventually_lt_of_limsup_lt (hl.trans hC)
  filter_upwards [hE, eventually_gt_atTop (0:ℕ)] with x hx hx1
  have hh : ((counting A x:ℝ)*counting B x)/(x:ℝ) < (13/10:ℝ) := EReal.coe_lt_coe_iff.mp hx
  exact ((div_lt_iff₀ (show (0:ℝ) < x by positivity)).1 hh).le

private theorem star_gap {A : Set ℕ} {x : ℕ} (hne : (trunc A x).Nonempty)
    (hgap : trunc A (x/2) = trunc A x) :
    aStar A x ∈ trunc A (aStar A x) ∧ trunc A (2*aStar A x) = trunc A (aStar A x) := by
  obtain ⟨ht,he⟩ := aStar_trunc hne
  have ht' : aStar A x ∈ trunc A (x/2) := hgap ▸ ht
  have ht2 := (mem_trunc.mp ht').2.2
  have hbig : 2*aStar A x ≤ x := by omega
  exact ⟨he ▸ ht,le_antisymm (he ▸ trunc_mono A hbig) (trunc_mono A (by omega))⟩

private theorem eventual_gap_at_bounded_excess {A B : Set ℕ} (hA0 : 0 ∉ A) (hB0 : 0 ∉ B)
    (hA : A.Infinite) (hB : B.Infinite)
    {r : ℕ} (hr : ∀ n ≥ r, n ∈ A+B)
    {C : ℝ} (hupper : ∀ᶠ x : ℕ in atTop, (counting A x:ℝ)*counting B x ≤ (13/10:ℝ)*x) :
    ∀ᶠ x : ℕ in atTop, (counting A x:ℝ)*counting B x-(x:ℝ) ≤ C →
      trunc A (x/2) = trunc A x ∨ trunc B (x/2) = trunc B x := by
  obtain ⟨K,hK⟩ := exists_nat_gt (C+(r:ℝ))
  let ε := 1/((100:ℝ)*(K+1:ℕ))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hupper' : ∀ᶠ x : ℕ in atTop, (counting B x:ℝ)*counting A x ≤ (13/10:ℝ)*x :=
    hupper.mono (fun x hx => by simpa [mul_comm] using hx)
  have hy := (div_atTop (L := 2) (by decide)).eventually hupper
  filter_upwards [eventually_ge_atTop (100*(r+1)), hy,
    slow_count hB hB0 hupper hε, slow_count hA hA0 hupper' hε]
    with x hx hy hAx hBx hbad
  let y := x/2
  let U := trunc A x
  let V := trunc B x
  let U₀ := trunc A y
  let V₀ := trunc B y
  have hU : U₀ ⊆ U := trunc_mono A (Nat.div_le_self _ _)
  have hV : V₀ ⊆ V := trunc_mono B (Nat.div_le_self _ _)
  by_contra! hgap
  let c := (U \ U₀).card
  let d := (V \ V₀).card
  have hc : 0 < c := card_pos.mpr (sdiff_nonempty.mpr (fun hh => hgap.1 (le_antisymm hU hh)))
  have hd : 0 < d := card_pos.mpr (sdiff_nonempty.mpr (fun hh => hgap.2 (le_antisymm hV hh)))
  have hT : (U \ U₀) ×ˢ (V \ V₀) ⊆ late A B x := by
    intro p hp
    obtain ⟨ha,hb⟩ := mem_product.mp hp
    obtain ⟨ha',ha''⟩ := mem_sdiff.mp ha
    obtain ⟨hb',hb''⟩ := mem_sdiff.mp hb
    have hpa := mem_trunc.mp ha'
    have hpb := mem_trunc.mp hb'
    have ha₁ : y < p.1 := by
      by_contra! he
      exact ha'' (mem_trunc.mpr ⟨hpa.1,hpa.2.1,he⟩)
    have hb₁ : y < p.2 := by
      by_contra! he
      exact hb'' (mem_trunc.mpr ⟨hpb.1,hpb.2.1,he⟩)
    exact mem_filter.mpr ⟨mem_product.mpr ⟨ha',hb'⟩,by dsimp [sumPair,y] at *; omega⟩
  have hTc := card_le_card hT
  rw [card_product] at hTc
  have hTc' : (c:ℝ)*(d:ℝ) ≤ (late A B x).card := by exact_mod_cast hTc
  have hL := late_upper hA0 hB0 hr (by omega : r≤x)
  have hcd : (c:ℝ)*(d:ℝ) ≤ C+(r:ℝ) := by linarith
  have hcK : c ≤ K := by
    have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
    have hh : (c:ℝ) ≤ c*d := le_mul_of_one_le_right (by positivity) hd'
    exact_mod_cast (hh.trans hcd).trans hK.le
  have hdK : d ≤ K := by
    have hc' : (1:ℝ) ≤ c := by exact_mod_cast hc
    have hh : (d:ℝ) ≤ c*d := le_mul_of_one_le_left (by positivity) hc'
    exact_mod_cast (hh.trans hcd).trans hK.le
  have huEq : (c:ℝ) = (counting A x:ℝ)-counting A y := by
    dsimp [c]
    rw [card_sdiff_of_subset hU, Nat.cast_sub (card_le_card hU)]
    simp [U,U₀,count_trunc]
  have hvEq : (d:ℝ) = (counting B x:ℝ)-counting B y := by
    dsimp [d]
    rw [card_sdiff_of_subset hV, Nat.cast_sub (card_le_card hV)]
    simp [V,V₀,count_trunc]
  have hP := inner_lower hA0 hB0 hr (by omega : r≤x)
  have hcard : (inner A B x).card ≤ (pairs A B x).card := card_filter_le _ _
  rw [card_pairs] at hcard
  have hP' : (x:ℝ)-(r:ℝ) ≤ (counting A x:ℝ)*counting B x := by
    exact hP.trans (by exact_mod_cast hcard)
  have hca : (counting A y:ℝ) ≤ counting A x := by
    exact_mod_cast count_mono A (Nat.div_le_self x 2)
  have hh₁ := mul_le_mul_of_nonneg_right (show (c:ℝ) ≤ K by exact_mod_cast hcK)
    (show 0 ≤ (counting B x:ℝ) by positivity)
  have hh₂ := mul_le_mul (show (d:ℝ) ≤ K by exact_mod_cast hdK) hca (by positivity)
    (show (0:ℝ) ≤ K by positivity)
  have hdif : (counting A x:ℝ)*counting B x-(counting A y:ℝ)*counting B y
      ≤ (K:ℝ)*((counting A x:ℝ)+counting B x) := by
    rw [huEq] at hh₁
    rw [hvEq] at hh₂
    nlinarith
  have hKε : (K:ℝ)*ε ≤ 1/100 := by
    dsimp [ε]
    push_cast
    rw [mul_one_div]
    apply (div_le_iff₀ (show (0:ℝ) < 100*((K:ℝ)+1) by positivity)).2
    nlinarith
  have hkn : (K:ℝ)*((counting A x:ℝ)+counting B x) ≤ 2*((x:ℝ)/100) := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add hAx hBx) (show (0:ℝ) ≤ K by positivity)
    have h' := mul_le_mul_of_nonneg_right hKε (show (0:ℝ) ≤ x by positivity)
    nlinarith
  have hy' : (y:ℝ) ≤ (x:ℝ)/2 := by
    have hh : ((y:ℝ)*(2:ℝ)) ≤ x := by exact_mod_cast Nat.div_mul_le_self x 2
    linarith
  have hr' : (r:ℝ) ≤ (x:ℝ)/100 := by
    have hh : (100:ℝ)*((r:ℝ)+1) ≤ (x:ℝ) := by exact_mod_cast hx
    linarith
  have hx' : (0:ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  change (counting A y:ℝ)*counting B y ≤ (13/10:ℝ)*y at hy
  linarith

private theorem chen_fang_limsup (A B : Set ℕ) (hA : A.Infinite) (hB : B.Infinite)
    (hA0 : 0 ∉ A) (hB0 : 0 ∉ B) (h : IsAdditiveComplement A B)
    (hl : limsup (fun x : ℕ => (((counting A x:ℝ)*counting B x/(x:ℝ)):EReal)) atTop <
      ((3-Real.sqrt 3:ℝ):EReal)) :
    Tendsto (fun x : ℕ => (counting A x:ℝ)*counting B x-(x:ℝ)) atTop atTop := by
  classical
  by_contra hn
  rw [tendsto_atTop] at hn
  push Not at hn
  obtain ⟨C,hC⟩ := hn
  have hbad : ∃ᶠ x : ℕ in atTop, (counting A x:ℝ)*counting B x-(x:ℝ) ≤ C :=
    hC.mono fun x hx => hx.le
  obtain ⟨r,hr⟩ := eventually_atTop.1 h
  have hBA : IsAdditiveComplement B A := h.symm
  obtain ⟨s,hs⟩ := eventually_atTop.1 hBA
  obtain ⟨N,hN⟩ := eventually_unique hA0 hB0 hr hbad
  have hbad' : ∃ᶠ x : ℕ in atTop, (counting B x:ℝ)*counting A x-(x:ℝ) ≤ C :=
    hbad.mono (fun x hx => by simpa [mul_comm] using hx)
  obtain ⟨M,hM⟩ := eventually_unique hB0 hA0 hs hbad'
  have hupper := upper_of_limsup hl
  have hupper' : ∀ᶠ x : ℕ in atTop, (counting B x:ℝ)*counting A x ≤ (13/10:ℝ)*x :=
    hupper.mono (fun x hx => by rwa [mul_comm (counting B x:ℝ)])
  have hnoA := (star_atTop hA hA0).eventually (no_large_gap hA0 hB0 hB hr hN hupper)
  have hnoB := (star_atTop hB hB0).eventually (no_large_gap hB0 hA0 hA hs hM hupper')
  have hgap := eventual_gap_at_bounded_excess hA0 hB0 hA hB hr (C := C) hupper
  have hac := tendsto_atTop.1 (count_atTop hA hA0) 1
  have hbc := tendsto_atTop.1 (count_atTop hB hB0) 1
  have hf := hbad.and_eventually (hnoA.and (hnoB.and (hgap.and (hac.and hbc))))
  obtain ⟨x,hbx,hxA,hxB,hgx,hacx,hbcx⟩ := hf.exists
  rcases hgx hbx with hA' | hB'
  · have hne : (trunc A x).Nonempty := card_pos.mp (by rw [count_trunc]; omega)
    obtain ⟨ht,he⟩ := star_gap hne hA'
    exact hxA ht he
  · have hne : (trunc B x).Nonempty := card_pos.mp (by rw [count_trunc]; omega)
    obtain ⟨ht,he⟩ := star_gap hne hB'
    exact hxB ht he

end OMA

theorem OMA.solution : type_of% @Erdos785.erdos_785.variants.chen_fang_limsup :=
  OMA.chen_fang_limsup