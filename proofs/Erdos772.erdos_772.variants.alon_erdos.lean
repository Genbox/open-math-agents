import FormalConjectures.ErdosProblems.«772»

/-! Average over all subsets with independent sampling, then delete one point
from each additive collision. -/

namespace SidonSample
open Finset

private def mass (A X : Finset ℕ) (p : ℝ) : ℝ :=
  p ^ X.card * (1-p) ^ (A\X).card

private theorem moment (A B : Finset ℕ) (h : B ⊆ A) (p : ℝ) :
    (∑ X ∈ A.powerset, if B ⊆ X then mass A X p else 0) = p ^ B.card := by
  classical
  let g (i : ℕ) := if i ∈ B then (0:ℝ) else 1-p
  have ha : (∏ i ∈ A, (p + g i)) = p^B.card := by
    have hf : A.filter (· ∈ B) = B := by ext i; simp; exact fun hi => h hi
    calc
      _ = ∏ i ∈ A, (if i∈B then p else 1) := by
        apply prod_congr rfl
        intro i _
        by_cases hi : i ∈ B <;> simp [g, hi]
      _ = _ := by rw [prod_ite]; simp [hf]
  rw [← ha, prod_add]
  apply sum_congr rfl
  intro X hX
  by_cases hBX : B ⊆ X
  · have hprod : (∏ i ∈ A\X, g i) = (1-p)^(A\X).card := by
      calc
        _ = ∏ _i ∈ A\X, (1-p) := by
          apply prod_congr rfl
          intro i hi
          exact if_neg (fun hh => (mem_sdiff.mp hi).2 (hBX hh))
        _ = _ := by simp
    simp [hBX, mass, hprod]
  · obtain ⟨v, hv, hvX⟩ := not_subset.mp hBX
    have hprod : (∏ i ∈ A\X, g i) = 0 :=
      prod_eq_zero (mem_sdiff.mpr ⟨h hv, hvX⟩) (if_pos hv)
    simp [hBX, hprod]

private theorem expected_count {α : Type*} (s : Finset α) (e : α → Finset ℕ)
    (A : Finset ℕ) (p : ℝ) (he : ∀ z ∈ s, e z ⊆ A) :
    (∑ X ∈ A.powerset, mass A X p * ((s.filter (fun z => e z ⊆ X)).card : ℝ)) =
      ∑ z ∈ s, p^(e z).card := by
  classical
  calc
    _ = ∑ X ∈ A.powerset, ∑ z ∈ s, if e z ⊆ X then mass A X p else 0 := by
      apply sum_congr rfl
      intro X _
      rw [← sum_filter]
      simp [mul_comm]
    _ = _ := by rw [sum_comm]; exact sum_congr rfl fun z hz => moment A _ (he z hz) p

private theorem expected_card (A : Finset ℕ) (p : ℝ) :
    (∑ X ∈ A.powerset, mass A X p * (X.card : ℝ)) = A.card*p := by
  classical
  have hh := expected_count A (fun z => {z}) A p (by simp)
  calc
    _ = ∑ X ∈ A.powerset, mass A X p * ((A.filter fun z => ({z}:Finset ℕ) ⊆ X).card : ℝ) := by
      apply sum_congr rfl
      intro X hX
      have hsub := mem_powerset.mp hX
      have hf : A.filter (fun z => ({z}:Finset ℕ) ⊆ X) = X := by
        ext i
        simp
        exact fun hi => hsub hi
      rw [hf]
    _ = _ := by simpa using hh

theorem select {α β : Type*} (A : Finset ℕ) (s : Finset α) (t : Finset β)
    (e : α → Finset ℕ) (g : β → Finset ℕ) (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (he : ∀ i ∈ s, e i ⊆ A ∧ (e i).card=3) (hg : ∀ i ∈ t, g i ⊆ A ∧ (g i).card=4) :
    ∃ X ⊆ A, (A.card : ℝ)*p - s.card*p^3 - t.card*p^4 ≤
      (X.card : ℝ) - (s.filter (fun i => e i ⊆ X)).card - (t.filter (fun i => g i ⊆ X)).card := by
  classical
  have hnorm := moment A ∅ (empty_subset _) p
  simp only [empty_subset, if_true, card_empty, pow_zero] at hnorm
  have h3 := expected_count s e A p (fun i hi => (he i hi).1)
  have h4 := expected_count t g A p (fun i hi => (hg i hi).1)
  rw [sum_congr rfl (fun i hi => congrArg (p^·) (he i hi).2)] at h3
  rw [sum_congr rfl (fun i hi => congrArg (p^·) (hg i hi).2)] at h4
  simp only [sum_const, nsmul_eq_mul] at h3 h4
  by_contra! h
  let v := (A.card : ℝ)*p - s.card*p^3 - t.card*p^4
  let score (X : Finset ℕ) := (X.card : ℝ) - (s.filter (fun i => e i ⊆ X)).card -
      (t.filter (fun i => g i ⊆ X)).card
  have hw X : 0 ≤ mass A X p := by
    unfold mass
    exact mul_nonneg (pow_nonneg hp _) (pow_nonneg (by linarith) _)
  obtain ⟨X, hX, hpos⟩ : ∃ X ∈ A.powerset, 0 < mass A X p := by
    by_contra! hz
    have h0 := sum_nonpos hz
    linarith
  have hlt : (∑ Y ∈ A.powerset, mass A Y p * score Y) < ∑ Y ∈ A.powerset, mass A Y p*v := by
    apply sum_lt_sum
    · intro Y hY
      exact mul_le_mul_of_nonneg_left (h Y (mem_powerset.mp hY)).le (hw Y)
    · exact ⟨X, hX, mul_lt_mul_of_pos_left (h X (mem_powerset.mp hX)) hpos⟩
  rw [← sum_mul, hnorm, one_mul] at hlt
  simp only [score, mul_sub, sum_sub_distrib, expected_card, h3, h4] at hlt
  exact (lt_irrefl v) hlt

end SidonSample

namespace SidonCollisions
open Finset AdditiveCombinatorics

private abbrev Pair := ℕ × ℕ
private abbrev Triple := Σ _ : ℕ, Pair
private abbrev Quad := Σ _ : Pair, Pair

private def reps (A : Finset ℕ) (m : ℕ) :=
  (antidiagonal m).filter (fun z : Pair => z.1 ∈ A ∧ z.2 ∈ A)

private theorem mem_reps {A : Finset ℕ} {m a b : ℕ} :
    (a,b) ∈ reps A m ↔ a+b=m ∧ a∈A ∧ b∈A := by simp [reps]

def triPoints (z : Triple) : Finset ℕ := {z.1,z.2.1,z.2.2}
def quadPoints (z : Quad) : Finset ℕ := {z.1.1,z.1.2,z.2.1,z.2.2}

def triples (A : Finset ℕ) : Finset Triple :=
  (A.sigma (fun x => reps A (x+x))).filter (fun z => (triPoints z).card=3)

def quads (A : Finset ℕ) : Finset Quad :=
  ((A.product A).sigma (fun z => reps A (z.1+z.2))).filter (fun z => (quadPoints z).card=4)

theorem tri_valid (A : Finset ℕ) (z : Triple) (hz : z ∈ triples A) : triPoints z ⊆ A ∧ (triPoints z).card = 3 := by
  rcases z with ⟨a,b,c⟩
  obtain ⟨hz, hc⟩ := mem_filter.mp hz
  obtain ⟨ha,hr⟩ := mem_sigma.mp hz
  obtain ⟨_,hb,hc'⟩ := mem_reps.mp hr
  exact ⟨insert_subset ha (insert_subset hb (singleton_subset_iff.mpr hc')), hc⟩

theorem quad_valid (A : Finset ℕ) (z : Quad) (hz : z ∈ quads A) : quadPoints z ⊆ A ∧ (quadPoints z).card = 4 := by
  rcases z with ⟨⟨a,b⟩,c,d⟩
  obtain ⟨hz, hc⟩ := mem_filter.mp hz
  obtain ⟨hab, hr⟩ := mem_sigma.mp hz
  obtain ⟨ha,hb⟩ := mem_product.mp hab
  obtain ⟨_,hc',hd⟩ := mem_reps.mp hr
  exact ⟨insert_subset ha (insert_subset hb (insert_subset hc' (singleton_subset_iff.mpr hd))), hc⟩

theorem tri_count (A : Finset ℕ) {k : ℕ} (hk : ∀ m, sumRep A m ≤ k) :
    (triples A).card ≤ A.card*k := by
  apply (card_filter_le _ _).trans
  rw [card_sigma]
  calc
    _ ≤ ∑ _a ∈ A, k := sum_le_sum fun a _ => by simpa [reps] using hk (a+a)
    _ = _ := by simp

theorem quad_count (A : Finset ℕ) {k : ℕ} (hk : ∀ m, sumRep A m ≤ k) :
    (quads A).card ≤ A.card^2*k := by
  apply (card_filter_le _ _).trans
  rw [card_sigma]
  calc
    _ ≤ ∑ _z ∈ A.product A, k := sum_le_sum fun z _ => by simpa [reps] using hk (z.1+z.2)
    _ = _ := by simp [sq]

theorem clean {A X : Finset ℕ} (hX : X ⊆ A) :
    ∃ S ⊆ X, IsSidon (S : Set ℕ) ∧ (X.card : ℝ) -
      ((triples A).filter (fun z => triPoints z ⊆ X)).card -
      ((quads A).filter (fun z => quadPoints z ⊆ X)).card ≤ S.card := by
  classical
  let T := (triples A).filter (fun z => triPoints z ⊆ X)
  let Q := (quads A).filter (fun z => quadPoints z ⊆ X)
  let bad := T.image Sigma.fst ∪ Q.image (fun z => z.1.1)
  let S := X\bad
  have hT (x a b : ℕ) (hx : x ∈ S) (ha : a ∈ S) (hb : b ∈ S)
      (h : x+x=a+b) (hn : a≠b) : False := by
    have hx' := mem_sdiff.mp hx
    have ha' := mem_sdiff.mp ha
    have hb' := mem_sdiff.mp hb
    have hxa : x≠a := by omega
    have hxb : x≠b := by omega
    let z : Triple := ⟨x,a,b⟩
    have hz : z ∈ T := by
      apply mem_filter.mpr
      constructor
      · apply mem_filter.mpr
        refine ⟨mem_sigma.mpr ⟨hX hx'.1, mem_reps.mpr ⟨h.symm,hX ha'.1,hX hb'.1⟩⟩, ?_⟩
        simp [z, triPoints, hxa,hxb,hn]
      · exact insert_subset hx'.1 (insert_subset ha'.1 (singleton_subset_iff.mpr hb'.1))
    exact hx'.2 (mem_union_left _ (mem_image.mpr ⟨z,hz,rfl⟩))
  have hbc : bad.card ≤ T.card+Q.card :=
    (card_union_le _ _).trans (Nat.add_le_add card_image_le card_image_le)
  have hsize : X.card ≤ S.card+bad.card := by
    have hsub : X ⊆ S ∪ bad := by
      intro x hx
      by_cases hb : x ∈ bad
      · exact mem_union_right _ hb
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hx, hb⟩)
    exact (card_le_card hsub).trans (card_union_le _ _)
  refine ⟨S,sdiff_subset,?_,?_⟩
  · intro a ha b hb c hc d hd he
    by_contra hnot
    have hab : a≠b := by intro hh; exact hnot (.inl ⟨hh,by omega⟩)
    have had : a≠d := by intro hh; exact hnot (.inr ⟨hh,by omega⟩)
    have hcb : c≠b := by omega
    have hcd : c≠d := by omega
    by_cases hac : a=c
    · subst c
      have hbd : b≠d := by omega
      exact hT a b d ha hb hd he hbd
    by_cases hbd : b=d
    · subst d
      exact hT b a c hb ha hc he.symm hac
    have ha' := mem_sdiff.mp ha
    have hb' := mem_sdiff.mp hb
    have hc' := mem_sdiff.mp hc
    have hd' := mem_sdiff.mp hd
    let z : Quad := ⟨(a,c),b,d⟩
    have hz : z ∈ Q := by
      apply mem_filter.mpr
      constructor
      · apply mem_filter.mpr
        refine ⟨mem_sigma.mpr ⟨mem_product.mpr ⟨hX ha'.1,hX hc'.1⟩,
          mem_reps.mpr ⟨he.symm,hX hb'.1,hX hd'.1⟩⟩, ?_⟩
        simp [z,quadPoints,hac,hab,had,hcb,hcd,hbd]
      · exact insert_subset ha'.1 (insert_subset hc'.1 (insert_subset hb'.1 (singleton_subset_iff.mpr hd'.1)))
    exact ha'.2 (mem_union_right _ (mem_image.mpr ⟨z,hz,rfl⟩))
  · change (X.card:ℝ)-T.card-Q.card ≤ S.card
    exact_mod_cast (show (X.card:ℤ)-T.card-Q.card ≤ S.card by omega)

end SidonCollisions

namespace SidonBound
open Finset Filter Erdos772 AdditiveCombinatorics

private theorem parameter (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∃ p : ℝ, 0 ≤ p ∧ p ≤ 1 ∧
    (n:ℝ)^(2/3:ℝ)/(8*k) ≤ n*p - (n*k)*p^3 - (n^2*k)*p^4 := by
  let r : ℝ := (n:ℝ)^(1/3 : ℝ)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : 1 ≤ r := Real.one_le_rpow hn' (by norm_num)
  have hrpos : 0 < r := by linarith
  have hkpos : 0 < (k : ℝ) := by linarith
  have h3 : r^3 = (n:ℝ) := by
    rw [← Real.rpow_natCast, show r = _ from rfl, ← Real.rpow_mul (by positivity : 0 ≤ (n:ℝ))]
    norm_num
  have h2 : r^2 = (n:ℝ)^(2/3:ℝ) := by
    rw [← Real.rpow_natCast, show r = _ from rfl, ← Real.rpow_mul (by positivity : 0 ≤ (n:ℝ))]
    norm_num
  let p : ℝ := 1/(4*k*r)
  have hkr : 1 ≤ (k:ℝ)*r := one_le_mul_of_one_le_of_one_le hk' hr
  refine ⟨p, by dsimp [p]; positivity, ?_, ?_⟩
  · apply (div_le_one (by positivity : (0 : ℝ)<4*k*r)).mpr
    linarith
  · have A : (n:ℝ)*p = r^2/(4*k) := by
      rw [← h3]
      dsimp [p]
      field_simp
    have B : ((n:ℝ)*k)*p^3 ≤ r^2/(16*k) := by
      have eqB : ((n:ℝ)*k)*p^3 = 1/(64*(k:ℝ)^2) := by
        rw [← h3]
        dsimp [p]
        field_simp
        ring
      rw [eqB]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      have hprod : 1 ≤ r^2 * (k:ℝ) := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hr) hk'
      calc
        _ = 16 * (k:ℝ) * 1 := by ring
        _ ≤ 16*(k:ℝ)*(r^2*k) := mul_le_mul_of_nonneg_left hprod (by positivity)
        _ ≤ 64*(k:ℝ)*(r^2*k) := by gcongr; norm_num
        _ = _ := by ring
    have C : ((n:ℝ)^2*k)*p^4 ≤ r^2/(16*k) := by
      have eqC : ((n:ℝ)^2*k)*p^4 = r^2/(256*(k:ℝ)^3) := by
        rw [← h3]
        dsimp [p]
        field_simp
        ring
      rw [eqC]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      calc
        16*(k:ℝ) ≤ 256*k := by gcongr; norm_num
        _ = 256*(k:ℝ)*1 := by ring
        _ ≤ 256*(k:ℝ)*k^2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hk') (by positivity)
        _ = _ := by ring
    rw [A, ← h2]
    have hh : r^2/(8*k) = r^2/(4*k)-r^2/(16*k)-r^2/(16*k) := by ring
    linarith

private theorem finish (k : ℕ) (hk : 1 ≤ k)
    (bound : ∀ (A : Finset ℕ), 0 < A.card → (∀ m, sumRep A m ≤ k) →
      ∃ S ⊆ A, IsSidon (S : Set ℕ) ∧ (A.card:ℝ)^(2/3:ℝ)/(8*k) ≤ S.card) :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, c*(n:ℝ)^(2/3:ℝ) ≤ H k n := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  refine ⟨1/(8*k), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  let b := (n:ℝ)^(2/3:ℝ)/(8*k)
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hb : b ≤ n := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<8*k)).mpr
    have hx := Real.rpow_le_rpow_of_exponent_le hn' (by norm_num : (2/3:ℝ) ≤ 1)
    rw [Real.rpow_one] at hx
    have hden : 1 ≤ (8:ℝ)*k := by linarith
    exact hx.trans (le_mul_of_one_le_right (by positivity) hden)
  have hh : ⌈b⌉₊ ≤ H k n := by
    apply le_csSup (show BddAbove {r : ℕ | r ≤ n ∧ ∀ A : Finset ℕ, A.card = n →
      (∀ m, sumRep A m ≤ k) → ∃ S ⊆ A, IsSidon (S : Set ℕ) ∧ r ≤ S.card} from
      ⟨n, fun _ hr => hr.1⟩)
    refine ⟨Nat.ceil_le.mpr hb, ?_⟩
    intro A hA hrep
    obtain ⟨S,hS,hsid,hsz⟩ := bound A (by omega) hrep
    rw [hA] at hsz
    exact ⟨S,hS,hsid,Nat.ceil_le.mpr hsz⟩
  calc
    _ = b := by dsimp [b]; ring
    _ ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
    _ ≤ _ := by exact_mod_cast hh

end SidonBound

theorem OMA.solution : type_of% @Erdos772.erdos_772.variants.alon_erdos := by
  intro k hk
  apply SidonBound.finish k hk
  intro A hn hrep
  obtain ⟨p,hp,hp',hparam⟩ := SidonBound.parameter A.card k hn hk
  obtain ⟨X, hXA, hscore⟩ := SidonSample.select A (SidonCollisions.triples A)
    (SidonCollisions.quads A) SidonCollisions.triPoints SidonCollisions.quadPoints p hp hp'
    (SidonCollisions.tri_valid A) (SidonCollisions.quad_valid A)
  obtain ⟨S, hSX, hsid, hclean⟩ := SidonCollisions.clean hXA
  refine ⟨S, hSX.trans hXA, hsid, hparam.trans ?_⟩
  apply le_trans _ (hscore.trans hclean)
  have h3 : ((SidonCollisions.triples A).card : ℝ) ≤ A.card*k := by
    exact_mod_cast SidonCollisions.tri_count A hrep
  have h4 : ((SidonCollisions.quads A).card : ℝ) ≤ (A.card:ℝ)^2*k := by
    exact_mod_cast SidonCollisions.quad_count A hrep
  exact sub_le_sub (sub_le_sub_left (mul_le_mul_of_nonneg_right h3 (pow_nonneg hp 3)) _)
    (mul_le_mul_of_nonneg_right h4 (pow_nonneg hp 4))