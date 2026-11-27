import FormalConjectures.ErdosProblems.«709»
import Mathlib.Logic.Godel.GodelBetaFunction

/-! A digit construction for intervals with no matching of distinct multiples. -/

open Finset Filter Asymptotics
open Erdos709

namespace DistinctWindow

-- The slope encodes the entire word. The intercept makes digit j disappear at time j.
abbrev Word (k : ℕ) := Fin (k+1) → Fin (k+2)

def slope {k : ℕ} (v : Word k) : ℕ := finFunctionFinEquiv v

def weight {k : ℕ} (v : Word k) : ℕ :=
  ∑ i : Fin (k+1), i.val * (v i).val * (k+2)^i.val

private theorem slope_inj (k : ℕ) : Function.Injective (@slope k) :=
  fun _ _ h => finFunctionFinEquiv.injective (Fin.ext h)

private theorem cancel_digit {k : ℕ} (j : Fin (k+1)) (v w : Word k)
    (h : v ∘ j.succAbove = w ∘ j.succAbove) :
    j.val * slope v + weight w = j.val * slope w + weight v := by
  unfold slope weight
  simp_rw [finFunctionFinEquiv_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases he : i = j
  · subst i
    ring
  · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq he
    have e : v (j.succAbove l) = w (j.succAbove l) := congrFun h l
    rw [e]

private theorem layer {a r start M k y : ℕ} (hr : 0 < r) (hra : r ≤ a)
    (hM : M ≤ a) (h0 : a ∣ start+r) (hy : a ∣ y)
    (hylo : start < y) (hyhi : y ≤ start+(k+1)*M) :
    ∃ j : Fin (k+1), y = start+r+j.val*a := by
  have hlo : start+r ≤ y := by
    by_contra! h
    have hdiv := Nat.dvd_sub h0 hy
    have := Nat.le_of_dvd (Nat.sub_pos_of_lt h) hdiv
    omega
  obtain ⟨j, hj⟩ := Nat.dvd_sub hy h0
  have eqy : y = start+r+j*a := by rw [mul_comm] at hj; omega
  refine ⟨⟨j, ?_⟩, eqy⟩
  by_contra! h
  have := Nat.mul_le_mul h hM
  omega

private theorem adm_nonempty (n : ℕ) : ({c : ℝ | IsAdmissible n c}).Nonempty := by
  classical
  refine ⟨(n : ℝ), ?_⟩
  intro A hcard ha start len hlen
  let M := A.sup id
  let ix : A ≃ Fin n := Fintype.equivFinOfCardEq (by simpa using hcard)
  have hlen' : n * M ≤ len := by exact_mod_cast hlen
  have hslot (a : A) : ∃ y ∈ window (start+(ix a).val*M) M, a.val ∣ y :=
    exists_multiple_in_window _ _ _ (by have := ha a.val a.prop; omega)
      (Finset.le_sup (f := id) a.prop)
  choose g hg hd using hslot
  refine ⟨fun x => if hx : x ∈ A then g ⟨x,hx⟩ else 0, ?_, ?_⟩
  · intro x hx y hy he
    change x ∈ A at hx
    change y ∈ A at hy
    simp only [dif_pos hx, dif_pos hy] at he
    let a : A := ⟨x,hx⟩
    let b : A := ⟨y,hy⟩
    have ga := hg a
    have gb := hg b
    simp only [window, mem_Icc] at ga gb
    have eqg : g a = g b := he
    have step (i j : ℕ) (h : i < j) : i*M+M ≤ j*M := by
      simpa [Nat.succ_mul] using Nat.mul_le_mul_right M (Nat.succ_le_of_lt h)
    have eqix : (ix a).val = (ix b).val := by
      rcases lt_trichotomy (ix a).val (ix b).val with h|h|h
      · have := step _ _ h; omega
      · exact h
      · have := step _ _ h; omega
    exact congrArg Subtype.val (ix.injective (Fin.ext eqix))
  · intro x hx
    simp only [dif_pos hx]
    let a : A := ⟨x,hx⟩
    refine ⟨?_, hd a⟩
    have z := hg a
    simp only [window, mem_Icc] at z ⊢
    have l := Nat.mul_le_mul_right M (Nat.succ_le_of_lt (ix a).isLt)
    rw [Nat.succ_mul] at l
    change start+1 ≤ g a ∧ g a ≤ start+len
    omega
-- Each layer has at most (k+2)^k values because one coordinate is invisible.
private theorem obstruction (n k : ℕ) (hn : (k+2)^(k+1) ≤ n) :
    ((k+1 : ℕ) : ℝ) / 2 ≤ f n := by
  classical
  let B := (k+2)^(k+1)
  let D := B.factorial
  let W := Finset.univ.sup (@weight k)
  let T := n+B+W+1
  let M := T*D+1
  let a (v : Word k) := (T+slope v)*D+1
  let r (v : Word k) := (W-weight v)*D+1
  have hD : 0 < D := Nat.factorial_pos _
  have hs (v : Word k) : slope v < B := (finFunctionFinEquiv v).isLt
  have hw (v : Word k) : weight v ≤ W := Finset.le_sup (by simp)
  have haeq (v : Word k) : a v = M+slope v*D := by dsimp [a,M]; ring
  have hM (v : Word k) : M ≤ a v := by rw [haeq]; omega
  have hr (v : Word k) : r v ≤ a v := by
    apply le_trans _ (hM v)
    exact Nat.succ_le_succ (Nat.mul_le_mul_right D (by dsimp [T]; omega))
  have hainj : Function.Injective a := by
    intro v w e
    rw [haeq,haeq] at e
    apply slope_inj k
    exact Nat.eq_of_mul_eq_mul_right hD (Nat.add_left_cancel e)
  have cp (v w : Word k) (h : slope v < slope w) : (a v).Coprime (a w) := by
    apply Nat.coprime_mul_succ
    rw [Nat.add_sub_add_left]
    exact Nat.dvd_factorial (by omega) (by have := hs w; omega)
  have pair : Set.Pairwise (↑(Finset.univ : Finset (Word k))) (fun v w => (a v).Coprime (a w)) := by
    intro v _ w _ h
    rcases lt_or_gt_of_ne (fun e => h (slope_inj k e)) with hl|hl
    · exact cp _ _ hl
    · exact (cp _ _ hl).symm
  let crt := Nat.chineseRemainderOfFinset (fun v => a v-r v) a univ
    (fun _ _ => Nat.succ_ne_zero _) pair
  let start := crt.val
  have hd (v : Word k) : a v ∣ start+r v := by
    apply Nat.modEq_zero_iff_dvd.mp
    have z := (crt.prop v (mem_univ v)).add_right (r v)
    rw [Nat.sub_add_cancel (hr v)] at z
    exact z.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl _))
  have hT : n+1 ≤ M := by
    have ht : T ≤ T*D := Nat.le_mul_of_pos_right _ hD
    dsimp [M,T] at *
    omega
  have hTpos : 2 ≤ M := by
    have hn1 : 0 < n := lt_of_lt_of_le (pow_pos (by omega) _) hn
    omega
  let U := Finset.Icc 2 (2*M)
  let S := Finset.univ.image a
  have hS : S ⊆ U := by
    intro x hx
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_Icc.mpr ⟨hTpos.trans (hM v), ?_⟩
    have hst : slope v ≤ T := by have := hs v; dsimp [T]; omega
    have := Nat.mul_le_mul_right D hst
    rw [haeq]
    dsimp [M] at *
    omega
  have hSc : S.card = B := by simp [S,Finset.card_image_of_injective _ hainj,B,Word]
  obtain ⟨A,hSA,hAU,hAc⟩ := Finset.exists_subsuperset_card_eq hS (n := n)
    (hSc ▸ hn) (by simp [U,Nat.card_Icc]; omega)
  have hAa (v : Word k) : a v ∈ A := hSA (Finset.mem_image_of_mem _ (mem_univ v))
  have hAn (x) (hx : x ∈ A) : 2 ≤ x := (Finset.mem_Icc.mp (hAU hx)).1
  have hsup : A.sup id ≤ 2*M := Finset.sup_le fun x hx => (Finset.mem_Icc.mp (hAU hx)).2
  apply le_csInf (adm_nonempty n)
  intro c hc
  by_contra! small
  have hc' : IsAdmissible n c := hc
  have len : c * ((A.sup id : ℕ) : ℝ) ≤ (((k+1)*M : ℕ) : ℝ) := by
    have hl := mul_le_mul_of_nonneg_right small.le (Nat.cast_nonneg (A.sup id) : (0 : ℝ) ≤ _)
    have hs' : ((A.sup id : ℕ) : ℝ) ≤ 2*(M : ℝ) := by exact_mod_cast hsup
    have hz := mul_le_mul_of_nonneg_left hs' (by positivity : (0 : ℝ) ≤ ((k+1 : ℕ) : ℝ)/2)
    push_cast at *
    nlinarith
  obtain ⟨g,hginj,hg⟩ := hc' A hAc hAn start ((k+1)*M) len
  have layers (v : Word k) :
      ∃ j : Fin (k+1), g (a v) = start+r v+j.val*a v := by
    obtain ⟨hy,hdiv⟩ := hg (a v) (hAa v)
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hy
    exact layer (Nat.succ_pos _) (hr v) (hM v) (hd v) hdiv (by omega) hu
  choose J hJ using layers
  let key (v : Word k) : Fin (k+1) × (Fin k → Fin (k+2)) := (J v, v ∘ (J v).succAbove)
  have inj : Function.Injective key := by
    intro v w e
    have ej : J v = J w := congrArg Prod.fst e
    have ev : v ∘ (J v).succAbove = w ∘ (J w).succAbove := congrArg Prod.snd e
    rw [← ej] at ev
    have hcancel := cancel_digit (J v) v w ev
    have hwv := Nat.sub_add_cancel (hw v)
    have hww := Nat.sub_add_cancel (hw w)
    have hsum : W-weight v+(J v).val*slope v = W-weight w+(J v).val*slope w := by omega
    have hmul := congrArg (· * D) hsum
    apply hainj
    apply hginj (hAa v) (hAa w)
    rw [hJ v,hJ w,← ej,haeq,haeq]
    dsimp only [r]
    nlinarith
  have h := Fintype.card_le_of_injective key inj
  simp [Word] at h
  rw [pow_succ] at h
  have hpos : 0 < (k+2)^k := pow_pos (by omega) _
  nlinarith
private theorem eventually_bound : ∀ᶠ n : ℕ in atTop,
    0 < Real.log (Real.log n) ∧ Real.log n / Real.log (Real.log n) ≤ 4*f n := by
  have hL := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hLL := Real.tendsto_log_atTop.comp hL
  filter_upwards [hL.eventually_ge_atTop 2, hLL.eventually_ge_atTop 2,
    eventually_ge_atTop (1 : ℕ)] with n hL2 hLL2 hn
  let L := Real.log n
  change 2 ≤ L at hL2
  change 2 ≤ Real.log L at hLL2
  change 0 < Real.log L ∧ L/Real.log L ≤ 4*f n
  have hpos : 0 < Real.log L := by linarith
  refine ⟨hpos, ?_⟩
  let x := L / Real.log L
  have hx : 1 ≤ x := (le_div_iff₀ hpos).mpr (by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < L); linarith)
  have hxl : x ≤ L/2 := (div_le_div_iff_of_pos_left (by linarith) hpos (by norm_num)).mpr hLL2
  let k := ⌊x⌋₊-1
  have hk1 : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith : 0 ≤ x)).mpr (by simpa using hx)
  have hk : k+1 = ⌊x⌋₊ := by dsimp [k]; omega
  have he : ((k+1 : ℕ) : ℝ) ≤ x := hk ▸ Nat.floor_le (by linarith)
  have hex : x < ((k+1 : ℕ) : ℝ)+1 := hk ▸ Nat.lt_floor_add_one x
  have hb : ((k+2 : ℕ) : ℝ) ≤ L := by push_cast at *; linarith
  have hlog : Real.log ((k+2 : ℕ) : ℝ) ≤ Real.log L := Real.log_le_log (by positivity) hb
  have hp : (k+2)^(k+1) ≤ n := by
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
    have aux : (((k+2 : ℕ) : ℝ)^(k+1)) ≤ (n : ℝ) := by
      apply (Real.log_le_log_iff (by positivity) hnpos).mp
      rw [Real.log_pow]
      calc
        _ ≤ ((k+1 : ℕ) : ℝ) * Real.log L := mul_le_mul_of_nonneg_left hlog (by positivity)
        _ ≤ x * Real.log L := mul_le_mul_of_nonneg_right he hpos.le
        _ = L := div_mul_cancel₀ _ hpos.ne'
    exact_mod_cast aux
  have hf := obstruction n k hp
  change x ≤ 4*f n
  push_cast at hex hf
  linarith [Nat.cast_nonneg (α := ℝ) k]

theorem weaker : ∃ c > (0 : ℝ), (fun n : ℕ => Real.log n ^ c) =O[atTop] f := by
  refine ⟨1/2, by norm_num, Asymptotics.isBigO_iff.mpr ⟨8, ?_⟩⟩
  filter_upwards [eventually_bound, (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1] with n hn hL
  let L := Real.log n
  change 1 ≤ L at hL
  have hp : 0 < L := by linarith
  have hs := Real.sqrt_pos.mpr hp
  have hsq := Real.sq_sqrt hp.le
  have hlog : Real.log L ≤ 2*Real.sqrt L := by
    have H := Real.log_le_sub_one_of_pos hs
    rw [Real.log_sqrt hp.le] at H
    linarith
  have haz : Real.sqrt L ≤ 2*(L / Real.log L) := by
    rw [← mul_div_assoc,le_div_iff₀ hn.1]
    nlinarith [mul_le_mul_of_nonneg_left hlog hs.le]
  have hbound : Real.sqrt L ≤ 8 * f n := by linarith [hn.2]
  have hf : 0 ≤ f n := by linarith
  change ‖L ^ (1/2 : ℝ)‖ ≤ 8 * ‖f n‖
  rw [← Real.sqrt_eq_rpow, Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg hf]
  exact hbound

end DistinctWindow

theorem OMA.solution : type_of% @Erdos709.erdos_709.variants.ersu_lower := DistinctWindow.weaker