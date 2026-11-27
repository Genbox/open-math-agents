import FormalConjectures.ErdosProblems.«806»

/-!
Count the sets that can be covered by a small sumset, after reducing
the proposed covering set modulo n.

Credit: @Genbox.
-/

open Finset Filter Real
open scoped Pointwise

namespace SmallSumsets

private def positiveRep {n : ℕ} (x : ZMod n) : ℕ :=
  if x.val = 0 then n else x.val

private theorem positiveRep_cast {n : ℕ} [NeZero n] (x : ZMod n) : (positiveRep x : ZMod n) = x := by
  unfold positiveRep
  split
  · rename_i h
    simpa [h] using (ZMod.natCast_zmod_val x)
  · exact ZMod.natCast_zmod_val x

private theorem positiveRep_inj (n : ℕ) [NeZero n] : Function.Injective (@positiveRep n) :=
  fun _ _ h => by simpa only [positiveRep_cast] using congrArg (fun a : ℕ => (a : ZMod n)) h

private theorem positiveRep_mem {n : ℕ} [NeZero n] (x : ZMod n) :
    positiveRep x ∈ Finset.Icc 1 n := by
  apply Finset.mem_Icc.mpr
  unfold positiveRep
  split
  · exact ⟨Nat.one_le_iff_ne_zero.mpr (NeZero.ne _), le_rfl⟩
  · have h := x.val_lt
    omega

private theorem exists_covering_tuple {n l : ℕ} (W : Finset (ZMod n)) (hW : W.card ≤ l) :
    ∃ b : Fin l → ZMod n, (↑W : Set (ZMod n)) ⊆ Set.range b := by
  classical
  let b (i : Fin l) : ZMod n :=
    if h : i.val < W.card then (W.equivFin.symm ⟨i.val, h⟩).val else 0
  refine ⟨b, ?_⟩
  intro w hw
  let j := W.equivFin ⟨w, hw⟩
  have hj := j.isLt
  refine ⟨⟨j.val, hj.trans_le hW⟩, ?_⟩
  simp [b, hj, j]

private theorem exists_uncovered {n m l : ℕ} [NeZero n]
    (hcount : n ^ l * (l ^ 2) ^ m < (n - m) ^ m) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 n ∧ A.card = m ∧
      ∀ B : Finset ℤ, A.map Nat.castEmbedding ⊆ B + B → l < B.card := by
  classical
  let U := Fin m ↪ ZMod n
  let V := Fin l → ZMod n
  let sums (b : V) : Finset (ZMod n) :=
    Finset.univ.image (fun p : Fin l × Fin l => b p.1 + b p.2)
  let bad (b : V) : Finset U := Finset.univ.filter (fun a => ∀ i, a i ∈ sums b)
  have hs (b : V) : (sums b).card ≤ l ^ 2 := by
    unfold sums
    exact Finset.card_image_le.trans (by simp [pow_two])
  have hb (b : V) : (bad b).card ≤ (l ^ 2) ^ m := by
    let f (a : bad b) (i : Fin m) : sums b :=
      ⟨a.val i, (Finset.mem_filter.mp a.property).2 i⟩
    have hf : Function.Injective f := by
      intro a c h
      apply Subtype.ext
      ext i
      exact congrArg Subtype.val (congrFun h i)
    have h := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] at h
    exact h.trans (Nat.pow_le_pow_left (hs b) _)
  let covered := (Finset.univ : Finset V).biUnion bad
  have hcov : covered.card ≤ n ^ l * (l ^ 2) ^ m := by
    calc
      _ ≤ ∑ b : V, (bad b).card := Finset.card_biUnion_le
      _ ≤ ∑ _b : V, (l ^ 2) ^ m := Finset.sum_le_sum (fun b _ => hb b)
      _ = _ := by simp [V, ZMod.card]
  have hu : (n - m) ^ m ≤ (Finset.univ : Finset U).card := by
    simp only [Finset.card_univ, U, Fintype.card_embedding_eq, Fintype.card_fin, ZMod.card]
    rw [Nat.descFactorial_eq_prod_range]
    calc
      _ = ∏ _i ∈ Finset.range m, (n - m) := by simp
      _ ≤ _ := Finset.prod_le_prod' (fun i hi => Nat.sub_le_sub_left (Finset.mem_range.mp hi).le n)
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card (hcov.trans_lt (hcount.trans_le hu))
  let A := Finset.univ.image (fun i : Fin m => positiveRep (a i))
  have hA : A.card = m := by
    have h : Function.Injective (fun i : Fin m => positiveRep (a i)) :=
      (positiveRep_inj n).comp a.injective
    change (Finset.univ.image (fun i : Fin m => positiveRep (a i))).card = m
    rw [Finset.card_image_of_injective _ h]
    simp
  refine ⟨A, ?_, hA, ?_⟩
  · intro q hq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hq
    exact positiveRep_mem (a i)
  · intro B hB
    by_contra! hsmall
    let W := B.image (fun x : ℤ => (x : ZMod n))
    have hW : W.card ≤ l := Finset.card_image_le.trans hsmall
    obtain ⟨b, hb'⟩ := exists_covering_tuple W hW
    apply ha
    refine Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro i
    have hi : positiveRep (a i) ∈ A := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hj : (positiveRep (a i) : ℤ) ∈ B + B :=
      hB (Finset.mem_map.mpr ⟨_, hi, rfl⟩)
    obtain ⟨u, hu, v, hv, he⟩ := Finset.mem_add.mp hj
    obtain ⟨j, hj⟩ := hb' (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
    obtain ⟨k, hk⟩ := hb' (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
    refine Finset.mem_image.mpr ⟨(j, k), Finset.mem_univ _, ?_⟩
    rw [hj, hk, ← Int.cast_add, he, Int.cast_natCast, positiveRep_cast]

theorem eventual_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 n ∧ c * √(n : ℝ) ≤ A.card ∧ (A.card : ℝ) ≤ √(n : ℝ) ∧
      ∀ B : Finset ℤ, A.map Nat.castEmbedding ⊆ B + B →
        c * log (log n) / log n * √(n : ℝ) ≤ B.card := by
  refine ⟨1 / 32, by norm_num, ?_⟩
  have hT : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (4 : ℕ), hT.eventually (eventually_ge_atTop (2 : ℝ))]
    with n hn ht
  let : NeZero n := ⟨by omega⟩
  let s := √(n : ℝ)
  let t := log (n : ℝ)
  let L := log t
  let x := (1 / 32 : ℝ) * L / t * s
  let m := ⌊s⌋₊
  let l := ⌊x⌋₊
  change 2 ≤ t at ht
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have ht0 : 0 < t := by linarith
  have hL : 0 < L := log_pos (by linarith)
  have hs : 2 ≤ s := by
    change (2 : ℝ) ≤ √(n : ℝ)
    rw [le_sqrt (by norm_num) hn0.le]
    norm_num
    exact_mod_cast hn
  have hs0 : 0 < s := by linarith
  have hm : (m : ℝ) ≤ s := Nat.floor_le hs0.le
  have hmlo : s / 2 ≤ (m : ℝ) := by
    have h := Nat.lt_floor_add_one s
    change s < (m : ℝ) + 1 at h
    linarith only [h, hs]
  have hm0 : 0 < m := by
    have h : 0 < (m : ℝ) := by linarith
    exact_mod_cast h
  have hl : (l : ℝ) ≤ x := Nat.floor_le (by dsimp [x]; positivity)
  have hxx : x * t = L * s / 32 := by
    dsimp only [x]
    field_simp [ht0.ne']
  have hlt : (l : ℝ) * t ≤ L * s / 32 := by
    rw [← hxx]
    exact mul_le_mul_of_nonneg_right hl ht0.le
  have hsq : s ^ 2 = (n : ℝ) := sq_sqrt hn0.le
  have hhalf : s ≤ (n : ℝ) / 2 := by nlinarith only [hsq, mul_nonneg hs0.le (sub_nonneg.mpr hs)]
  have hmn : m ≤ n := by
    have h : (m : ℝ) ≤ n := by linarith
    exact_mod_cast h
  have hdiff : (n : ℝ) / 2 ≤ ((n - m : ℕ) : ℝ) := by
    rw [Nat.cast_sub hmn]
    linarith
  have hcount : n ^ l * (l ^ 2) ^ m < (n - m) ^ m := by
    by_cases hl0 : l = 0
    · have hpos : 0 < n - m := by
        have h : 0 < ((n - m : ℕ) : ℝ) := by linarith
        exact_mod_cast h
      simpa [hl0, zero_pow hm0.ne'] using (pow_pos hpos m)
    · have hlpos : 0 < (l : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hl0
      have hsqt : (√t)^2 = t := sq_sqrt ht0.le
      have hsqt0 : 0 < √t := sqrt_pos.mpr ht0
      have hlog : L ≤ 2 * √t := by
        have h := log_le_sub_one_of_pos hsqt0
        rw [log_sqrt ht0.le] at h
        change log t ≤ 2 * √t
        linarith
      have hxs : x ≤ (2 * √t) * s / (32 * t) := by
        calc
          x = L * (s / (32 * t)) := by dsimp [x]; ring
          _ ≤ (2 * √t) * (s / (32 * t)) :=
            mul_le_mul_of_nonneg_right hlog (div_nonneg hs0.le (by positivity))
          _ = _ := by ring
      have hsqle : (l : ℝ)^2 ≤ (n : ℝ) / (2 * t) := by
        calc
          _ ≤ ((2 * √t) * s / (32 * t))^2 :=
            pow_le_pow_left₀ hlpos.le (hl.trans hxs) 2
          _ = (n : ℝ) / (256 * t) := by
            rw [div_pow, mul_pow, mul_pow, hsqt, hsq]
            field_simp [ht0.ne']
            ring
          _ ≤ _ := div_le_div_of_nonneg_left hn0.le (by positivity) (by nlinarith)
      have hlogs : log ((l : ℝ)^2) ≤ t - log 2 - L := by
        calc
          _ ≤ log ((n : ℝ) / (2 * t)) := (log_le_log_iff (by positivity) (by positivity)).mpr hsqle
          _ = _ := by
            rw [log_div hn0.ne' (by positivity), log_mul (by norm_num) ht0.ne']
            change log (n : ℝ) - (log 2 + log t) = log (n : ℝ) - log 2 - log t
            ring
      have hsmall : (n : ℝ) ^ l * ((l : ℝ) ^ 2) ^ m < ((n : ℝ) / 2) ^ m := by
        apply (log_lt_log_iff (by positivity) (by positivity)).mp
        rw [log_mul (by positivity) (by positivity), log_pow (n : ℝ) l,
          log_pow ((l : ℝ)^2) m, log_pow ((n : ℝ) / 2) m,
          log_div hn0.ne' (by norm_num)]
        have h₁ := mul_le_mul_of_nonneg_left hlogs (Nat.cast_nonneg m)
        have hmL := mul_le_mul_of_nonneg_right hmlo hL.le
        have hsL : 0 < L * s := mul_pos hL hs0
        change (l : ℝ) * t + (m : ℝ) * log ((l : ℝ) ^ 2) < (m : ℝ) * (t - log 2)
        nlinarith only [hlt, h₁, hmL, hsL]
      have hR := hsmall.trans_le (pow_le_pow_left₀ (by positivity) hdiff m)
      exact_mod_cast hR
  obtain ⟨A, ha, hac, hB⟩ := exists_uncovered hcount
  refine ⟨A, ha, ?_, ?_, ?_⟩
  · rw [hac]
    linarith
  · rw [hac]
    exact hm
  · intro B hcover
    have hbig : (l : ℝ) + 1 ≤ B.card := by exact_mod_cast Nat.succ_le_of_lt (hB B hcover)
    exact ((Nat.lt_floor_add_one x).le.trans hbig)

end SmallSumsets

theorem OMA.solution : type_of% @Erdos806.erdos_806.variants.erdos_newman :=
  SmallSumsets.eventual_lower