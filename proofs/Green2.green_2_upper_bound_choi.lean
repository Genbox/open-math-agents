import FormalConjectures.GreensOpenProblems.«2»

/-!
Ruzsa's dyadic lattice construction, ordered so an initial segment can have
any prescribed cardinality. A same-layer sum of equally paritied points
has lower score than one of its summands.

Reference: I. Z. Ruzsa, Sum-avoiding subsets, Ramanujan J. 9 (2005), 77–82.
Credit: @Genbox.
-/

open Filter Finset

namespace OMA

private theorem initial_segment {α : Type*} [DecidableEq α] (s : Finset α)
    (score : α → ℕ) (n : ℕ) (hn : n ≤ s.card) :
    ∃ t ⊆ s, t.card = n ∧ ∀ {x y}, x ∈ t → y ∈ s → score y < score x → y ∈ t := by
  suffices h : ∀ m, ∀ s : Finset α, s.card = m → n ≤ m →
      ∃ t ⊆ s, t.card = n ∧ ∀ {x y}, x ∈ t → y ∈ s → score y < score x → y ∈ t by
    exact h _ s rfl hn
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro s hm hn
    rcases eq_or_lt_of_le hn with rfl | hlt
    · exact ⟨s, Subset.rfl, hm, fun _ hy _ => hy⟩
    have hne : s.Nonempty := card_pos.mp (hm ▸ (by omega : 0 < m))
    obtain ⟨w, hw, hmax⟩ := exists_max_image s score hne
    have hc : (s.erase w).card = m - 1 := by rw [card_erase_of_mem hw, hm]
    obtain ⟨t, ht, hcard, hdown⟩ := ih (m - 1) (by omega) _ hc (by omega)
    refine ⟨t, ht.trans (erase_subset _ _), hcard, ?_⟩
    intro x y hx hy hxy
    apply hdown hx (mem_erase.mpr ⟨?_, hy⟩) hxy
    rintro rfl
    exact (not_lt_of_ge (hmax _ ((erase_subset _ _) (ht hx)))) hxy

private def digitsValue {d : ℕ} (b : ℕ) (x : Fin d → ℕ) : ℕ :=
  ∑ j, x j * b ^ j.val

private theorem digitsValue_succ {d b : ℕ} (x : Fin (d + 1) → ℕ) :
    digitsValue b x = x 0 + b * digitsValue b (fun j => x j.succ) := by
  unfold digitsValue
  rw [Fin.sum_univ_succ, mul_sum]
  simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
  congr 1
  apply sum_congr rfl
  intro j hj
  ring

private theorem digitsValue_inj {d b : ℕ} (hb : 1 < b) {x y : Fin d → ℕ}
    (hx : ∀ j, x j < b) (hy : ∀ j, y j < b)
    (h : digitsValue b x = digitsValue b y) : x = y := by
  induction d with
  | zero => exact Subsingleton.elim _ _
  | succ d ih =>
    rw [digitsValue_succ, digitsValue_succ] at h
    have hhead : x 0 = y 0 := by
      simpa [Nat.add_mod, Nat.mod_eq_of_lt (hx 0), Nat.mod_eq_of_lt (hy 0),
        Nat.mul_mod_right] using congrArg (fun t : ℕ => t % b) h
    rw [hhead, Nat.add_right_inj] at h
    have ht := ih (fun j => hx j.succ) (fun j => hy j.succ)
      (Nat.eq_of_mul_eq_mul_left (by omega) h)
    funext j
    exact Fin.cases hhead (congrFun ht) j

private abbrev Layer (d M R : ℕ) := Fin R × (Fin d → Fin M)

private def weight {d M R : ℕ} (p : Layer d M R) : ℕ :=
  p.1.val + 2 * ∑ j : Fin d, (p.2 j).val ^ 2

private def row {d M R : ℕ} (p : Layer d M R) : Fin (d + 1) → ℕ :=
  Fin.cons (2 ^ p.1.val) (fun j => 2 ^ p.1.val * (p.2 j).val)

private def base (M R : ℕ) : ℕ := 2 ^ R * (M + 1) + 1

private def code {d M R : ℕ} (p : Layer d M R) : ℤ :=
  digitsValue (base M R) (row p)

private theorem row_bound {d M R : ℕ} (p : Layer d M R) (j : Fin (d+1)) :
    row p j < base M R := by
  have hp : 2 ^ p.1.val ≤ 2 ^ R := Nat.pow_le_pow_right (by decide) p.1.isLt.le
  refine Fin.cases ?_ (fun j => ?_) j
  · change 2 ^ p.1.val < 2 ^ R * (M + 1) + 1
    calc
      2 ^ p.1.val ≤ 2 ^ R := hp
      _ ≤ 2 ^ R * (M + 1) := by simp [Nat.mul_add]
      _ < _ := by omega
  · change 2 ^ p.1.val * (p.2 j).val < 2 ^ R * (M + 1) + 1
    exact Nat.lt_succ_of_le (Nat.mul_le_mul hp (by have := (p.2 j).isLt; omega))

private theorem code_inj {d M R : ℕ} : Function.Injective (@code d M R) := by
  intro p q h
  have hb : 1 < base M R := by
    have hp : 0 < 2 ^ R * (M + 1) := by positivity
    unfold base
    omega
  unfold code at h
  have hrs := digitsValue_inj hb (row_bound p) (row_bound q) (Int.ofNat.inj h)
  have hfirst : (2 : ℕ) ^ p.1.val = 2 ^ q.1.val := congrFun hrs 0
  have hexp : p.1.val = q.1.val :=
    (pow_right_strictMono₀ (by decide : 1 < (2 : ℕ))).injective hfirst
  refine Prod.ext (Fin.ext hexp) ?_
  funext j
  apply Fin.ext
  have hs : 2 ^ p.1.val * (p.2 j).val = 2 ^ q.1.val * (q.2 j).val :=
    congrFun hrs j.succ
  rw [← hfirst] at hs
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hs

private def classOf {d M R : ℕ} (p : Layer d M R) : Fin R × (Fin d → Fin 2) :=
  (p.1, fun j => ⟨(p.2 j).val % 2, Nat.mod_lt _ (by decide)⟩)

private theorem weight_base_le {d M R : ℕ} (p : Layer d M R) (hp : p.1.val = 0) :
    weight p ≤ 2 * d * M^2 := by
  unfold weight
  rw [hp, zero_add, mul_assoc]
  apply Nat.mul_le_mul_left
  calc
    ∑ j : Fin d, (p.2 j).val ^ 2 ≤ ∑ _j : Fin d, M ^ 2 := by
      apply sum_le_sum
      exact fun j hj => Nat.pow_le_pow_left (p.2 j).isLt.le 2
    _ = d * M ^ 2 := by simp

private theorem same_class_sum {d M R : ℕ} {p q : Layer d M R} (hpq : p ≠ q)
    (hc : classOf p = classOf q) (hcap : max (weight p) (weight q) < R) :
    ∃ r : Layer d M R, weight r < max (weight p) (weight q) ∧
      code r = code p + code q := by
  have hi : p.1 = q.1 := congrArg (fun c : Fin R × (Fin d → Fin 2) => c.1) hc
  let i := p.1.val
  let x := fun j : Fin d => (p.2 j).val
  let y := fun j : Fin d => (q.2 j).val
  let z := fun j : Fin d => (x j + y j) / 2
  have hpar (j : Fin d) : x j % 2 = y j % 2 := by
    exact congrArg (fun c : Fin R × (Fin d → Fin 2) => (c.2 j).val) hc
  have hz (j : Fin d) : 2 * z j = x j + y j := by
    have := hpar j
    dsimp [z]
    omega
  have hzm (j : Fin d) : z j < M := by
    have hx : x j < M := (p.2 j).isLt
    have hy : y j < M := (q.2 j).isLt
    have := hz j
    omega
  have hdiff : ∃ j, x j ≠ y j := by
    by_contra! hall
    exact hpq (Prod.ext hi (funext (fun j => Fin.ext (hall j))))
  obtain ⟨j, hj⟩ := hdiff
  have hd : 4 ≤ ((x j : ℤ) - (y j : ℤ)) ^ 2 := by
    have hdif : 2 + x j ≤ y j ∨ 2 + y j ≤ x j := by
      have := hpar j
      omega
    rcases hdif with h | h
    · have h' : 2 + (x j : ℤ) ≤ y j := by exact_mod_cast h
      nlinarith [sq_nonneg ((x j : ℤ) - y j + 2)]
    · have h' : 2 + (y j : ℤ) ≤ x j := by exact_mod_cast h
      nlinarith [sq_nonneg ((x j : ℤ) - y j - 2)]
  have hsq : 4 ≤ ∑ l : Fin d, ((x l : ℤ) - (y l : ℤ)) ^ 2 :=
    hd.trans (single_le_sum (fun l _ => sq_nonneg ((x l : ℤ) - (y l : ℤ)))
      (mem_univ j))
  have hidentity :
      4 * (∑ l : Fin d, (z l : ℤ) ^ 2) +
        (∑ l : Fin d, ((x l : ℤ) - (y l : ℤ)) ^ 2) =
      2 * (∑ l : Fin d, (x l : ℤ) ^ 2) + 2 * ∑ l : Fin d, (y l : ℤ) ^ 2 := by
    simp only [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro l hl
    have hcast : 2 * (z l : ℤ) = (x l : ℤ) + (y l : ℤ) := by
      exact_mod_cast hz l
    calc
      4 * (z l : ℤ) ^ 2 + ((x l : ℤ) - (y l : ℤ)) ^ 2 =
          (2 * (z l : ℤ)) ^ 2 + ((x l : ℤ) - (y l : ℤ)) ^ 2 := by ring
      _ = _ := by rw [hcast]; ring
  have himprove : 2 * (∑ l : Fin d, (z l)^2) + 1 <
      max (2 * ∑ l : Fin d, (x l)^2) (2 * ∑ l : Fin d, (y l)^2) := by
    have hs' : 4 * (∑ l : Fin d, (z l : ℤ) ^ 2) + 4 ≤
        2 * (∑ l : Fin d, (x l : ℤ)^2) + 2 * ∑ l : Fin d, (y l : ℤ)^2 := by omega
    have hs : 4 * (∑ l : Fin d, (z l)^2) + 4 ≤
        2 * (∑ l : Fin d, (x l)^2) + 2 * ∑ l : Fin d, (y l)^2 := by
      exact_mod_cast hs'
    omega
  have hp : weight p = i + 2 * ∑ l : Fin d, (x l)^2 := rfl
  have hq : weight q = i + 2 * ∑ l : Fin d, (y l)^2 := by
    rw [weight, ← hi]
  have hiR : i + 1 < R := by omega
  let r : Layer d M R := (⟨i+1, hiR⟩, fun l => ⟨z l, hzm l⟩)
  refine ⟨r, ?_, ?_⟩
  · have hr : weight r = i + 1 + 2 * ∑ l : Fin d, (z l)^2 := rfl
    omega
  · have hrow (l : Fin (d+1)) : row r l = row p l + row q l := by
      refine Fin.cases ?_ (fun l => ?_) l
      · change (2:ℕ)^(i+1) = 2^p.1.val + 2^q.1.val
        rw [← hi, pow_succ]
        dsimp [i]
        omega
      · change (2:ℕ)^(i+1) * z l = 2^p.1.val * x l + 2^q.1.val * y l
        rw [← hi, pow_succ, mul_assoc, hz, mul_add]
    unfold code digitsValue
    norm_cast
    simp only [hrow, add_mul, sum_add_distrib]

private theorem ruzsa_finite {n d M : ℕ} (hn : n ≤ M^d) :
    ∃ A : Finset ℤ, A.card = n ∧
      Green2.maxRestrictedSumAvoidingSubsetSize A ≤ (2*d*M^2+1)*2^d := by
  classical
  let R := 2*d*M^2+1
  let s := (univ : Finset (Layer d M R)).filter (fun p => weight p < R)
  have hpz : 0 < R := by dsimp [R]; omega
  let zeroLayer : (Fin d → Fin M) → Layer d M R := fun x => (⟨0, hpz⟩, x)
  have hz_inj : Function.Injective zeroLayer := fun _ _ h => congrArg Prod.snd h
  have hz_into : univ.image zeroLayer ⊆ s := by
    intro p hp
    obtain ⟨x, -, rfl⟩ := mem_image.mp hp
    exact mem_filter.mpr ⟨mem_univ _, Nat.lt_succ_of_le (weight_base_le _ rfl)⟩
  have hsn : n ≤ s.card := by
    refine hn.trans ?_
    have h := card_le_card hz_into
    simpa [card_image_of_injective _ hz_inj, Fintype.card_fun] using h
  obtain ⟨t, ht, htn, hdown⟩ := initial_segment s weight n hsn
  let A := t.image code
  have hA : A.card = n := (card_image_of_injective _ code_inj).trans htn
  refine ⟨A, hA, ?_⟩
  unfold Green2.maxRestrictedSumAvoidingSubsetSize
  apply Finset.sup_le
  intro B hB
  obtain ⟨hBA, hdis⟩ := mem_filter.mp hB
  have hBA := mem_powerset.mp hBA
  let C := t.filter (fun p => code p ∈ B)
  have hC : C.image code = B := by
    ext b
    constructor
    · intro hb
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hb
      exact (mem_filter.mp hp).2
    · intro hb
      obtain ⟨p, hp, rfl⟩ := mem_image.mp (hBA hb)
      exact mem_image.mpr ⟨p, mem_filter.mpr ⟨hp, hb⟩, rfl⟩
  have hclass : Set.InjOn classOf (C : Set (Layer d M R)) := by
    intro p hp q hq heq
    by_contra hne
    obtain ⟨hpt, hpB⟩ := mem_filter.mp (mem_coe.mp hp)
    obtain ⟨hqt, hqB⟩ := mem_filter.mp (mem_coe.mp hq)
    have hpc : weight p < R := (mem_filter.mp (ht hpt)).2
    have hqc : weight q < R := (mem_filter.mp (ht hqt)).2
    obtain ⟨r, hw, hrs⟩ := same_class_sum hne heq (max_lt hpc hqc)
    have hrs' : r ∈ s := mem_filter.mpr ⟨mem_univ _, hw.trans (max_lt hpc hqc)⟩
    have hrt : r ∈ t := by
      rcases le_total (weight p) (weight q) with h | h
      · exact hdown hqt hrs' (by rwa [max_eq_right h] at hw)
      · exact hdown hpt hrs' (by rwa [max_eq_left h] at hw)
    have hrA : code r ∈ A := mem_image.mpr ⟨r, hrt, rfl⟩
    have hrB : code r ∈ B.restrictedSumset := by
      rw [hrs]
      exact mem_image.mpr ⟨(code p, code q), mem_offDiag.mpr
        ⟨hpB, hqB, fun h => hne (code_inj h)⟩, rfl⟩
    exact (Finset.disjoint_left.mp hdis hrB hrA)
  have hcard : C.card ≤ (univ : Finset (Fin R × (Fin d → Fin 2))).card :=
    card_le_card_of_injOn classOf (fun _ _ => mem_univ _) hclass
  rw [← hC, card_image_of_injective _ code_inj]
  simpa [Fintype.card_prod, Fintype.card_fun, R] using hcard

open Real

private theorem ruzsa_eventual :
    ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∃ A : Finset ℤ, A.card = n ∧
      (Green2.maxRestrictedSumAvoidingSubsetSize A : ℝ) < exp (C * √(log n)) := by
  refine ⟨10, by norm_num, ?_⟩
  have hT : Tendsto (fun n : ℕ => √(log (n : ℝ))) atTop atTop :=
    tendsto_sqrt_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hT.eventually (eventually_ge_atTop (2 : ℝ)), eventually_ge_atTop (2 : ℕ)]
    with n ht hn
  let t := √(log (n : ℝ))
  change 2 ≤ t at ht
  let d := ⌈t⌉₊
  let M := ⌈exp t⌉₊
  have ht0 : 0 ≤ t := by linarith
  have hd : t ≤ (d : ℝ) := Nat.le_ceil _
  have hd' : (d : ℝ) ≤ t+1 := (Nat.ceil_lt_add_one ht0).le
  have hd2 : (d : ℝ) ≤ 2*t := by linarith
  have hM : exp t ≤ (M : ℝ) := Nat.le_ceil _
  have hM0 : 0 < (M : ℝ) := (exp_pos _).trans_le hM
  have hM1 : 1 ≤ (M : ℝ) := (one_le_exp ht0).trans hM
  have hMlo : t ≤ log (M : ℝ) := by
    rw [← log_exp t]
    exact (log_le_log_iff (exp_pos _) hM0).mpr hM
  have hn0 : 0 < (n : ℝ) := by positivity
  have htsq : t^2 = log (n : ℝ) := sq_sqrt (log_natCast_nonneg n)
  have hnM : n ≤ M^d := by
    have hreal : (n : ℝ) ≤ (M : ℝ)^d := by
      apply (log_le_log_iff hn0 (pow_pos hM0 _)).mp
      rw [log_pow, ← htsq]
      simpa only [pow_two] using mul_le_mul hd hMlo ht0 (Nat.cast_nonneg d)
    exact_mod_cast hreal
  obtain ⟨A, hA, hbound⟩ := ruzsa_finite hnM
  refine ⟨A, hA, ?_⟩
  have hbound' : (Green2.maxRestrictedSumAvoidingSubsetSize A : ℝ) ≤
      (2*(d:ℝ)*(M:ℝ)^2+1)*(2:ℝ)^d := by exact_mod_cast hbound
  refine hbound'.trans_lt ?_
  have htwo : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
  have hlogtwo : log (2 : ℝ) ≤ 1 := by
    rw [← log_exp 1]
    exact (log_le_log_iff (by norm_num) (exp_pos _)).mpr htwo
  have hMhi : log (M : ℝ) ≤ t+1 := by
    have hm : (M : ℝ) ≤ 2 * exp t := by
      have hceil := (Nat.ceil_lt_add_one (exp_pos t).le).le
      linarith [one_le_exp ht0]
    calc
      log (M : ℝ) ≤ log (2*exp t) :=
        (log_le_log_iff hM0 (by positivity)).mpr hm
      _ ≤ t+1 := by rw [log_mul (by norm_num) (exp_pos _).ne', log_exp]; linarith
  have hR : 2*(d:ℝ)*(M:ℝ)^2+1 ≤ (2*(d:ℝ)+1)*(M:ℝ)^2 := by nlinarith
  have hLR : log (2*(d:ℝ)*(M:ℝ)^2+1) ≤ 2*(d:ℝ) + 2*log (M:ℝ) := by
    have h := (log_le_log_iff (by positivity) (by positivity)).mpr hR
    rw [log_mul (by positivity) (by positivity), log_pow] at h
    have hsmall := log_le_sub_one_of_pos (show 0 < 2*(d:ℝ)+1 by positivity)
    norm_num at h
    linarith
  apply (log_lt_log_iff (by positivity) (exp_pos _)).mp
  rw [log_mul (by positivity) (by positivity), log_pow, log_exp]
  have hdL := mul_le_mul_of_nonneg_left hlogtwo (Nat.cast_nonneg d)
  linarith

private theorem exp_sqrt_le_pow {C a : ℝ} (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, exp (C * √(log (n : ℝ))) ≤ (n : ℝ)^a := by
  have hT : Tendsto (fun n : ℕ => √(log (n : ℝ))) atTop atTop :=
    tendsto_sqrt_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hT.eventually (eventually_ge_atTop (C / a)), eventually_ge_atTop (1 : ℕ)]
    with n ht hn
  have h0 : 0 < (n : ℝ) := by positivity
  have ht0 : 0 ≤ √(log (n : ℝ)) := sqrt_nonneg _
  have ht' : C ≤ a * √(log (n : ℝ)) := by
    have h := (div_le_iff₀ ha).mp ht
    linarith
  rw [rpow_def_of_pos h0, exp_le_exp]
  calc
    C * √(log (n : ℝ)) ≤ (a * √(log (n : ℝ))) * √(log (n : ℝ)) :=
      mul_le_mul_of_nonneg_right ht' ht0
    _ = (√(log (n : ℝ)))^2 * a := by ring
    _ = _ := by rw [sq_sqrt (log_natCast_nonneg n)]

end OMA

theorem OMA.solution : type_of% @Green2.green_2_upper_bound_choi := by
  refine ⟨fun _ => 0, tendsto_const_nhds, ?_⟩
  obtain ⟨C, -, hw⟩ := OMA.ruzsa_eventual
  filter_upwards [hw, OMA.exp_sqrt_le_pow (by norm_num : 0 < (2 / 5 : ℝ))]
    with n ⟨A, hA, hb⟩ h₂
  exact ⟨A, hA, by simpa [hA] using hb.le.trans h₂⟩