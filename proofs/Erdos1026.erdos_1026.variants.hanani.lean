import FormalConjectures.ErdosProblems.«1026»

/-!
Hanani's bound on monotonic partitions. See Haim Hanani,
*On the number of monotonic subsequences*, Bulletin of the Research Council of Israel,
Section F (1957/58), pp. 11–13. Erdős reports the finite threshold in Problem 22 of
*Some unsolved problems in graph theory and combinatorial analysis* (1971),
https://www.renyi.hu/~p_erdos/1971-25.pdf#page=11.
-/

open Filter
open scoped Finset

/-- If increasing subsequences have bounded length, their ending lengths give decreasing classes. -/
theorem OMA.decreasing_partition_of_bounded_increasing {n k : ℕ} (x : Fin n → ℝ)
    (U : Finset (Fin n))
    (hbound : ∀ S ⊆ U, MonotoneOn x (S : Set (Fin n)) → S.card ≤ k) :
    ∃ W : Fin k → Finset (Fin n),
      (∀ j, AntitoneOn x (W j : Set (Fin n))) ∧
      (Pairwise fun i j => Disjoint (W i) (W j)) ∧
      Finset.univ.biUnion W = U := by
  classical
  let chains (i : Fin n) : Finset (Finset (Fin n)) := U.powerset.filter fun (S : Finset (Fin n)) =>
    MonotoneOn x (S : Set (Fin n)) ∧ i ∈ S ∧ ∀ j ∈ S, j ≤ i
  let height (i : Fin n) := (chains i).sup Finset.card
  have hsingle (i : Fin n) (hi : i ∈ U) : ({i} : Finset (Fin n)) ∈ chains i := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hi), ?_⟩
    simp only [Finset.coe_singleton, Finset.mem_singleton, forall_eq, le_refl, and_true]
    intro a ha b hb _
    simp only [Set.mem_singleton_iff] at ha hb
    simp [ha, hb]
  have hpos (i : Fin n) (hi : i ∈ U) : 1 ≤ height i := by
    simpa only [Finset.card_singleton] using Finset.le_sup (f := Finset.card) (hsingle i hi)
  have hmax (i : Fin n) : height i ≤ k := by
    apply Finset.sup_le
    intro S hS
    obtain ⟨hSU, hmono, _, _⟩ := Finset.mem_filter.mp hS
    exact hbound S (Finset.mem_powerset.mp hSU) hmono
  have hstep (i j : Fin n) (hi : i ∈ U) (hj : j ∈ U) (hij : i < j) (hxy : x i ≤ x j) :
      height i < height j := by
    obtain ⟨S, hS, hcard⟩ := Finset.exists_mem_eq_sup (chains i) ⟨{i}, hsingle i hi⟩ Finset.card
    obtain ⟨hSU, hmono, hiS, htop⟩ := Finset.mem_filter.mp hS
    have hjS : j ∉ S := fun h => (not_le_of_gt hij) (htop j h)
    have hins : insert j S ∈ chains j := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr (Finset.insert_subset hj (Finset.mem_powerset.mp hSU)),
        ?_, Finset.mem_insert_self j S, ?_⟩
      · intro a ha b hb hab
        obtain haj | haS := Finset.mem_insert.mp ha
        · subst a
          obtain hbj | hbS := Finset.mem_insert.mp hb
          · subst b
            rfl
          · exact ((not_lt_of_ge hab) ((htop b hbS).trans_lt hij)).elim
        · obtain hbj | hbS := Finset.mem_insert.mp hb
          · subst b
            exact (hmono haS hiS (htop a haS)).trans hxy
          · exact hmono haS hbS hab
      · intro a ha
        obtain rfl | ha := Finset.mem_insert.mp ha
        · rfl
        · exact (htop a ha).trans hij.le
    have hle := Finset.le_sup (f := Finset.card) hins
    rw [Finset.card_insert_of_notMem hjS, ← hcard] at hle
    exact hle
  let W (j : Fin k) := U.filter fun i => height i = j.val + 1
  refine ⟨W, ?_, ?_, ?_⟩
  · intro j a ha b hb hab
    obtain ⟨haU, haeq⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbU, hbeq⟩ := Finset.mem_filter.mp hb
    by_contra! h
    have hab' : a < b := lt_of_le_of_ne hab (by
      intro he
      exact (lt_irrefl _) (he ▸ h))
    exact ((hstep a b haU hbU hab' h.le).ne) (haeq.trans hbeq.symm)
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro a hai haj
    have hi := (Finset.mem_filter.mp hai).2
    have hj := (Finset.mem_filter.mp haj).2
    apply hij
    apply Fin.ext
    omega
  · ext a
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj⟩
      exact (Finset.mem_filter.mp hj).1
    · intro ha
      let j : Fin k := ⟨height a - 1, by
        have hp := hpos a ha
        have hm := hmax a
        omega⟩
      refine ⟨j, Finset.mem_filter.mpr ⟨ha, ?_⟩⟩
      change height a = height a - 1 + 1
      have hp := hpos a ha
      omega

/-- The finite size bound for Hanani's inductive monotonic partition. -/
theorem OMA.hanani_finite_partition {n : ℕ} (x : Fin n → ℝ)
    (k : ℕ) (U : Finset (Fin n)) (hcard : 2 * U.card ≤ k * (k + 3)) :
    ∃ W : Fin k → Finset (Fin n),
      (∀ j, MonotoneOn x (W j : Set (Fin n)) ∨ AntitoneOn x (W j : Set (Fin n))) ∧
      (Pairwise fun i j => Disjoint (W i) (W j)) ∧
      Finset.univ.biUnion W = U := by
  classical
  induction k generalizing U with
  | zero =>
    have hU : U = ∅ := Finset.card_eq_zero.mp (by omega)
    refine ⟨fun _ => ∅, ?_, ?_, ?_⟩
    · exact fun j => j.elim0
    · exact fun j => j.elim0
    · simp [hU]
  | succ k ih =>
    by_cases hlarge : ∃ S ⊆ U, MonotoneOn x (S : Set (Fin n)) ∧ k + 2 ≤ S.card
    · obtain ⟨T, hTU, hTmono, hTcard⟩ := hlarge
      obtain ⟨S, hST, hScard⟩ := Finset.exists_subset_card_eq hTcard
      have hSmono : MonotoneOn x (S : Set (Fin n)) := hTmono.mono hST
      have hSU : S ⊆ U := hST.trans hTU
      let R := U \ S
      have hsum : R.card + S.card = U.card := Finset.card_sdiff_add_card_eq_card hSU
      have htriangle : (k + 1) * (k + 1 + 3) = k * (k + 3) + 2 * (k + 2) := by ring
      have hR : 2 * R.card ≤ k * (k + 3) := by omega
      obtain ⟨V, hVmono, hVdisj, hVcover⟩ := ih R hR
      have hVsub (j : Fin k) : V j ⊆ R := by
        intro a ha
        rw [← hVcover]
        exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ha⟩
      have hVsep (j : Fin k) : Disjoint S (V j) := by
        apply Finset.disjoint_left.mpr
        intro a ha hV
        exact (Finset.mem_sdiff.mp (hVsub j hV)).2 ha
      let W : Fin (k + 1) → Finset (Fin n) := Fin.cases S V
      refine ⟨W, ?_, ?_, ?_⟩
      · exact Fin.cases (.inl hSmono) hVmono
      · intro a
        refine Fin.cases ?_ (fun i => ?_) a
        · intro b
          refine Fin.cases ?_ (fun j => ?_) b
          · intro h
            exact (h rfl).elim
          · exact fun _ => hVsep j
        · intro b
          refine Fin.cases ?_ (fun j => ?_) b
          · exact fun _ => (hVsep i).symm
          · exact fun h => hVdisj (fun he => h (congrArg Fin.succ he))
      · ext a
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Fin.exists_fin_succ, W,
          Fin.cases_zero, Fin.cases_succ]
        have hm : (∃ j, a ∈ V j) ↔ a ∈ R := by
          rw [← hVcover]
          simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        rw [hm]
        exact ⟨fun h => h.elim (fun hS => hSU hS) (fun hR => (Finset.mem_sdiff.mp hR).1), fun ha => by
          by_cases h : a ∈ S
          · exact .inl h
          · exact .inr (Finset.mem_sdiff.mpr ⟨ha, h⟩)⟩
    · have hbound (S : Finset (Fin n)) (hSU : S ⊆ U) (hmono : MonotoneOn x (S : Set (Fin n))) :
          S.card ≤ k + 1 := by
        by_contra! h
        exact hlarge ⟨S, hSU, hmono, by omega⟩
      obtain ⟨W, hanti, hdisj, hcover⟩ := OMA.decreasing_partition_of_bounded_increasing x U hbound
      exact ⟨W, fun j => .inr (hanti j), hdisj, hcover⟩

theorem OMA.solution : type_of% @Erdos1026.erdos_1026.variants.hanani := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_ge ((1 / ε) ^ 2)
  refine eventually_atTop.mpr ⟨N, fun n hn x _ => ?_⟩
  let k := ⌈Real.sqrt (2 * (n : ℝ))⌉₊
  have hk : Real.sqrt (2 * (n : ℝ)) ≤ (k : ℝ) := Nat.le_ceil _
  have hsquare : (Real.sqrt (2 * (n : ℝ))) ^ 2 = 2 * (n : ℝ) := Real.sq_sqrt (by positivity)
  have hksq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hk 2
  have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hcard : 2 * n ≤ k * (k + 3) := by
    have hc : (2 : ℝ) * n ≤ (k : ℝ) * ((k : ℝ) + 3) := by
      nlinarith only [hsquare, hksq, hkR]
    exact_mod_cast hc
  obtain ⟨W, hmono, hdisj, hcover⟩ :=
    OMA.hanani_finite_partition x k Finset.univ (by simpa only [Finset.card_univ, Fintype.card_fin]
      using hcard)
  refine ⟨k, W, hmono, hdisj, hcover, ?_⟩
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hlower : (1 / ε : ℝ) ≤ Real.sqrt (n : ℝ) := by
    calc
      _ = Real.sqrt ((1 / ε) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (hN.trans hnR)
  have hsmall : (1 : ℝ) ≤ Real.sqrt (n : ℝ) * ε := (div_le_iff₀ hε).mp hlower
  have hceil : (k : ℝ) < Real.sqrt (2 * (n : ℝ)) + 1 := Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at hceil
  nlinarith only [hceil, hsmall]