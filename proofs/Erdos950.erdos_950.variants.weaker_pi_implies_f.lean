import FormalConjectures.ErdosProblems.«950»
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.NumberTheory.Harmonic.Bounds

/-! A short interval sieve and a dyadic summation for reciprocal prime differences. -/

noncomputable section
open Finset Filter Asymptotics
namespace PrimeWindows



private def valFactor (p n : ℕ) : ℝ := if p ∣ n then (1:ℝ)/p-1 else 1/(p:ℝ)
private def K (d n : ℕ) : ℝ := ∏ p ∈ d.primeFactors, valFactor p n

set_option maxHeartbeats 1200000 in
private theorem val_bound {p : ℕ} (hp : p.Prime) (n : ℕ) : |valFactor p n| ≤ 1 := by
  have h : (1:ℝ)/(p:ℝ) ≤ 1 := (div_le_one (by exact_mod_cast hp.pos)).2 (by exact_mod_cast hp.one_le)
  unfold valFactor
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith [show (0:ℝ) ≤ 1/(p:ℝ) by positivity]

set_option maxHeartbeats 1200000 in
private theorem K_bound (d n : ℕ) : |K d n| ≤ 1 := by
  rw [K,Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun p hp => val_bound (Nat.prime_of_mem_primeFactors hp) n)

set_option maxHeartbeats 1200000 in
private theorem K_prime {d p : ℕ} (hd : Squarefree d) (hp : p.Prime) (hlt : d < p) :
    K d p = 1/(d:ℝ) := by
  have z (q : ℕ) (hq : q ∈ d.primeFactors) : ¬ q ∣ p := by
    have hqp := Nat.prime_of_mem_primeFactors hq
    intro hdiv
    have he := (Nat.prime_dvd_prime_iff_eq hqp hp).mp hdiv
    have hqd := Nat.le_of_dvd (Nat.pos_of_ne_zero hd.ne_zero) (Nat.dvd_of_mem_primeFactors hq)
    omega
  unfold K
  calc
    _ = ∏ q ∈ d.primeFactors, (q:ℝ)⁻¹ := by
      apply Finset.prod_congr rfl
      intro q hq
      simp [valFactor,z q hq]
    _ = _ := by rw [Finset.prod_inv_distrib,← Nat.cast_prod,Nat.prod_primeFactors_of_squarefree hd]; simp

set_option maxHeartbeats 1200000 in
private theorem crt_sum (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime) (start : ℕ)
    (g : ℕ → ℕ → ℝ) :
    ∑ i ∈ Finset.range (∏ p ∈ P, p), ∏ p ∈ P, g p ((start+i)%p) =
    ∏ p ∈ P, ∑ j ∈ Finset.range p, g p j := by
  classical
  let a (p : P) := p.val
  have hne (p : P) : a p ≠ 0 := (hp _ p.prop).ne_zero
  let (p : P) : NeZero (a p) := ⟨hne p⟩
  let m := ∏ p : P, a p
  have : NeZero m := ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => hne p)⟩
  let e := ZMod.prodEquivPi a (fun i j hij => (Nat.coprime_primes (hp _ i.prop) (hp _ j.prop)).mpr
    (fun eq => hij (Subtype.ext eq)))
  let shift := Equiv.addLeft (start : ZMod m)
  let F (v : (p : P) → ZMod (a p)) := ∏ p, g p.val (v p).val
  have aux (q : ℕ) [NeZero q] (i : Fin q) : ZMod.finEquiv q i = (i.val : ZMod q) := by
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q => apply Fin.ext; exact (Nat.mod_eq_of_lt i.isLt).symm
  have eqg (i : Fin m) : F (e (shift (ZMod.finEquiv m i))) = ∏ p ∈ P, g p ((start+i.val)%p) := by
    change (∏ p : P, g p.val ((e ((start:ZMod m)+ZMod.finEquiv m i)) p).val) = _
    rw [aux, ← Nat.cast_add]
    rw [map_natCast]
    change (∏ p : P, g p.val (((start+i.val:ℕ) : ZMod (a p)).val)) = _
    simp only [ZMod.val_natCast]
    exact Finset.prod_coe_sort P (fun p => g p ((start+i.val)%p))
  have hm : m = ∏ p ∈ P, p := Finset.prod_coe_sort P id
  rw [← hm,← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ i : Fin m, F (e (shift (ZMod.finEquiv m i))) := Finset.sum_congr rfl (fun i _ => (eqg i).symm)
    _ = ∑ v, F v := Equiv.sum_comp (((ZMod.finEquiv m).toEquiv.trans shift).trans e.toEquiv) F
    _ = ∏ p : P, ∑ j : ZMod (a p), g p.val j.val := (Fintype.prod_sum (fun (p : P) (j : ZMod (a p)) => g p.val j.val)).symm
    _ = ∏ p : P, ∑ j ∈ Finset.range p.val, g p.val j := by
      apply Finset.prod_congr rfl
      intro p _
      rw [← Fin.sum_univ_eq_sum_range]
      symm
      calc
        _ = ∑ i : Fin (a p), g p.val (ZMod.finEquiv (a p) i).val := by
          apply Finset.sum_congr rfl
          intro i _
          rw [aux,ZMod.val_natCast,Nat.mod_eq_of_lt i.isLt]
        _ = _ := Equiv.sum_comp (ZMod.finEquiv (a p)).toEquiv (fun j => g p.val j.val)
    _ = _ := Finset.prod_coe_sort P (fun p => ∑ j ∈ Finset.range p, g p j)
private def localVal (p r : ℕ) : ℝ := 1/(p:ℝ) - (if r=0 then 1 else 0)
private def cell (d p r : ℕ) : ℝ := if p ∈ d.primeFactors then localVal p r else 1

set_option maxHeartbeats 1200000 in
private theorem K_extend {d : ℕ} {P : Finset ℕ} (h : d.primeFactors ⊆ P) (n : ℕ) :
    K d n = ∏ p ∈ P, cell d p (n%p) := by
  calc
    _ = ∏ p ∈ d.primeFactors, cell d p (n%p) := by
      apply Finset.prod_congr rfl
      intro p hp
      by_cases z : p ∣ n <;> simp [cell,localVal,valFactor,hp,Nat.dvd_iff_mod_eq_zero] at z ⊢ <;> simp [z]
    _ = _ := Finset.prod_subset h (by intro p _ hp; simp [cell,hp])

set_option maxHeartbeats 1200000 in
private theorem local_zero {p : ℕ} (hp : 0 < p) :
    ∑ r ∈ range p, localVal p r = 0 := by
  simp [localVal, Finset.sum_sub_distrib, hp, hp.ne']

set_option maxHeartbeats 1200000 in
private theorem local_sq {p : ℕ} (hp : 0 < p) :
    ∑ r ∈ range p, localVal p r * localVal p r ≤ 1 := by
  have e (r : ℕ) : localVal p r * localVal p r =
      ((1:ℝ)/p)^2 + (if r=0 then 1-2/(p:ℝ) else 0) := by
    unfold localVal; split_ifs <;> ring
  simp_rw [e]
  simp [Finset.sum_add_distrib,hp]
  have h : (0:ℝ) < p := by exact_mod_cast hp
  field_simp
  nlinarith

private def period (d e : ℕ) := ∏ p ∈ d.primeFactors ∪ e.primeFactors, p

set_option maxHeartbeats 1200000 in
private theorem period_property {d e : ℕ} (hd : Squarefree d) (he : Squarefree e) :
    0 < period d e ∧ period d e ≤ d*e := by
  let P := d.primeFactors ∪ e.primeFactors
  have pp (p) (hp : p ∈ P) : p.Prime :=
    (Finset.mem_union.mp hp).elim Nat.prime_of_mem_primeFactors Nat.prime_of_mem_primeFactors
  have h1 : 0 < period d e := Finset.prod_pos (fun p hp => (pp p hp).pos)
  have h2 : 0 < ∏ p ∈ d.primeFactors ∩ e.primeFactors, p :=
    Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp hp).1).pos)
  refine ⟨h1, ?_⟩
  calc
    _ ≤ period d e * (∏ p ∈ d.primeFactors ∩ e.primeFactors, p) := Nat.le_mul_of_pos_right _ h2
    _ = d*e := by rw [period,Finset.prod_union_inter,Nat.prod_primeFactors_of_squarefree hd,Nat.prod_primeFactors_of_squarefree he]

set_option maxHeartbeats 1200000 in
private theorem block {d e : ℕ} (hd : Squarefree d) (he : Squarefree e) (start : ℕ) :
    ∑ i ∈ range (period d e), K d (start+i)*K e (start+i) ≤
      if d=e then 1 else 0 := by
  let P := d.primeFactors ∪ e.primeFactors
  have pp (p) (hp : p ∈ P) : p.Prime :=
    (Finset.mem_union.mp hp).elim Nat.prime_of_mem_primeFactors Nat.prime_of_mem_primeFactors
  let g (p r : ℕ) := cell d p r * cell e p r
  have ec (n : ℕ) : K d n*K e n = ∏ p ∈ P, g p (n%p) := by
    rw [K_extend (P := P) Finset.subset_union_left, K_extend (d := e) (P := P) Finset.subset_union_right,
      ← Finset.prod_mul_distrib]
  simp_rw [ec]
  change ∑ i ∈ range (∏ p ∈ P, p), _ ≤ _
  rw [crt_sum P pp start g]
  by_cases eq : d=e
  · subst e
    rw [if_pos rfl]
    apply Finset.prod_le_one
    · intro p _
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    · intro p hp
      have z : p ∈ d.primeFactors := by simpa [P] using hp
      simpa only [g,cell,if_pos z] using local_sq (pp p hp).pos
  · rw [if_neg eq]
    apply le_of_eq
    apply Finset.prod_eq_zero_iff.mpr
    have neq : d.primeFactors ≠ e.primeFactors := by
      intro hp
      have := congrArg (fun x : Finset ℕ => ∏ p ∈ x, p) hp
      simp [Nat.prod_primeFactors_of_squarefree hd,Nat.prod_primeFactors_of_squarefree he] at this
      contradiction
    obtain ⟨p,hp⟩ := Finset.ext_iff.not.mp neq |> Classical.not_forall.mp
    by_cases hpd : p ∈ d.primeFactors
    · have hpe : p ∉ e.primeFactors := by tauto
      have hm : p ∈ P := Finset.mem_union_left _ hpd
      exact ⟨p,hm,by simpa only [g,cell,if_pos hpd,if_neg hpe,mul_one] using local_zero (pp p hm).pos⟩
    · have hpe : p ∈ e.primeFactors := by tauto
      have hm : p ∈ P := Finset.mem_union_right _ hpe
      exact ⟨p,hm,by simpa only [g,cell,if_neg hpd,if_pos hpe,one_mul] using local_zero (pp p hm).pos⟩
set_option maxHeartbeats 1200000 in
private theorem interval_corr {d e : ℕ} (hd : Squarefree d) (he : Squarefree e) (start h : ℕ) :
    ∑ i ∈ range h, K d (start+i)*K e (start+i) ≤
      (if d=e then (h:ℝ)/d else 0) + d*e := by
  let m := period d e
  have hm := (period_property hd he).1
  have hm0 : 0 < m := hm
  have hblocks (b : ℕ) :
      ∑ i ∈ range (b*m), K d (start+i)*K e (start+i) ≤ (b:ℝ)*(if d=e then 1 else 0) := by
    induction b with
    | zero => simp
    | succ b ih =>
      rw [Nat.succ_mul,Finset.sum_range_add,Nat.cast_succ,add_mul,one_mul]
      apply add_le_add ih
      simpa [Nat.add_assoc] using block hd he (start+b*m)
  have hrest (b r : ℕ) : ∑ i ∈ range r, K d (start+(b+i))*K e (start+(b+i)) ≤ r := by
    calc
      _ ≤ ∑ i ∈ range r, (1:ℝ) := Finset.sum_le_sum fun i _ =>
        (le_abs_self _).trans (by rw [abs_mul]; exact
          (mul_le_mul (K_bound d _) (K_bound e _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _))
      _ = _ := by simp
  have hx : h/m*m+h%m = h := Nat.div_add_mod' h m
  conv_lhs => rw [← hx,Finset.sum_range_add]
  have H := add_le_add (hblocks (h/m)) (hrest (h/m*m) (h%m))
  apply H.trans
  have hr : ((h%m:ℕ):ℝ) ≤ (d:ℝ)*e := by
    exact_mod_cast (Nat.mod_lt h hm0).le.trans (period_property hd he).2
  apply add_le_add _ hr
  by_cases eq : d=e
  · subst e
    have hdm : m=d := by simp [m,period,Nat.prod_primeFactors_of_squarefree hd]
    simp only [if_true,mul_one,hdm]
    rw [le_div_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hd.ne_zero : (0:ℝ) < d)]
    exact_mod_cast Nat.div_mul_le_self h d
  · simp [eq]

private def divisorsTo (Q : ℕ) : Finset ℕ := (Icc 1 Q).filter Squarefree
private def mass (Q : ℕ) : ℝ := ∑ d ∈ divisorsTo Q, 1/(d:ℝ)
private def kernel (Q n : ℕ) : ℝ := ∑ d ∈ divisorsTo Q, K d n

set_option maxHeartbeats 1200000 in
private theorem energy (start h Q : ℕ) :
    ∑ i ∈ range h, kernel Q (start+i)^2 ≤ h*mass Q + (Q:ℝ)^4 := by
  let D := divisorsTo Q
  have hd (d : ℕ) (h : d ∈ D) : d ≤ Q ∧ Squarefree d := by
    obtain ⟨h,h'⟩ := Finset.mem_filter.mp h
    exact ⟨(Finset.mem_Icc.mp h).2,h'⟩
  have hcard : D.card ≤ Q := (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
    (show (Icc 1 Q).card = Q by simp)
  have hsum (i : ℕ) : kernel Q (start+i)^2 =
      ∑ d ∈ D, ∑ e ∈ D, K d (start+i)*K e (start+i) := by
    simp [kernel,D,pow_two,Finset.mul_sum,mul_comm]
  simp_rw [hsum]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ d ∈ D, ∑ e ∈ D, ((if d=e then (h:ℝ)/d else 0)+(Q:ℝ)^2) := by
      apply Finset.sum_le_sum
      intro d hD
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro e hE
      apply (interval_corr (hd d hD).2 (hd e hE).2 start h).trans
      apply add_le_add le_rfl
      exact_mod_cast (Nat.mul_le_mul (hd d hD).1 (hd e hE).1).trans_eq (pow_two Q).symm
    _ = h * mass Q + (D.card:ℝ)^2*Q^2 := by
      simp [Finset.sum_add_distrib, mass,← Finset.mul_sum,div_eq_mul_inv,D,mul_assoc,pow_two]
    _ ≤ _ := by
      apply add_le_add le_rfl
      calc
        _ ≤ (Q:ℝ)^2*Q^2 := by gcongr
        _ = _ := by ring
private def zetaTwo : ℝ := ∑' n : ℕ, 1/(n:ℝ)^2

set_option maxHeartbeats 1200000 in
private theorem size_mass (Q : ℕ) : Real.log (Q+1 : ℕ) ≤ zetaTwo*mass Q := by
  classical
  let I := Finset.Icc 1 Q
  let D := divisorsTo Q
  choose a b eqn sf using Nat.sq_mul_squarefree
  let pair (n : ℕ) := (b n,a n)
  have hinj : Function.Injective pair := by
    intro n m h
    have eb : b n = b m := congrArg Prod.fst h
    have ea : a n = a m := congrArg Prod.snd h
    rw [←eqn n,eb,ea,eqn m]
  have sub : I.image pair ⊆ I ×ˢ D := by
    rintro u hu
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hn1,hnQ⟩ := Finset.mem_Icc.mp hn
    have e := eqn n
    have ha : 0 < a n := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at e; omega
    have hb : 0 < b n := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at e; omega
    have ha' := Nat.le_mul_of_pos_left (a n) (pow_pos hb 2)
    have hb' := Nat.le_mul_of_pos_right (b n ^ 2) ha
    have hb2 : b n ≤ b n^2 := by nlinarith
    change (b n,a n) ∈ I ×ˢ D
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hb,by dsimp; omega⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ha,by dsimp; omega⟩,sf n⟩⟩
  let wt (u : ℕ × ℕ) : ℝ := (1/(u.1:ℝ)^2)*(1/(u.2:ℝ))
  calc
    _ ≤ (harmonic Q : ℝ) := log_add_one_le_harmonic Q
    _ = ∑ n ∈ I, wt (pair n) := by
      simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
      apply Finset.sum_congr rfl
      intro n _
      have e := eqn n
      dsimp [wt,pair]
      conv_lhs => rw [←e]
      push_cast
      simp [one_div,mul_comm]
    _ = ∑ u ∈ I.image pair, wt u := (Finset.sum_image hinj.injOn).symm
    _ ≤ ∑ u ∈ I ×ˢ D, wt u := Finset.sum_le_sum_of_subset_of_nonneg sub
        (fun _ _ _ => by dsimp [wt]; positivity)
    _ = (∑ b ∈ I, 1/(b:ℝ)^2)*mass Q := by
      rw [Finset.sum_product]
      simp [wt,D,mass,Finset.sum_mul,Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => by positivity)
      exact (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).sum_le_tsum I (fun _ _ => by positivity)

set_option maxHeartbeats 1200000 in
private theorem prime_block (start j : ℕ) :
    (((range (16^j)).filter (fun i => (start+i).Prime)).card : ℝ) * (j+1) ≤
      (1+4*(zetaTwo+1)/Real.log 2) * 16^j := by
  classical
  let Q := 2^j
  let h := 16^j
  let A := (range h).filter (fun i => (start+i).Prime)
  let B := A.filter (fun i => Q < start+i)
  have hQ : 0 < Q := pow_pos (by decide) _
  have hQ4 : Q^4 = h := by dsimp [Q,h]; rw [← pow_mul, Nat.mul_comm j 4, pow_mul]; norm_num
  have h1 : (1:ℝ) ≤ mass Q := by
    have z := Finset.single_le_sum (f := fun d : ℕ => 1/(d:ℝ))
      (fun i (_ : i ∈ divisorsTo Q) => by positivity) (a := 1)
      (show 1 ∈ divisorsTo Q by simp [divisorsTo,show 1 ≤ Q from hQ])
    simpa [mass] using z
  have ke (i : ℕ) (hi : i ∈ B) : kernel Q (start+i) = mass Q := by
    obtain ⟨hi,hq⟩ := Finset.mem_filter.mp hi
    have hp := (Finset.mem_filter.mp hi).2
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨hr,hs⟩ := Finset.mem_filter.mp hd
    exact K_prime hs hp ((Finset.mem_Icc.mp hr).2.trans_lt hq)
  have bs : B ⊆ range h := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have e := calc
    (B.card:ℝ)*(mass Q)^2 = ∑ i ∈ B, kernel Q (start+i)^2 := by
      rw [← Finset.sum_congr rfl (fun i hi => congrArg (·^2) (ke i hi).symm)]
      simp
    _ ≤ ∑ i ∈ range h, kernel Q (start+i)^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg bs (fun _ _ _ => sq_nonneg _)
    _ ≤ _ := energy start h Q
  have h4 : (Q:ℝ)^4=h := by exact_mod_cast hQ4
  rw [h4] at e
  have hBC : (B.card:ℝ)*mass Q ≤ 2*h := by
    apply (mul_le_mul_iff_of_pos_right (by linarith : 0 < mass Q)).mp
    nlinarith [mul_nonneg (Nat.cast_nonneg h : (0:ℝ) ≤ h) (sub_nonneg.mpr h1)]
  have hAC : A.card ≤ B.card+Q := by
    have inj : (A \ B).card ≤ (Icc 1 Q).card := by
      apply Finset.card_le_card_of_injOn (fun i => start+i)
      · intro i hi
        obtain ⟨ha,hb⟩ := Finset.mem_sdiff.mp hi
        change start+i ∈ Icc 1 Q
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp ha).2.pos,
          le_of_not_gt fun h => hb (Finset.mem_filter.mpr ⟨ha,h⟩)⟩
      · intro i _ k _ eq
        exact Nat.add_left_cancel eq
    rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _)] at inj
    change A.card - B.card ≤ (Icc 1 Q).card at inj
    rw [show (Icc 1 Q).card = Q by simp] at inj
    omega
  have hz : 0 ≤ zetaTwo := tsum_nonneg fun _ => by positivity
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmass : (j:ℝ)*Real.log 2 ≤ zetaTwo*mass Q := by
    apply le_trans _ (size_mass Q)
    have l := Real.log_le_log (by exact_mod_cast hQ : 0 < (Q:ℝ)) (by exact_mod_cast Nat.le_succ Q :
      (Q:ℝ) ≤ ((Q+1:ℕ):ℝ))
    simpa [Q,Real.log_pow] using l
  have hj : j+1 ≤ Q := j.lt_two_pow_self
  have hQ2 : Q*Q ≤ h := by rw [←hQ4,←sq]; exact Nat.pow_le_pow_right hQ (by decide : 2 ≤ 4)
  have hpad : (Q:ℝ)*(j+1) ≤ h := by exact_mod_cast (Nat.mul_le_mul_left Q hj).trans hQ2
  have hblog := mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg B.card : (0:ℝ) ≤ _)
  have hbound := mul_le_mul_of_nonneg_left hBC hz
  have hsmall : (B.card:ℝ) ≤ 2*h := by
    nlinarith [mul_nonneg (Nat.cast_nonneg B.card : (0:ℝ) ≤ _) (sub_nonneg.mpr h1)]
  have hlog1 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  suffices (A.card:ℝ)*((j:ℝ)+1) ≤ (1+4*(zetaTwo+1)/Real.log 2)*h by simpa [A,h] using this
  have hAC' : (A.card:ℝ) ≤ B.card+Q := by exact_mod_cast hAC
  apply (mul_le_mul_iff_of_pos_right hlog).mp
  have ha := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAC'
    (by positivity : 0 ≤ (j:ℝ)+1)) hlog.le
  field_simp [hlog.ne']
  nlinarith [mul_le_mul_of_nonneg_right hpad hlog.le,
    mul_le_mul_of_nonneg_left hlog1 (Nat.cast_nonneg B.card : (0:ℝ) ≤ _), mul_nonneg hz (Nat.cast_nonneg h : (0:ℝ) ≤ _)]
private def shell (n j : ℕ) := n.primesBelow.filter (fun p => Nat.log 16 (n-p) = j)

set_option maxHeartbeats 1200000 in
private theorem shell_props {n j p : ℕ} (h : p ∈ shell n j) :
    p < n ∧ p.Prime ∧ 16^j ≤ n-p ∧ n-p < 16^(j+1) := by
  obtain ⟨hp,hj⟩ := Finset.mem_filter.mp h
  obtain ⟨hp,hq⟩ := Nat.mem_primesBelow.mp hp
  subst j
  exact ⟨hp,hq,Nat.pow_log_le_self 16 (by omega),Nat.lt_pow_succ_log_self (by decide) _⟩

set_option maxHeartbeats 1200000 in
private theorem sum_shell (n : ℕ) :
    Erdos950.f n ≤ ∑ j ∈ range (Nat.log 16 n+1), ((shell n j).card:ℝ)/(16:ℝ)^j := by
  classical
  let g (p : ℕ) := (1:ℝ)/((n:ℝ)-p)
  have maps (p : ℕ) (_ : p ∈ n.primesBelow) :
      Nat.log 16 (n-p) ∈ range (Nat.log 16 n+1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (Nat.sub_le n p)))
  have eqf : Erdos950.f n = ∑ p ∈ n.primesBelow, g p := by
    unfold Erdos950.f
    rw [Nat.primesBelow_eq_filter_range]
    simp only [← Nat.prime_iff,g]
  rw [eqf]
  rw [← Finset.sum_fiberwise_of_maps_to maps g]
  apply Finset.sum_le_sum
  intro j _
  calc
    _ ≤ ∑ p ∈ shell n j, (1:ℝ)/(16:ℝ)^j := by
      apply Finset.sum_le_sum
      intro p hp
      have ⟨hp',_,hle,_⟩ := shell_props hp
      have hle' : (16:ℝ)^j ≤ (n:ℝ)-p := by
        simpa [Nat.cast_sub hp'.le] using (show ((16^j:ℕ):ℝ) ≤ ((n-p:ℕ):ℝ) by exact_mod_cast hle)
      exact one_div_le_one_div_of_le (by positivity) hle'
    _ = _ := by simp [div_eq_mul_inv]

set_option maxHeartbeats 1200000 in
private theorem short_shell {B : ℝ} (hb : ∀ start j : ℕ,
    (((range (16^j)).filter (fun i => (start+i).Prime)).card : ℝ) * (j+1) ≤ B * 16^j)
    (n j : ℕ) : ((shell n j).card:ℝ)/(16:ℝ)^j ≤ 16*B/((j:ℝ)+1) := by
  let h := 16^(j+1)
  let start := n-h
  let T := (range h).filter (fun i => (start+i).Prime)
  have hs (p : ℕ) (hp : p ∈ shell n j) : start ≤ p := by
    obtain ⟨_,_,_,hlt⟩ := shell_props hp
    dsimp [start,h]; omega
  have hj : (shell n j).card ≤ T.card := by
    apply Finset.card_le_card_of_injOn (fun p => p-start)
    · intro p hp
      obtain ⟨pn,pp,_,_⟩ := shell_props hp
      have hx := hs p hp
      have hh : 0 < h := pow_pos (by decide) _
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (by dsimp [start]; omega),
        by simpa [Nat.add_sub_of_le hx] using pp⟩
    · intro p hp q hq e
      have hp' := hs p hp
      have hq' := hs q hq
      dsimp at e
      omega
  have hT := hb start (j+1)
  change (T.card:ℝ)*(((j+1:ℕ):ℝ)+1) ≤ _ at hT
  rw [Nat.cast_add,Nat.cast_one,pow_succ] at hT
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hj' : ((shell n j).card:ℝ) ≤ T.card := by exact_mod_cast hj
  nlinarith [mul_le_mul_of_nonneg_right hj' (by positivity : 0 ≤ (j:ℝ)+1),Nat.cast_nonneg T.card (α := ℝ)]

set_option maxHeartbeats 1200000 in
private theorem long_shell {K C : ℝ} {n : ℕ} (hk : 0 < K) (hn : 0 < Real.log n)
    (hl : Real.log n ^ C < n)
    (bound : ∀ y : ℕ, (y:ℝ) < n-Real.log n^C →
      (n.primeCounting:ℝ) < y.primeCounting + K*(((n:ℝ)-y)/Real.log n))
    (j : ℕ) (large : Real.log n ^ C < (16:ℝ)^(j+1)) :
    ((shell n j).card:ℝ)/(16:ℝ)^j ≤ 16*K/Real.log n := by
  let h := 16^(j+1)
  let y := n-h
  have y_le : y ≤ n := Nat.sub_le _ _
  have ys : y.primesLE ⊆ n.primesLE := Nat.primesLE_mono y_le
  have sub : shell n j ⊆ n.primesLE \ y.primesLE := by
    intro p hp
    obtain ⟨pn,pp,_,ph⟩ := shell_props hp
    have pp' := pp.pos
    apply Finset.mem_sdiff.mpr
    exact ⟨Nat.mem_primesLE.mpr ⟨pn.le,pp⟩,fun k => by
      have := (Nat.mem_primesLE.mp k).1
      dsimp [y,h] at this
      omega⟩
  have c := Finset.card_le_card sub
  rw [Finset.card_sdiff_of_subset ys,Nat.primesLE_card_eq_primeCounting,Nat.primesLE_card_eq_primeCounting] at c
  have mono : y.primeCounting ≤ n.primeCounting := by
    simpa [Nat.primesLE_card_eq_primeCounting] using Finset.card_le_card ys
  have c' : ((shell n j).card:ℝ) ≤ (n.primeCounting:ℝ)-y.primeCounting := by
    simpa [Nat.cast_sub mono] using (show ((shell n j).card:ℝ) ≤ ((n.primeCounting-y.primeCounting:ℕ):ℝ) by exact_mod_cast c)
  have hr : (h:ℝ)=(16:ℝ)^(j+1) := by simp [h]
  have yc : (y:ℝ) < n-Real.log n^C := by
    by_cases hh : h ≤ n
    · dsimp [y]; rw [Nat.cast_sub hh,hr]; linarith
    · have hy : y=0 := Nat.sub_eq_zero_of_le (by omega)
      rw [hy,Nat.cast_zero]; linarith
  have dif : (n:ℝ)-y ≤ (h:ℝ) := by
    have h' : n ≤ y+h := by dsimp [y]; omega
    exact sub_le_iff_le_add.mpr (by rw [add_comm]; exact_mod_cast h')
  have z := bound y yc
  have a : ((shell n j).card:ℝ) ≤ K*((h:ℝ)/Real.log n) := by
    exact (show ((shell n j).card:ℝ) ≤ K*(((n:ℝ)-y)/Real.log n) by linarith).trans
      (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right dif hn.le) hk.le)
  rw [hr,pow_succ] at a
  apply (div_le_div_iff₀ (by positivity) hn).2
  have := (le_div_iff₀ hn).mp (show ((shell n j).card:ℝ) ≤ K*((16:ℝ)^j*16)/Real.log n by simpa only [mul_div_assoc] using a)
  linarith
set_option maxHeartbeats 1200000 in
private theorem bound_total {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (n J : ℕ) (hn : 0 < Real.log n)
    (hs : ∀ j : ℕ, ((shell n j).card:ℝ)/(16:ℝ)^j ≤ 16*B/((j:ℝ)+1))
    (hl : ∀ j : ℕ, J ≤ j → ((shell n j).card:ℝ)/(16:ℝ)^j ≤ 16*K/Real.log n) :
    Erdos950.f n ≤ 16*B*(1+Real.log J) + ((Nat.log 16 n:ℝ)+1)*(16*K/Real.log n) := by
  classical
  let D := Nat.log 16 n+1
  let term (j : ℕ) := 16*B/((j:ℝ)+1)
  let L := 16*K/Real.log n
  have posL : 0 ≤ L := by dsimp [L]; positivity
  have localBound (j : ℕ) : ((shell n j).card:ℝ)/(16:ℝ)^j ≤ (if j<J then term j else 0)+L := by
    split_ifs with hj
    · exact (hs j).trans (le_add_of_nonneg_right posL)
    · simpa [L] using hl j (by omega)
  have sub : (range D).filter (· < J) ⊆ range J := by
    intro i hi
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  have harmonicSum : (∑ i ∈ range J, term i) = 16*B*(harmonic J:ℝ) := by
    simp [term,harmonic,Finset.mul_sum,div_eq_mul_inv]
  calc
    _ ≤ _ := sum_shell n
    _ ≤ ∑ j ∈ range D, ((if j<J then term j else 0)+L) :=
      Finset.sum_le_sum fun j _ => localBound j
    _ = (∑ j ∈ (range D).filter (· < J), term j) + (D:ℝ)*L := by
      rw [Finset.sum_add_distrib,Finset.sum_filter]
      simp
    _ ≤ (∑ j ∈ range J, term j) + (D:ℝ)*L := by
      apply add_le_add_left
      exact Finset.sum_le_sum_of_subset_of_nonneg sub (fun j _ _ => by dsimp [term]; positivity)
    _ ≤ _ := by
      rw [harmonicSum]
      dsimp [D,L]
      push_cast
      exact add_le_add_left (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log J) (by positivity)) _

set_option maxHeartbeats 1200000 in
private theorem implication {B : ℝ} (hB : 0 ≤ B) (blocks : ∀ start j : ℕ,
    (((range (16^j)).filter (fun i => (start+i).Prime)).card : ℝ) * (j+1) ≤ B*16^j)
    (hyp : ∃ C > (0:ℝ), ∃ K > (0:ℝ), ∀ᶠ n : ℕ in atTop, ∀ y : ℕ,
      (y:ℝ) < n-Real.log n^C → (n.primeCounting:ℝ) < y.primeCounting + K*(((n:ℝ)-y)/Real.log n)) :
    Erdos950.f =O[atTop] fun n : ℕ => Real.log (Real.log (Real.log n)) := by
  obtain ⟨C,hC,K,hK,bound⟩ := hyp
  let d := C/Real.log 16
  have hl16 : 0 < Real.log 16 := Real.log_pos (by norm_num)
  have hd : 0 ≤ d := (div_pos hC hl16).le
  have hd2 : 0 < d+2 := by linarith
  let M := 16*B*(2+Real.log (d+2)) + (1/Real.log 16+1)*(16*K)
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨M,?_⟩
  have t := tendsto_natCast_atTop_atTop (R := ℝ)
  have t1 := Real.tendsto_log_atTop.comp t
  have t2 := Real.tendsto_log_atTop.comp t1
  have t3 := Real.tendsto_log_atTop.comp t2
  have powSmall := ((isLittleO_log_rpow_rpow_atTop C (by norm_num : (0:ℝ)<1)).comp_tendsto t).bound
    (by norm_num : (0:ℝ)<1/2)
  filter_upwards [bound,t1.eventually_ge_atTop 1,t2.eventually_ge_atTop 1,
    t3.eventually_ge_atTop 1,powSmall,eventually_ge_atTop (2:ℕ)] with n hypN hn1 hn2 hn3 hp hn0
  let L := Real.log n
  let LL := Real.log L
  let LLL := Real.log LL
  change 1 ≤ L at hn1
  change 1 ≤ LL at hn2
  change 1 ≤ LLL at hn3
  have posn : (0:ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have posL : 0 < L := by linarith
  have posLL : 0 < LL := by linarith
  have posR := Real.rpow_pos_of_pos posL C
  change ‖L^C‖ ≤ 1/2*‖(n:ℝ)^(1:ℝ)‖ at hp
  rw [Real.rpow_one,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos posR,abs_of_pos posn] at hp
  have hl : L^C < n := by linarith
  let J := ⌈d*LL⌉₊ + 1
  have hj0 : 0 < J := Nat.succ_pos _
  have jlo : d*LL ≤ (J:ℝ) := by
    have := Nat.le_ceil (d*LL)
    dsimp [J]; push_cast; linarith
  have jhi : (J:ℝ) ≤ (d+2)*LL := by
    have hc := Nat.ceil_lt_add_one (mul_nonneg hd posLL.le)
    dsimp [J]; push_cast; nlinarith
  have logJ : Real.log J ≤ Real.log (d+2)+LLL := by
    have h := Real.log_le_log (by exact_mod_cast hj0) jhi
    rwa [Real.log_mul hd2.ne' posLL.ne'] at h
  have long (j : ℕ) (hj : J ≤ j) : ((shell n j).card:ℝ)/(16:ℝ)^j ≤ 16*K/L := by
    apply long_shell hK posL hl hypN
    apply (Real.log_lt_log_iff posR (by positivity)).mp
    rw [Real.log_rpow posL,Real.log_pow]
    have dd : d*Real.log 16=C := div_mul_cancel₀ _ hl16.ne'
    have hh := mul_le_mul_of_nonneg_right (jlo.trans (by exact_mod_cast hj : (J:ℝ) ≤ j)) hl16.le
    dsimp [LL,L] at hh
    push_cast
    nlinarith [show d*Real.log (Real.log n)*Real.log 16 = C*Real.log (Real.log n) by rw [←dd]; ring]
  have fin := bound_total hK.le hB n J posL (short_shell blocks n) long
  let k := Nat.log 16 n
  have hpow : (16:ℝ)^k ≤ n := by exact_mod_cast Nat.pow_log_le_self 16 (show n ≠ 0 by omega)
  have klog := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow] at klog
  have kbound : (k:ℝ)+1 ≤ (1/Real.log 16+1)*L := by
    have hk : (k:ℝ) ≤ L/Real.log 16 := (le_div_iff₀ hl16).mpr klog
    rw [add_mul,one_mul]
    linarith [show 1/Real.log 16*L = L/Real.log 16 by ring]
  have c1 : 0 ≤ 16*B := by positivity
  have c2 : 0 ≤ (1/Real.log 16+1)*(16*K) := by positivity
  have upper : ((k:ℝ)+1)*(16*K/L) ≤ (1/Real.log 16+1)*(16*K) := by
    calc
      _ ≤ (1/Real.log 16+1)*L*(16*K/L) := mul_le_mul_of_nonneg_right kbound (by positivity)
      _ = _ := by field_simp
  have logd : 0 ≤ Real.log (d+2) := Real.log_nonneg (by linarith)
  have dom : 1+Real.log J ≤ (2+Real.log (d+2))*LLL := by
    nlinarith [mul_nonneg logd (sub_nonneg.mpr hn3)]
  have nonnegF : 0 ≤ Erdos950.f n := by
    unfold Erdos950.f
    exact Finset.sum_nonneg fun p hp => by
      have hp' := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
      exact div_nonneg zero_le_one (sub_nonneg.mpr (by exact_mod_cast hp'.le))
  change ‖Erdos950.f n‖ ≤ M * ‖LLL‖
  rw [Real.norm_eq_abs,abs_of_nonneg nonnegF,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ LLL)]
  change Erdos950.f n ≤ 16*B*(1+Real.log J)+((k:ℝ)+1)*(16*K/L) at fin
  dsimp [M]
  nlinarith [mul_le_mul_of_nonneg_left dom c1,mul_nonneg c2 (sub_nonneg.mpr hn3)]
end PrimeWindows

theorem OMA.solution : type_of% @Erdos950.erdos_950.variants.weaker_pi_implies_f := by
  intro h
  apply PrimeWindows.implication _ PrimeWindows.prime_block h
  have hz : 0 ≤ PrimeWindows.zetaTwo := tsum_nonneg fun _ => by positivity
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity