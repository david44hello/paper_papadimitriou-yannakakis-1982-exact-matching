/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import ExactMatching.Defs.PitAlgorithm
public import ExactMatching.Proofs.CircuitsTransfer
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Proofs for Theorem 1 (Ryser, modulus exactness, parameter & asymptotic bounds) and Remark 1

Proves:
- `step_thm1_ryser_proved`: Ryser's formula equals `Matrix.permanent`.
- `step_thm1_eq1_proved`: `μ^(c (log₂ μ)^(1/3)) = exp₂(c (log₂ μ)^(4/3)) ≥ s^κ`.
- `step_thm1_threshold_proved`: existence of `s₀ ≥ 4` with `log₂ s < m < s` and `s μ + 1 ≤ s^2`.
- `step_thm1_small_inputs_proved`: small-input grid test mod `2^{B₀}` exactness.
- `step_thm1_modulus_exact_proved`: large-input NW-permanent modulus `2^B` exactness.
- `step_thm1_B_bound_proved`: `B ≤ 10 * s^{3/2} * log₂ s` when `m < s`.
- `step_thm1_exponent_bound_proved`: evaluation-point & work-count upper bound.
- `cov_asymptotic_between_proved`: `exp₂(exp₂(K (log₂ s)^(3/4)))` identity & regime comparison.
- `cov_grid_prior_pit_proved`: `(s + 1)^s ≤ 2^(2 s log₂ s)`.
- `step_rem1_ln_vs_log2_proved`: `(ln μ)^2 / (ln ln μ)^2 > (log₂ μ)^2 / (log₂ log₂ μ)^2` for `μ ≥ 3`.
-/

namespace ExactMatching.Proofs

open scoped BigOperators

/-! ### Part 1: Ryser's formula -/

private theorem sum_powerset_neg_one_pow {α : Type*} [DecidableEq α] {R : Type*} [CommRing R]
    (S : Finset α) :
    ∑ U ∈ S.powerset, (-1 : R) ^ U.card = if S = ∅ then 1 else 0 := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.powerset_insert, Finset.sum_union]
    · rw [Finset.sum_image]
      · have hcard : ∀ U ∈ s.powerset, (-1 : R) ^ (insert a U).card = -((-1 : R) ^ U.card) := by
          intro U hU
          have haU : a ∉ U := fun h => ha (Finset.mem_powerset.mp hU h)
          rw [Finset.card_insert_of_notMem haU, pow_succ]
          ring
        rw [Finset.sum_congr rfl hcard, Finset.sum_neg_distrib, add_neg_cancel]
        simp [Finset.insert_ne_empty]
      · intro U₁ hU₁ U₂ hU₂ hEq
        have ha1 : a ∉ U₁ := fun h => ha (Finset.mem_powerset.mp hU₁ h)
        have ha2 : a ∉ U₂ := fun h => ha (Finset.mem_powerset.mp hU₂ h)
        have h := congrArg (fun T => T.erase a) hEq
        simpa [Finset.erase_insert ha1, Finset.erase_insert ha2] using h
    · rw [Finset.disjoint_left]
      intro U hU hIm
      rw [Finset.mem_image] at hIm
      obtain ⟨V, _, rfl⟩ := hIm
      exact ha (Finset.mem_powerset.mp hU (Finset.mem_insert_self a V))

private theorem sum_superset_neg_one_pow {μ : ℕ} {R : Type*} [CommRing R] (I : Finset (Fin μ)) :
    ∑ T : Finset (Fin μ), (if I ⊆ T then (-1 : R) ^ T.card else 0) =
      if I = Finset.univ then (-1 : R) ^ μ else 0 := by
  rw [← Finset.sum_filter]
  have hbij :
      ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin μ) => I ⊆ T), (-1 : R) ^ T.card =
      ∑ U ∈ Iᶜ.powerset, (-1 : R) ^ (I ∪ U).card := by
    refine Finset.sum_bij (fun T _ => T \ I) ?_ ?_ ?_ ?_
    · intro T _
      rw [Finset.mem_powerset]
      intro x hx
      rw [Finset.mem_sdiff] at hx
      exact Finset.mem_compl.mpr hx.2
    · intro T₁ hT₁ T₂ hT₂ hEq
      have h1 : I ⊆ T₁ := (Finset.mem_filter.mp hT₁).2
      have h2 : I ⊆ T₂ := (Finset.mem_filter.mp hT₂).2
      rw [← Finset.union_sdiff_of_subset h1, ← Finset.union_sdiff_of_subset h2, hEq]
    · intro U hU
      have hsub : U ⊆ Iᶜ := Finset.mem_powerset.mp hU
      have hdisj : Disjoint I U :=
        Finset.disjoint_left.mpr fun x hxI hxU => (Finset.mem_compl.mp (hsub hxU)) hxI
      refine ⟨I ∪ U, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.subset_union_left⟩, ?_⟩
      rw [Finset.union_sdiff_cancel_left hdisj]
    · intro T hT
      rw [Finset.union_sdiff_of_subset (Finset.mem_filter.mp hT).2]
  rw [hbij]
  have hsplit :
      ∑ U ∈ Iᶜ.powerset, (-1 : R) ^ (I ∪ U).card =
      (-1 : R) ^ I.card * ∑ U ∈ Iᶜ.powerset, (-1 : R) ^ U.card := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun U hU => ?_
    have hdisj : Disjoint I U :=
      Finset.disjoint_left.mpr fun x hxI hxU =>
        (Finset.mem_compl.mp (Finset.mem_powerset.mp hU hxU)) hxI
    rw [Finset.card_union_of_disjoint hdisj, pow_add]
  rw [hsplit, sum_powerset_neg_one_pow]
  by_cases hI : I = Finset.univ
  · subst hI
    simp
  · have hne : Iᶜ ≠ ∅ := by
      intro h0
      apply hI
      rw [← compl_compl I, h0]
      simp
    simp [hI, hne]

/-- Ryser's formula equals `Matrix.permanent` over every commutative ring `R`. -/
theorem step_thm1_ryser_proved {μ : ℕ} {R : Type*} [CommRing R]
    (M : Matrix (Fin μ) (Fin μ) R) :
    ryserPerm M = M.permanent := by
  unfold ryserPerm
  have hexpand : ∀ T : Finset (Fin μ),
      (∏ r : Fin μ, ∑ j ∈ T, M r j) =
      ∑ f : Fin μ → Fin μ, if Finset.univ.image f ⊆ T then ∏ r : Fin μ, M r (f r) else 0 := by
    intro T
    have h1 : (∏ r : Fin μ, ∑ j ∈ T, M r j) =
        ∑ f : Fin μ → Fin μ, (∏ r : Fin μ, if f r ∈ T then M r (f r) else 0) := by
      have hrow : ∀ r : Fin μ, ∑ j ∈ T, M r j = ∑ j : Fin μ, if j ∈ T then M r j else 0 := by
        intro r; rw [Finset.sum_ite_mem, Finset.univ_inter]
      simp_rw [hrow]
      exact Fintype.prod_sum (fun r j => if j ∈ T then M r j else 0)
    rw [h1]
    refine Finset.sum_congr rfl fun f _ => ?_
    by_cases hf : Finset.univ.image f ⊆ T
    · simp only [hf, ite_true]
      refine Finset.prod_congr rfl fun r _ => ?_
      simp [hf (Finset.mem_image_of_mem f (Finset.mem_univ r))]
    · simp only [hf, ite_false]
      have hex : ∃ r : Fin μ, f r ∉ T := by
        by_contra h
        push Not at h
        apply hf
        intro y hy
        rw [Finset.mem_image] at hy
        obtain ⟨r, _, rfl⟩ := hy
        exact h r
      obtain ⟨r₀, hr₀⟩ := hex
      exact Finset.prod_eq_zero (Finset.mem_univ r₀) (by simp [hr₀])
  have hinner_sum :
      (∑ T : Finset (Fin μ), (-1 : R) ^ T.card * ∏ r : Fin μ, ∑ j ∈ T, M r j) =
      ∑ f : Fin μ → Fin μ,
        (if Finset.univ.image f = Finset.univ then (-1 : R) ^ μ else 0) *
          (∏ r : Fin μ, M r (f r)) := by
    simp_rw [hexpand, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun f _ => ?_
    have hfactor :
        (∑ T : Finset (Fin μ),
          (-1 : R) ^ T.card * (if Finset.univ.image f ⊆ T then ∏ r : Fin μ, M r (f r) else 0)) =
        (∑ T : Finset (Fin μ),
          if Finset.univ.image f ⊆ T then (-1 : R) ^ T.card else 0) *
          (∏ r : Fin μ, M r (f r)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun T _ => ?_
      split_ifs <;> ring
    rw [hfactor, sum_superset_neg_one_pow]
  rw [hinner_sum, Finset.mul_sum]
  have hcancel :
      (∑ f : Fin μ → Fin μ,
        (-1 : R) ^ μ *
          ((if Finset.univ.image f = Finset.univ then (-1 : R) ^ μ else 0) *
            (∏ r : Fin μ, M r (f r)))) =
      ∑ f : Fin μ → Fin μ,
        if Function.Bijective f then ∏ r : Fin μ, M r (f r) else 0 := by
    refine Finset.sum_congr rfl fun f _ => ?_
    have hiff : Finset.univ.image f = Finset.univ ↔ Function.Bijective f := by
      rw [← Finite.surjective_iff_bijective]
      constructor
      · intro h y
        have hy : y ∈ Finset.univ.image f := h.symm ▸ Finset.mem_univ y
        rw [Finset.mem_image] at hy
        obtain ⟨x, _, rfl⟩ := hy
        exact ⟨x, rfl⟩
      · intro hsurj
        ext y
        simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
        exact hsurj y
    by_cases hbij : Function.Bijective f
    · simp only [hiff.mpr hbij, hbij, ite_true]
      rw [← mul_assoc, ← mul_pow]
      simp
    · have hne : Finset.univ.image f ≠ Finset.univ := mt hiff.mp hbij
      simp only [hne, hbij, ite_false, zero_mul, mul_zero]
  rw [hcancel, ← Finset.sum_filter, ← Matrix.permanent_transpose]
  unfold Matrix.permanent
  symm
  refine Finset.sum_bij (fun (σ : Equiv.Perm (Fin μ)) _ => (σ : Fin μ → Fin μ)) ?_ ?_ ?_ ?_
  · intro σ _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, σ.bijective⟩
  · intro σ₁ _ σ₂ _ h
    exact Equiv.ext (congrFun h)
  · intro f hf
    have hbij : Function.Bijective f := (Finset.mem_filter.mp hf).2
    exact ⟨Equiv.ofBijective f hbij, Finset.mem_univ _, rfl⟩
  · intro σ _
    rfl

/-! ### Part 2: `IntCircuit.evalAt` homomorphism & monomial-count / modulus exactness -/

theorem evalGateAt_var {n : ℕ} {R : Type*} [CommRing R] (C : IntCircuit n)
    (x : Fin n → R) (k : Fin C.size) (v : Fin n) (h : C.gate k = .var v) :
    C.evalGateAt x k = x v := by
  conv_lhs => unfold IntCircuit.evalGateAt; rw [WellFounded.fix_eq]
  split <;> simp_all

theorem evalGateAt_const {n : ℕ} {R : Type*} [CommRing R] (C : IntCircuit n)
    (x : Fin n → R) (k : Fin C.size) (a : ℤ) (h : C.gate k = .const a) :
    C.evalGateAt x k = (a : R) := by
  conv_lhs => unfold IntCircuit.evalGateAt; rw [WellFounded.fix_eq]
  split <;> simp_all

theorem evalGateAt_add {n : ℕ} {R : Type*} [CommRing R] (C : IntCircuit n)
    (x : Fin n → R) (k : Fin C.size) (i j : ℕ) (h : C.gate k = .add i j)
    (hi : i < C.size) (hj : j < C.size) :
    C.evalGateAt x k = C.evalGateAt x ⟨i, hi⟩ + C.evalGateAt x ⟨j, hj⟩ := by
  conv_lhs => unfold IntCircuit.evalGateAt; rw [WellFounded.fix_eq]
  split <;> simp_all
  rcases h with ⟨rfl, rfl⟩; rfl

theorem evalGateAt_sub {n : ℕ} {R : Type*} [CommRing R] (C : IntCircuit n)
    (x : Fin n → R) (k : Fin C.size) (i j : ℕ) (h : C.gate k = .sub i j)
    (hi : i < C.size) (hj : j < C.size) :
    C.evalGateAt x k = C.evalGateAt x ⟨i, hi⟩ - C.evalGateAt x ⟨j, hj⟩ := by
  conv_lhs => unfold IntCircuit.evalGateAt; rw [WellFounded.fix_eq]
  split <;> simp_all
  rcases h with ⟨rfl, rfl⟩; rfl

theorem evalGateAt_mul {n : ℕ} {R : Type*} [CommRing R] (C : IntCircuit n)
    (x : Fin n → R) (k : Fin C.size) (i j : ℕ) (h : C.gate k = .mul i j)
    (hi : i < C.size) (hj : j < C.size) :
    C.evalGateAt x k = C.evalGateAt x ⟨i, hi⟩ * C.evalGateAt x ⟨j, hj⟩ := by
  conv_lhs => unfold IntCircuit.evalGateAt; rw [WellFounded.fix_eq]
  split <;> simp_all
  rcases h with ⟨rfl, rfl⟩; rfl

/-- Evaluating an `IntCircuit` in any commutative ring `R` agrees with `MvPolynomial.aeval`
of its formal polynomial `C.evalPoly`. -/
theorem intCircuit_evalAt_eq_aeval {n : ℕ} {R : Type*} [CommRing R] (C : IntCircuit n)
    (x : Fin n → R) :
    C.evalAt R x = MvPolynomial.aeval x C.evalPoly := by
  suffices ∀ (m : ℕ) (hm : m < C.size),
      C.evalGateAt x ⟨m, hm⟩ = MvPolynomial.aeval x (C.evalGateAt MvPolynomial.X ⟨m, hm⟩) by
    exact this C.out.val C.out.isLt
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    let k : Fin C.size := ⟨m, hm⟩
    cases h : C.gate k with
    | var v =>
      rw [evalGateAt_var C x k v h, evalGateAt_var C MvPolynomial.X k v h, MvPolynomial.aeval_X]
    | const a =>
      rw [evalGateAt_const C x k a h, evalGateAt_const C MvPolynomial.X k a h]
      simp
    | add i j =>
      have hwf := C.wf k; rw [h] at hwf
      have hi : i < m := hwf.1
      have hj : j < m := hwf.2
      rw [evalGateAt_add C x k i j h (Nat.lt_trans hi hm) (Nat.lt_trans hj hm),
        evalGateAt_add C MvPolynomial.X k i j h (Nat.lt_trans hi hm) (Nat.lt_trans hj hm),
        map_add, ih i hi _, ih j hj _]
    | sub i j =>
      have hwf := C.wf k; rw [h] at hwf
      have hi : i < m := hwf.1
      have hj : j < m := hwf.2
      rw [evalGateAt_sub C x k i j h (Nat.lt_trans hi hm) (Nat.lt_trans hj hm),
        evalGateAt_sub C MvPolynomial.X k i j h (Nat.lt_trans hi hm) (Nat.lt_trans hj hm),
        map_sub, ih i hi _, ih j hj _]
    | mul i j =>
      have hwf := C.wf k; rw [h] at hwf
      have hi : i < m := hwf.1
      have hj : j < m := hwf.2
      rw [evalGateAt_mul C x k i j h (Nat.lt_trans hi hm) (Nat.lt_trans hj hm),
        evalGateAt_mul C MvPolynomial.X k i j h (Nat.lt_trans hi hm) (Nat.lt_trans hj hm),
        map_mul, ih i hi _, ih j hj _]

/-- Two strictly increasing functions `Fin s → α` with the same image Finset are equal. -/
theorem strictMono_eq_of_image_eq {s : ℕ} {α : Type*} [LinearOrder α]
    {p₁ p₂ : Fin s → α} (h₁ : StrictMono p₁) (h₂ : StrictMono p₂)
    (himg : Finset.univ.image p₁ = Finset.univ.image p₂) : p₁ = p₂ := by
  ext i
  obtain ⟨k, hk⟩ := i
  induction k using Nat.strong_induction_on with
  | h k ih =>
    -- Every `j < k` satisfies `p₁ j = p₂ j`; both `p₁ k` and `p₂ k` are the minimum of the remaining elements
    have hlt_le : ∀ (q₁ q₂ : Fin s → α), StrictMono q₁ → StrictMono q₂ →
        Finset.univ.image q₁ = Finset.univ.image q₂ →
        (∀ j : Fin s, j.val < k → q₁ j = q₂ j) →
        q₁ ⟨k, hk⟩ ≤ q₂ ⟨k, hk⟩ := by
      intro q₁ q₂ hq₁ hq₂ hqimg hprev
      have hmem : q₂ ⟨k, hk⟩ ∈ Finset.univ.image q₁ := by
        rw [hqimg]; exact Finset.mem_image_of_mem q₂ (Finset.mem_univ _)
      rw [Finset.mem_image] at hmem
      obtain ⟨j, _, hj⟩ := hmem
      by_cases hjk : j.val < k
      · exfalso
        have h1 : q₂ j = q₂ ⟨k, hk⟩ := (hprev j hjk).symm.trans hj
        have h2 := hq₂.injective h1
        exact ne_of_lt hjk (congrArg Fin.val h2)
      · have hkj : (⟨k, hk⟩ : Fin s) ≤ j := by exact_mod_cast Nat.le_of_not_lt hjk
        rw [← hj]
        exact hq₁.monotone hkj
    exact le_antisymm
      (hlt_le p₁ p₂ h₁ h₂ himg (fun j hj => ih j.val hj j.isLt))
      (hlt_le p₂ p₁ h₂ h₁ himg.symm (fun j hj => (ih j.val hj j.isLt).symm))

/-- Stars-and-bars bound: a polynomial in `s` variables of total degree at most `s` has at
most `2 ^ (2 * s)` monomials in its support. -/
theorem support_card_le_pow_two_mul {s : ℕ} (f : MvPolynomial (Fin s) ℤ)
    (hdeg : f.totalDegree ≤ s) :
    f.support.card ≤ 2 ^ (2 * s) := by
  let enc : (Fin s →₀ ℕ) → Finset (Fin (2 * s)) := fun d =>
    Finset.univ.image fun i : Fin s =>
      let pos := (∑ j ∈ Finset.univ.filter (fun j : Fin s => j < i), (d j + 1)) + d i
      if hp : pos < 2 * s then ⟨pos, hp⟩ else ⟨0, by
        by_contra h0
        have hs0 : s = 0 := by omega
        subst hs0
        exact Fin.elim0 i⟩
  have hpos_lt : ∀ d ∈ f.support, ∀ i : Fin s,
      (∑ j ∈ Finset.univ.filter (fun j : Fin s => j < i), (d j + 1)) + d i < 2 * s := by
    intro d hd i
    have hd_le : d.sum (fun _ e => e) ≤ s :=
      le_trans (Finset.le_sup (f := fun d => d.sum (fun _ e => e)) hd) hdeg
    have hsum_d : ∑ j : Fin s, d j ≤ s := by
      rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hd_le
    have hsplit :
        (∑ j ∈ Finset.univ.filter (fun j : Fin s => j < i), (d j + 1)) + d i + 1 =
        ∑ j ∈ Finset.univ.filter (fun j : Fin s => j ≤ i), (d j + 1) := by
      have hcons : Finset.univ.filter (fun j : Fin s => j ≤ i) =
          insert i (Finset.univ.filter (fun j : Fin s => j < i)) := by
        ext j; simp [le_iff_lt_or_eq, or_comm]
      rw [hcons, Finset.sum_insert (by simp)]
      omega
    have hbound : ∑ j ∈ Finset.univ.filter (fun j : Fin s => j ≤ i), (d j + 1) ≤ 2 * s := by
      calc
        ∑ j ∈ Finset.univ.filter (fun j : Fin s => j ≤ i), (d j + 1)
            ≤ ∑ j : Fin s, (d j + 1) := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
        _ = (∑ j : Fin s, d j) + s := by rw [Finset.sum_add_distrib]; simp
        _ ≤ s + s := Nat.add_le_add_right hsum_d s
        _ = 2 * s := by omega
    omega
  have hinj : Set.InjOn enc (f.support : Set (Fin s →₀ ℕ)) := by
    intro d₁ hd₁ d₂ hd₂ hEq
    have hpos_eq : ∀ i : Fin s,
        (∑ j ∈ Finset.univ.filter (fun j : Fin s => j < i), (d₁ j + 1)) + d₁ i =
        (∑ j ∈ Finset.univ.filter (fun j : Fin s => j < i), (d₂ j + 1)) + d₂ i := by
      let p₁ : Fin s → Fin (2 * s) := fun i =>
        ⟨(∑ j ∈ Finset.univ.filter (fun j : Fin s => j < i), (d₁ j + 1)) + d₁ i,
          hpos_lt d₁ hd₁ i⟩
      let p₂ : Fin s → Fin (2 * s) := fun i =>
        ⟨(∑ j ∈ Finset.univ.filter (fun j : Fin s => j < i), (d₂ j + 1)) + d₂ i,
          hpos_lt d₂ hd₂ i⟩
      have hmono : ∀ (d : Fin s →₀ ℕ) (hd : d ∈ f.support),
          StrictMono (fun i : Fin s =>
            (⟨(∑ j ∈ Finset.univ.filter (fun j : Fin s => j < i), (d j + 1)) + d i,
              hpos_lt d hd i⟩ : Fin (2 * s))) := by
        intro d hd a b hab
        change (∑ j ∈ Finset.univ.filter (fun j : Fin s => j < a), (d j + 1)) + d a <
          (∑ j ∈ Finset.univ.filter (fun j : Fin s => j < b), (d j + 1)) + d b
        have hsub : insert a (Finset.univ.filter (fun j : Fin s => j < a)) ⊆
            Finset.univ.filter (fun j : Fin s => j < b) := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          rcases hx with rfl | hxa
          · exact hab
          · exact lt_trans hxa hab
        have hle := Finset.sum_le_sum_of_subset (f := fun j => d j + 1) hsub
        rw [Finset.sum_insert (by simp)] at hle
        omega
      have himg : Finset.univ.image p₁ = Finset.univ.image p₂ := by
        have h1 : enc d₁ = Finset.univ.image p₁ := by
          ext x; simp [enc, p₁, hpos_lt d₁ hd₁]
        have h2 : enc d₂ = Finset.univ.image p₂ := by
          ext x; simp [enc, p₂, hpos_lt d₂ hd₂]
        rw [← h1, ← h2, hEq]
      have hp_eq := strictMono_eq_of_image_eq (hmono d₁ hd₁) (hmono d₂ hd₂) himg
      intro i
      exact congrArg Fin.val (congrFun hp_eq i)
    ext i
    obtain ⟨n, hn⟩ := i
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have hEq_i := hpos_eq ⟨n, hn⟩
      have hsum_eq :
          ∑ j ∈ Finset.univ.filter (fun j : Fin s => j < ⟨n, hn⟩), (d₁ j + 1) =
          ∑ j ∈ Finset.univ.filter (fun j : Fin s => j < ⟨n, hn⟩), (d₂ j + 1) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjn : j.val < n := (Finset.mem_filter.mp hj).2
        rw [ih j.val hjn j.isLt]
      omega
  calc
    f.support.card ≤ (Finset.univ : Finset (Finset (Fin (2 * s)))).card :=
      Finset.card_le_card_of_injOn enc (fun _ _ => Finset.mem_univ _) hinj
    _ = 2 ^ (2 * s) := by simp

private theorem int_natAbs_finset_sum_le {α : Type*} [DecidableEq α] (S : Finset α) (g : α → ℤ) :
    (∑ a ∈ S, g a).natAbs ≤ ∑ a ∈ S, (g a).natAbs := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add_left ih _)

private theorem int_natAbs_finset_prod {α : Type*} [DecidableEq α] (S : Finset α) (g : α → ℤ) :
    (∏ a ∈ S, g a).natAbs = ∏ a ∈ S, (g a).natAbs := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Int.natAbs_mul, ih]

/-- General bound `|(eval v f)| ≤ 2^(3*s) * M^s`. -/
theorem eval_natAbs_le_of_bound {s M : ℕ} (hM : 1 ≤ M) (f : MvPolynomial (Fin s) ℤ)
    (hdeg : f.totalDegree ≤ s) (hcoeff : CoeffBitBound f s)
    (v : Fin s → ℤ) (hv : ∀ i, (v i).natAbs ≤ M) :
    (MvPolynomial.eval v f).natAbs ≤ 2 ^ (3 * s) * M ^ s := by
  rw [MvPolynomial.eval_eq']
  calc
    (∑ d ∈ f.support, f.coeff d * ∏ i : Fin s, v i ^ d i).natAbs
        ≤ ∑ d ∈ f.support, (f.coeff d * ∏ i : Fin s, v i ^ d i).natAbs :=
          int_natAbs_finset_sum_le _ _
    _ ≤ ∑ _d ∈ f.support, 2 ^ s * M ^ s := by
      refine Finset.sum_le_sum fun d hd => ?_
      rw [Int.natAbs_mul, int_natAbs_finset_prod]
      have hprod : ∏ i : Fin s, (v i ^ d i).natAbs ≤ M ^ s := by
        calc
          ∏ i : Fin s, (v i ^ d i).natAbs
              = ∏ i : Fin s, (v i).natAbs ^ d i := by
                refine Finset.prod_congr rfl fun i _ => Int.natAbs_pow _ _
          _ ≤ ∏ i : Fin s, M ^ d i :=
                Finset.prod_le_prod' fun i _ => Nat.pow_le_pow_left (hv i) _
          _ = M ^ (∑ i : Fin s, d i) := Finset.prod_pow_eq_pow_sum _ _ _
          _ ≤ M ^ s := by
                apply Nat.pow_le_pow_right hM
                have h1 : d.sum (fun _ e => e) ≤ s :=
                  le_trans (Finset.le_sup (f := fun d => d.sum (fun _ e => e)) hd) hdeg
                rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h1
      exact Nat.mul_le_mul (hcoeff d) hprod
    _ = f.support.card * (2 ^ s * M ^ s) := by simp
    _ ≤ 2 ^ (2 * s) * (2 ^ s * M ^ s) := Nat.mul_le_mul_right _ (support_card_le_pow_two_mul f hdeg)
    _ = 2 ^ (3 * s) * M ^ s := by
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega

theorem zmod_intCast_eq_zero_iff_of_natAbs_lt {B : ℕ} {z : ℤ} (hz : z.natAbs < 2 ^ B) :
    ((z : ZMod (2 ^ B)) = 0) ↔ z = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro hdvd
    have hnat : (2 ^ B : ℕ) ∣ z.natAbs := Int.natCast_dvd.mp hdvd
    have h0 : z.natAbs = 0 := Nat.eq_zero_of_dvd_of_lt hnat hz
    exact Int.natAbs_eq_zero.mp h0
  · intro h0; rw [h0]; exact dvd_zero _

theorem aeval_intCast_eq_intCast_eval {n : ℕ} {R : Type*} [CommRing R]
    (f : MvPolynomial (Fin n) ℤ) (v : Fin n → ℤ) :
    MvPolynomial.aeval (fun i => (v i : R)) f = ((MvPolynomial.eval v f : ℤ) : R) := by
  have h : MvPolynomial.aeval (fun i => (v i : R)) f =
      (Int.castRingHom R) (MvPolynomial.eval v f) := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval]
    change MvPolynomial.eval₂ (Int.castRingHom R) (fun i => (Int.castRingHom R) (v i)) f =
      (Int.castRingHom R) (MvPolynomial.eval₂ (RingHom.id ℤ) v f)
    rw [MvPolynomial.hom_eval₂]
    rfl
  exact h

/-- Small-input modulus exactness and completeness (`s ≥ 2`). -/
theorem step_thm1_small_inputs_proved (s : ℕ) (hs : 2 ≤ s) (C : IntCircuit s)
    (hdeg : C.evalPoly.totalDegree ≤ s) (hcoeff : CoeffBitBound C.evalPoly s) :
    pitSmallTest s C ↔ C.evalPoly = 0 := by
  constructor
  · intro htest
    by_contra hne
    let fQ : MvPolynomial (Fin s) ℚ := MvPolynomial.map (Int.castRingHom ℚ) C.evalPoly
    have hfQ_ne : fQ ≠ 0 := by
      intro h0
      apply hne
      ext d
      have h1 : fQ.coeff d = 0 := by simp [h0]
      rw [show fQ = MvPolynomial.map (Int.castRingHom ℚ) C.evalPoly from rfl,
        MvPolynomial.coeff_map] at h1
      simpa using h1
    have hfQ_deg : fQ.totalDegree ≤ s := by
      rw [MvPolynomial.totalDegree]
      refine Finset.sup_le fun d hd => ?_
      have hd' : d ∈ C.evalPoly.support := MvPolynomial.support_map_subset _ _ hd
      exact le_trans (Finset.le_sup (f := fun d => d.sum (fun _ e => e)) hd') hdeg
    let S : Finset ℚ := (Finset.range (s + 1)).image (fun k : ℕ => (k : ℚ))
    have hScard : fQ.totalDegree < S.card := by
      have hinj : Function.Injective (fun k : ℕ => (k : ℚ)) := Nat.cast_injective
      rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
      omega
    obtain ⟨aQ, haQS, haQ_ne⟩ := step_2_2_nonvanishing_proved fQ hfQ_ne S hScard
    have ha_ex : ∀ i : Fin s, ∃ k : Fin (s + 1), (k.val : ℚ) = aQ i := by
      intro i
      have hi := haQS i
      rw [Finset.mem_image] at hi
      obtain ⟨k, hk, hkq⟩ := hi
      exact ⟨⟨k, Finset.mem_range.mp hk⟩, hkq⟩
    choose a ha using ha_ex
    have hzero_mod := htest a
    rw [intCircuit_evalAt_eq_aeval] at hzero_mod
    have hcomp :
        (fun i => ((a i).val : ZMod (2 ^ pitB0 s))) =
        (fun i => (((a i).val : ℤ) : ZMod (2 ^ pitB0 s))) := by ext i; simp
    rw [hcomp, aeval_intCast_eq_intCast_eval] at hzero_mod
    have hbound : (MvPolynomial.eval (fun i => ((a i).val : ℤ)) C.evalPoly).natAbs < 2 ^ pitB0 s := by
      have h1 := eval_natAbs_le_of_bound (M := s) (by omega) C.evalPoly hdeg hcoeff
        (fun i => ((a i).val : ℤ)) (fun i => by simp; omega)
      have hs_pow : s ≤ 2 ^ Nat.clog 2 s :=
        (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp le_rfl
      calc
        (MvPolynomial.eval (fun i => ((a i).val : ℤ)) C.evalPoly).natAbs
            ≤ 2 ^ (3 * s) * s ^ s := h1
        _ ≤ 2 ^ (3 * s) * (2 ^ Nat.clog 2 s) ^ s :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs_pow s)
        _ = 2 ^ (3 * s + s * Nat.clog 2 s) := by
            rw [← pow_mul, ← pow_add, Nat.mul_comm (Nat.clog 2 s) s]
        _ < 2 ^ pitB0 s := Nat.pow_lt_pow_right (by decide) (by unfold pitB0; omega)
    have hzero_int : MvPolynomial.eval (fun i => ((a i).val : ℤ)) C.evalPoly = 0 :=
      (zmod_intCast_eq_zero_iff_of_natAbs_lt hbound).mp hzero_mod
    apply haQ_ne
    have hmap_eval : MvPolynomial.eval aQ fQ =
        ((MvPolynomial.eval (fun i => ((a i).val : ℤ)) C.evalPoly : ℤ) : ℚ) := by
      have haQ_eq : aQ = fun i => (((a i).val : ℤ) : ℚ) := by
        ext i; rw [← ha i]; simp
      rw [haQ_eq]
      change MvPolynomial.eval (fun i => (((a i).val : ℤ) : ℚ))
        (MvPolynomial.map (Int.castRingHom ℚ) C.evalPoly) = _
      rw [MvPolynomial.eval_map]
      have h2 : MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun i => (((a i).val : ℤ) : ℚ)) C.evalPoly =
          MvPolynomial.aeval (fun i => (((a i).val : ℤ) : ℚ)) C.evalPoly := rfl
      rw [h2]
      exact aeval_intCast_eq_intCast_eval C.evalPoly _
    rw [hmap_eval, hzero_int, Int.cast_zero]
  · intro h0 a
    rw [intCircuit_evalAt_eq_aeval, h0, map_zero]

/-- Generic large-input modulus `2^B` exactness for any `μ ≥ 1` with `B = 3s + s*μ*clog 2 (s*μ²) + 2`. -/
theorem nwPermModTest_modulus_exact (μ s : ℕ) (hs : 2 ≤ s) (hμ1 : 1 ≤ μ) (hm : 2 ≤ μ ^ 2)
    (hcard : ∀ i : Fin s, (designSets (μ ^ 2) s hm i).card = μ ^ 2)
    (C : IntCircuit s) (hdeg : C.evalPoly.totalDegree ≤ s) (hcoeff : CoeffBitBound C.evalPoly s)
    (a : Fin (designL (μ ^ 2)) → Fin (s * μ + 1)) :
    let B := 3 * s + s * μ * Nat.clog 2 (s * μ ^ 2) + 2
    let S := designSets (μ ^ 2) s hm
    let v : Fin s → ℤ := fun i =>
      ryserPerm (R := ℤ)
        (matrixOfVec (fun j : Fin (μ ^ 2) => ((a ((S i).orderEmbOfFin (hcard i) j)).val : ℤ)))
    (∀ i, 0 ≤ v i ∧ v i ≤ ((s * μ ^ 2 : ℕ) : ℤ) ^ μ) ∧
    (MvPolynomial.eval v C.evalPoly).natAbs < 2 ^ (B - 1) ∧
    (C.evalAt (ZMod (2 ^ B)) (fun i => (v i : ZMod (2 ^ B))) = 0 ↔
      MvPolynomial.eval v C.evalPoly = 0) := by
  intro B S v
  have hv_bounds : ∀ i, 0 ≤ v i ∧ v i ≤ ((s * μ ^ 2 : ℕ) : ℤ) ^ μ := by
    intro i
    have hv_perm : v i = (matrixOfVec (fun j : Fin (μ ^ 2) =>
        ((a ((S i).orderEmbOfFin (hcard i) j)).val : ℤ))).permanent :=
      step_thm1_ryser_proved _
    rw [hv_perm]
    unfold Matrix.permanent
    constructor
    · refine Finset.sum_nonneg fun σ _ => Finset.prod_nonneg fun r _ => ?_
      simp [matrixOfVec]
    · calc
        ∑ σ : Equiv.Perm (Fin μ),
            ∏ r : Fin μ,
              matrixOfVec (fun j : Fin (μ ^ 2) =>
                ((a ((S i).orderEmbOfFin (hcard i) j)).val : ℤ)) (σ r) r
            ≤ ∑ _σ : Equiv.Perm (Fin μ), ((s * μ : ℕ) : ℤ) ^ μ := by
              refine Finset.sum_le_sum fun σ _ => ?_
              calc
                ∏ r : Fin μ,
                    matrixOfVec (fun j : Fin (μ ^ 2) =>
                      ((a ((S i).orderEmbOfFin (hcard i) j)).val : ℤ)) (σ r) r
                    ≤ ∏ _r : Fin μ, ((s * μ : ℕ) : ℤ) := by
                      have hnat :
                          ∏ r : Fin μ,
                            matrixOfVec (fun j : Fin (μ ^ 2) =>
                              (a ((S i).orderEmbOfFin (hcard i) j)).val) (σ r) r
                          ≤ ∏ _r : Fin μ, (s * μ) :=
                        Finset.prod_le_prod' fun r _ => by
                          dsimp only [matrixOfVec]
                          exact Nat.le_of_lt_succ (a _).isLt
                      have hcastL :
                          ((∏ r : Fin μ,
                              matrixOfVec (fun j : Fin (μ ^ 2) =>
                                (a ((S i).orderEmbOfFin (hcard i) j)).val) (σ r) r : ℕ) : ℤ) =
                          ∏ r : Fin μ,
                            matrixOfVec (fun j : Fin (μ ^ 2) =>
                              ((a ((S i).orderEmbOfFin (hcard i) j)).val : ℤ)) (σ r) r := by
                        rw [Nat.cast_prod]; rfl
                      have hcastR : ((∏ _r : Fin μ, (s * μ) : ℕ) : ℤ) = ∏ _r : Fin μ, ((s * μ : ℕ) : ℤ) :=
                        Nat.cast_prod _ _
                      rw [← hcastL, ← hcastR]
                      exact_mod_cast hnat
                _ = ((s * μ : ℕ) : ℤ) ^ μ := by simp
        _ = (μ.factorial : ℤ) * ((s * μ : ℕ) : ℤ) ^ μ := by
              simp [Fintype.card_perm, Fintype.card_fin]
        _ ≤ ((μ ^ μ : ℕ) : ℤ) * ((s * μ : ℕ) : ℤ) ^ μ := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact_mod_cast Nat.factorial_le_pow μ
        _ = ((s * μ ^ 2 : ℕ) : ℤ) ^ μ := by
              push_cast
              rw [← mul_pow]
              congr 1
              ring
  have hf_lt : (MvPolynomial.eval v C.evalPoly).natAbs < 2 ^ (B - 1) := by
    have hM1 : 1 ≤ (s * μ ^ 2) ^ μ := Nat.one_le_pow _ _ (by nlinarith)
    have hv_abs : ∀ i, (v i).natAbs ≤ (s * μ ^ 2) ^ μ := by
      intro i
      have h0 := (hv_bounds i).1
      have h1 := (hv_bounds i).2
      have hcast : ((v i).natAbs : ℤ) ≤ ((s * μ ^ 2 : ℕ) : ℤ) ^ μ := by
        rwa [Int.natAbs_of_nonneg h0]
      exact_mod_cast hcast
    have h1 := eval_natAbs_le_of_bound hM1 C.evalPoly hdeg hcoeff v hv_abs
    have hclog : s * μ ^ 2 ≤ 2 ^ Nat.clog 2 (s * μ ^ 2) :=
      (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp le_rfl
    have hB_gt : 3 * s + s * μ * Nat.clog 2 (s * μ ^ 2) < B - 1 := by
      have hBeq : B = 3 * s + s * μ * Nat.clog 2 (s * μ ^ 2) + 2 := rfl
      omega
    calc
      (MvPolynomial.eval v C.evalPoly).natAbs
          ≤ 2 ^ (3 * s) * ((s * μ ^ 2) ^ μ) ^ s := h1
      _ = 2 ^ (3 * s) * (s * μ ^ 2) ^ (s * μ) := by rw [← pow_mul, Nat.mul_comm μ s]
      _ ≤ 2 ^ (3 * s) * (2 ^ Nat.clog 2 (s * μ ^ 2)) ^ (s * μ) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hclog _)
      _ = 2 ^ (3 * s + s * μ * Nat.clog 2 (s * μ ^ 2)) := by
          rw [← pow_mul, ← pow_add, Nat.mul_comm (Nat.clog 2 (s * μ ^ 2)) (s * μ)]
      _ < 2 ^ (B - 1) := Nat.pow_lt_pow_right (by decide) hB_gt
  refine ⟨hv_bounds, hf_lt, ?_⟩
  rw [intCircuit_evalAt_eq_aeval, aeval_intCast_eq_intCast_eval]
  have hf_lt_B : (MvPolynomial.eval v C.evalPoly).natAbs < 2 ^ B :=
    lt_of_lt_of_le hf_lt (Nat.pow_le_pow_right (by decide) (Nat.sub_le B 1))
  exact zmod_intCast_eq_zero_iff_of_natAbs_lt hf_lt_B

/-- Large-input modulus `2^B` exactness. -/
theorem step_thm1_modulus_exact_proved (A μ₀ s : ℕ) (hs : 2 ≤ s) (hm : 2 ≤ pitM A μ₀ s)
    (hcard : ∀ i : Fin s, (designSets (pitM A μ₀ s) s hm i).card = pitM A μ₀ s)
    (C : IntCircuit s) (hdeg : C.evalPoly.totalDegree ≤ s) (hcoeff : CoeffBitBound C.evalPoly s)
    (a : Fin (designL (pitM A μ₀ s)) → Fin (s * pitMu A μ₀ s + 1)) :
    let μ := pitMu A μ₀ s
    let m := pitM A μ₀ s
    let B := pitB A μ₀ s
    let S := designSets m s hm
    let v : Fin s → ℤ := fun i =>
      ryserPerm (R := ℤ)
        (matrixOfVec (fun j : Fin (μ ^ 2) => ((a ((S i).orderEmbOfFin (hcard i) j)).val : ℤ)))
    (∀ i, 0 ≤ v i ∧ v i ≤ ((s * μ ^ 2 : ℕ) : ℤ) ^ μ) ∧
    (MvPolynomial.eval v C.evalPoly).natAbs < 2 ^ (B - 1) ∧
    (C.evalAt (ZMod (2 ^ B)) (fun i => (v i : ZMod (2 ^ B))) = 0 ↔
      MvPolynomial.eval v C.evalPoly = 0) := by
  have hμ1 : 1 ≤ pitMu A μ₀ s := by
    have h1 : 1 ≤ pitT A s := (Nat.find_spec (pitT_exists A s)).1
    have h2 : 2 ≤ 2 ^ pitT A s := le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) h1)
    exact le_trans (by decide) (le_trans h2 (le_max_right μ₀ _))
  exact nwPermModTest_modulus_exact (pitMu A μ₀ s) s hs hμ1 hm hcard C hdeg hcoeff a

/-! ### Part 3: Parameter & Asymptotic Bounds (Theorem 1, Table 1, Remark 1) -/

theorem logb_two_ge_one {s : ℕ} (hs : 2 ≤ s) : (1 : ℝ) ≤ Real.logb 2 s := by
  rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by exact_mod_cast hs)

theorem logb_two_le_clog (s : ℕ) (hs : 1 ≤ s) :
    Real.logb 2 s ≤ (Nat.clog 2 s : ℝ) := by
  have h1 : (s : ℝ) ≤ (2 : ℝ) ^ (Nat.clog 2 s : ℕ) := by
    exact_mod_cast (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp le_rfl
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) h1
  rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hlog

theorem clog_lt_logb_add_one (s : ℕ) (hs : 2 ≤ s) :
    (Nat.clog 2 s : ℝ) < Real.logb 2 s + 1 := by
  have hpos : 1 ≤ Nat.clog 2 s := Nat.clog_pos (by decide) (by omega)
  have hlt : 2 ^ (Nat.clog 2 s - 1) < s := by
    by_contra h
    push Not at h
    have hle : Nat.clog 2 s ≤ Nat.clog 2 s - 1 :=
      (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr h
    omega
  have hltR : ((2 : ℝ) ^ (Nat.clog 2 s - 1 : ℕ)) < (s : ℝ) := by exact_mod_cast hlt
  have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (by positivity) hltR
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hlog
  have hsub : ((Nat.clog 2 s - 1 : ℕ) : ℝ) = (Nat.clog 2 s : ℝ) - 1 := by
    rw [Nat.cast_sub hpos, Nat.cast_one]
  linarith

private theorem mul_rpow_self {x a : ℝ} (hx : 0 < x) : x * x ^ a = x ^ (1 + a) := by
  rw [Real.rpow_add hx, Real.rpow_one]

private theorem div_rpow_self {x a : ℝ} (hx : 0 < x) : x / x ^ a = x ^ (1 - a) := by
  rw [Real.rpow_sub hx, Real.rpow_one]

/-- Equation (1) of Theorem 1. -/
theorem step_thm1_eq1_proved (c : ℝ) (hc : 0 < c) (κ μ₀ s : ℕ) (hκ : 1 ≤ κ) (hs : 2 ≤ s) :
    let A := Nat.ceil ((κ : ℝ) / c)
    let μ := pitMu A μ₀ s
    μ₀ ≤ μ ∧
    (μ : ℝ) ^ (c * (Real.logb 2 μ) ^ (1 / 3 : ℝ)) = expTwo (c * (Real.logb 2 μ) ^ (4 / 3 : ℝ)) ∧
    ((s : ℝ) ^ κ) ≤ (μ : ℝ) ^ (c * (Real.logb 2 μ) ^ (1 / 3 : ℝ)) := by
  dsimp only
  set A := Nat.ceil ((κ : ℝ) / c)
  set t := pitT A s
  set μ := pitMu A μ₀ s
  have ht_spec := Nat.find_spec (pitT_exists A s)
  have ht1 : 1 ≤ t := ht_spec.1
  have ht4 : (A * pitL s) ^ 3 ≤ t ^ 4 := ht_spec.2
  have hμ_ge_2t : 2 ^ t ≤ μ := le_max_right μ₀ (2 ^ t)
  have hμ2 : 2 ≤ μ :=
    le_trans (le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) ht1)) hμ_ge_2t
  have hμ_pos : (0 : ℝ) < (μ : ℝ) := by positivity
  have hlogμ_ge_t : (t : ℝ) ≤ Real.logb 2 μ := by
    have h1 : ((2 : ℝ) ^ (t : ℕ)) ≤ (μ : ℝ) := by exact_mod_cast hμ_ge_2t
    have h2 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) h1
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h2
  have hlogμ_pos : (0 : ℝ) < Real.logb 2 μ := lt_of_lt_of_le (by positivity) hlogμ_ge_t
  have hid : (μ : ℝ) ^ (c * (Real.logb 2 μ) ^ (1 / 3 : ℝ)) =
      expTwo (c * (Real.logb 2 μ) ^ (4 / 3 : ℝ)) := by
    unfold expTwo
    have hμ_eq : (μ : ℝ) = (2 : ℝ) ^ Real.logb 2 μ :=
      (Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hμ_pos).symm
    conv_lhs => arg 1; rw [hμ_eq]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    have hpow : Real.logb 2 μ * (Real.logb 2 μ) ^ (1 / 3 : ℝ) = (Real.logb 2 μ) ^ (4 / 3 : ℝ) := by
      rw [mul_rpow_self hlogμ_pos]; norm_num
    calc
      Real.logb 2 μ * (c * (Real.logb 2 μ) ^ (1 / 3 : ℝ))
          = c * (Real.logb 2 μ * (Real.logb 2 μ) ^ (1 / 3 : ℝ)) := by ring
      _ = c * (Real.logb 2 μ) ^ (4 / 3 : ℝ) := by rw [hpow]
  refine ⟨le_max_left _ _, hid, ?_⟩
  rw [hid]
  unfold expTwo
  have hAL_le : ((A * pitL s : ℕ) : ℝ) ≤ (t : ℝ) ^ (4 / 3 : ℝ) := by
    have hpow3 : ((A * pitL s : ℕ) : ℝ) ^ (3 : ℕ) ≤ (t : ℝ) ^ (4 : ℕ) := by exact_mod_cast ht4
    have h3r : ((A * pitL s : ℕ) : ℝ) ^ (3 : ℝ) ≤ (t : ℝ) ^ (4 : ℝ) := by
      simpa [Real.rpow_natCast] using hpow3
    have hr := Real.rpow_le_rpow (by positivity) h3r (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rw [← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)] at hr
    have h31 : (3 : ℝ) * (1 / 3 : ℝ) = 1 := by norm_num
    have h41 : (4 : ℝ) * (1 / 3 : ℝ) = 4 / 3 := by norm_num
    rw [h31, h41, Real.rpow_one] at hr
    exact hr
  have hexp_ge : (κ : ℝ) * Real.logb 2 s ≤ c * (Real.logb 2 μ) ^ (4 / 3 : ℝ) := by
    have hA_ge : (κ : ℝ) / c ≤ (A : ℝ) := Nat.le_ceil _
    have hL_ge : Real.logb 2 s ≤ (pitL s : ℝ) := logb_two_le_clog s (by omega)
    have hlog_ge : (0 : ℝ) ≤ Real.logb 2 s := le_trans (by norm_num) (logb_two_ge_one hs)
    have hprod : ((κ : ℝ) / c) * Real.logb 2 s ≤ ((A * pitL s : ℕ) : ℝ) := by
      rw [Nat.cast_mul]
      exact mul_le_mul hA_ge hL_ge hlog_ge (by positivity)
    have ht_le : (t : ℝ) ^ (4 / 3 : ℝ) ≤ (Real.logb 2 μ) ^ (4 / 3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hlogμ_ge_t (by norm_num)
    have hdiv : (κ : ℝ) / c * Real.logb 2 s ≤ (Real.logb 2 μ) ^ (4 / 3 : ℝ) :=
      le_trans hprod (le_trans hAL_le ht_le)
    have := mul_le_mul_of_nonneg_left hdiv hc.le
    rwa [← mul_assoc, mul_div_cancel₀ _ hc.ne'] at this
  have hs_eq : (s : ℝ) ^ κ = (2 : ℝ) ^ ((κ : ℝ) * Real.logb 2 s) := by
    have hs_pos : (0 : ℝ) < (s : ℝ) := by positivity
    conv_lhs => rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hs_pos]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm]
  rw [hs_eq]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_ge

/-- Upper bound `pitT A s ≤ (2 * A * log₂ s)^(3/4) + 1` for all `s ≥ 2`, `A ≥ 1`. -/
private theorem pitT_le_rpow (A s : ℕ) (hA : 1 ≤ A) (hs : 2 ≤ s) :
    (pitT A s : ℝ) ≤ (2 * (A : ℝ) * Real.logb 2 s) ^ (3 / 4 : ℝ) + 1 := by
  set t := pitT A s
  have ht1 : 1 ≤ t := (Nat.find_spec (pitT_exists A s)).1
  have hlt : (t - 1) ^ 4 < (A * pitL s) ^ 3 := by
    by_cases ht_eq : t = 1
    · rw [ht_eq]
      have hL1 : 1 ≤ pitL s := Nat.clog_pos (by decide) (by omega)
      have hAL1 : 1 ≤ A * pitL s := Nat.mul_pos hA hL1
      have : 1 ≤ (A * pitL s) ^ 3 := Nat.one_le_pow _ _ hAL1
      omega
    · have hlt_prev : t - 1 < t := by omega
      have hprev : ¬ (1 ≤ t - 1 ∧ (A * pitL s) ^ 3 ≤ (t - 1) ^ 4) :=
        Nat.find_min (pitT_exists A s) hlt_prev
      have hge1 : 1 ≤ t - 1 := by omega
      push Not at hprev
      exact hprev hge1
  have hlog_ge1 : (1 : ℝ) ≤ Real.logb 2 s := logb_two_ge_one hs
  have hL_le : (pitL s : ℝ) ≤ 2 * Real.logb 2 s := by
    have h1 : (pitL s : ℝ) < Real.logb 2 s + 1 := clog_lt_logb_add_one s hs
    linarith
  have hAL_le : ((A * pitL s : ℕ) : ℝ) ≤ 2 * (A : ℝ) * Real.logb 2 s := by
    rw [Nat.cast_mul]
    nlinarith [show (0 : ℝ) ≤ (A : ℝ) by positivity]
  have hlog_nn : 0 ≤ Real.logb 2 s := by linarith
  have h4 : ((t - 1 : ℕ) : ℝ) ^ (4 : ℝ) ≤ (2 * (A : ℝ) * Real.logb 2 s) ^ (3 : ℝ) := by
    have hltR : ((t - 1 : ℕ) : ℝ) ^ (4 : ℕ) ≤ ((A * pitL s : ℕ) : ℝ) ^ (3 : ℕ) := by
      exact_mod_cast le_of_lt hlt
    have h1 : ((t - 1 : ℕ) : ℝ) ^ (4 : ℝ) ≤ ((A * pitL s : ℕ) : ℝ) ^ (3 : ℝ) := by
      simpa [Real.rpow_natCast] using hltR
    have h2 : ((A * pitL s : ℕ) : ℝ) ^ (3 : ℝ) ≤ (2 * (A : ℝ) * Real.logb 2 s) ^ (3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hAL_le (by norm_num)
    exact le_trans h1 h2
  have hbase_nn : 0 ≤ 2 * (A : ℝ) * Real.logb 2 s := by positivity
  have hr := Real.rpow_le_rpow (by positivity) h4 (by norm_num : (0 : ℝ) ≤ 1 / 4)
  rw [← Real.rpow_mul (by positivity), ← Real.rpow_mul hbase_nn] at hr
  have h41 : (4 : ℝ) * (1 / 4 : ℝ) = 1 := by norm_num
  have h31 : (3 : ℝ) * (1 / 4 : ℝ) = 3 / 4 := by norm_num
  rw [h41, h31, Real.rpow_one] at hr
  have hsub : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by rw [Nat.cast_sub ht1, Nat.cast_one]
  linarith

/-- Elementary inequality: for any `C > 0` and `0 < α < 1`, eventually `C * u^α < u`. -/
theorem exists_rpow_lt_self (C α : ℝ) (hC : 0 < C) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ U₀ : ℝ, 1 ≤ U₀ ∧ ∀ u ≥ U₀, C * u ^ α < u := by
  let β := 1 - α
  have hβ : 0 < β := sub_pos.mpr hα1
  let U₀ := max 1 ((C + 1) ^ (1 / β))
  refine ⟨U₀, le_max_left _ _, fun u hu => ?_⟩
  have hu1 : 1 ≤ u := le_trans (le_max_left _ _) hu
  have hu0 : 0 < u := by linarith
  have hu_ge : (C + 1) ^ (1 / β) ≤ u := le_trans (le_max_right _ _) hu
  have hpow := Real.rpow_le_rpow (by positivity) hu_ge hβ.le
  rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hβ.ne', Real.rpow_one] at hpow
  have hlt : C < u ^ β := by linarith
  have hmul := mul_lt_mul_of_pos_right hlt (Real.rpow_pos_of_pos hu0 α)
  rw [← Real.rpow_add hu0] at hmul
  have hsum : β + α = 1 := sub_add_cancel 1 α
  rw [hsum, Real.rpow_one] at hmul
  exact hmul

/-- Threshold `s₀ = s₀(A, μ₀) ≥ 4` for Theorem 1. -/
theorem step_thm1_threshold_proved (A μ₀ : ℕ) (hA : 1 ≤ A) (hμ₀ : 1 ≤ μ₀) :
    ∃ s₀ : ℕ, 4 ≤ s₀ ∧ ∀ s ≥ s₀,
      Real.logb 2 s < (pitM A μ₀ s : ℝ) ∧
      pitM A μ₀ s < s ∧
      s * pitMu A μ₀ s + 1 ≤ s ^ 2 := by
  let C₁ : ℝ := 2 * (2 * (A : ℝ)) ^ (3 / 4 : ℝ) + 2
  obtain ⟨U₁, hU₁1, hU₁⟩ := exists_rpow_lt_self C₁ (3 / 4) (by positivity) (by norm_num) (by norm_num)
  let U := max (max U₁ 16) (2 * Real.logb 2 ((μ₀ : ℝ) + 1) + 4)
  let s₀ := max 4 (Nat.ceil ((2 : ℝ) ^ U) + 1)
  refine ⟨s₀, le_max_left _ _, fun s hs => ?_⟩
  have hs4 : 4 ≤ s := le_trans (le_max_left _ _) hs
  have hs2 : 2 ≤ s := by omega
  have hs_gt_2U : (2 : ℝ) ^ U < (s : ℝ) := by
    have h1 : Nat.ceil ((2 : ℝ) ^ U) + 1 ≤ s := le_trans (le_max_right _ _) hs
    have h2 : (2 : ℝ) ^ U ≤ (Nat.ceil ((2 : ℝ) ^ U) : ℝ) := Nat.le_ceil _
    have h3 : (Nat.ceil ((2 : ℝ) ^ U) : ℝ) + 1 ≤ (s : ℝ) := by exact_mod_cast h1
    linarith
  set u := Real.logb 2 s
  have hu_gt_U : U < u := by
    have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (by positivity) hs_gt_2U
    rwa [Real.logb_rpow (by norm_num) (by norm_num)] at hlog
  have hu_ge_U1 : U₁ ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hu_gt_U.le
  have hu_ge_16 : (16 : ℝ) ≤ u := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hu_gt_U.le
  have hu_pos : 0 < u := by linarith
  have h2t_lt_u : 2 * (pitT A s : ℝ) < u := by
    have ht_le := pitT_le_rpow A s hA hs2
    have hu1 : (1 : ℝ) ≤ u ^ (3 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have hbound : 2 * (pitT A s : ℝ) ≤ C₁ * u ^ (3 / 4 : ℝ) := by
      have hmul : (2 * (A : ℝ) * u) ^ (3 / 4 : ℝ) = (2 * (A : ℝ)) ^ (3 / 4 : ℝ) * u ^ (3 / 4 : ℝ) :=
        Real.mul_rpow (by positivity) hu_pos.le
      dsimp only [C₁]
      nlinarith [ht_le, hmul, hu1]
    exact lt_of_le_of_lt hbound (hU₁ u hu_ge_U1)
  have hpow2t_lt_s : (2 ^ pitT A s) ^ 2 < s := by
    have hR : ((2 : ℝ) ^ (2 * (pitT A s : ℝ))) < (s : ℝ) := by
      have h1 := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) h2t_lt_u
      rwa [Real.rpow_logb (by norm_num) (by norm_num) (by positivity)] at h1
    have hnat : (((2 ^ pitT A s) ^ 2 : ℕ) : ℝ) < (s : ℝ) := by
      have heq : (((2 ^ pitT A s) ^ 2 : ℕ) : ℝ) = (2 : ℝ) ^ (2 * (pitT A s : ℝ)) := by
        rw [← pow_mul, Nat.mul_comm, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
        push_cast; rfl
      rwa [heq]
    exact_mod_cast hnat
  have hμ0_sq_lt_s : μ₀ ^ 2 < s := by
    have hu_gt : 2 * Real.logb 2 ((μ₀ : ℝ) + 1) < u := by
      have h1 : 2 * Real.logb 2 ((μ₀ : ℝ) + 1) + 4 ≤ U := le_max_right _ _
      linarith
    have h1 := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hu_gt
    rw [Real.rpow_logb (by norm_num) (by norm_num) (by positivity)] at h1
    have h2 : (2 : ℝ) ^ (2 * Real.logb 2 ((μ₀ : ℝ) + 1)) = ((μ₀ : ℝ) + 1) ^ (2 : ℝ) := by
      rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
    rw [h2] at h1
    have h3 : ((μ₀ ^ 2 : ℕ) : ℝ) < (s : ℝ) := by
      have hsq : ((μ₀ : ℝ) + 1) ^ (2 : ℝ) = ((μ₀ : ℝ) + 1) ^ (2 : ℕ) := Real.rpow_natCast _ 2
      rw [hsq] at h1
      have hposμ : (0 : ℝ) ≤ (μ₀ : ℝ) := Nat.cast_nonneg _
      push_cast
      nlinarith
    exact_mod_cast h3
  have hm_lt_s : pitM A μ₀ s < s := by
    unfold pitM pitMu
    rcases max_cases μ₀ (2 ^ pitT A s) with ⟨hmax, _⟩ | ⟨hmax, _⟩
    · rw [hmax]; exact hμ0_sq_lt_s
    · rw [hmax]; exact hpow2t_lt_s
  have hlog_lt_m : u < (pitM A μ₀ s : ℝ) := by
    have ht4_ge_u3 : u ^ (3 : ℕ) ≤ (pitT A s : ℝ) ^ (4 : ℕ) := by
      have ht_spec := (Nat.find_spec (pitT_exists A s)).2
      have hL_ge : u ≤ (pitL s : ℝ) := logb_two_le_clog s (by omega)
      have hAL_ge : u ≤ ((A * pitL s : ℕ) : ℝ) := by
        rw [Nat.cast_mul]
        have hA1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
        nlinarith
      have h3 : u ^ (3 : ℕ) ≤ ((A * pitL s : ℕ) : ℝ) ^ (3 : ℕ) :=
        pow_le_pow_left₀ hu_pos.le hAL_ge 3
      exact le_trans h3 (by exact_mod_cast ht_spec)
    have ht_ge_4 : 4 ≤ pitT A s := by
      by_contra hlt4
      have ht3 : (pitT A s : ℝ) ≤ 3 := by exact_mod_cast (show pitT A s ≤ 3 by omega)
      have ht0 : (0 : ℝ) ≤ (pitT A s : ℝ) := Nat.cast_nonneg _
      have h1 : (pitT A s : ℝ) ^ (4 : ℕ) ≤ (3 : ℝ) ^ (4 : ℕ) := pow_le_pow_left₀ ht0 ht3 4
      have h2 : (16 : ℝ) ^ (3 : ℕ) ≤ u ^ (3 : ℕ) := pow_le_pow_left₀ (by norm_num) hu_ge_16 3
      norm_num at h1 h2
      linarith
    have hpow2_ge_sq : ∀ k : ℕ, 4 ≤ k → k ^ 2 ≤ 2 ^ k := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => decide
      | succ n hn ih =>
        have h2n : 2 * n + 1 ≤ n ^ 2 := by nlinarith
        calc
          (n + 1) ^ 2 = n ^ 2 + (2 * n + 1) := by ring
          _ ≤ n ^ 2 + n ^ 2 := Nat.add_le_add_left h2n _
          _ = 2 * n ^ 2 := by ring
          _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
          _ = 2 ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]
    have ht4_le_m : (pitT A s) ^ 4 ≤ pitM A μ₀ s := by
      have h1 : (pitT A s) ^ 4 = ((pitT A s) ^ 2) ^ 2 := by ring
      rw [h1]
      exact le_trans (Nat.pow_le_pow_left (hpow2_ge_sq _ ht_ge_4) 2)
        (Nat.pow_le_pow_left (le_max_right μ₀ _) 2)
    have hu_lt_u3 : u < u ^ (3 : ℕ) := by
      have hsq : u ^ (2 : ℕ) ≥ 256 := by nlinarith
      nlinarith [show u ^ (3 : ℕ) = u * u ^ (2 : ℕ) by ring]
    exact lt_of_lt_of_le (lt_of_lt_of_le hu_lt_u3 ht4_ge_u3) (by exact_mod_cast ht4_le_m)
  have hμ_lt_s : pitMu A μ₀ s < s := by
    have hμ_le_m : pitMu A μ₀ s ≤ pitM A μ₀ s := by
      simpa [pitM, sq] using Nat.le_mul_self (pitMu A μ₀ s)
    exact lt_of_le_of_lt hμ_le_m hm_lt_s
  have hsmu : s * pitMu A μ₀ s + 1 ≤ s ^ 2 := by nlinarith
  exact ⟨hlog_lt_m, hm_lt_s, hsmu⟩

/-- Bound `pitB A μ₀ s ≤ 10 * s^(3/2) * log₂ s` whenever `s ≥ 2` and `pitM A μ₀ s < s`. -/
theorem step_thm1_B_bound_proved (A μ₀ s : ℕ) (hs : 2 ≤ s) (hms : pitM A μ₀ s < s) :
    (pitB A μ₀ s : ℝ) ≤ 10 * (s : ℝ) ^ (3 / 2 : ℝ) * Real.logb 2 s := by
  set μ := pitMu A μ₀ s
  have hμ_sq_lt : μ ^ 2 < s := hms
  have hμ_le_sqrt : (μ : ℝ) ≤ (s : ℝ) ^ (1 / 2 : ℝ) := by
    have h1 : (μ : ℝ) ^ (2 : ℝ) ≤ (s : ℝ) := by
      have : ((μ ^ 2 : ℕ) : ℝ) ≤ (s : ℝ) := by exact_mod_cast hμ_sq_lt.le
      simpa [Real.rpow_natCast] using this
    have h2 := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [← Real.rpow_mul (by positivity)] at h2
    have h21 : (2 : ℝ) * (1 / 2 : ℝ) = 1 := by norm_num
    rw [h21, Real.rpow_one] at h2
    exact h2
  have hlog_ge1 : (1 : ℝ) ≤ Real.logb 2 s := logb_two_ge_one hs
  have hs_ge1 : (1 : ℝ) ≤ (s : ℝ) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ s)) (by norm_num)
  have hsm2_le : s * μ ^ 2 ≤ s ^ 2 := by
    calc s * μ ^ 2 ≤ s * s := Nat.mul_le_mul_left s hμ_sq_lt.le
    _ = s ^ 2 := by ring
  have hclog_le : (Nat.clog 2 (s * μ ^ 2) : ℝ) ≤ 2 * Real.logb 2 s + 1 := by
    have h1 : Nat.clog 2 (s * μ ^ 2) ≤ Nat.clog 2 (s ^ 2) := Nat.clog_mono_right 2 hsm2_le
    have h2 : (Nat.clog 2 (s ^ 2) : ℝ) < Real.logb 2 (s ^ 2 : ℕ) + 1 :=
      clog_lt_logb_add_one (s ^ 2) (by nlinarith)
    have h3 : Real.logb 2 ((s ^ 2 : ℕ) : ℝ) = 2 * Real.logb 2 s := by
      rw [Nat.cast_pow, Real.logb_pow]; norm_num
    linarith [show (Nat.clog 2 (s * μ ^ 2) : ℝ) ≤ (Nat.clog 2 (s ^ 2) : ℝ) by exact_mod_cast h1]
  have hs32 : (s : ℝ) * (s : ℝ) ^ (1 / 2 : ℝ) = (s : ℝ) ^ (3 / 2 : ℝ) := by
    rw [mul_rpow_self (by positivity)]; norm_num
  have hB_eq : (pitB A μ₀ s : ℝ) = 3 * (s : ℝ) + (s : ℝ) * (μ : ℝ) * (Nat.clog 2 (s * μ ^ 2) : ℝ) + 2 := by
    unfold pitB; push_cast; ring
  rw [hB_eq]
  have hterm : (s : ℝ) * (μ : ℝ) * (Nat.clog 2 (s * μ ^ 2) : ℝ) ≤
      (s : ℝ) ^ (3 / 2 : ℝ) * (3 * Real.logb 2 s) := by
    have hsmu : (s : ℝ) * (μ : ℝ) ≤ (s : ℝ) ^ (3 / 2 : ℝ) := by
      rw [← hs32]; exact mul_le_mul_of_nonneg_left hμ_le_sqrt (by positivity)
    have hc3 : (Nat.clog 2 (s * μ ^ 2) : ℝ) ≤ 3 * Real.logb 2 s := by linarith
    exact mul_le_mul hsmu hc3 (by positivity) (by positivity)
  have hs_ge2 : (2 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hs_le_32 : (s : ℝ) ≤ (s : ℝ) ^ (3 / 2 : ℝ) := by
    rw [← hs32]; nlinarith
  have hs32_ge2 : (2 : ℝ) ≤ (s : ℝ) ^ (3 / 2 : ℝ) := le_trans hs_ge2 hs_le_32
  have hs32_le_prod : (s : ℝ) ^ (3 / 2 : ℝ) ≤ (s : ℝ) ^ (3 / 2 : ℝ) * Real.logb 2 s := by
    nlinarith
  linarith

/-- Evaluation-point & work-count exponent bound of Theorem 1. -/
theorem step_thm1_exponent_bound_proved (A μ₀ s₀ d : ℕ) (hA : 1 ≤ A) (hμ₀ : 1 ≤ μ₀)
    (hs₀ : 4 ≤ s₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ s ≥ 2,
      (pitEvalPointCount A μ₀ s₀ s : ℝ) * ((2 : ℝ) ^ pitMu A μ₀ s) * ((s : ℝ) ^ d) ≤
        expTwo (expTwo (K * (Real.logb 2 s) ^ (3 / 4 : ℝ))) := by
  let M_small : ℝ :=
    ((s₀ + 1 : ℕ) ^ s₀ : ℝ) * (2 : ℝ) ^ (pitMu A μ₀ s₀) * ((s₀ : ℝ) ^ d) + 2
  let C_base : ℝ := 5 * (2 * (A : ℝ)) ^ (3 / 4 : ℝ)
  let K_small : ℝ := Real.logb 2 (Real.logb 2 M_small + 2) + 2
  let K_large : ℝ := C_base + 5 * Real.logb 2 ((μ₀ : ℝ) + 2) + (d : ℝ) + 30
  let K : ℝ := max K_small K_large
  have hlogμ0_nn : 0 ≤ Real.logb 2 ((μ₀ : ℝ) + 2) :=
    Real.logb_nonneg (by norm_num) (by linarith [show (0 : ℝ) ≤ (μ₀ : ℝ) by positivity])
  have hK_pos : 0 < K := by
    have hC : 0 ≤ C_base := by positivity
    have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
    have hKl_pos : 0 < K_large := by dsimp only [K_large]; linarith
    exact lt_of_lt_of_le hKl_pos (le_max_right _ _)
  refine ⟨K, hK_pos, fun s hs => ?_⟩
  have hlog_ge1 : (1 : ℝ) ≤ Real.logb 2 s := logb_two_ge_one hs
  have hlog34_ge1 : (1 : ℝ) ≤ (Real.logb 2 s) ^ (3 / 4 : ℝ) := Real.one_le_rpow hlog_ge1 (by norm_num)
  by_cases hsmall : s < s₀
  · have hμ_mono : pitMu A μ₀ s ≤ pitMu A μ₀ s₀ := by
      unfold pitMu
      apply max_le_max_left
      apply Nat.pow_le_pow_right (by decide)
      apply Nat.find_mono
      intro t ht
      refine ⟨ht.1, le_trans ?_ ht.2⟩
      exact Nat.pow_le_pow_left (Nat.mul_le_mul_left A (Nat.clog_mono_right 2 hsmall.le)) 3
    have hlhs_le :
        (pitEvalPointCount A μ₀ s₀ s : ℝ) * ((2 : ℝ) ^ pitMu A μ₀ s) * ((s : ℝ) ^ d) ≤ M_small := by
      unfold pitEvalPointCount
      simp only [hsmall, ite_true]
      have h1 : (((s + 1) ^ s : ℕ) : ℝ) ≤ (((s₀ + 1) ^ s₀ : ℕ) : ℝ) := by
        exact_mod_cast le_trans (Nat.pow_le_pow_left (by omega) s)
          (Nat.pow_le_pow_right (by omega) hsmall.le)
      have h2 : (2 : ℝ) ^ pitMu A μ₀ s ≤ (2 : ℝ) ^ pitMu A μ₀ s₀ :=
        pow_le_pow_right₀ (by norm_num) hμ_mono
      have h3 : (s : ℝ) ^ d ≤ (s₀ : ℝ) ^ d :=
        pow_le_pow_left₀ (by positivity) (by exact_mod_cast hsmall.le) d
      have hprod : (((s + 1) ^ s : ℕ) : ℝ) * (2 : ℝ) ^ pitMu A μ₀ s * (s : ℝ) ^ d ≤
          (((s₀ + 1) ^ s₀ : ℕ) : ℝ) * (2 : ℝ) ^ pitMu A μ₀ s₀ * (s₀ : ℝ) ^ d :=
        mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) h3 (by positivity) (by positivity)
      dsimp only [M_small]
      have hcast_eq : (((s₀ + 1) ^ s₀ : ℕ) : ℝ) = ((s₀ + 1 : ℕ) : ℝ) ^ s₀ := Nat.cast_pow _ _
      rw [hcast_eq] at hprod
      linarith
    have hM_le : M_small ≤ expTwo (expTwo (K * (Real.logb 2 s) ^ (3 / 4 : ℝ))) := by
      unfold expTwo
      have hM_ge2 : (2 : ℝ) ≤ M_small := by
        dsimp only [M_small]
        have : 0 ≤ ((s₀ + 1 : ℕ) ^ s₀ : ℝ) * (2 : ℝ) ^ pitMu A μ₀ s₀ * (s₀ : ℝ) ^ d := by positivity
        linarith
      have hlogM_ge1 : (1 : ℝ) ≤ Real.logb 2 M_small := by
        rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
        exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) hM_ge2
      have hK_ge : Real.logb 2 (Real.logb 2 M_small + 2) ≤ K * (Real.logb 2 s) ^ (3 / 4 : ℝ) := by
        have hKs : K_small ≤ K := le_max_left _ _
        have h1 : K_small ≤ K * (Real.logb 2 s) ^ (3 / 4 : ℝ) := by
          calc K_small ≤ K := hKs
          _ = K * 1 := (mul_one K).symm
          _ ≤ K * (Real.logb 2 s) ^ (3 / 4 : ℝ) := mul_le_mul_of_nonneg_left hlog34_ge1 hK_pos.le
        dsimp only [K_small] at h1
        linarith
      have hstep1 : Real.logb 2 M_small ≤ (2 : ℝ) ^ (K * (Real.logb 2 s) ^ (3 / 4 : ℝ)) := by
        have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hK_ge
        rw [Real.rpow_logb (by norm_num) (by norm_num) (by linarith)] at h
        linarith
      have hstep2 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hstep1
      rwa [Real.rpow_logb (by norm_num) (by norm_num) (by linarith)] at hstep2
    exact le_trans hlhs_le hM_le
  · unfold pitEvalPointCount
    simp only [hsmall, ite_false]
    set μ := pitMu A μ₀ s
    set m := pitM A μ₀ s
    set u := Real.logb 2 s
    have hu_pos : 0 < u := by linarith
    have hμ_ge2 : 2 ≤ μ := by
      have ht1 : 1 ≤ pitT A s := (Nat.find_spec (pitT_exists A s)).1
      exact le_trans (le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) ht1))
        (le_max_right _ _)
    have hl_lt : designL m < 2 * μ ^ 4 := by
      have hr1 : 1 ≤ designR m := Nat.clog_pos (by decide) (by dsimp [m, pitM]; nlinarith)
      have hpow_lt : 2 ^ (designR m - 1) < m := by
        by_contra h; push Not at h
        have hle : designR m ≤ designR m - 1 := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr h
        omega
      have hq_lt : designQ m < 2 * m := by
        unfold designQ
        have hsplit : 2 ^ designR m = 2 * 2 ^ (designR m - 1) := by
          conv_lhs => rw [← Nat.sub_add_cancel hr1, pow_succ, Nat.mul_comm]
        omega
      calc designL m = m * designQ m := rfl
      _ < m * (2 * m) := Nat.mul_lt_mul_of_pos_left hq_lt (by dsimp [m, pitM]; nlinarith)
      _ = 2 * μ ^ 4 := by dsimp [m, pitM]; ring
    have hbase_le : ((s * μ + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (u + (μ : ℝ) + 1) := by
      have hs_eq : (s : ℝ) = (2 : ℝ) ^ u :=
        (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
      have hμ_le_2μ : (μ : ℝ) ≤ (2 : ℝ) ^ (μ : ℝ) := by
        have hnat : μ ≤ 2 ^ μ := Nat.le_of_lt Nat.lt_two_pow_self
        simpa [Real.rpow_natCast] using (show (μ : ℝ) ≤ ((2 ^ μ : ℕ) : ℝ) by exact_mod_cast hnat)
      have hprod : (s : ℝ) * (μ : ℝ) ≤ (2 : ℝ) ^ (u + (μ : ℝ)) := by
        rw [Real.rpow_add (by norm_num), ← hs_eq]
        exact mul_le_mul_of_nonneg_left hμ_le_2μ (by positivity)
      have h2ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (u + (μ : ℝ)) :=
        Real.one_le_rpow (by norm_num) (by linarith [show (0 : ℝ) ≤ (μ : ℝ) by positivity])
      rw [Real.rpow_add (by norm_num), Real.rpow_one]
      push_cast
      linarith
    have hpow_smu : (((s * μ + 1) ^ designL m : ℕ) : ℝ) ≤
        (2 : ℝ) ^ ((2 * (μ : ℝ) ^ 4) * (u + (μ : ℝ) + 1)) := by
      rw [Nat.cast_pow]
      calc
        ((s * μ + 1 : ℕ) : ℝ) ^ designL m
            ≤ ((2 : ℝ) ^ (u + (μ : ℝ) + 1)) ^ designL m :=
              pow_le_pow_left₀ (by positivity) hbase_le _
        _ = (2 : ℝ) ^ ((designL m : ℝ) * (u + (μ : ℝ) + 1)) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
        _ ≤ (2 : ℝ) ^ ((2 * (μ : ℝ) ^ 4) * (u + (μ : ℝ) + 1)) := by
              apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
              have hle : (designL m : ℝ) ≤ 2 * (μ : ℝ) ^ 4 := by exact_mod_cast hl_lt.le
              exact mul_le_mul_of_nonneg_right hle (by linarith [show (0 : ℝ) ≤ (μ : ℝ) by positivity])
    have hsd : (s : ℝ) ^ d = (2 : ℝ) ^ ((d : ℝ) * u) := by
      have hs_eq : (s : ℝ) = (2 : ℝ) ^ u :=
        (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
      conv_lhs => rw [hs_eq]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
    have h2μ : (2 : ℝ) ^ μ = (2 : ℝ) ^ (μ : ℝ) := (Real.rpow_natCast 2 μ).symm
    have htotal :
        (((s * μ + 1) ^ designL m : ℕ) : ℝ) * ((2 : ℝ) ^ μ) * ((s : ℝ) ^ d) ≤
        (2 : ℝ) ^ ((2 * (μ : ℝ) ^ 4) * (u + (μ : ℝ) + 1) + (μ : ℝ) + (d : ℝ) * u) := by
      calc
        (((s * μ + 1) ^ designL m : ℕ) : ℝ) * ((2 : ℝ) ^ μ) * ((s : ℝ) ^ d)
            ≤ (2 : ℝ) ^ ((2 * (μ : ℝ) ^ 4) * (u + (μ : ℝ) + 1)) * (2 : ℝ) ^ (μ : ℝ) *
                (2 : ℝ) ^ ((d : ℝ) * u) := by
              rw [h2μ, hsd]
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hpow_smu (by positivity)) (by positivity)
        _ = (2 : ℝ) ^ ((2 * (μ : ℝ) ^ 4) * (u + (μ : ℝ) + 1) + (μ : ℝ) + (d : ℝ) * u) := by
              rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
    let E₀ : ℝ := (2 * (A : ℝ)) ^ (3 / 4 : ℝ) + Real.logb 2 ((μ₀ : ℝ) + 2)
    have hE₀_nonneg : 0 ≤ E₀ := add_nonneg (by positivity) hlogμ0_nn
    have hμ_ub : (μ : ℝ) ≤ ((μ₀ : ℝ) + 2) * (2 : ℝ) ^ ((2 * (A : ℝ)) ^ (3 / 4 : ℝ) * u ^ (3 / 4 : ℝ)) := by
      have ht_le := pitT_le_rpow A s hA hs
      have hmul : (2 * (A : ℝ) * u) ^ (3 / 4 : ℝ) = (2 * (A : ℝ)) ^ (3 / 4 : ℝ) * u ^ (3 / 4 : ℝ) :=
        Real.mul_rpow (by positivity) hu_pos.le
      have h2t : ((2 ^ pitT A s : ℕ) : ℝ) ≤ 2 * (2 : ℝ) ^ ((2 * (A : ℝ)) ^ (3 / 4 : ℝ) * u ^ (3 / 4 : ℝ)) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
        have h1 : (2 : ℝ) ^ (pitT A s : ℝ) ≤ (2 : ℝ) ^ ((2 * (A : ℝ)) ^ (3 / 4 : ℝ) * u ^ (3 / 4 : ℝ) + 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        rw [Real.rpow_add (by norm_num), Real.rpow_one, mul_comm] at h1
        exact h1
      have hpow_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((2 * (A : ℝ)) ^ (3 / 4 : ℝ) * u ^ (3 / 4 : ℝ)) :=
        Real.one_le_rpow (by norm_num) (by positivity)
      have hμ_le_max : (μ : ℝ) ≤ max (μ₀ : ℝ) ((2 ^ pitT A s : ℕ) : ℝ) := by
        dsimp only [μ, pitMu]; exact_mod_cast le_rfl
      have h1 : (μ₀ : ℝ) ≤ ((μ₀ : ℝ) + 2) * (2 : ℝ) ^ ((2 * (A : ℝ)) ^ (3 / 4 : ℝ) * u ^ (3 / 4 : ℝ)) := by
        nlinarith [show (0 : ℝ) ≤ (μ₀ : ℝ) by positivity]
      have h2 : ((2 ^ pitT A s : ℕ) : ℝ) ≤ ((μ₀ : ℝ) + 2) * (2 : ℝ) ^ ((2 * (A : ℝ)) ^ (3 / 4 : ℝ) * u ^ (3 / 4 : ℝ)) := by
        nlinarith [show (0 : ℝ) ≤ (μ₀ : ℝ) by positivity]
      exact le_trans hμ_le_max (max_le h1 h2)
    have hμ_exp : (μ : ℝ) ≤ (2 : ℝ) ^ (E₀ * u ^ (3 / 4 : ℝ)) := by
      have hE : (2 * (A : ℝ)) ^ (3 / 4 : ℝ) * u ^ (3 / 4 : ℝ) + Real.logb 2 ((μ₀ : ℝ) + 2) ≤
          E₀ * u ^ (3 / 4 : ℝ) := by
        dsimp only [E₀]
        have h1 : Real.logb 2 ((μ₀ : ℝ) + 2) ≤ Real.logb 2 ((μ₀ : ℝ) + 2) * u ^ (3 / 4 : ℝ) := by
          nlinarith
        linarith
      calc
        (μ : ℝ) ≤ ((μ₀ : ℝ) + 2) * (2 : ℝ) ^ ((2 * (A : ℝ)) ^ (3 / 4 : ℝ) * u ^ (3 / 4 : ℝ)) := hμ_ub
        _ = (2 : ℝ) ^ (Real.logb 2 ((μ₀ : ℝ) + 2)) * (2 : ℝ) ^ ((2 * (A : ℝ)) ^ (3 / 4 : ℝ) * u ^ (3 / 4 : ℝ)) := by
              rw [Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
        _ = (2 : ℝ) ^ ((2 * (A : ℝ)) ^ (3 / 4 : ℝ) * u ^ (3 / 4 : ℝ) + Real.logb 2 ((μ₀ : ℝ) + 2)) := by
              rw [← Real.rpow_add (by norm_num), add_comm]
        _ ≤ (2 : ℝ) ^ (E₀ * u ^ (3 / 4 : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hE
    have h_self_le_two_pow : ∀ x : ℝ, 0 ≤ x → x ≤ (2 : ℝ) ^ (2 * x) := by
      intro x hx
      have hln2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      have hexp : 2 * x * Real.log 2 + 1 ≤ Real.exp (2 * x * Real.log 2) := Real.add_one_le_exp _
      have hrpow : (2 : ℝ) ^ (2 * x) = Real.exp (2 * x * Real.log 2) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]
      rw [hrpow]
      nlinarith
    have hu_le_exp : u ≤ (2 : ℝ) ^ (8 * u ^ (3 / 4 : ℝ)) := by
      have hv_pos : 0 ≤ u ^ (1 / 4 : ℝ) := by positivity
      have hv_le := h_self_le_two_pow (u ^ (1 / 4 : ℝ)) hv_pos
      have h4 : u = (u ^ (1 / 4 : ℝ)) ^ (4 : ℝ) := by
        rw [← Real.rpow_mul hu_pos.le]; norm_num
      have hu14_le_34 : u ^ (1 / 4 : ℝ) ≤ u ^ (3 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlog_ge1 (by norm_num)
      calc
        u = (u ^ (1 / 4 : ℝ)) ^ (4 : ℝ) := h4
        _ ≤ ((2 : ℝ) ^ (2 * u ^ (1 / 4 : ℝ))) ^ (4 : ℝ) :=
            Real.rpow_le_rpow hv_pos hv_le (by norm_num)
        _ = (2 : ℝ) ^ (8 * u ^ (1 / 4 : ℝ)) := by
            rw [← Real.rpow_mul (by norm_num)]; congr 1; ring
        _ ≤ (2 : ℝ) ^ (8 * u ^ (3 / 4 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hd_le_2d : (d : ℝ) ≤ (2 : ℝ) ^ (d : ℝ) := by
      have hnat : d ≤ 2 ^ d := Nat.le_of_lt Nat.lt_two_pow_self
      simpa [Real.rpow_natCast] using (show (d : ℝ) ≤ ((2 ^ d : ℕ) : ℝ) by exact_mod_cast hnat)
    have hμ4_le : (μ : ℝ) ^ (4 : ℕ) ≤ (2 : ℝ) ^ (4 * E₀ * u ^ (3 / 4 : ℝ)) := by
      calc
        (μ : ℝ) ^ (4 : ℕ) ≤ ((2 : ℝ) ^ (E₀ * u ^ (3 / 4 : ℝ))) ^ (4 : ℕ) :=
          pow_le_pow_left₀ (by positivity) hμ_exp 4
        _ = (2 : ℝ) ^ (4 * E₀ * u ^ (3 / 4 : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; push_cast; congr 1; ring
    have hμ5_le : (μ : ℝ) ^ (4 : ℕ) * (μ : ℝ) ≤ (2 : ℝ) ^ (5 * E₀ * u ^ (3 / 4 : ℝ)) := by
      calc
        (μ : ℝ) ^ (4 : ℕ) * (μ : ℝ)
            ≤ (2 : ℝ) ^ (4 * E₀ * u ^ (3 / 4 : ℝ)) * (2 : ℝ) ^ (E₀ * u ^ (3 / 4 : ℝ)) :=
              mul_le_mul hμ4_le hμ_exp (by positivity) (by positivity)
        _ = (2 : ℝ) ^ (5 * E₀ * u ^ (3 / 4 : ℝ)) := by
              rw [← Real.rpow_add (by norm_num)]; congr 1; ring
    set U34 : ℝ := u ^ (3 / 4 : ℝ)
    set Big : ℝ := (2 : ℝ) ^ ((5 * E₀ + 8 + (d : ℝ)) * U34)
    have hU34_ge1 : 1 ≤ U34 := hlog34_ge1
    have hU34_nn : 0 ≤ U34 := by linarith
    have hBig_nn : 0 ≤ Big := by positivity
    have hd_nn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
    have hE0_U : 0 ≤ E₀ * U34 := mul_nonneg hE₀_nonneg hU34_nn
    have hd_U : (d : ℝ) ≤ (d : ℝ) * U34 := by
      calc (d : ℝ) = (d : ℝ) * 1 := (mul_one _).symm
      _ ≤ (d : ℝ) * U34 := mul_le_mul_of_nonneg_left hU34_ge1 hd_nn
    have hP1 : (2 : ℝ) ^ (4 * E₀ * U34) * (2 : ℝ) ^ (8 * U34) ≤ Big := by
      rw [← Real.rpow_add (by norm_num)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [mul_nonneg hd_nn hU34_nn])
    have hP2 : (2 : ℝ) ^ (5 * E₀ * U34) ≤ Big :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [mul_nonneg hd_nn hU34_nn])
    have hP3 : (2 : ℝ) ^ (4 * E₀ * U34) ≤ Big :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [mul_nonneg hd_nn hU34_nn])
    have hP4 : (2 : ℝ) ^ (E₀ * U34) ≤ Big :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [mul_nonneg hd_nn hU34_nn])
    have hP5 : (2 : ℝ) ^ (d : ℝ) * (2 : ℝ) ^ (8 * U34) ≤ Big := by
      rw [← Real.rpow_add (by norm_num)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have ht1 : (μ : ℝ) ^ 4 * u ≤ Big :=
      le_trans (mul_le_mul hμ4_le hu_le_exp hu_pos.le (by positivity)) hP1
    have ht2 : (μ : ℝ) ^ 4 * (μ : ℝ) ≤ Big := le_trans hμ5_le hP2
    have ht3 : (μ : ℝ) ^ 4 ≤ Big := le_trans hμ4_le hP3
    have ht4 : (μ : ℝ) ≤ Big := le_trans hμ_exp hP4
    have ht5 : (d : ℝ) * u ≤ Big :=
      le_trans (mul_le_mul hd_le_2d hu_le_exp hu_pos.le (by positivity)) hP5
    have hM_big : (2 * (μ : ℝ) ^ 4) * (u + (μ : ℝ) + 1) + (μ : ℝ) + (d : ℝ) * u ≤ 16 * Big := by
      have hexp_eq : (2 * (μ : ℝ) ^ 4) * (u + (μ : ℝ) + 1) + (μ : ℝ) + (d : ℝ) * u =
          2 * ((μ : ℝ) ^ 4 * u) + 2 * ((μ : ℝ) ^ 4 * (μ : ℝ)) + 2 * (μ : ℝ) ^ 4 + (μ : ℝ) + (d : ℝ) * u := by
        ring
      rw [hexp_eq]
      linarith
    have h16 : 16 * Big = (2 : ℝ) ^ (4 + (5 * E₀ + 8 + (d : ℝ)) * U34) := by
      dsimp only [Big]
      rw [Real.rpow_add (by norm_num)]; norm_num
    have hKl : K_large ≤ K := le_max_right _ _
    have hexp_K : 4 + (5 * E₀ + 8 + (d : ℝ)) * U34 ≤ K * U34 := by
      have hK_diff : 5 * E₀ + 12 + (d : ℝ) ≤ K := by
        dsimp only [K_large, C_base, E₀] at hKl ⊢; linarith
      have h1 : (5 * E₀ + 12 + (d : ℝ)) * U34 ≤ K * U34 :=
        mul_le_mul_of_nonneg_right hK_diff hU34_nn
      linarith
    have hexp_le : (2 * (μ : ℝ) ^ 4) * (u + (μ : ℝ) + 1) + (μ : ℝ) + (d : ℝ) * u ≤ (2 : ℝ) ^ (K * U34) := by
      rw [h16] at hM_big
      exact le_trans hM_big (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_K)
    unfold expTwo
    exact le_trans htotal (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le)

/-- In-text asymptotic identity & comparison. -/
theorem cov_asymptotic_between_proved (K : ℝ) (hK : 0 < K) :
    (∀ s : ℕ, 2 ≤ s →
      expTwo (expTwo (K * (Real.logb 2 s) ^ (3 / 4 : ℝ))) =
        (2 : ℝ) ^ ((s : ℝ) ^ (K / (Real.logb 2 s) ^ (1 / 4 : ℝ)))) ∧
    (∀ (d : ℕ) (ε : ℝ), 0 < ε → ∃ S₀ : ℕ, ∀ s ≥ S₀,
      (2 : ℝ) ^ ((Real.logb 2 s) ^ d) < expTwo (expTwo (K * (Real.logb 2 s) ^ (3 / 4 : ℝ))) ∧
      expTwo (expTwo (K * (Real.logb 2 s) ^ (3 / 4 : ℝ))) < (2 : ℝ) ^ ((s : ℝ) ^ ε)) := by
  constructor
  · intro s hs
    unfold expTwo
    set u := Real.logb 2 s
    have hlog_pos : (0 : ℝ) < u := lt_of_lt_of_le (by norm_num) (logb_two_ge_one hs)
    have hs_pos : (0 : ℝ) < (s : ℝ) := by positivity
    congr 1
    have hs_eq : (s : ℝ) ^ (K / u ^ (1 / 4 : ℝ)) = (2 : ℝ) ^ (u * (K / u ^ (1 / 4 : ℝ))) := by
      conv_lhs => rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hs_pos]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hs_eq]
    congr 1
    have hdiv : u / u ^ (1 / 4 : ℝ) = u ^ (3 / 4 : ℝ) := by
      rw [div_rpow_self hlog_pos]; norm_num
    calc
      K * u ^ (3 / 4 : ℝ) = K * (u / u ^ (1 / 4 : ℝ)) := by rw [hdiv]
      _ = u * (K / u ^ (1 / 4 : ℝ)) := by ring
  · intro d ε hε
    obtain ⟨U_hi, hU_hi1, hU_hi⟩ :=
      exists_rpow_lt_self (K / ε) (3 / 4) (div_pos hK hε) (by norm_num) (by norm_num)
    obtain ⟨U_lo, hU_lo1, hU_lo⟩ :=
      exists_rpow_lt_self ((8 * (d : ℝ) + 1) / K) (1 / 2) (by positivity) (by norm_num) (by norm_num)
    let U := max (max U_hi U_lo) 4
    let S₀ := max 4 (Nat.ceil ((2 : ℝ) ^ U) + 1)
    refine ⟨S₀, fun s hs => ?_⟩
    have hs2 : 2 ≤ s := le_trans (by decide) (le_trans (le_max_left _ _) hs)
    have hs_gt : (2 : ℝ) ^ U < (s : ℝ) := by
      have h1 : Nat.ceil ((2 : ℝ) ^ U) + 1 ≤ s := le_trans (le_max_right _ _) hs
      have h2 : (2 : ℝ) ^ U ≤ (Nat.ceil ((2 : ℝ) ^ U) : ℝ) := Nat.le_ceil _
      have h3 : (Nat.ceil ((2 : ℝ) ^ U) : ℝ) + 1 ≤ (s : ℝ) := by exact_mod_cast h1
      linarith
    set u := Real.logb 2 s
    have hu_gt_U : U < u := by
      have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (by positivity) hs_gt
      rwa [Real.logb_rpow (by norm_num) (by norm_num)] at hlog
    have hu_ge1 : (1 : ℝ) ≤ u := by
      have : (4 : ℝ) ≤ U := le_max_right _ _
      linarith
    have hu_pos : 0 < u := by linarith
    constructor
    · unfold expTwo
      apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
      have hlog_u_le : Real.logb 2 u ≤ 8 * u ^ (1 / 4 : ℝ) := by
        have hln2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
        have h1 : Real.log (u ^ (1 / 4 : ℝ)) ≤ u ^ (1 / 4 : ℝ) :=
          le_trans (Real.log_le_sub_one_of_pos (by positivity)) (by linarith)
        rw [Real.log_rpow hu_pos] at h1
        rw [Real.logb]
        have h2 : Real.log u ≤ 4 * u ^ (1 / 4 : ℝ) := by linarith
        rw [div_le_iff₀ (by linarith)]
        nlinarith [show 0 ≤ u ^ (1 / 4 : ℝ) by positivity]
      have hu_eq : u ^ d = (2 : ℝ) ^ ((d : ℝ) * Real.logb 2 u) := by
        conv_lhs => rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hu_pos]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
      rw [hu_eq]
      apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
      have hlo := hU_lo u (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hu_gt_U.le)
      have hlo2 := mul_lt_mul_of_pos_left hlo hK
      rw [← mul_assoc, mul_div_cancel₀ _ hK.ne'] at hlo2
      have hdiv_pow : (8 * (d : ℝ) + 1) * u ^ (1 / 4 : ℝ) < K * u ^ (3 / 4 : ℝ) := by
        have h1 := div_lt_div_of_pos_right hlo2 (Real.rpow_pos_of_pos hu_pos (1 / 4))
        rw [mul_div_assoc, mul_div_assoc] at h1
        have hp1 : u ^ (1 / 2 : ℝ) / u ^ (1 / 4 : ℝ) = u ^ (1 / 4 : ℝ) := by
          rw [← Real.rpow_sub hu_pos]; norm_num
        have hp2 : u / u ^ (1 / 4 : ℝ) = u ^ (3 / 4 : ℝ) := by
          rw [div_rpow_self hu_pos]; norm_num
        rwa [hp1, hp2] at h1
      have hd_log : (d : ℝ) * Real.logb 2 u ≤ (8 * (d : ℝ)) * u ^ (1 / 4 : ℝ) := by
        have := mul_le_mul_of_nonneg_left hlog_u_le (by positivity : (0 : ℝ) ≤ (d : ℝ))
        linarith
      have hpos14 : 0 < u ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hu_pos _
      linarith
    · unfold expTwo
      apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
      have hs_eq : (s : ℝ) ^ ε = (2 : ℝ) ^ (ε * u) := by
        conv_lhs => rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) (by positivity : (0 : ℝ) < s)]
        rw [← Real.rpow_mul (by norm_num), mul_comm]
      rw [hs_eq]
      apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
      have h1 := hU_hi u (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hu_gt_U.le)
      have h2 := mul_lt_mul_of_pos_left h1 hε
      rwa [← mul_assoc, mul_div_cancel₀ _ hε.ne'] at h2

/-- Table 1 naive grid evaluation size `(s + 1)^s ≤ 2^(2 * s * log₂ s)` for `s ≥ 2`. -/
theorem cov_grid_prior_pit_proved (s : ℕ) (hs : 2 ≤ s) :
    ((s + 1 : ℕ) ^ s : ℝ) ≤ (2 : ℝ) ^ (2 * (s : ℝ) * Real.logb 2 s) := by
  have hs1 : ((s + 1 : ℕ) : ℝ) ≤ (s : ℝ) ^ (2 : ℕ) := by
    push_cast; nlinarith [show (2 : ℝ) ≤ (s : ℝ) by exact_mod_cast hs]
  have h1 : (((s + 1 : ℕ) ^ s : ℕ) : ℝ) ≤ ((s : ℝ) ^ (2 : ℕ)) ^ s := by
    rw [Nat.cast_pow]; exact pow_le_pow_left₀ (by positivity) hs1 s
  have h2 : ((s : ℝ) ^ (2 : ℕ)) ^ s = (2 : ℝ) ^ (2 * (s : ℝ) * Real.logb 2 s) := by
    have hs_eq : (s : ℝ) = (2 : ℝ) ^ Real.logb 2 s :=
      (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
    conv_lhs => rw [hs_eq]
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    push_cast
    congr 1; ring
  rw [← h2]
  simpa [Nat.cast_pow] using h1

/-- Remark 1 logarithm inequality: `(ln μ)^2 / (ln ln μ)^2 > (log₂ μ)^2 / (log₂ log₂ μ)^2`
for all `μ ≥ 3`. -/
theorem step_rem1_ln_vs_log2_proved (μ : ℕ) (hμ : 3 ≤ μ) :
    (Real.logb 2 μ) ^ 2 / (Real.logb 2 (Real.logb 2 μ)) ^ 2 <
      (Real.log μ) ^ 2 / (Real.log (Real.log μ)) ^ 2 := by
  have hln2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hln2_lt1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hln_ln2_neg : Real.log (Real.log 2) < 0 := Real.log_neg hln2_pos hln2_lt1
  have hμ_gt_e : Real.exp 1 < (μ : ℝ) := by
    have h1 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    have h2 : (3 : ℝ) ≤ (μ : ℝ) := by exact_mod_cast hμ
    linarith
  have hlnμ_gt1 : 1 < Real.log μ := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) hμ_gt_e
  have hlnlnμ_pos : 0 < Real.log (Real.log μ) := Real.log_pos hlnμ_gt1
  have hlog2μ_gt1 : 1 < Real.logb 2 μ := by
    rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    exact Real.logb_lt_logb (by norm_num) (by norm_num) (by exact_mod_cast (by omega : 2 < μ))
  have hlog2log2_pos : 0 < Real.logb 2 (Real.logb 2 μ) :=
    Real.logb_pos (by norm_num) hlog2μ_gt1
  have hlnμ_eq : Real.log μ = Real.log 2 * Real.logb 2 μ := by
    rw [Real.logb, mul_div_cancel₀ _ hln2_pos.ne']
  have hdenom_lt : Real.log (Real.log μ) < Real.log 2 * Real.logb 2 (Real.logb 2 μ) := by
    rw [hlnμ_eq, Real.log_mul hln2_pos.ne' (by linarith)]
    have h2 : Real.log (Real.logb 2 μ) = Real.log 2 * Real.logb 2 (Real.logb 2 μ) := by
      have hdef : Real.logb 2 (Real.logb 2 μ) = Real.log (Real.logb 2 μ) / Real.log 2 := rfl
      rw [hdef, mul_div_cancel₀ _ hln2_pos.ne']
    linarith
  have hfrac_lt :
      Real.logb 2 μ / Real.logb 2 (Real.logb 2 μ) < Real.log μ / Real.log (Real.log μ) := by
    have h1 : Real.logb 2 μ / Real.logb 2 (Real.logb 2 μ) =
        (Real.log 2 * Real.logb 2 μ) / (Real.log 2 * Real.logb 2 (Real.logb 2 μ)) := by
      rw [mul_div_mul_left _ _ hln2_pos.ne']
    rw [h1, ← hlnμ_eq]
    exact div_lt_div_of_pos_left (by linarith) hlnlnμ_pos hdenom_lt
  have hpos_lhs : 0 < Real.logb 2 μ / Real.logb 2 (Real.logb 2 μ) :=
    div_pos (by linarith) hlog2log2_pos
  have hsq := sq_lt_sq' (by linarith) hfrac_lt
  simpa [div_pow] using hsq

end ExactMatching.Proofs
