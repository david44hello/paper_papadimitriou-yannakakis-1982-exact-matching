/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import ExactMatching.Defs.Circuits
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

/-!
# Proofs of multivariate grid nonvanishing and `RatCircuit` model transfer (Lemma 2.2)

Proves:
- `step_2_2_nonvanishing_proved`: multivariate polynomial nonvanishing on a grid `S^l`
  with `|S| > totalDegree f` over `ℚ`.
- `step_2_2_model_transfer_proved`: `RatCircuit` translates into `Computes` with at most
  `3 * C.size` gates, and functional equality on `ℚ^m` implies formal equality.
-/

namespace ExactMatching.Proofs

open scoped BigOperators

universe u

/-- Agreement between paper's permanent `paperPerm` and `[A26]`'s `perm`. -/
theorem paperPerm_eq_perm_proved (R : Type*) [CommSemiring R] (μ : ℕ) :
    paperPerm R μ = perm R μ := by
  unfold paperPerm perm
  rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin μ)))]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Equiv.prod_comp σ]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp

/-- Model inclusion: `Computes f s → O26ExactComputes f s`. -/
theorem step_rem1_computes_to_o26_proved {R : Type u} {V : Type} [CommRing R]
    (f : MvPolynomial V R) (s : ℕ) (h : Computes f s) :
    O26ExactComputes f s := by
  classical
  rcases h with ⟨l, hstep, k₀, hk₀, hlk₀⟩
  let isBin : ℕ → Bool := fun k =>
    decide (¬ ((∃ v : V, l k = MvPolynomial.X v) ∨ (∃ a : R, l k = MvPolynomial.C a)))
  refine ⟨s, l, isBin, ?_, ?_, k₀, hk₀, hlk₀⟩
  · intro k hk
    dsimp only [isBin]
    by_cases hbase : (∃ v : V, l k = MvPolynomial.X v) ∨ (∃ a : R, l k = MvPolynomial.C a)
    · simp only [hbase, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false]
    · simp only [hbase, not_false_eq_true, decide_true, ite_true]
      rcases hstep k hk with h1 | h2 | h3 | h4
      · exact absurd (Or.inl h1) hbase
      · exact absurd (Or.inr h2) hbase
      · exact Or.inl h3
      · exact Or.inr (Or.inr h4)
  · exact le_trans (Finset.card_filter_le _ _) (by simp)

/-- Multivariate polynomial nonvanishing on a grid `S^l` over `ℚ`. -/
theorem step_2_2_nonvanishing_proved :
    ∀ {l : ℕ} (f : MvPolynomial (Fin l) ℚ), f ≠ 0 →
      ∀ (S : Finset ℚ), f.totalDegree < S.card →
        ∃ a : Fin l → ℚ, (∀ i, a i ∈ S) ∧ MvPolynomial.eval a f ≠ 0
  | 0, f, hf, S, _ => by
    refine ⟨Fin.elim0, fun i => Fin.elim0 i, ?_⟩
    have heq : f = MvPolynomial.C (f.coeff 0) := by
      ext d
      have hd : d = 0 := Finsupp.ext (fun i => Fin.elim0 i)
      subst hd
      simp
    intro h0
    rw [heq, MvPolynomial.eval_C] at h0
    exact hf (by rw [heq, h0, map_zero])
  | l + 1, f, hf, S, hS => by
    let P : Polynomial (MvPolynomial (Fin l) ℚ) := MvPolynomial.finSuccEquiv ℚ l f
    have hP_ne : P ≠ 0 := by
      intro h0
      exact hf ((MvPolynomial.finSuccEquiv ℚ l).injective (by simpa [P] using h0))
    have hlead_ne : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP_ne
    have hdeg_add : P.leadingCoeff.totalDegree + P.natDegree ≤ f.totalDegree :=
      MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le f P.natDegree hlead_ne
    have hlead_deg : P.leadingCoeff.totalDegree < S.card := lt_of_le_of_lt (by omega) hS
    obtain ⟨a', ha'S, ha'_ne⟩ := step_2_2_nonvanishing_proved P.leadingCoeff hlead_ne S hlead_deg
    let Q : Polynomial ℚ := P.map (MvPolynomial.eval a')
    have hQ_coeff : Q.coeff P.natDegree ≠ 0 := by
      rw [Polynomial.coeff_map]
      exact ha'_ne
    have hQ_ne : Q ≠ 0 := fun h0 => hQ_coeff (by rw [h0, Polynomial.coeff_zero])
    have hQ_deg : Q.natDegree ≤ P.natDegree := Polynomial.natDegree_map_le
    have hroots_lt : Q.roots.toFinset.card < S.card := by
      calc
        Q.roots.toFinset.card ≤ Q.roots.card := Multiset.toFinset_card_le _
        _ ≤ Q.natDegree := Polynomial.card_roots' Q
        _ ≤ P.natDegree := hQ_deg
        _ ≤ f.totalDegree := by omega
        _ < S.card := hS
    have hnot_sub : ¬ S ⊆ Q.roots.toFinset := fun hsub =>
      not_lt.mpr (Finset.card_le_card hsub) hroots_lt
    obtain ⟨a₀, ha₀S, ha₀_not_root⟩ := Finset.not_subset.mp hnot_sub
    have hQa₀ : Q.eval a₀ ≠ 0 := by
      intro h0
      exact ha₀_not_root (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hQ_ne).mpr h0))
    refine ⟨Fin.cons a₀ a', fun i => Fin.cases ha₀S ha'S i, ?_⟩
    rw [MvPolynomial.eval_eq_eval_mv_eval']
    exact hQa₀

private theorem evalGatePoly_var {m : ℕ} (C : RatCircuit m) (k : Fin C.size) (v : Fin m)
    (h : C.gate k = .var v) : C.evalGatePoly k = MvPolynomial.X v := by
  conv_lhs => unfold RatCircuit.evalGatePoly; rw [WellFounded.fix_eq]
  split <;> simp_all

private theorem evalGatePoly_const {m : ℕ} (C : RatCircuit m) (k : Fin C.size) (a : ℚ)
    (h : C.gate k = .const a) : C.evalGatePoly k = MvPolynomial.C a := by
  conv_lhs => unfold RatCircuit.evalGatePoly; rw [WellFounded.fix_eq]
  split <;> simp_all

private theorem evalGatePoly_add {m : ℕ} (C : RatCircuit m) (k : Fin C.size) (i j : ℕ)
    (h : C.gate k = .add i j) (hi : i < C.size) (hj : j < C.size) :
    C.evalGatePoly k = C.evalGatePoly ⟨i, hi⟩ + C.evalGatePoly ⟨j, hj⟩ := by
  conv_lhs => unfold RatCircuit.evalGatePoly; rw [WellFounded.fix_eq]
  split <;> simp_all
  rcases h with ⟨rfl, rfl⟩; rfl

private theorem evalGatePoly_sub {m : ℕ} (C : RatCircuit m) (k : Fin C.size) (i j : ℕ)
    (h : C.gate k = .sub i j) (hi : i < C.size) (hj : j < C.size) :
    C.evalGatePoly k = C.evalGatePoly ⟨i, hi⟩ - C.evalGatePoly ⟨j, hj⟩ := by
  conv_lhs => unfold RatCircuit.evalGatePoly; rw [WellFounded.fix_eq]
  split <;> simp_all
  rcases h with ⟨rfl, rfl⟩; rfl

private theorem evalGatePoly_mul {m : ℕ} (C : RatCircuit m) (k : Fin C.size) (i j : ℕ)
    (h : C.gate k = .mul i j) (hi : i < C.size) (hj : j < C.size) :
    C.evalGatePoly k = C.evalGatePoly ⟨i, hi⟩ * C.evalGatePoly ⟨j, hj⟩ := by
  conv_lhs => unfold RatCircuit.evalGatePoly; rw [WellFounded.fix_eq]
  split <;> simp_all
  rcases h with ⟨rfl, rfl⟩; rfl

private theorem evalGatePoly_smul {m : ℕ} (C : RatCircuit m) (k : Fin C.size) (a : ℚ) (i : ℕ)
    (h : C.gate k = .smul a i) (hi : i < C.size) :
    C.evalGatePoly k = MvPolynomial.C a * C.evalGatePoly ⟨i, hi⟩ := by
  conv_lhs => unfold RatCircuit.evalGatePoly; rw [WellFounded.fix_eq]
  split <;> simp_all
  rcases h with ⟨rfl, rfl⟩; exact Or.inl rfl

/-- Non-dependent 3-slot expansion of each gate `k` of `C : RatCircuit m`. -/
private noncomputable def ratSlotVal {m : ℕ} (C : RatCircuit m) (k : Fin C.size) (r : ℕ) :
    MvPolynomial (Fin m) ℚ :=
  match C.gate k with
  | .var v => MvPolynomial.X v
  | .const a => MvPolynomial.C a
  | .add _ _ => C.evalGatePoly k
  | .mul _ _ => C.evalGatePoly k
  | .sub _ j =>
    if r = 0 then MvPolynomial.C (-1 : ℚ)
    else if r = 1 then
      if hj : j < C.size then MvPolynomial.C (-1 : ℚ) * C.evalGatePoly ⟨j, hj⟩ else 0
    else C.evalGatePoly k
  | .smul a _ => if r = 2 then C.evalGatePoly k else MvPolynomial.C a

private theorem ratSlotVal_two {m : ℕ} (C : RatCircuit m) (k : Fin C.size) :
    ratSlotVal C k 2 = C.evalGatePoly k := by
  unfold ratSlotVal
  cases h : C.gate k with
  | var v => exact (evalGatePoly_var C k v h).symm
  | const a => exact (evalGatePoly_const C k a h).symm
  | add i j => rfl
  | mul i j => rfl
  | sub i j => simp
  | smul a i => simp

/-- Circuit-model transfer (`RatCircuit` → `Computes` with `≤ 3 * C.size` gates, and
functional equality on `ℚ^m` implies formal equality). -/
theorem step_2_2_model_transfer_proved {m : ℕ} (C : RatCircuit m) :
    Computes C.evalPoly (3 * C.size) ∧
    ∀ q : MvPolynomial (Fin m) ℚ,
      (∀ x : Fin m → ℚ, MvPolynomial.eval x C.evalPoly = MvPolynomial.eval x q) →
      C.evalPoly = q := by
  constructor
  · let l : ℕ → MvPolynomial (Fin m) ℚ := fun t =>
      if ht : t / 3 < C.size then ratSlotVal C ⟨t / 3, ht⟩ (t % 3) else 0
    have hl_eq : ∀ (k : Fin C.size) (r : ℕ), r < 3 →
        l (3 * k.val + r) = ratSlotVal C k r := by
      intro k r hr
      have hd : (3 * k.val + r) / 3 = k.val := by omega
      have hm : (3 * k.val + r) % 3 = r := by omega
      simp only [l, hd, k.isLt, dite_true, hm]
    have hl_slot2 : ∀ k : Fin C.size, l (3 * k.val + 2) = C.evalGatePoly k := by
      intro k
      rw [hl_eq k 2 (by omega), ratSlotVal_two]
    refine ⟨l, ?_, ⟨3 * C.out.val + 2, by omega, hl_slot2 C.out⟩⟩
    intro t ht
    have hdiv_lt : t / 3 < C.size := by omega
    let k : Fin C.size := ⟨t / 3, hdiv_lt⟩
    have hkval : k.val = t / 3 := rfl
    have hlt_l : l t = ratSlotVal C k (t % 3) := by simp only [l, hdiv_lt, dite_true]; rfl
    rw [hlt_l]
    unfold ratSlotVal
    cases h : C.gate k with
    | var v => exact Or.inl ⟨v, rfl⟩
    | const a => exact Or.inr (Or.inl ⟨a, rfl⟩)
    | add i j =>
      have hwf := C.wf k; rw [h] at hwf
      have hi : i < k.val := hwf.1
      have hj : j < k.val := hwf.2
      refine Or.inr (Or.inr (Or.inl ⟨3 * i + 2, by omega, 3 * j + 2, by omega, ?_⟩))
      rw [hl_slot2 ⟨i, Nat.lt_trans hi k.isLt⟩, hl_slot2 ⟨j, Nat.lt_trans hj k.isLt⟩]
      exact evalGatePoly_add C k i j h _ _
    | mul i j =>
      have hwf := C.wf k; rw [h] at hwf
      have hi : i < k.val := hwf.1
      have hj : j < k.val := hwf.2
      refine Or.inr (Or.inr (Or.inr ⟨3 * i + 2, by omega, 3 * j + 2, by omega, ?_⟩))
      rw [hl_slot2 ⟨i, Nat.lt_trans hi k.isLt⟩, hl_slot2 ⟨j, Nat.lt_trans hj k.isLt⟩]
      exact evalGatePoly_mul C k i j h _ _
    | sub i j =>
      have hwf := C.wf k; rw [h] at hwf
      have hi : i < k.val := hwf.1
      have hj : j < k.val := hwf.2
      have hjs : j < C.size := Nat.lt_trans hj k.isLt
      by_cases hm0 : t % 3 = 0
      · simp only [hm0, ite_true]
        exact Or.inr (Or.inl ⟨-1, rfl⟩)
      · by_cases hm1 : t % 3 = 1
        · simp only [hm1, Nat.one_ne_zero, ite_false, ite_true, hjs, dite_true]
          have hslot0 : l (3 * k.val + 0) = MvPolynomial.C (-1 : ℚ) := by
            rw [hl_eq k 0 (by omega)]; simp [ratSlotVal, h]
          refine Or.inr (Or.inr (Or.inr ⟨3 * k.val + 0, by omega, 3 * j + 2, by omega, ?_⟩))
          rw [hslot0, hl_slot2 ⟨j, hjs⟩]
        · simp only [hm0, hm1, ite_false]
          have hslot1 : l (3 * k.val + 1) = MvPolynomial.C (-1 : ℚ) * C.evalGatePoly ⟨j, hjs⟩ := by
            rw [hl_eq k 1 (by omega)]; simp [ratSlotVal, h, hjs]
          refine Or.inr (Or.inr (Or.inl ⟨3 * i + 2, by omega, 3 * k.val + 1, by omega, ?_⟩))
          rw [hl_slot2 ⟨i, Nat.lt_trans hi k.isLt⟩, hslot1, evalGatePoly_sub C k i j h _ hjs]
          rw [map_neg, map_one, neg_one_mul, sub_eq_add_neg]
    | smul a i =>
      have hwf := C.wf k; rw [h] at hwf
      have hi : i < k.val := hwf
      by_cases hm2 : t % 3 = 2
      · simp only [hm2, ite_true]
        have hslot0 : l (3 * k.val + 0) = MvPolynomial.C a := by
          rw [hl_eq k 0 (by omega)]; simp [ratSlotVal, h]
        refine Or.inr (Or.inr (Or.inr ⟨3 * k.val + 0, by omega, 3 * i + 2, by omega, ?_⟩))
        rw [hslot0, hl_slot2 ⟨i, Nat.lt_trans hi k.isLt⟩]
        exact evalGatePoly_smul C k a i h _
      · simp only [hm2, ite_false]
        exact Or.inr (Or.inl ⟨a, rfl⟩)
  · intro q hfun
    by_contra hne
    have hsub : C.evalPoly - q ≠ 0 := sub_ne_zero.mpr hne
    let S : Finset ℚ := (Finset.range ((C.evalPoly - q).totalDegree + 1)).image (fun k : ℕ => (k : ℚ))
    have hScard : (C.evalPoly - q).totalDegree < S.card := by
      have hinj : Function.Injective (fun k : ℕ => (k : ℚ)) := Nat.cast_injective
      rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
      exact Nat.lt_succ_self _
    obtain ⟨a, _, ha⟩ := step_2_2_nonvanishing_proved (C.evalPoly - q) hsub S hScard
    apply ha
    simp [map_sub, hfun a]

end ExactMatching.Proofs
