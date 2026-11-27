/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import ExactMatching.Defs.Circuits
import ExactMatching.Defs.CitedHypotheses
import ExactMatching.Proofs.CircuitsTransfer
import ExactMatching.Proofs.StrassenHomog
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Unconditional Proof of `KI04_Cor_7_4` via Coupled Division-Free Newton Iteration

Proves `KI04_Cor_7_4` (non-constructive existence of a polynomial-size division-free `RatCircuit`
computing any polynomial root `p ∈ ℤ[x_1, ..., x_m]` of a nonzero polynomial `g = C_g.evalPoly`
of total degree `≤ d`) from Lean's three standard axioms alone, parameterized by Strassen's
homogenization theorem (`StrassenHomog.lean`):

1. `RatCircuit` combinators: `ofIntCircuit`, `shiftVars`, `linComb`, `newtonCircuit`.
2. Polynomial algebra: degree bound `p.totalDegree ≤ d`, simple-root reduction via maximal
   vanishing Hasse derivative `H = hasseDeriv r G`, and Vandermonde-interpolated `y`-derivative
   circuits for `H` and `H'`.
3. Coupled division-free quadratic Newton iteration modulo `(z_1, ..., z_m)^{2^k}` producing a
   circuit `C_Y` of size `O(d^2 * s)` with `ZeroMod (d + 1) (C_Y.evalPoly - p̃)`.
4. Assembly with Strassen homogenization (`O(d^4 * s)`) and variable unshifting (`3×`) to yield
   `KI04_Cor_7_4`.
-/

namespace ExactMatching.Proofs.KI04Newton

open MvPolynomial
open scoped BigOperators

/-! ### 1. `RatCircuit` evaluation helpers and combinators -/

private lemma evalGatePoly_var {n : ℕ} (C : RatCircuit n) (idx : Fin C.size) (v : Fin n)
    (h : C.gate idx = .var v) : C.evalGatePoly idx = MvPolynomial.X v := by
  unfold RatCircuit.evalGatePoly
  rw [WellFounded.fix_eq]
  split
  all_goals (rename_i heq; rw [h] at heq; cases heq; try rfl)

private lemma evalGatePoly_const {n : ℕ} (C : RatCircuit n) (idx : Fin C.size) (a : ℚ)
    (h : C.gate idx = .const a) : C.evalGatePoly idx = MvPolynomial.C a := by
  unfold RatCircuit.evalGatePoly
  rw [WellFounded.fix_eq]
  split
  all_goals (rename_i heq; rw [h] at heq; cases heq; try rfl)

private lemma evalGatePoly_add {n : ℕ} (C : RatCircuit n) (idx : Fin C.size) (i j : ℕ)
    (h : C.gate idx = .add i j) (hi : i < C.size) (hj : j < C.size) :
    C.evalGatePoly idx = C.evalGatePoly ⟨i, hi⟩ + C.evalGatePoly ⟨j, hj⟩ := by
  unfold RatCircuit.evalGatePoly
  rw [WellFounded.fix_eq]
  split
  all_goals (rename_i heq; rw [h] at heq; cases heq; try rfl)

private lemma evalGatePoly_sub {n : ℕ} (C : RatCircuit n) (idx : Fin C.size) (i j : ℕ)
    (h : C.gate idx = .sub i j) (hi : i < C.size) (hj : j < C.size) :
    C.evalGatePoly idx = C.evalGatePoly ⟨i, hi⟩ - C.evalGatePoly ⟨j, hj⟩ := by
  unfold RatCircuit.evalGatePoly
  rw [WellFounded.fix_eq]
  split
  all_goals (rename_i heq; rw [h] at heq; cases heq; try rfl)

private lemma evalGatePoly_mul {n : ℕ} (C : RatCircuit n) (idx : Fin C.size) (i j : ℕ)
    (h : C.gate idx = .mul i j) (hi : i < C.size) (hj : j < C.size) :
    C.evalGatePoly idx = C.evalGatePoly ⟨i, hi⟩ * C.evalGatePoly ⟨j, hj⟩ := by
  unfold RatCircuit.evalGatePoly
  rw [WellFounded.fix_eq]
  split
  all_goals (rename_i heq; rw [h] at heq; cases heq; try rfl)

private lemma evalGatePoly_smul {n : ℕ} (C : RatCircuit n) (idx : Fin C.size) (a : ℚ) (i : ℕ)
    (h : C.gate idx = .smul a i) (hi : i < C.size) :
    C.evalGatePoly idx = MvPolynomial.C a * C.evalGatePoly ⟨i, hi⟩ := by
  unfold RatCircuit.evalGatePoly
  rw [WellFounded.fix_eq]
  split
  all_goals (rename_i heq; rw [h] at heq; cases heq; try rfl)

private lemma intEvalGateAt_var {n : ℕ} (C : IntCircuit n) (idx : Fin C.size) (v : Fin n)
    (h : C.gate idx = .var v) :
    C.evalGateAt (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℤ) idx = MvPolynomial.X v := by
  unfold IntCircuit.evalGateAt; rw [WellFounded.fix_eq]
  split; all_goals (rename_i heq; rw [h] at heq; cases heq; try rfl)

private lemma intEvalGateAt_const {n : ℕ} (C : IntCircuit n) (idx : Fin C.size) (a : ℤ)
    (h : C.gate idx = .const a) :
    C.evalGateAt (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℤ) idx = (a : MvPolynomial (Fin n) ℤ) := by
  unfold IntCircuit.evalGateAt; rw [WellFounded.fix_eq]
  split; all_goals (rename_i heq; rw [h] at heq; cases heq; try rfl)

private lemma intEvalGateAt_add {n : ℕ} (C : IntCircuit n) (idx : Fin C.size) (i j : ℕ)
    (h : C.gate idx = .add i j) (hi : i < C.size) (hj : j < C.size) :
    C.evalGateAt (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℤ) idx =
      C.evalGateAt MvPolynomial.X ⟨i, hi⟩ + C.evalGateAt MvPolynomial.X ⟨j, hj⟩ := by
  unfold IntCircuit.evalGateAt; rw [WellFounded.fix_eq]
  split; all_goals (rename_i heq; rw [h] at heq; cases heq; try rfl)

private lemma intEvalGateAt_sub {n : ℕ} (C : IntCircuit n) (idx : Fin C.size) (i j : ℕ)
    (h : C.gate idx = .sub i j) (hi : i < C.size) (hj : j < C.size) :
    C.evalGateAt (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℤ) idx =
      C.evalGateAt MvPolynomial.X ⟨i, hi⟩ - C.evalGateAt MvPolynomial.X ⟨j, hj⟩ := by
  unfold IntCircuit.evalGateAt; rw [WellFounded.fix_eq]
  split; all_goals (rename_i heq; rw [h] at heq; cases heq; try rfl)

private lemma intEvalGateAt_mul {n : ℕ} (C : IntCircuit n) (idx : Fin C.size) (i j : ℕ)
    (h : C.gate idx = .mul i j) (hi : i < C.size) (hj : j < C.size) :
    C.evalGateAt (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℤ) idx =
      C.evalGateAt MvPolynomial.X ⟨i, hi⟩ * C.evalGateAt MvPolynomial.X ⟨j, hj⟩ := by
  unfold IntCircuit.evalGateAt; rw [WellFounded.fix_eq]
  split; all_goals (rename_i heq; rw [h] at heq; cases heq; try rfl)

/-- Every gate in an `IntCircuit` has encoding bit-cost at least `1`, so `C.size ≤ C.encodingLength`. -/
lemma intCircuit_size_le_encodingLength {n : ℕ} (C : IntCircuit n) :
    C.size ≤ C.encodingLength := by
  unfold IntCircuit.encodingLength
  have h1 : ∀ k : Fin C.size, 1 ≤ (C.gate k).bitCost := by
    intro k
    cases C.gate k <;> simp [IntGate.bitCost, intBitLen]
  calc
    C.size = ∑ _k : Fin C.size, 1 := by simp
    _ ≤ ∑ k : Fin C.size, (C.gate k).bitCost := Finset.sum_le_sum (fun k _ => h1 k)

/-- Direct lift of an `IntCircuit n` to a `RatCircuit n` of the same size. -/
def ratCircuitOfIntCircuit {n : ℕ} (C : IntCircuit n) : RatCircuit n where
  size := C.size
  size_pos := C.size_pos
  gate k := match C.gate k with
    | .var v => .var v
    | .const a => .const (a : ℚ)
    | .add i j => .add i j
    | .sub i j => .sub i j
    | .mul i j => .mul i j
  wf k := by
    have hwf := C.wf k
    cases hg : C.gate k <;> simp [hg, IntGate.WF, RatGate.WF] at hwf ⊢ <;> exact hwf
  out := C.out

lemma ratCircuitOfIntCircuit_evalGatePoly {n : ℕ} (C : IntCircuit n) :
    ∀ k : Fin C.size,
      (ratCircuitOfIntCircuit C).evalGatePoly k =
        MvPolynomial.map (Int.castRingHom ℚ) (C.evalGateAt MvPolynomial.X k) := by
  intro k
  induction k using WellFounded.induction (InvImage.wf Fin.val Nat.lt_wfRel.wf) with
  | h k ih =>
    have hwf := C.wf k
    cases hg : C.gate k with
    | var v =>
      have hg' : (ratCircuitOfIntCircuit C).gate k = .var v := by dsimp [ratCircuitOfIntCircuit]; rw [hg]
      rw [evalGatePoly_var (ratCircuitOfIntCircuit C) k v hg',
          intEvalGateAt_var _ _ _ hg, MvPolynomial.map_X]
    | const a =>
      have hg' : (ratCircuitOfIntCircuit C).gate k = .const (a : ℚ) := by dsimp [ratCircuitOfIntCircuit]; rw [hg]
      rw [evalGatePoly_const (ratCircuitOfIntCircuit C) k (a : ℚ) hg',
          intEvalGateAt_const _ _ _ hg]
      simp [Int.castRingHom]
    | add i j =>
      rw [hg] at hwf
      have hg' : (ratCircuitOfIntCircuit C).gate k = .add i j := by dsimp [ratCircuitOfIntCircuit]; rw [hg]
      rw [evalGatePoly_add (ratCircuitOfIntCircuit C) k i j hg' (lt_trans hwf.1 k.isLt) (lt_trans hwf.2 k.isLt),
          intEvalGateAt_add _ _ _ _ hg (lt_trans hwf.1 k.isLt) (lt_trans hwf.2 k.isLt), map_add]
      exact congrArg₂ (· + ·) (ih ⟨i, lt_trans hwf.1 k.isLt⟩ hwf.1) (ih ⟨j, lt_trans hwf.2 k.isLt⟩ hwf.2)
    | sub i j =>
      rw [hg] at hwf
      have hg' : (ratCircuitOfIntCircuit C).gate k = .sub i j := by dsimp [ratCircuitOfIntCircuit]; rw [hg]
      rw [evalGatePoly_sub (ratCircuitOfIntCircuit C) k i j hg' (lt_trans hwf.1 k.isLt) (lt_trans hwf.2 k.isLt),
          intEvalGateAt_sub _ _ _ _ hg (lt_trans hwf.1 k.isLt) (lt_trans hwf.2 k.isLt), map_sub]
      exact congrArg₂ (· - ·) (ih ⟨i, lt_trans hwf.1 k.isLt⟩ hwf.1) (ih ⟨j, lt_trans hwf.2 k.isLt⟩ hwf.2)
    | mul i j =>
      rw [hg] at hwf
      have hg' : (ratCircuitOfIntCircuit C).gate k = .mul i j := by dsimp [ratCircuitOfIntCircuit]; rw [hg]
      rw [evalGatePoly_mul (ratCircuitOfIntCircuit C) k i j hg' (lt_trans hwf.1 k.isLt) (lt_trans hwf.2 k.isLt),
          intEvalGateAt_mul _ _ _ _ hg (lt_trans hwf.1 k.isLt) (lt_trans hwf.2 k.isLt), map_mul]
      exact congrArg₂ (· * ·) (ih ⟨i, lt_trans hwf.1 k.isLt⟩ hwf.1) (ih ⟨j, lt_trans hwf.2 k.isLt⟩ hwf.2)

lemma ratCircuitOfIntCircuit_evalPoly {n : ℕ} (C : IntCircuit n) :
    (ratCircuitOfIntCircuit C).evalPoly = MvPolynomial.map (Int.castRingHom ℚ) C.evalPoly :=
  ratCircuitOfIntCircuit_evalGatePoly C C.out

/-- Affine variable shift `x_v ↦ x_v + a v` on a `RatCircuit n`, expanding each gate into a
3-slot block (`size = 3 * C.size`, completely independent of `n`). -/
def shiftVarsCircuit {n : ℕ} (C : RatCircuit n) (a : Fin n → ℚ) : RatCircuit n where
  size := 3 * C.size
  size_pos := by have := C.size_pos; omega
  gate idx :=
    let k := idx.val / 3
    let r := idx.val % 3
    if hk : k < C.size then
      match C.gate ⟨k, hk⟩ with
      | .var v =>
        if r = 0 then .var v
        else if r = 1 then .const (a v)
        else .add (3 * k) (3 * k + 1)
      | .const c => if r = 2 then .const c else .const 0
      | .add i j => if r = 2 then .add (3 * i + 2) (3 * j + 2) else .const 0
      | .sub i j => if r = 2 then .sub (3 * i + 2) (3 * j + 2) else .const 0
      | .mul i j => if r = 2 then .mul (3 * i + 2) (3 * j + 2) else .const 0
      | .smul c i => if r = 2 then .smul c (3 * i + 2) else .const 0
    else .const 0
  wf idx := by
    have hk : idx.val / 3 < C.size := by have := idx.isLt; omega
    dsimp only
    rw [dif_pos hk]
    have hwf := C.wf ⟨idx.val / 3, hk⟩
    cases hg : C.gate ⟨idx.val / 3, hk⟩ with
    | var v =>
      dsimp only
      split_ifs with h0 h1
      · trivial
      · trivial
      · unfold RatGate.WF; omega
    | const c =>
      dsimp only; split_ifs <;> trivial
    | add i j =>
      rw [hg] at hwf; dsimp only; split_ifs with h2
      · unfold RatGate.WF; dsimp [RatGate.WF] at hwf; omega
      · trivial
    | sub i j =>
      rw [hg] at hwf; dsimp only; split_ifs with h2
      · unfold RatGate.WF; dsimp [RatGate.WF] at hwf; omega
      · trivial
    | mul i j =>
      rw [hg] at hwf; dsimp only; split_ifs with h2
      · unfold RatGate.WF; dsimp [RatGate.WF] at hwf; omega
      · trivial
    | smul c i =>
      rw [hg] at hwf; dsimp only; split_ifs with h2
      · unfold RatGate.WF; dsimp [RatGate.WF] at hwf; omega
      · trivial
  out := ⟨3 * C.out.val + 2, by have := C.out.isLt; omega⟩

lemma shiftVarsCircuit_evalGatePoly {n : ℕ} (C : RatCircuit n) (a : Fin n → ℚ) :
    ∀ k : Fin C.size,
      (shiftVarsCircuit C a).evalGatePoly ⟨3 * k.val + 2, by dsimp [shiftVarsCircuit]; omega⟩ =
        MvPolynomial.bind₁ (fun v => MvPolynomial.X v + MvPolynomial.C (a v)) (C.evalGatePoly k) := by
  intro k
  induction k using WellFounded.induction (InvImage.wf Fin.val Nat.lt_wfRel.wf) with
  | h k ih =>
    have hwf := C.wf k
    have hdiv2 : (3 * k.val + 2) / 3 = k.val := by omega
    have hmod2 : (3 * k.val + 2) % 3 = 2 := by omega
    have hdiv1 : (3 * k.val + 1) / 3 = k.val := by omega
    have hmod1 : (3 * k.val + 1) % 3 = 1 := by omega
    have hdiv0 : (3 * k.val) / 3 = k.val := by omega
    have hmod0 : (3 * k.val) % 3 = 0 := by omega
    cases hg : C.gate k with
    | var v =>
      have hg0 : (shiftVarsCircuit C a).gate ⟨3 * k.val, by dsimp [shiftVarsCircuit]; omega⟩ = .var v := by
        dsimp [shiftVarsCircuit]; simp [hdiv0, hmod0, k.isLt, hg]
      have hg1 : (shiftVarsCircuit C a).gate ⟨3 * k.val + 1, by dsimp [shiftVarsCircuit]; omega⟩ = .const (a v) := by
        dsimp [shiftVarsCircuit]; simp [hdiv1, hmod1, k.isLt, hg]
      have hg2 : (shiftVarsCircuit C a).gate ⟨3 * k.val + 2, by dsimp [shiftVarsCircuit]; omega⟩ =
          .add (3 * k.val) (3 * k.val + 1) := by
        dsimp [shiftVarsCircuit]; simp [hdiv2, hmod2, k.isLt, hg]
      rw [evalGatePoly_add _ _ _ _ hg2 (by dsimp [shiftVarsCircuit]; omega) (by dsimp [shiftVarsCircuit]; omega),
          evalGatePoly_var _ _ _ hg0, evalGatePoly_const _ _ _ hg1,
          evalGatePoly_var _ _ _ hg, MvPolynomial.bind₁_X_right]
    | const c =>
      have hg2 : (shiftVarsCircuit C a).gate ⟨3 * k.val + 2, by dsimp [shiftVarsCircuit]; omega⟩ = .const c := by
        dsimp [shiftVarsCircuit]; simp [hdiv2, hmod2, k.isLt, hg]
      rw [evalGatePoly_const _ _ _ hg2, evalGatePoly_const _ _ _ hg, MvPolynomial.bind₁_C_right]
    | add i j =>
      rw [hg] at hwf; dsimp [RatGate.WF] at hwf
      have hg2 : (shiftVarsCircuit C a).gate ⟨3 * k.val + 2, by dsimp [shiftVarsCircuit]; omega⟩ =
          .add (3 * i + 2) (3 * j + 2) := by
        dsimp [shiftVarsCircuit]; simp [hdiv2, hmod2, k.isLt, hg]
      rw [evalGatePoly_add _ _ _ _ hg2 (by dsimp [shiftVarsCircuit]; omega) (by dsimp [shiftVarsCircuit]; omega),
          evalGatePoly_add _ _ _ _ hg (lt_trans hwf.1 k.isLt) (lt_trans hwf.2 k.isLt),
          map_add, ih ⟨i, lt_trans hwf.1 k.isLt⟩ hwf.1, ih ⟨j, lt_trans hwf.2 k.isLt⟩ hwf.2]
    | sub i j =>
      rw [hg] at hwf; dsimp [RatGate.WF] at hwf
      have hg2 : (shiftVarsCircuit C a).gate ⟨3 * k.val + 2, by dsimp [shiftVarsCircuit]; omega⟩ =
          .sub (3 * i + 2) (3 * j + 2) := by
        dsimp [shiftVarsCircuit]; simp [hdiv2, hmod2, k.isLt, hg]
      rw [evalGatePoly_sub _ _ _ _ hg2 (by dsimp [shiftVarsCircuit]; omega) (by dsimp [shiftVarsCircuit]; omega),
          evalGatePoly_sub _ _ _ _ hg (lt_trans hwf.1 k.isLt) (lt_trans hwf.2 k.isLt),
          map_sub, ih ⟨i, lt_trans hwf.1 k.isLt⟩ hwf.1, ih ⟨j, lt_trans hwf.2 k.isLt⟩ hwf.2]
    | mul i j =>
      rw [hg] at hwf; dsimp [RatGate.WF] at hwf
      have hg2 : (shiftVarsCircuit C a).gate ⟨3 * k.val + 2, by dsimp [shiftVarsCircuit]; omega⟩ =
          .mul (3 * i + 2) (3 * j + 2) := by
        dsimp [shiftVarsCircuit]; simp [hdiv2, hmod2, k.isLt, hg]
      rw [evalGatePoly_mul _ _ _ _ hg2 (by dsimp [shiftVarsCircuit]; omega) (by dsimp [shiftVarsCircuit]; omega),
          evalGatePoly_mul _ _ _ _ hg (lt_trans hwf.1 k.isLt) (lt_trans hwf.2 k.isLt),
          map_mul, ih ⟨i, lt_trans hwf.1 k.isLt⟩ hwf.1, ih ⟨j, lt_trans hwf.2 k.isLt⟩ hwf.2]
    | smul c i =>
      rw [hg] at hwf; dsimp [RatGate.WF] at hwf
      have hg2 : (shiftVarsCircuit C a).gate ⟨3 * k.val + 2, by dsimp [shiftVarsCircuit]; omega⟩ =
          .smul c (3 * i + 2) := by
        dsimp [shiftVarsCircuit]; simp [hdiv2, hmod2, k.isLt, hg]
      rw [evalGatePoly_smul _ _ _ _ hg2 (by dsimp [shiftVarsCircuit]; omega),
          evalGatePoly_smul _ _ _ _ hg (lt_trans hwf k.isLt),
          map_mul, MvPolynomial.bind₁_C_right, ih ⟨i, lt_trans hwf k.isLt⟩ hwf]

lemma shiftVarsCircuit_evalPoly {n : ℕ} (C : RatCircuit n) (a : Fin n → ℚ) :
    (shiftVarsCircuit C a).evalPoly =
      MvPolynomial.bind₁ (fun v => MvPolynomial.X v + MvPolynomial.C (a v)) C.evalPoly :=
  shiftVarsCircuit_evalGatePoly C a C.out

/-- Shift a `RatGate`'s internal wire indices by `offset`. -/
private def shiftGate {n : ℕ} (offset : ℕ) : RatGate n → RatGate n
  | .var v => .var v
  | .const a => .const a
  | .add i j => .add (offset + i) (offset + j)
  | .sub i j => .sub (offset + i) (offset + j)
  | .mul i j => .mul (offset + i) (offset + j)
  | .smul a i => .smul a (offset + i)

private lemma shiftGate_wf {n : ℕ} (offset k : ℕ) (g : RatGate n) (hg : g.WF k) :
    (shiftGate offset g).WF (offset + k) := by
  cases g <;> simp [shiftGate, RatGate.WF] at hg ⊢ <;> omega

/-- Linear combination `∑ i : Fin N, C (coeff i) * (circ i).evalPoly` of `N ≥ 1` circuits of
size at most `B`, with total size `N * (B + 2)`. -/
def linCombCircuit {n : ℕ} (N : ℕ) (hN : 1 ≤ N) (B : ℕ) (hB : 1 ≤ B)
    (coeff : Fin N → ℚ) (circ : Fin N → RatCircuit n)
    (hsize : ∀ i, (circ i).size ≤ B) : RatCircuit n where
  size := N * B + N + N
  size_pos := by nlinarith
  gate idx :=
    if h1 : idx.val < N * B then
      let b := idx.val / B
      let k := idx.val % B
      if hb : b < N then
        if hk : k < (circ ⟨b, hb⟩).size then
          shiftGate (b * B) ((circ ⟨b, hb⟩).gate ⟨k, hk⟩)
        else .const 0
      else .const 0
    else if h2 : idx.val < N * B + N then
      let i := idx.val - N * B
      if hi : i < N then .smul (coeff ⟨i, hi⟩) (i * B + (circ ⟨i, hi⟩).out.val)
      else .const 0
    else
      let i := idx.val - (N * B + N)
      if i = 0 then .smul 1 (N * B)
      else .add (N * B + N + (i - 1)) (N * B + i)
  wf idx := by
    dsimp only
    split_ifs with h1 hb hk h2 hi h0
    · have hwf := (circ ⟨idx.val / B, hb⟩).wf ⟨idx.val % B, hk⟩
      have hdiv := shiftGate_wf (idx.val / B * B) (idx.val % B) _ hwf
      have heq : idx.val / B * B + idx.val % B = idx.val := by
        rw [mul_comm]; exact Nat.div_add_mod idx.val B
      rwa [heq] at hdiv
    · trivial
    · trivial
    · unfold RatGate.WF
      have hlt : (circ ⟨idx.val - N * B, hi⟩).out.val < B :=
        lt_of_lt_of_le (circ ⟨idx.val - N * B, hi⟩).out.isLt (hsize ⟨idx.val - N * B, hi⟩)
      have hmul : (idx.val - N * B) * B + B ≤ N * B := by
        have : (idx.val - N * B) + 1 ≤ N := hi
        nlinarith
      omega
    · trivial
    · unfold RatGate.WF; omega
    · unfold RatGate.WF
      have hlt : idx.val < N * B + N + N := idx.isLt
      omega
  out := ⟨N * B + N + (N - 1), by omega⟩

lemma linCombCircuit_evalPoly {n : ℕ} (N : ℕ) (hN : 1 ≤ N) (B : ℕ) (hB : 1 ≤ B)
    (coeff : Fin N → ℚ) (circ : Fin N → RatCircuit n)
    (hsize : ∀ i, (circ i).size ≤ B) :
    (linCombCircuit N hN B hB coeff circ hsize).evalPoly =
      ∑ i : Fin N, MvPolynomial.C (coeff i) * (circ i).evalPoly := by
  let L := linCombCircuit N hN B hB coeff circ hsize
  have hcopy : ∀ (i : Fin N) (k : Fin (circ i).size),
      L.evalGatePoly ⟨i.val * B + k.val, by
        dsimp [L, linCombCircuit]
        have hkB : k.val < B := lt_of_lt_of_le k.isLt (hsize i)
        have : (i.val + 1) * B ≤ N * B := Nat.mul_le_mul_right B i.isLt
        nlinarith⟩ = (circ i).evalGatePoly k := by
    intro i k
    induction k using WellFounded.induction (InvImage.wf Fin.val Nat.lt_wfRel.wf) with
    | h k ih =>
      have hkB : k.val < B := lt_of_lt_of_le k.isLt (hsize i)
      have hltNB : i.val * B + k.val < N * B := by
        have : (i.val + 1) * B ≤ N * B := Nat.mul_le_mul_right B i.isLt
        nlinarith
      have hdiv : (i.val * B + k.val) / B = i.val := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hkB, zero_add]
      have hmod : (i.val * B + k.val) % B = k.val := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hkB]
      have hgate : L.gate ⟨i.val * B + k.val, by dsimp [L, linCombCircuit]; omega⟩ =
          shiftGate (i.val * B) ((circ i).gate k) := by
        dsimp only [L, linCombCircuit]
        rw [dif_pos hltNB]
        have hb : (i.val * B + k.val) / B < N := by rw [hdiv]; exact i.isLt
        rw [dif_pos hb]
        have hi_eq : (⟨(i.val * B + k.val) / B, hb⟩ : Fin N) = i := Fin.ext hdiv
        have hk' : (i.val * B + k.val) % B < (circ ⟨(i.val * B + k.val) / B, hb⟩).size := by
          rw [hi_eq, hmod]; exact k.isLt
        rw [dif_pos hk']
        refine congrArg₂ shiftGate (by rw [hdiv]) ?_
        generalize hj : (⟨(i.val * B + k.val) / B, hb⟩ : Fin N) = j at hi_eq hk' ⊢
        subst hi_eq
        exact congrArg (circ j).gate (Fin.ext hmod)
      have hwf := (circ i).wf k
      cases hg : (circ i).gate k with
      | var v =>
        rw [hg] at hgate
        rw [evalGatePoly_var _ _ _ hgate, evalGatePoly_var _ _ _ hg]
      | const a =>
        rw [hg] at hgate
        rw [evalGatePoly_const _ _ _ hgate, evalGatePoly_const _ _ _ hg]
      | add p q =>
        rw [hg] at hgate hwf
        have hp : p < (circ i).size := lt_trans hwf.1 k.isLt
        have hq : q < (circ i).size := lt_trans hwf.2 k.isLt
        have hpB : i.val * B + p < L.size := by
          dsimp [L, linCombCircuit]; have := lt_of_lt_of_le hp (hsize i); nlinarith [i.isLt]
        have hqB : i.val * B + q < L.size := by
          dsimp [L, linCombCircuit]; have := lt_of_lt_of_le hq (hsize i); nlinarith [i.isLt]
        rw [evalGatePoly_add _ _ _ _ hgate hpB hqB, evalGatePoly_add _ _ _ _ hg hp hq,
            ih ⟨p, hp⟩ hwf.1, ih ⟨q, hq⟩ hwf.2]
      | sub p q =>
        rw [hg] at hgate hwf
        have hp : p < (circ i).size := lt_trans hwf.1 k.isLt
        have hq : q < (circ i).size := lt_trans hwf.2 k.isLt
        have hpB : i.val * B + p < L.size := by
          dsimp [L, linCombCircuit]; have := lt_of_lt_of_le hp (hsize i); nlinarith [i.isLt]
        have hqB : i.val * B + q < L.size := by
          dsimp [L, linCombCircuit]; have := lt_of_lt_of_le hq (hsize i); nlinarith [i.isLt]
        rw [evalGatePoly_sub _ _ _ _ hgate hpB hqB, evalGatePoly_sub _ _ _ _ hg hp hq,
            ih ⟨p, hp⟩ hwf.1, ih ⟨q, hq⟩ hwf.2]
      | mul p q =>
        rw [hg] at hgate hwf
        have hp : p < (circ i).size := lt_trans hwf.1 k.isLt
        have hq : q < (circ i).size := lt_trans hwf.2 k.isLt
        have hpB : i.val * B + p < L.size := by
          dsimp [L, linCombCircuit]; have := lt_of_lt_of_le hp (hsize i); nlinarith [i.isLt]
        have hqB : i.val * B + q < L.size := by
          dsimp [L, linCombCircuit]; have := lt_of_lt_of_le hq (hsize i); nlinarith [i.isLt]
        rw [evalGatePoly_mul _ _ _ _ hgate hpB hqB, evalGatePoly_mul _ _ _ _ hg hp hq,
            ih ⟨p, hp⟩ hwf.1, ih ⟨q, hq⟩ hwf.2]
      | smul a p =>
        rw [hg] at hgate hwf
        have hp : p < (circ i).size := lt_trans hwf k.isLt
        have hpB : i.val * B + p < L.size := by
          dsimp [L, linCombCircuit]; have := lt_of_lt_of_le hp (hsize i); nlinarith [i.isLt]
        rw [evalGatePoly_smul _ _ _ _ hgate hpB, evalGatePoly_smul _ _ _ _ hg hp,
            ih ⟨p, hp⟩ hwf]
  have hscaled : ∀ (i : Fin N),
      L.evalGatePoly ⟨N * B + i.val, by dsimp [L, linCombCircuit]; omega⟩ =
        MvPolynomial.C (coeff i) * (circ i).evalPoly := by
    intro i
    have hgate : L.gate ⟨N * B + i.val, by dsimp [L, linCombCircuit]; omega⟩ =
        .smul (coeff i) (i.val * B + (circ i).out.val) := by
      dsimp only [L, linCombCircuit]
      have h1 : ¬ (N * B + i.val < N * B) := by omega
      have h2 : N * B + i.val < N * B + N := by omega
      have hsub : N * B + i.val - N * B = i.val := by omega
      rw [dif_neg h1, dif_pos h2]
      have hi : N * B + i.val - N * B < N := by rw [hsub]; exact i.isLt
      rw [dif_pos hi]
      have hi_eq : (⟨N * B + i.val - N * B, hi⟩ : Fin N) = i := Fin.ext hsub
      rw [hi_eq, hsub]
    have hltOut : i.val * B + (circ i).out.val < L.size := by
      dsimp [L, linCombCircuit]
      have := lt_of_lt_of_le (circ i).out.isLt (hsize i)
      nlinarith [i.isLt]
    rw [evalGatePoly_smul _ _ _ _ hgate hltOut]
    exact congrArg (MvPolynomial.C (coeff i) * ·) (hcopy i (circ i).out)
  have hacc : ∀ (r : ℕ) (hr : r < N),
      L.evalGatePoly ⟨N * B + N + r, by dsimp [L, linCombCircuit]; omega⟩ =
        ∑ i ∈ Finset.range (r + 1),
          if hi : i < N then MvPolynomial.C (coeff ⟨i, hi⟩) * (circ ⟨i, hi⟩).evalPoly else 0 := by
    intro r
    induction r with
    | zero =>
      intro hr
      have hgate : L.gate ⟨N * B + N + 0, by dsimp [L, linCombCircuit]; omega⟩ = .smul 1 (N * B) := by
        dsimp [L, linCombCircuit]
        have h1 : ¬ (N * B + N + 0 < N * B) := by omega
        have h2 : ¬ (N * B + N + 0 < N * B + N) := by omega
        simp [h1, h2]
      rw [evalGatePoly_smul _ _ _ _ hgate (by dsimp [L, linCombCircuit]; omega)]
      have h0 := hscaled ⟨0, hr⟩
      simp only [add_zero] at h0
      rw [h0, map_one, one_mul]
      simp [hr]
    | succ r ihr =>
      intro hr
      have hgate : L.gate ⟨N * B + N + (r + 1), by dsimp [L, linCombCircuit]; omega⟩ =
          .add (N * B + N + r) (N * B + (r + 1)) := by
        dsimp [L, linCombCircuit]
        have h1 : ¬ (N * B + N + (r + 1) < N * B) := by omega
        have h2 : ¬ (N * B + N + (r + 1) < N * B + N) := by omega
        have hsub : N * B + N + (r + 1) - (N * B + N) = r + 1 := by omega
        simp [h1, h2, hsub]
      rw [evalGatePoly_add _ _ _ _ hgate (by dsimp [L, linCombCircuit]; omega) (by dsimp [L, linCombCircuit]; omega),
          ihr (by omega), hscaled ⟨r + 1, hr⟩, Finset.sum_range_succ _ (r + 1), dif_pos hr]
  have hfinal := hacc (N - 1) (by omega)
  rw [Nat.sub_add_cancel hN] at hfinal
  change L.evalGatePoly ⟨N * B + N + (N - 1), _⟩ = _
  rw [hfinal, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => by simp [i.isLt]

/-- Convert a gate in `RatGate (m + 1)` into a gate in `RatGate m` shifted by `offset`, replacing
`.var (Fin.last m)` by a 1-gate reference `.smul 1 ySlot`. -/
private def substLastGate {m : ℕ} (offset ySlot : ℕ) : RatGate (m + 1) → RatGate m
  | .var v =>
      if hv : v.val < m then .var ⟨v.val, hv⟩
      else .smul 1 ySlot
  | .const a => .const a
  | .add i j => .add (offset + i) (offset + j)
  | .sub i j => .sub (offset + i) (offset + j)
  | .mul i j => .mul (offset + i) (offset + j)
  | .smul a i => .smul a (offset + i)

private lemma substLastGate_wf {m : ℕ} (offset ySlot k : ℕ) (hy : ySlot < offset)
    (g : RatGate (m + 1)) (hg : g.WF k) :
    (substLastGate offset ySlot g).WF (offset + k) := by
  cases g with
  | var v =>
    dsimp [substLastGate]
    split_ifs
    · trivial
    · unfold RatGate.WF; omega
  | const a => trivial
  | add i j => dsimp [substLastGate, RatGate.WF] at hg ⊢; omega
  | sub i j => dsimp [substLastGate, RatGate.WF] at hg ⊢; omega
  | mul i j => dsimp [substLastGate, RatGate.WF] at hg ⊢; omega
  | smul a i => dsimp [substLastGate, RatGate.WF] at hg ⊢; omega

/-- Coupled quadratic Newton iteration polynomials `(y_k, u_k)` for `H, H' : MvPolynomial (Fin (m + 1)) ℚ`. -/
noncomputable def newtonStep {m : ℕ} (H H' : MvPolynomial (Fin (m + 1)) ℚ) :
    MvPolynomial (Fin m) ℚ × MvPolynomial (Fin m) ℚ →
    MvPolynomial (Fin m) ℚ × MvPolynomial (Fin m) ℚ :=
  fun ⟨y, u⟩ =>
    let y' := y - u * MvPolynomial.bind₁ (Fin.lastCases y MvPolynomial.X) H
    let u' := u * (MvPolynomial.C 2 - u * MvPolynomial.bind₁ (Fin.lastCases y' MvPolynomial.X) H')
    (y', u')

noncomputable def newtonIter {m : ℕ} (H H' : MvPolynomial (Fin (m + 1)) ℚ) (y0 u0 : ℚ) :
    ℕ → MvPolynomial (Fin m) ℚ × MvPolynomial (Fin m) ℚ
  | 0 => (MvPolynomial.C y0, MvPolynomial.C u0)
  | k + 1 => newtonStep H H' (newtonIter H H' y0 u0 k)

private def newtonBlockSize (S : ℕ) : ℕ := 2 * S + 5
private def newtonBase (S k : ℕ) : ℕ := 3 + k * newtonBlockSize S
private def newtonYSlot (S : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => newtonBase S k + S + 1
private def newtonUSlot (S : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => newtonBase S k + 2 * S + 4

private lemma newtonYSlot_lt_base (S k : ℕ) : newtonYSlot S k < newtonBase S k := by
  cases k <;> unfold newtonYSlot newtonBase newtonBlockSize <;> nlinarith

private lemma newtonUSlot_lt_base (S k : ℕ) : newtonUSlot S k < newtonBase S k := by
  cases k <;> unfold newtonUSlot newtonBase newtonBlockSize <;> nlinarith

private def newtonGateFn {m : ℕ} (C_h C_hy : RatCircuit (m + 1)) (y0 u0 : ℚ) (S : ℕ) (idx : ℕ) :
    RatGate m :=
  if idx = 0 then .const y0
  else if idx = 1 then .const u0
  else if idx = 2 then .const 2
  else
    let k := (idx - 3) / newtonBlockSize S
    let off := (idx - 3) % newtonBlockSize S
    let base := newtonBase S k
    if hoff1 : off < S then
      if hch : off < C_h.size then
        substLastGate base (newtonYSlot S k) (C_h.gate ⟨off, hch⟩)
      else .const 0
    else if off = S then
      .mul (newtonUSlot S k) (base + C_h.out.val)
    else if off = S + 1 then
      .sub (newtonYSlot S k) (base + S)
    else if hoff2 : off < 2 * S + 2 then
      let r := off - (S + 2)
      if hchy : r < C_hy.size then
        substLastGate (base + S + 2) (newtonYSlot S (k + 1)) (C_hy.gate ⟨r, hchy⟩)
      else .const 0
    else if off = 2 * S + 2 then
      .mul (newtonUSlot S k) (base + S + 2 + C_hy.out.val)
    else if off = 2 * S + 3 then
      .sub 2 (base + 2 * S + 2)
    else
      .mul (newtonUSlot S k) (base + 2 * S + 3)

/-- Explicit fixed-slot `RatCircuit m` computing the `K`-th coupled Newton iterate `y_K`
of size `3 + K * (2 * max C_h.size C_hy.size + 5)`. -/
def newtonCircuit {m : ℕ} (C_h C_hy : RatCircuit (m + 1)) (y0 u0 : ℚ) (K : ℕ) : RatCircuit m :=
  let S := max C_h.size C_hy.size
  let M := newtonBlockSize S
  { size := 3 + K * M
    size_pos := by omega
    gate := fun idx => newtonGateFn C_h C_hy y0 u0 S idx.val
    wf := fun idx => by
      dsimp only [newtonGateFn]
      have hMpos : 0 < newtonBlockSize S := by unfold newtonBlockSize; omega
      have hbase_all : ∀ (_ : 3 ≤ idx.val),
          newtonBase S ((idx.val - 3) / newtonBlockSize S) + (idx.val - 3) % newtonBlockSize S = idx.val := by
        intro h3
        unfold newtonBase
        have hdm := Nat.div_add_mod (idx.val - 3) (newtonBlockSize S)
        have hmul : (idx.val - 3) / newtonBlockSize S * newtonBlockSize S =
            newtonBlockSize S * ((idx.val - 3) / newtonBlockSize S) := mul_comm _ _
        omega
      split_ifs with h0 h1 h2 hoff1 hch hS hS1 hoff2 hchy h2S2 h2S3
      · trivial
      · trivial
      · trivial
      · have hbase_eq := hbase_all (by omega)
        have hwf := substLastGate_wf (newtonBase S ((idx.val - 3) / newtonBlockSize S))
          (newtonYSlot S ((idx.val - 3) / newtonBlockSize S)) ((idx.val - 3) % newtonBlockSize S)
          (newtonYSlot_lt_base S _) (C_h.gate ⟨_, hch⟩) (C_h.wf ⟨_, hch⟩)
        rwa [hbase_eq] at hwf
      · trivial
      · unfold RatGate.WF
        have hu := newtonUSlot_lt_base S ((idx.val - 3) / newtonBlockSize S)
        have hout : C_h.out.val < S := lt_of_lt_of_le C_h.out.isLt (le_max_left _ _)
        have hbase_eq := hbase_all (by omega)
        omega
      · unfold RatGate.WF
        have hy := newtonYSlot_lt_base S ((idx.val - 3) / newtonBlockSize S)
        have hbase_eq := hbase_all (by omega)
        omega
      · have hbase_eq0 := hbase_all (by omega)
        have hbase_eq : newtonBase S ((idx.val - 3) / newtonBlockSize S) + S + 2 +
            ((idx.val - 3) % newtonBlockSize S - (S + 2)) = idx.val := by omega
        have hy1 : newtonYSlot S ((idx.val - 3) / newtonBlockSize S + 1) <
            newtonBase S ((idx.val - 3) / newtonBlockSize S) + S + 2 := by
          dsimp only [newtonYSlot]; omega
        have hwf := substLastGate_wf (newtonBase S ((idx.val - 3) / newtonBlockSize S) + S + 2)
          (newtonYSlot S ((idx.val - 3) / newtonBlockSize S + 1)) ((idx.val - 3) % newtonBlockSize S - (S + 2))
          hy1 (C_hy.gate ⟨_, hchy⟩) (C_hy.wf ⟨_, hchy⟩)
        rwa [hbase_eq] at hwf
      · trivial
      · unfold RatGate.WF
        have hu := newtonUSlot_lt_base S ((idx.val - 3) / newtonBlockSize S)
        have hout : C_hy.out.val < S := lt_of_lt_of_le C_hy.out.isLt (le_max_right _ _)
        have hbase_eq := hbase_all (by omega)
        omega
      · unfold RatGate.WF
        have hbase_eq := hbase_all (by omega)
        omega
      · unfold RatGate.WF
        have hu := newtonUSlot_lt_base S ((idx.val - 3) / newtonBlockSize S)
        have hbase_eq := hbase_all (by omega)
        have hmod_lt : (idx.val - 3) % newtonBlockSize S < newtonBlockSize S := Nat.mod_lt _ hMpos
        have hmod_eq : (idx.val - 3) % newtonBlockSize S = 2 * S + 4 := by
          unfold newtonBlockSize at hmod_lt hoff2 h2S2 h2S3 ⊢; omega
        omega
    out := ⟨newtonYSlot S K, by
      have h1 := newtonYSlot_lt_base S K
      unfold newtonBase at h1; dsimp [M]; omega⟩ }

private lemma newtonCircuit_gate_eq {m : ℕ} (C_h C_hy : RatCircuit (m + 1)) (y0 u0 : ℚ) (K i : ℕ)
    (hi : i < (newtonCircuit C_h C_hy y0 u0 K).size) {S : ℕ} (hS : S = max C_h.size C_hy.size) :
    (newtonCircuit C_h C_hy y0 u0 K).gate ⟨i, hi⟩ = newtonGateFn C_h C_hy y0 u0 S i := by
  subst hS; rfl

private lemma evalGatePoly_substLast_block {m : ℕ} (C : RatCircuit m) (D : RatCircuit (m + 1))
    (base ySlot : ℕ) (hbound : base + D.size ≤ C.size) (hy : ySlot < C.size)
    (hblock : ∀ (k : Fin D.size),
      C.gate ⟨base + k.val, lt_of_lt_of_le (Nat.add_lt_add_left k.isLt base) hbound⟩ =
        substLastGate base ySlot (D.gate k)) :
    ∀ k : Fin D.size,
      C.evalGatePoly ⟨base + k.val, lt_of_lt_of_le (Nat.add_lt_add_left k.isLt base) hbound⟩ =
        MvPolynomial.bind₁ (Fin.lastCases (C.evalGatePoly ⟨ySlot, hy⟩) MvPolynomial.X) (D.evalGatePoly k) := by
  intro k
  induction k using WellFounded.induction (InvImage.wf Fin.val Nat.lt_wfRel.wf) with
  | h k ih =>
    have hwf := D.wf k
    have hgk := hblock k
    cases hg : D.gate k with
    | var v =>
      rw [hg] at hgk
      rw [evalGatePoly_var _ _ _ hg, MvPolynomial.bind₁_X_right]
      by_cases hv : v.val < m
      · have hgv : C.gate ⟨base + k.val, lt_of_lt_of_le (Nat.add_lt_add_left k.isLt base) hbound⟩ = .var ⟨v.val, hv⟩ := by
          rw [hgk]; simp [substLastGate, hv]
        rw [evalGatePoly_var _ _ _ hgv]
        have hlc : Fin.lastCases (C.evalGatePoly ⟨ySlot, hy⟩) MvPolynomial.X v = MvPolynomial.X ⟨v.val, hv⟩ := by
          cases v using Fin.lastCases with
          | last => simp at hv
          | cast i => simp
        rw [hlc]
      · have hgv : C.gate ⟨base + k.val, lt_of_lt_of_le (Nat.add_lt_add_left k.isLt base) hbound⟩ = .smul 1 ySlot := by
          rw [hgk]; simp [substLastGate, hv]
        rw [evalGatePoly_smul _ _ _ _ hgv hy, map_one, one_mul]
        have hv_eq : v = Fin.last m := by ext; dsimp [Fin.last]; omega
        rw [hv_eq, Fin.lastCases_last]
    | const a =>
      rw [hg] at hgk
      rw [evalGatePoly_const _ _ _ hgk, evalGatePoly_const _ _ _ hg, MvPolynomial.bind₁_C_right]
    | add i j =>
      rw [hg] at hgk hwf
      have hi : i < D.size := lt_trans hwf.1 k.isLt
      have hj : j < D.size := lt_trans hwf.2 k.isLt
      rw [evalGatePoly_add _ _ _ _ hgk (lt_of_lt_of_le (Nat.add_lt_add_left hi base) hbound)
            (lt_of_lt_of_le (Nat.add_lt_add_left hj base) hbound),
          evalGatePoly_add _ _ _ _ hg hi hj, map_add, ih ⟨i, hi⟩ hwf.1, ih ⟨j, hj⟩ hwf.2]
    | sub i j =>
      rw [hg] at hgk hwf
      have hi : i < D.size := lt_trans hwf.1 k.isLt
      have hj : j < D.size := lt_trans hwf.2 k.isLt
      rw [evalGatePoly_sub _ _ _ _ hgk (lt_of_lt_of_le (Nat.add_lt_add_left hi base) hbound)
            (lt_of_lt_of_le (Nat.add_lt_add_left hj base) hbound),
          evalGatePoly_sub _ _ _ _ hg hi hj, map_sub, ih ⟨i, hi⟩ hwf.1, ih ⟨j, hj⟩ hwf.2]
    | mul i j =>
      rw [hg] at hgk hwf
      have hi : i < D.size := lt_trans hwf.1 k.isLt
      have hj : j < D.size := lt_trans hwf.2 k.isLt
      rw [evalGatePoly_mul _ _ _ _ hgk (lt_of_lt_of_le (Nat.add_lt_add_left hi base) hbound)
            (lt_of_lt_of_le (Nat.add_lt_add_left hj base) hbound),
          evalGatePoly_mul _ _ _ _ hg hi hj, map_mul, ih ⟨i, hi⟩ hwf.1, ih ⟨j, hj⟩ hwf.2]
    | smul a i =>
      rw [hg] at hgk hwf
      have hi : i < D.size := lt_trans hwf k.isLt
      rw [evalGatePoly_smul _ _ _ _ hgk (lt_of_lt_of_le (Nat.add_lt_add_left hi base) hbound),
          evalGatePoly_smul _ _ _ _ hg hi, map_mul, MvPolynomial.bind₁_C_right, ih ⟨i, hi⟩ hwf]

lemma newtonCircuit_evalPoly {m : ℕ} (C_h C_hy : RatCircuit (m + 1)) (y0 u0 : ℚ) (K : ℕ) :
    (newtonCircuit C_h C_hy y0 u0 K).evalPoly =
      (newtonIter C_h.evalPoly C_hy.evalPoly y0 u0 K).1 := by
  set S := max C_h.size C_hy.size
  set M := newtonBlockSize S
  set N := newtonCircuit C_h C_hy y0 u0 K
  have hMpos : 0 < M := by dsimp [M, newtonBlockSize]; omega
  have h2 : N.evalGatePoly ⟨2, by dsimp [N, newtonCircuit]; omega⟩ = MvPolynomial.C 2 :=
    evalGatePoly_const N _ 2 (by dsimp [N, newtonCircuit, newtonGateFn])
  have hiter : ∀ k (hk : k ≤ K),
      N.evalGatePoly ⟨newtonYSlot S k, by
        have h1 := newtonYSlot_lt_base S k
        unfold newtonBase at h1; dsimp [N, newtonCircuit, M]; nlinarith⟩ =
        (newtonIter C_h.evalPoly C_hy.evalPoly y0 u0 k).1 ∧
      N.evalGatePoly ⟨newtonUSlot S k, by
        have h1 := newtonUSlot_lt_base S k
        unfold newtonBase at h1; dsimp [N, newtonCircuit, M]; nlinarith⟩ =
        (newtonIter C_h.evalPoly C_hy.evalPoly y0 u0 k).2 := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨evalGatePoly_const N _ y0 (by dsimp [N, newtonCircuit, newtonGateFn, newtonYSlot]),
              evalGatePoly_const N _ u0 (by dsimp [N, newtonCircuit, newtonGateFn, newtonUSlot])⟩
    | succ k ih =>
      intro hk
      rcases ih (by omega) with ⟨hyk, huk⟩
      have hbase_le : newtonBase S k + M ≤ N.size := by
        dsimp [N, newtonCircuit, newtonBase, M]; nlinarith
      have hbase_le' : newtonBase S k + (2 * S + 5) ≤ N.size := by
        simpa [M, newtonBlockSize] using hbase_le
      have hdiv_off : ∀ off < newtonBlockSize S,
          (newtonBase S k + off - 3) / newtonBlockSize S = k ∧
          (newtonBase S k + off - 3) % newtonBlockSize S = off := by
        intro off hoff
        have hsub : newtonBase S k + off - 3 = k * newtonBlockSize S + off := by
          unfold newtonBase; omega
        rw [hsub]
        exact ⟨by rw [Nat.add_comm, Nat.add_mul_div_right _ _ hMpos, Nat.div_eq_of_lt hoff, zero_add],
               by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hoff]⟩
      have hge3 : ∀ off, 3 ≤ newtonBase S k + off := by intro off; unfold newtonBase; omega
      have hH_bound : newtonBase S k + C_h.size ≤ N.size := by
        have : C_h.size ≤ S := le_max_left _ _; omega
      have hHy_bound : newtonBase S k + S + 2 + C_hy.size ≤ N.size := by
        have : C_hy.size ≤ S := le_max_right _ _; omega
      have hyk_lt : newtonYSlot S k < N.size := by
        have := newtonYSlot_lt_base S k; omega
      have huk_lt : newtonUSlot S k < N.size := by
        have := newtonUSlot_lt_base S k; omega
      have hH_eval := evalGatePoly_substLast_block N C_h (newtonBase S k) (newtonYSlot S k)
        hH_bound hyk_lt (fun j => by
          have hjS : j.val < S := lt_of_lt_of_le j.isLt (le_max_left _ _)
          have hjM : j.val < M := by dsimp [M, newtonBlockSize]; omega
          rcases hdiv_off j.val hjM with ⟨hd, hm⟩
          have h3 := hge3 j.val
          rw [newtonCircuit_gate_eq (S := S) (hS := rfl)]; dsimp only [newtonGateFn]
          have hn0 : newtonBase S k + j.val ≠ 0 := by omega
          have hn1 : newtonBase S k + j.val ≠ 1 := by omega
          have hn2 : newtonBase S k + j.val ≠ 2 := by omega
          simp only [hn0, hn1, hn2, ↓reduceIte, hd, hm, hjS, j.isLt, ↓reduceDIte, Fin.eta]) C_h.out
      rw [hyk] at hH_eval
      have hg_mul1 : N.gate ⟨newtonBase S k + S, by omega⟩ =
          .mul (newtonUSlot S k) (newtonBase S k + C_h.out.val) := by
        rcases hdiv_off S (by dsimp [M, newtonBlockSize]; omega) with ⟨hd, hm⟩
        have h3 := hge3 S
        rw [newtonCircuit_gate_eq (S := S) (hS := rfl)]; dsimp only [newtonGateFn]
        have hn0 : newtonBase S k + S ≠ 0 := by omega
        have hn1 : newtonBase S k + S ≠ 1 := by omega
        have hn2 : newtonBase S k + S ≠ 2 := by omega
        have hnotS : ¬ (S < S) := by omega
        simp only [hn0, hn1, hn2, hnotS, ↓reduceIte, ↓reduceDIte, hd, hm]
      have hmul1_eval : N.evalGatePoly ⟨newtonBase S k + S, by omega⟩ =
          (newtonIter C_h.evalPoly C_hy.evalPoly y0 u0 k).2 *
            MvPolynomial.bind₁ (Fin.lastCases (newtonIter C_h.evalPoly C_hy.evalPoly y0 u0 k).1 MvPolynomial.X) C_h.evalPoly := by
        rw [evalGatePoly_mul N _ _ _ hg_mul1 huk_lt (lt_of_lt_of_le (Nat.add_lt_add_left C_h.out.isLt _) hH_bound),
            huk, hH_eval]
        rfl
      have hy1_lt : newtonYSlot S (k + 1) < N.size := by
        dsimp only [newtonYSlot]; omega
      have hg_y1 : N.gate ⟨newtonYSlot S (k + 1), hy1_lt⟩ =
          .sub (newtonYSlot S k) (newtonBase S k + S) := by
        rcases hdiv_off (S + 1) (by unfold newtonBlockSize; omega) with ⟨hd, hm⟩
        have h3 := hge3 (S + 1)
        have heq_y : newtonYSlot S (k + 1) = newtonBase S k + (S + 1) := by dsimp only [newtonYSlot]; omega
        rw [newtonCircuit_gate_eq (S := S) (hS := rfl), heq_y]; dsimp only [newtonGateFn]
        have hn0 : newtonBase S k + (S + 1) ≠ 0 := by omega
        have hn1 : newtonBase S k + (S + 1) ≠ 1 := by omega
        have hn2 : newtonBase S k + (S + 1) ≠ 2 := by omega
        have hnotS : ¬ (S + 1 < S) := by omega
        have hneS : S + 1 ≠ S := by omega
        simp only [hn0, hn1, hn2, hnotS, hneS, ↓reduceIte, ↓reduceDIte, hd, hm]
      have hy1_eval : N.evalGatePoly ⟨newtonYSlot S (k + 1), hy1_lt⟩ =
          (newtonIter C_h.evalPoly C_hy.evalPoly y0 u0 (k + 1)).1 := by
        rw [evalGatePoly_sub N _ _ _ hg_y1 hyk_lt (by omega),
            hyk, hmul1_eval]
        rfl
      have hHy_eval := evalGatePoly_substLast_block N C_hy (newtonBase S k + S + 2) (newtonYSlot S (k + 1))
        hHy_bound hy1_lt (fun j => by
          have hjS : j.val < S := lt_of_lt_of_le j.isLt (le_max_right _ _)
          have hoff_eq : newtonBase S k + S + 2 + j.val = newtonBase S k + (S + 2 + j.val) := by omega
          have hjM : S + 2 + j.val < M := by dsimp [M, newtonBlockSize]; omega
          rcases hdiv_off (S + 2 + j.val) hjM with ⟨hd, hm⟩
          have h3 := hge3 (S + 2 + j.val)
          rw [newtonCircuit_gate_eq (S := S) (hS := rfl), hoff_eq]; dsimp only [newtonGateFn]
          have hn0 : newtonBase S k + (S + 2 + j.val) ≠ 0 := by omega
          have hn1 : newtonBase S k + (S + 2 + j.val) ≠ 1 := by omega
          have hn2 : newtonBase S k + (S + 2 + j.val) ≠ 2 := by omega
          have hnot1 : ¬ (S + 2 + j.val < S) := by omega
          have hneS : S + 2 + j.val ≠ S := by omega
          have hneS1 : S + 2 + j.val ≠ S + 1 := by omega
          have hlt2 : S + 2 + j.val < 2 * S + 2 := by omega
          have hsub : S + 2 + j.val - (S + 2) = j.val := by omega
          simp only [hn0, hn1, hn2, hnot1, hneS, hneS1, hlt2, ↓reduceIte, ↓reduceDIte, hd, hm, hsub, j.isLt, Fin.eta]) C_hy.out
      rw [hy1_eval] at hHy_eval
      have hg_mul2 : N.gate ⟨newtonBase S k + 2 * S + 2, by omega⟩ =
          .mul (newtonUSlot S k) (newtonBase S k + S + 2 + C_hy.out.val) := by
        rcases hdiv_off (2 * S + 2) (by dsimp [M, newtonBlockSize]; omega) with ⟨hd, hm⟩
        have h3 := hge3 (2 * S + 2)
        have heq_m2 : newtonBase S k + 2 * S + 2 = newtonBase S k + (2 * S + 2) := by omega
        rw [newtonCircuit_gate_eq (S := S) (hS := rfl), heq_m2]; dsimp only [newtonGateFn]
        have hn0 : newtonBase S k + (2 * S + 2) ≠ 0 := by omega
        have hn1 : newtonBase S k + (2 * S + 2) ≠ 1 := by omega
        have hn2 : newtonBase S k + (2 * S + 2) ≠ 2 := by omega
        have hnot1 : ¬ (2 * S + 2 < S) := by omega
        have hneS : 2 * S + 2 ≠ S := by omega
        have hneS1 : 2 * S + 2 ≠ S + 1 := by omega
        have hnot2 : ¬ (2 * S + 2 < 2 * S + 2) := by omega
        simp only [hn0, hn1, hn2, hnot1, hneS, hneS1, hnot2, ↓reduceIte, ↓reduceDIte, hd, hm]
      have hmul2_eval : N.evalGatePoly ⟨newtonBase S k + 2 * S + 2, by omega⟩ =
          (newtonIter C_h.evalPoly C_hy.evalPoly y0 u0 k).2 *
            MvPolynomial.bind₁ (Fin.lastCases (newtonIter C_h.evalPoly C_hy.evalPoly y0 u0 (k + 1)).1 MvPolynomial.X) C_hy.evalPoly := by
        rw [evalGatePoly_mul N _ _ _ hg_mul2 huk_lt (lt_of_lt_of_le (Nat.add_lt_add_left C_hy.out.isLt _) hHy_bound),
            huk, hHy_eval]
        rfl
      have hg_sub2 : N.gate ⟨newtonBase S k + 2 * S + 3, by omega⟩ =
          .sub 2 (newtonBase S k + 2 * S + 2) := by
        rcases hdiv_off (2 * S + 3) (by dsimp [M, newtonBlockSize]; omega) with ⟨hd, hm⟩
        have h3 := hge3 (2 * S + 3)
        have heq_s2 : newtonBase S k + 2 * S + 3 = newtonBase S k + (2 * S + 3) := by omega
        rw [newtonCircuit_gate_eq (S := S) (hS := rfl), heq_s2]; dsimp only [newtonGateFn]
        have hn0 : newtonBase S k + (2 * S + 3) ≠ 0 := by omega
        have hn1 : newtonBase S k + (2 * S + 3) ≠ 1 := by omega
        have hn2 : newtonBase S k + (2 * S + 3) ≠ 2 := by omega
        have hnot1 : ¬ (2 * S + 3 < S) := by omega
        have hneS : 2 * S + 3 ≠ S := by omega
        have hneS1 : 2 * S + 3 ≠ S + 1 := by omega
        have hnot2 : ¬ (2 * S + 3 < 2 * S + 2) := by omega
        have hne22 : 2 * S + 3 ≠ 2 * S + 2 := by omega
        simp only [hn0, hn1, hn2, hnot1, hneS, hneS1, hnot2, hne22, ↓reduceIte, ↓reduceDIte, hd, hm]
      have hsub2_eval : N.evalGatePoly ⟨newtonBase S k + 2 * S + 3, by omega⟩ =
          MvPolynomial.C 2 - (newtonIter C_h.evalPoly C_hy.evalPoly y0 u0 k).2 *
            MvPolynomial.bind₁ (Fin.lastCases (newtonIter C_h.evalPoly C_hy.evalPoly y0 u0 (k + 1)).1 MvPolynomial.X) C_hy.evalPoly := by
        rw [evalGatePoly_sub N _ _ _ hg_sub2 (by dsimp [N, newtonCircuit]; omega) (by omega),
            h2, hmul2_eval]
      have hu1_lt : newtonUSlot S (k + 1) < N.size := by
        dsimp only [newtonUSlot]; omega
      have hg_u1 : N.gate ⟨newtonUSlot S (k + 1), hu1_lt⟩ =
          .mul (newtonUSlot S k) (newtonBase S k + 2 * S + 3) := by
        rcases hdiv_off (2 * S + 4) (by unfold newtonBlockSize; omega) with ⟨hd, hm⟩
        have h3 := hge3 (2 * S + 4)
        have heq_u1 : newtonUSlot S (k + 1) = newtonBase S k + (2 * S + 4) := by dsimp only [newtonUSlot]; omega
        rw [newtonCircuit_gate_eq (S := S) (hS := rfl), heq_u1]; dsimp only [newtonGateFn]
        have hn0 : newtonBase S k + (2 * S + 4) ≠ 0 := by omega
        have hn1 : newtonBase S k + (2 * S + 4) ≠ 1 := by omega
        have hn2 : newtonBase S k + (2 * S + 4) ≠ 2 := by omega
        have hnot1 : ¬ (2 * S + 4 < S) := by omega
        have hneS : 2 * S + 4 ≠ S := by omega
        have hneS1 : 2 * S + 4 ≠ S + 1 := by omega
        have hnot2 : ¬ (2 * S + 4 < 2 * S + 2) := by omega
        have hne22 : 2 * S + 4 ≠ 2 * S + 2 := by omega
        have hne23 : 2 * S + 4 ≠ 2 * S + 3 := by omega
        simp only [hn0, hn1, hn2, hnot1, hneS, hneS1, hnot2, hne22, hne23, ↓reduceIte, ↓reduceDIte, hd, hm]
      have hu1_eval : N.evalGatePoly ⟨newtonUSlot S (k + 1), hu1_lt⟩ =
          (newtonIter C_h.evalPoly C_hy.evalPoly y0 u0 (k + 1)).2 := by
        rw [evalGatePoly_mul N _ _ _ hg_u1 huk_lt (by omega),
            huk, hsub2_eval]
        rfl
      exact ⟨hy1_eval, hu1_eval⟩
  exact (hiter K (le_refl K)).1

/-! ### 2. Polynomial algebra: last-variable view, degree bound, simple root, Vandermonde derivatives -/

/-- Equivalence `Fin (m + 1) ≃ Option (Fin m)` sending `Fin.last m ↦ none` and `i.castSucc ↦ some i`. -/
def finLastEquivOption (m : ℕ) : Fin (m + 1) ≃ Option (Fin m) where
  toFun := Fin.lastCases none some
  invFun o := Option.rec (Fin.last m) Fin.castSucc o
  left_inv x := by
    refine Fin.lastCases ?_ (fun i => ?_) x
    · simp
    · simp
  right_inv o := by
    cases o <;> simp

/-- `AlgEquiv` viewing `MvPolynomial (Fin (m + 1)) ℚ` as univariate polynomials in the last
variable `y = X (Fin.last m)` over `MvPolynomial (Fin m) ℚ`. -/
noncomputable def toLastPoly (m : ℕ) :
    MvPolynomial (Fin (m + 1)) ℚ ≃ₐ[ℚ] Polynomial (MvPolynomial (Fin m) ℚ) :=
  (MvPolynomial.renameEquiv ℚ (finLastEquivOption m)).trans (MvPolynomial.optionEquivLeft ℚ (Fin m))

lemma toLastPoly_eval {m : ℕ} (g : MvPolynomial (Fin (m + 1)) ℚ) (p : MvPolynomial (Fin m) ℚ) :
    (toLastPoly m g).eval p = MvPolynomial.bind₁ (Fin.lastCases p MvPolynomial.X) g := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    simp [toLastPoly, MvPolynomial.optionEquivLeft_C]
  | add g₁ g₂ ih₁ ih₂ =>
    simp [map_add, Polynomial.eval_add, ih₁, ih₂]
  | mul_X g v ih =>
    simp only [map_mul, Polynomial.eval_mul, ih]
    congr 1
    refine Fin.lastCases ?_ (fun i => ?_) v
    · simp [toLastPoly, finLastEquivOption, MvPolynomial.optionEquivLeft_X_none]
    · simp [toLastPoly, finLastEquivOption, MvPolynomial.optionEquivLeft_X_some]

lemma toLastPoly_shiftLast {m : ℕ} (g : MvPolynomial (Fin (m + 1)) ℚ) (t : ℚ) :
    toLastPoly m (MvPolynomial.bind₁ (fun v => MvPolynomial.X v + MvPolynomial.C (Fin.lastCases t (fun _ => 0) v)) g) =
      (toLastPoly m g).comp (Polynomial.X + Polynomial.C (MvPolynomial.C t)) := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.bind₁_C_right]
    dsimp [toLastPoly]
    rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_C, MvPolynomial.optionEquivLeft_C, Polynomial.C_comp]
  | add g₁ g₂ ih₁ ih₂ =>
    rw [map_add, map_add, map_add, Polynomial.add_comp, ih₁, ih₂]
  | mul_X g v ih =>
    rw [map_mul, map_mul, map_mul, Polynomial.mul_comp, ih, MvPolynomial.bind₁_X_right]
    congr 1
    refine Fin.lastCases ?_ (fun i => ?_) v
    · rw [Fin.lastCases_last, map_add]
      dsimp [toLastPoly]
      rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, MvPolynomial.renameEquiv_apply,
          MvPolynomial.rename_C, finLastEquivOption, Equiv.coe_fn_mk, Fin.lastCases_last,
          MvPolynomial.optionEquivLeft_X_none, MvPolynomial.optionEquivLeft_C, Polynomial.X_comp]
    · rw [Fin.lastCases_castSucc, map_zero, add_zero]
      dsimp [toLastPoly]
      rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
          finLastEquivOption, Equiv.coe_fn_mk, Fin.lastCases_castSucc,
          MvPolynomial.optionEquivLeft_X_some, Polynomial.C_comp]

lemma toLastPoly_shiftBase {m : ℕ} (g : MvPolynomial (Fin (m + 1)) ℚ) (a : Fin m → ℚ) :
    toLastPoly m (MvPolynomial.bind₁ (fun v => MvPolynomial.X v + MvPolynomial.C (Fin.lastCases 0 a v)) g) =
      (toLastPoly m g).map (MvPolynomial.bind₁ (fun i => MvPolynomial.X i + MvPolynomial.C (a i))) := by
  induction g using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.bind₁_C_right]
    dsimp [toLastPoly]
    rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_C, MvPolynomial.optionEquivLeft_C,
        Polynomial.map_C]
    simp
  | add g₁ g₂ ih₁ ih₂ =>
    rw [map_add, map_add, map_add, Polynomial.map_add, ih₁, ih₂]
  | mul_X g v ih =>
    rw [map_mul, map_mul, map_mul, Polynomial.map_mul, ih, MvPolynomial.bind₁_X_right]
    congr 1
    refine Fin.lastCases ?_ (fun i => ?_) v
    · rw [Fin.lastCases_last, map_zero, add_zero]
      dsimp [toLastPoly]
      rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
          finLastEquivOption, Equiv.coe_fn_mk, Fin.lastCases_last,
          MvPolynomial.optionEquivLeft_X_none, Polynomial.map_X]
    · rw [Fin.lastCases_castSucc, map_add]
      dsimp [toLastPoly]
      rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, MvPolynomial.renameEquiv_apply,
          MvPolynomial.rename_C, finLastEquivOption, Equiv.coe_fn_mk, Fin.lastCases_castSucc,
          MvPolynomial.optionEquivLeft_X_some, MvPolynomial.optionEquivLeft_C,
          Polynomial.map_C]
      simp

/-- Every coefficient `coeff j` of `toLastPoly m g` satisfies `totalDegree (coeff j) + j ≤ g.totalDegree`. -/
lemma totalDegree_toLastPoly_coeff_add_le {m : ℕ} (g : MvPolynomial (Fin (m + 1)) ℚ) (j : ℕ) :
    ((toLastPoly m g).coeff j).totalDegree + j ≤ g.totalDegree ∨ (toLastPoly m g).coeff j = 0 := by
  by_cases h0 : (toLastPoly m g).coeff j = 0
  · exact Or.inr h0
  · left
    rw [MvPolynomial.totalDegree]
    have hne : ((toLastPoly m g).coeff j).support.Nonempty := MvPolynomial.support_nonempty.mpr h0
    have hsup : ((toLastPoly m g).coeff j).support.sup (fun s => s.sum fun _ e => e) + j =
        ((toLastPoly m g).coeff j).support.sup (fun s => s.sum (fun _ e => e) + j) := by
      refine le_antisymm ?_ ?_
      · have hle : ∀ s ∈ ((toLastPoly m g).coeff j).support,
            s.sum (fun _ e => e) ≤ ((toLastPoly m g).coeff j).support.sup (fun s => s.sum (fun _ e => e) + j) - j := by
          intro s hs
          have h1 : s.sum (fun _ e => e) + j ≤
              ((toLastPoly m g).coeff j).support.sup (fun s => s.sum (fun _ e => e) + j) :=
            Finset.le_sup (f := fun s => s.sum (fun _ e => e) + j) hs
          omega
        have h2 := Finset.sup_le hle
        have h3 : j ≤ ((toLastPoly m g).coeff j).support.sup (fun s => s.sum (fun _ e => e) + j) := by
          rcases hne with ⟨s0, hs0⟩
          exact le_trans (Nat.le_add_left _ _) (Finset.le_sup (f := fun s => s.sum (fun _ e => e) + j) hs0)
        omega
      · refine Finset.sup_le fun s hs => ?_
        exact Nat.add_le_add_right (Finset.le_sup (f := fun s => s.sum fun _ e => e) hs) j
    rw [hsup]
    refine Finset.sup_le fun s hs => ?_
    let t : Fin (m + 1) →₀ ℕ :=
      Finsupp.equivFunOnFinite.symm (Fin.lastCases j (fun i => s i))
    have ht_mem : t ∈ g.support := by
      dsimp [toLastPoly] at hs
      rw [MvPolynomial.mem_support_coeff_optionEquivLeft] at hs
      rw [MvPolynomial.mem_support_iff] at hs ⊢
      have hmap : Finsupp.mapDomain (finLastEquivOption m) t = s.optionElim j := by
        ext o
        rw [Finsupp.mapDomain_equiv_apply]
        cases o with
        | none => simp [t, finLastEquivOption]
        | some i => simp [t, finLastEquivOption]
      rw [← hmap, MvPolynomial.renameEquiv_apply, MvPolynomial.coeff_rename_mapDomain _ (finLastEquivOption m).injective] at hs
      exact hs
    have hsum_t : t.sum (fun _ e => e) = s.sum (fun _ e => e) + j := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Finsupp.sum_fintype _ _ (fun _ => rfl),
          Fin.sum_univ_castSucc]
      simp [t]
    rw [← hsum_t]
    exact MvPolynomial.le_totalDegree ht_mem

lemma toLastPoly_natDegree_le {m : ℕ} (g : MvPolynomial (Fin (m + 1)) ℚ) :
    (toLastPoly m g).natDegree ≤ g.totalDegree := by
  by_cases h0 : toLastPoly m g = 0
  · simp [h0]
  · have hlc : (toLastPoly m g).coeff (toLastPoly m g).natDegree ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr h0
    rcases totalDegree_toLastPoly_coeff_add_le g (toLastPoly m g).natDegree with hle | hzero
    · omega
    · exact absurd hzero hlc

/-- **Degree bound:** if `g(x, p(x)) = 0` with `g ≠ 0` and `g.totalDegree ≤ d`, then `p.totalDegree ≤ d`. -/
theorem totalDegree_le_of_eval_eq_zero {m d : ℕ} (g : MvPolynomial (Fin (m + 1)) ℚ)
    (hg_nz : g ≠ 0) (hg_deg : g.totalDegree ≤ d)
    (p : MvPolynomial (Fin m) ℚ) (hroot : MvPolynomial.bind₁ (Fin.lastCases p MvPolynomial.X) g = 0) :
    p.totalDegree ≤ d := by
  by_contra hgt
  push_neg at hgt
  have hp_nz : p ≠ 0 := by
    intro hp0; subst hp0; simp at hgt
  let G := toLastPoly m g
  have hG_nz : G ≠ 0 := fun h => hg_nz ((toLastPoly m).injective (by simpa [G] using h))
  have hG_eval : G.eval p = 0 := by rwa [toLastPoly_eval]
  set D := G.natDegree
  have hD_pos : 1 ≤ D := by
    by_contra hD0
    have hDeq : D = 0 := by omega
    have hGC : G = Polynomial.C (G.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hDeq
    have hc0 : G.coeff 0 = 0 := by
      have := hG_eval; rw [hGC, Polynomial.eval_C] at this; exact this
    exact hG_nz (by rw [hGC, hc0, map_zero])
  have hlc_nz : G.coeff D ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hG_nz
  have hpow_nz : ∀ j : ℕ, p ^ j ≠ 0 := fun j => pow_ne_zero j hp_nz
  have hpow_deg : ∀ j : ℕ, (p ^ j).totalDegree = j * p.totalDegree := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, MvPolynomial.totalDegree_mul_of_isDomain (hpow_nz j) hp_nz, ih]
      ring
  have htop_deg : (G.coeff D * p ^ D).totalDegree = (G.coeff D).totalDegree + D * p.totalDegree := by
    rw [MvPolynomial.totalDegree_mul_of_isDomain hlc_nz (hpow_nz D), hpow_deg D]
  have htop_pos : 0 < (G.coeff D * p ^ D).totalDegree := by
    rw [htop_deg]; nlinarith
  have hlt_rest : (∑ j ∈ Finset.range D, G.coeff j * p ^ j).totalDegree < (G.coeff D * p ^ D).totalDegree := by
    have hle_sup := MvPolynomial.totalDegree_finsetSum (Finset.range D) (fun j => G.coeff j * p ^ j)
    refine lt_of_le_of_lt hle_sup ?_
    rw [Finset.sup_lt_iff htop_pos]
    intro j hj
    rw [Finset.mem_range] at hj
    rcases totalDegree_toLastPoly_coeff_add_le g j with hcj | hcj0
    · have hmul_le := MvPolynomial.totalDegree_mul (G.coeff j) (p ^ j)
      rw [hpow_deg j] at hmul_le
      have h1 : (G.coeff j).totalDegree + j * p.totalDegree < D * p.totalDegree := by
        have hstep : (j + 1) * p.totalDegree ≤ D * p.totalDegree := Nat.mul_le_mul_right _ hj
        nlinarith
      rw [htop_deg]; omega
    · rw [hcj0, zero_mul, MvPolynomial.totalDegree_zero]
      exact htop_pos
  have hsum_eq : G.eval p = (∑ j ∈ Finset.range D, G.coeff j * p ^ j) + G.coeff D * p ^ D := by
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ]
  rw [hG_eval] at hsum_eq
  have heq_neg : G.coeff D * p ^ D = -(∑ j ∈ Finset.range D, G.coeff j * p ^ j) :=
    eq_neg_of_add_eq_zero_right hsum_eq.symm
  have hdeg_eq : (G.coeff D * p ^ D).totalDegree = (∑ j ∈ Finset.range D, G.coeff j * p ^ j).totalDegree := by
    rw [heq_neg, MvPolynomial.totalDegree_neg]
  omega

/-- Relation between `derivative (hasseDeriv r G)` and `hasseDeriv (r + 1) G`. -/
lemma derivative_hasseDeriv {R : Type*} [CommRing R] (r : ℕ) (G : Polynomial R) :
    Polynomial.derivative (Polynomial.hasseDeriv r G) =
      ((r + 1 : ℕ) : R) • Polynomial.hasseDeriv (r + 1) G := by
  ext i
  rw [Polynomial.coeff_derivative, Polynomial.hasseDeriv_coeff, Polynomial.coeff_smul,
      Polynomial.hasseDeriv_coeff, smul_eq_mul]
  have hbinom : (i + (r + 1)).choose r * (i + 1) = (r + 1) * (i + (r + 1)).choose (r + 1) := by
    have hsym := Nat.choose_succ_right_eq (i + (r + 1)) r
    have h4 : i + (r + 1) - r = i + 1 := by omega
    rw [h4] at hsym
    linarith
  have hidx : i + 1 + r = i + (r + 1) := by omega
  rw [hidx]
  have hcast : (((i + (r + 1)).choose r : R) * ((i + 1 : ℕ) : R)) =
      ((r + 1 : ℕ) : R) * ((i + (r + 1)).choose (r + 1) : R) := by
    have := congrArg (Nat.cast (R := R)) hbinom
    simpa [Nat.cast_mul] using this
  push_cast at hcast ⊢
  linear_combination G.coeff (i + (r + 1)) * hcast

/-- Simple-root reduction: if `G ≠ 0`, `G.natDegree ≤ d`, and `G.eval p = 0`, then there exists
`r < d` such that `(hasseDeriv r G).eval p = 0` and `(derivative (hasseDeriv r G)).eval p ≠ 0`. -/
theorem exists_simple_root_hasseDeriv {m d : ℕ} (G : Polynomial (MvPolynomial (Fin m) ℚ))
    (hG_nz : G ≠ 0) (hG_deg : G.natDegree ≤ d)
    (p : MvPolynomial (Fin m) ℚ) (hroot : G.eval p = 0) :
    ∃ r < d,
      (Polynomial.hasseDeriv r G).eval p = 0 ∧
      (Polynomial.derivative (Polynomial.hasseDeriv r G)).eval p ≠ 0 := by
  classical
  let S := (Finset.range (G.natDegree + 1)).filter (fun r => (Polynomial.hasseDeriv r G).eval p = 0)
  have h0_mem : 0 ∈ S := by
    simp [S, Polynomial.hasseDeriv_zero', hroot]
  let r := S.max' ⟨0, h0_mem⟩
  have hr_mem : r ∈ S := Finset.max'_mem S ⟨0, h0_mem⟩
  have hr_eval : (Polynomial.hasseDeriv r G).eval p = 0 := (Finset.mem_filter.mp hr_mem).2
  have hr_le : r ≤ G.natDegree := by
    have := (Finset.mem_filter.mp hr_mem).1; rw [Finset.mem_range] at this; omega
  have hr_ne_deg : r ≠ G.natDegree := by
    intro heq
    rw [heq, Polynomial.hasseDeriv_natDegree_eq_C, Polynomial.eval_C] at hr_eval
    exact Polynomial.leadingCoeff_ne_zero.mpr hG_nz hr_eval
  have hr_lt : r < G.natDegree := lt_of_le_of_ne hr_le hr_ne_deg
  have hr1_not : r + 1 ∉ S := fun hmem => by
    have := Finset.le_max' S (r + 1) hmem; omega
  have hr1_nz : (Polynomial.hasseDeriv (r + 1) G).eval p ≠ 0 := by
    intro h0
    exact hr1_not (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h0⟩)
  refine ⟨r, lt_of_lt_of_le hr_lt hG_deg, hr_eval, ?_⟩
  rw [derivative_hasseDeriv, Polynomial.smul_eq_C_mul, Polynomial.eval_mul, Polynomial.eval_C]
  have hne : ((r + 1 : ℕ) : MvPolynomial (Fin m) ℚ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero r
  exact mul_ne_zero hne hr1_nz

/-- Shift expansion via Hasse derivatives:
`G.comp (X + C t) = ∑ k ∈ range (d + 1), C (t ^ k) * hasseDeriv k G`. -/
lemma comp_X_add_C_eq_sum_hasseDeriv {R : Type*} [CommRing R] (G : Polynomial R) (d : ℕ)
    (hd : G.natDegree ≤ d) (t : R) :
    G.comp (Polynomial.X + Polynomial.C t) =
      ∑ k ∈ Finset.range (d + 1), Polynomial.C (t ^ k) * Polynomial.hasseDeriv k G := by
  have hmon : ∀ (n : ℕ) (hn : n ≤ d) (c : R),
      (Polynomial.monomial n c).comp (Polynomial.X + Polynomial.C t) =
        ∑ k ∈ Finset.range (d + 1), Polynomial.C (t ^ k) * Polynomial.hasseDeriv k (Polynomial.monomial n c) := by
    intro n hn c
    rw [Polynomial.monomial_comp, add_pow]
    have hsplit : Finset.range (d + 1) = Finset.range (n + 1) ∪ (Finset.range (d + 1) \ Finset.range (n + 1)) := by
      rw [Finset.union_sdiff_of_subset (Finset.range_mono (by omega))]
    rw [hsplit, Finset.sum_union Finset.disjoint_sdiff]
    have hzero : ∑ k ∈ Finset.range (d + 1) \ Finset.range (n + 1),
        Polynomial.C (t ^ k) * Polynomial.hasseDeriv k (Polynomial.monomial n c) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      have hk_gt : n < k := by
        have := (Finset.mem_sdiff.mp hk).2; rw [Finset.mem_range] at this; omega
      rw [Polynomial.hasseDeriv_monomial, Nat.choose_eq_zero_of_lt hk_gt]
      simp
    rw [hzero, add_zero, Finset.mul_sum]
    rw [← Finset.sum_flip]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [Polynomial.hasseDeriv_monomial, ← Polynomial.C_pow]
    have hsub : n - (n - k) = k := by omega
    rw [hsub, Nat.choose_symm (by omega), ← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_natCast]
    ring
  rw [G.as_sum_range_C_mul_X_pow]
  have hsum_deg : ∑ i ∈ Finset.range (G.natDegree + 1), Polynomial.C (G.coeff i) * Polynomial.X ^ i =
      ∑ i ∈ Finset.range (G.natDegree + 1), Polynomial.monomial i (G.coeff i) := by
    refine Finset.sum_congr rfl fun i _ => Polynomial.C_mul_X_pow_eq_monomial
  have hcomp_sum : ∀ (S : Finset ℕ) (f : ℕ → Polynomial R),
      (∑ i ∈ S, f i).comp (Polynomial.X + Polynomial.C t) =
        ∑ i ∈ S, (f i).comp (Polynomial.X + Polynomial.C t) := by
    intro S f
    classical
    induction S using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Polynomial.add_comp, ih, Finset.sum_insert ha]
  rw [hsum_deg, hcomp_sum]
  have h1 : ∑ i ∈ Finset.range (G.natDegree + 1), (Polynomial.monomial i (G.coeff i)).comp (Polynomial.X + Polynomial.C t) =
      ∑ i ∈ Finset.range (G.natDegree + 1),
        ∑ k ∈ Finset.range (d + 1), Polynomial.C (t ^ k) * Polynomial.hasseDeriv k (Polynomial.monomial i (G.coeff i)) := by
    refine Finset.sum_congr rfl fun i hi => hmon i (by rw [Finset.mem_range] at hi; omega) (G.coeff i)
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.mul_sum, ← map_sum, ← hsum_deg, ← G.as_sum_range_C_mul_X_pow]

/-- Vandermonde inversion over `ℚ`: for every `d` and `r ≤ d`, there exist rational coefficients
`α : Fin (d + 1) → ℚ` extracting `hasseDeriv r G` from `G.comp (X + C j)` (`j = 0..d`). -/
theorem vandermonde_hasseDeriv_coeffs (d r : ℕ) (hr : r ≤ d) :
    ∃ α : Fin (d + 1) → ℚ, ∀ (m : ℕ) (G : Polynomial (MvPolynomial (Fin m) ℚ)),
      G.natDegree ≤ d →
      Polynomial.hasseDeriv r G =
        ∑ j : Fin (d + 1),
          (MvPolynomial.C (α j) : MvPolynomial (Fin m) ℚ) •
            G.comp (Polynomial.X + Polynomial.C (MvPolynomial.C (j.val : ℚ))) := by
  let v : Fin (d + 1) → ℚ := fun j => (j.val : ℚ)
  let V : Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ := Matrix.vandermonde v
  have hdet : V.det ≠ 0 := by
    rw [Matrix.det_vandermonde_ne_zero_iff]
    intro i j hij
    have : i.val = j.val := by dsimp [v] at hij; exact_mod_cast hij
    exact Fin.ext this
  have hinv : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V (isUnit_iff_ne_zero.mpr hdet)
  let rFin : Fin (d + 1) := ⟨r, by omega⟩
  refine ⟨fun j => V⁻¹ rFin j, fun m G hG_deg => ?_⟩
  have hstep : ∀ j : Fin (d + 1),
      G.comp (Polynomial.X + Polynomial.C (MvPolynomial.C (j.val : ℚ))) =
        ∑ k : Fin (d + 1),
          Polynomial.C (MvPolynomial.C (V j k)) * Polynomial.hasseDeriv k.val G := by
    intro j
    rw [comp_X_add_C_eq_sum_hasseDeriv G d hG_deg (MvPolynomial.C (j.val : ℚ)),
        ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [V, Matrix.vandermonde_apply, v, map_pow]
  simp_rw [hstep, Finset.smul_sum]
  rw [Finset.sum_comm]
  have hinner : ∀ k : Fin (d + 1),
      (∑ j : Fin (d + 1), (MvPolynomial.C (V⁻¹ rFin j) : MvPolynomial (Fin m) ℚ) •
        (Polynomial.C (MvPolynomial.C (V j k)) * Polynomial.hasseDeriv k.val G)) =
      if k = rFin then Polynomial.hasseDeriv k.val G else 0 := by
    intro k
    have hcoeff : ∑ j : Fin (d + 1), V⁻¹ rFin j * V j k = if rFin = k then 1 else 0 := by
      have hmul := congrFun (congrFun hinv rFin) k
      simpa [Matrix.mul_apply, Matrix.one_apply] using hmul
    have hrw : ∀ j : Fin (d + 1),
        (MvPolynomial.C (V⁻¹ rFin j) : MvPolynomial (Fin m) ℚ) •
          (Polynomial.C (MvPolynomial.C (V j k)) * Polynomial.hasseDeriv k.val G) =
        Polynomial.C (MvPolynomial.C (V⁻¹ rFin j * V j k)) * Polynomial.hasseDeriv k.val G := by
      intro j
      rw [Polynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul, ← map_mul]
    simp_rw [hrw]
    rw [← Finset.sum_mul, ← map_sum Polynomial.C, ← map_sum MvPolynomial.C, hcoeff]
    by_cases hk : k = rFin
    · subst hk; simp
    · have hne : rFin ≠ k := Ne.symm hk; simp [hk, hne]
  simp_rw [hinner]
  simp [rFin]

/-! ### 3. Coupled quadratic Newton iteration modulo `(z_1, ..., z_m)^N` -/

open ExactMatching.Proofs (ZeroMod zeroMod_zero zeroMod_mono zeroMod_neg zeroMod_add zeroMod_sub zeroMod_mul)

lemma zeroMod_mul_right {m : ℕ} {N : ℕ} {f : MvPolynomial (Fin m) ℚ} (g : MvPolynomial (Fin m) ℚ)
    (hf : ZeroMod N f) : ZeroMod N (f * g) := by
  have hg : ZeroMod 0 g := fun _ _ => Nat.zero_le _
  simpa using zeroMod_mul hf hg

lemma zeroMod_mul_left {m : ℕ} {N : ℕ} (f : MvPolynomial (Fin m) ℚ) {g : MvPolynomial (Fin m) ℚ}
    (hg : ZeroMod N g) : ZeroMod N (f * g) := by
  rw [mul_comm]; exact zeroMod_mul_right f hg

lemma zeroMod_one_of_eval_zero {m : ℕ} {f : MvPolynomial (Fin m) ℚ}
    (h0 : MvPolynomial.eval 0 f = 0) : ZeroMod 1 f := by
  intro e he
  by_contra hlt
  have hsum0 : e.sum (fun _ v => v) = 0 := by omega
  have he0 : e = 0 := by
    ext i
    have hle : e i ≤ e.sum (fun _ v => v) := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    simp; omega
  subst he0
  rw [MvPolynomial.mem_support_iff] at he
  have heval : MvPolynomial.eval 0 f = f.coeff 0 := by
    rw [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq]
  rw [heval] at h0
  exact he h0

/-- Second-order algebraic Taylor expansion for univariate polynomials over any commutative ring. -/
lemma poly_taylor_quad {R : Type*} [CommRing R] (P : Polynomial R) (a b : R) :
    ∃ Q : R, P.eval (a + b) = P.eval a + (Polynomial.derivative P).eval a * b + b ^ 2 * Q := by
  induction P using Polynomial.induction_on' with
  | add P₁ P₂ ih₁ ih₂ =>
    rcases ih₁ with ⟨Q₁, h₁⟩
    rcases ih₂ with ⟨Q₂, h₂⟩
    refine ⟨Q₁ + Q₂, ?_⟩
    simp only [Polynomial.eval_add, Polynomial.derivative_add, h₁, h₂]
    ring
  | monomial n c =>
    have hpow : ∀ k : ℕ, ∃ q : R, (a + b) ^ k = a ^ k + (k : R) * a ^ (k - 1) * b + b ^ 2 * q := by
      intro k
      induction k with
      | zero => exact ⟨0, by simp⟩
      | succ k ihk =>
        rcases ihk with ⟨q, hq⟩
        cases k with
        | zero => exact ⟨0, by simp⟩
        | succ k =>
          refine ⟨a * q + ((k + 1 : ℕ) : R) * a ^ k + b * q, ?_⟩
          rw [pow_succ, hq]
          have hsub : k + 1 + 1 - 1 = k + 1 := by omega
          have hsub0 : k + 1 - 1 = k := by omega
          rw [hsub, hsub0]
          push_cast
          rw [pow_succ]
          ring
    rcases hpow n with ⟨q, hq⟩
    refine ⟨c * q, ?_⟩
    rw [Polynomial.eval_monomial, Polynomial.eval_monomial, Polynomial.derivative_monomial,
        Polynomial.eval_monomial, hq]
    ring

private lemma eval_bind₁_eq {σ τ R : Type*} [CommSemiring R]
    (x : τ → R) (f : σ → MvPolynomial τ R) (g : MvPolynomial σ R) :
    MvPolynomial.eval x (MvPolynomial.bind₁ f g) = MvPolynomial.eval (fun v => MvPolynomial.eval x (f v)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q ihp ihq => simp [map_add, ihp, ihq]
  | mul_X p v ihp => simp [map_mul, ihp]

/-- Coupled quadratic Newton iteration converges quadratically modulo `(z_1, ..., z_m)^{2^k}`. -/
theorem newtonIter_zeroMod {m : ℕ} (H H' : MvPolynomial (Fin (m + 1)) ℚ)
    (hderiv : toLastPoly m H' = Polynomial.derivative (toLastPoly m H))
    (p : MvPolynomial (Fin m) ℚ)
    (hroot : MvPolynomial.bind₁ (Fin.lastCases p MvPolynomial.X) H = 0)
    (hunit : MvPolynomial.eval 0 (MvPolynomial.bind₁ (Fin.lastCases p MvPolynomial.X) H') ≠ 0) :
    let y0 := MvPolynomial.eval 0 p
    let u0 := (MvPolynomial.eval 0 (MvPolynomial.bind₁ (Fin.lastCases p MvPolynomial.X) H'))⁻¹
    ∀ k : ℕ,
      ZeroMod (2 ^ k) (p - (newtonIter H H' y0 u0 k).1) ∧
      ZeroMod (2 ^ k) (1 - (newtonIter H H' y0 u0 k).2 *
        MvPolynomial.bind₁ (Fin.lastCases (newtonIter H H' y0 u0 k).1 MvPolynomial.X) H') := by
  intro y0 u0 k
  induction k with
  | zero =>
    dsimp [newtonIter]
    have hy0 : ZeroMod 1 (p - MvPolynomial.C y0) := by
      apply zeroMod_one_of_eval_zero
      simp [y0]
    have hhy0_eval : MvPolynomial.eval 0 (MvPolynomial.bind₁ (Fin.lastCases (MvPolynomial.C y0) MvPolynomial.X) H') =
        MvPolynomial.eval 0 (MvPolynomial.bind₁ (Fin.lastCases p MvPolynomial.X) H') := by
      rw [eval_bind₁_eq, eval_bind₁_eq]
      exact congrArg (fun f => MvPolynomial.eval f H') (by
        ext v; refine Fin.lastCases ?_ (fun i => ?_) v <;> simp [y0])
    have hu0 : ZeroMod 1 (1 - MvPolynomial.C u0 * MvPolynomial.bind₁ (Fin.lastCases (MvPolynomial.C y0) MvPolynomial.X) H') := by
      apply zeroMod_one_of_eval_zero
      rw [map_sub, map_one, map_mul, MvPolynomial.eval_C, hhy0_eval, inv_mul_cancel₀ hunit, sub_self]
    simpa using And.intro hy0 hu0
  | succ k ih =>
    rcases ih with ⟨hyk, huk⟩
    set yk := (newtonIter H H' y0 u0 k).1
    set uk := (newtonIter H H' y0 u0 k).2
    set y1 := (newtonIter H H' y0 u0 (k + 1)).1
    set u1 := (newtonIter H H' y0 u0 (k + 1)).2
    have hy1_def : y1 = yk - uk * MvPolynomial.bind₁ (Fin.lastCases yk MvPolynomial.X) H := rfl
    have hu1_def : u1 = uk * (MvPolynomial.C 2 - uk * MvPolynomial.bind₁ (Fin.lastCases y1 MvPolynomial.X) H') := rfl
    -- Step 1: Quadratic convergence of y1
    rcases poly_taylor_quad (toLastPoly m H) yk (p - yk) with ⟨Q, hQ⟩
    rw [add_sub_cancel, toLastPoly_eval, hroot, toLastPoly_eval, ← hderiv, toLastPoly_eval] at hQ
    have hy1_eq : p - y1 =
        (p - yk) * (1 - uk * MvPolynomial.bind₁ (Fin.lastCases yk MvPolynomial.X) H') -
        (p - yk) * (p - yk) * (uk * Q) := by
      rw [hy1_def]
      have hH : MvPolynomial.bind₁ (Fin.lastCases yk MvPolynomial.X) H =
          -(MvPolynomial.bind₁ (Fin.lastCases yk MvPolynomial.X) H' * (p - yk) + (p - yk) ^ 2 * Q) := by
        linear_combination -hQ
      rw [hH]; ring
    have hpow2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    have hy1_mod : ZeroMod (2 ^ (k + 1)) (p - y1) := by
      rw [hy1_eq, hpow2]
      exact zeroMod_sub (zeroMod_mul hyk huk) (zeroMod_mul_right (uk * Q) (zeroMod_mul hyk hyk))
    -- Step 2: Quadratic convergence of u1
    have hdy : ZeroMod (2 ^ k) (y1 - yk) := by
      have heq : y1 - yk = (p - yk) - (p - y1) := by ring
      rw [heq]
      exact zeroMod_sub hyk (zeroMod_mono (Nat.pow_le_pow_right (by omega) (Nat.le_succ k)) hy1_mod)
    have hdiff_H' : ZeroMod (2 ^ k)
        (MvPolynomial.bind₁ (Fin.lastCases y1 MvPolynomial.X) H' -
         MvPolynomial.bind₁ (Fin.lastCases yk MvPolynomial.X) H') := by
      rw [← toLastPoly_eval, ← toLastPoly_eval]
      obtain ⟨R, hR⟩ := Polynomial.sub_dvd_eval_sub y1 yk (toLastPoly m H')
      rw [hR]
      exact zeroMod_mul_right R hdy
    set e := 1 - uk * MvPolynomial.bind₁ (Fin.lastCases y1 MvPolynomial.X) H'
    have he_mod : ZeroMod (2 ^ k) e := by
      have he_eq : e = (1 - uk * MvPolynomial.bind₁ (Fin.lastCases yk MvPolynomial.X) H') -
          uk * (MvPolynomial.bind₁ (Fin.lastCases y1 MvPolynomial.X) H' -
                MvPolynomial.bind₁ (Fin.lastCases yk MvPolynomial.X) H') := by
        dsimp [e]; ring
      rw [he_eq]
      exact zeroMod_sub huk (zeroMod_mul_left uk hdiff_H')
    have hu1_eq : 1 - u1 * MvPolynomial.bind₁ (Fin.lastCases y1 MvPolynomial.X) H' = e * e := by
      rw [hu1_def]; dsimp [e]
      have hC2 : (MvPolynomial.C (2 : ℚ) : MvPolynomial (Fin m) ℚ) = 2 := map_ofNat MvPolynomial.C 2
      rw [hC2]; ring
    have hu1_mod : ZeroMod (2 ^ (k + 1)) (1 - u1 * MvPolynomial.bind₁ (Fin.lastCases y1 MvPolynomial.X) H') := by
      rw [hu1_eq, hpow2]
      exact zeroMod_mul he_mod he_mod
    exact ⟨hy1_mod, hu1_mod⟩

/-! ### 4. Assembly of `KI04_Cor_7_4` given Strassen homogenization -/

/-- Interface of Strassen homogenization (`StrassenHomog.lean`). -/
def StrassenHomogInterface : Prop :=
  (∀ {m d : ℕ} (Y p : MvPolynomial (Fin m) ℚ),
    p.totalDegree ≤ d → ZeroMod (d + 1) (Y - p) →
    (∑ r ∈ Finset.range (d + 1), MvPolynomial.homogeneousComponent r Y) = p) ∧
  (∀ {m : ℕ} (C : RatCircuit m) (d : ℕ),
    ∃ C_h : RatCircuit m,
      C_h.size ≤ (2 * (d + 1) ^ 2 + 2 * (d + 1) + 4) * C.size + (d + 2) ∧
      C_h.evalPoly = ∑ r ∈ Finset.range (d + 1), MvPolynomial.homogeneousComponent r C.evalPoly)

private lemma ki04_size_arith (s d a gsz K hsz : ℕ)
    (hs_ge : gsz ≤ s) (hK_le : K ≤ d + 1)
    (hChom : hsz ≤ (2 * (d + 1) ^ 2 + 2 * (d + 1) + 4) *
      (3 + K * newtonBlockSize (3 * ((d + 1) * (3 * gsz) + (d + 1) + (d + 1)))) + (d + 2)) :
    3 * hsz ≤ 1000 * (s + d + a + 2) ^ 6 := by
  set N := s + d + a + 2
  have hN2 : 2 ≤ N := by omega
  have hS_le : 3 * ((d + 1) * (3 * gsz) + (d + 1) + (d + 1)) ≤ 15 * N ^ 2 := by
    have h1 : d + 1 ≤ N := by omega
    have h2 : gsz ≤ N := by omega
    nlinarith
  have hCY_le : 3 + K * newtonBlockSize (3 * ((d + 1) * (3 * gsz) + (d + 1) + (d + 1))) ≤ 35 * N ^ 3 := by
    unfold newtonBlockSize
    have h1 : K ≤ N := by omega
    have h2 : 1 ≤ N ^ 2 := by nlinarith
    have h3 : N ≤ N ^ 3 := by nlinarith
    have h4 : N ^ 2 ≤ N ^ 3 := by nlinarith
    nlinarith
  have hChom_le : hsz ≤ 300 * N ^ 5 := by
    have h1 : d + 1 ≤ N := by omega
    have h2 : 2 * (d + 1) ^ 2 + 2 * (d + 1) + 4 ≤ 8 * N ^ 2 := by nlinarith
    have h3 : (2 * (d + 1) ^ 2 + 2 * (d + 1) + 4) *
        (3 + K * newtonBlockSize (3 * ((d + 1) * (3 * gsz) + (d + 1) + (d + 1)))) ≤ (8 * N ^ 2) * (35 * N ^ 3) :=
      Nat.mul_le_mul h2 hCY_le
    have h4 : d + 2 ≤ N ^ 5 := by
      have : N ≤ N ^ 2 := by nlinarith
      have : N ^ 2 ≤ N ^ 3 := by nlinarith
      have : N ^ 3 ≤ N ^ 4 := by nlinarith
      have : N ^ 4 ≤ N ^ 5 := by nlinarith
      omega
    nlinarith
  have hN5_le : N ^ 5 ≤ N ^ 6 := by
    have : 1 ≤ N ^ 5 := Nat.one_le_pow 5 N (by omega)
    nlinarith
  nlinarith

/-- **Main theorem:** `KI04_Cor_7_4` follows unconditionally from Strassen homogenization! -/
theorem ki04_cor_7_4_of_strassen (hStr : StrassenHomogInterface) : KI04_Cor_7_4 := by
  rcases hStr with ⟨hsum_homog, hrat_homog⟩
  refine ⟨1000, 6, by omega, by omega, ?_⟩
  intro m g_circ d a p g hg_nz hg_deg _hg_bit hroot
  let s := g_circ.encodingLength
  have hs_ge : g_circ.size ≤ s := intCircuit_size_le_encodingLength g_circ
  let C_g : RatCircuit (m + 1) := ratCircuitOfIntCircuit g_circ
  have hCg_size : C_g.size = g_circ.size := rfl
  let gQ : MvPolynomial (Fin (m + 1)) ℚ := MvPolynomial.map (Int.castRingHom ℚ) g
  let pQ : MvPolynomial (Fin m) ℚ := MvPolynomial.map (Int.castRingHom ℚ) p
  have hCg_eval : C_g.evalPoly = gQ := ratCircuitOfIntCircuit_evalPoly g_circ
  have hgQ_nz : gQ ≠ 0 := by
    intro h0
    apply hg_nz
    exact MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective (by simpa [gQ] using h0)
  have hgQ_deg : gQ.totalDegree ≤ d :=
    le_trans (Finset.sup_mono (MvPolynomial.support_map_subset _ _)) hg_deg
  have hrootQ : MvPolynomial.bind₁ (Fin.lastCases pQ MvPolynomial.X) gQ = 0 := by
    have hmap : MvPolynomial.map (Int.castRingHom ℚ) (MvPolynomial.bind₁ (Fin.lastCases p MvPolynomial.X) g) =
        MvPolynomial.bind₁ (Fin.lastCases pQ MvPolynomial.X) gQ := by
      rw [MvPolynomial.map_bind₁]
      congr 1; ext v
      refine Fin.lastCases ?_ (fun i => ?_) v
      · simp [pQ]
      · simp
    rw [← hmap, hroot, map_zero]
  -- Step 1: Degree bound `pQ.totalDegree ≤ d` and simple-root reduction `r < d`
  have hpQ_deg : pQ.totalDegree ≤ d := totalDegree_le_of_eval_eq_zero gQ hgQ_nz hgQ_deg pQ hrootQ
  let G := toLastPoly m gQ
  have hG_nz : G ≠ 0 := fun h => hgQ_nz ((toLastPoly m).injective (by simpa [G] using h))
  have hG_deg : G.natDegree ≤ d := le_trans (toLastPoly_natDegree_le gQ) hgQ_deg
  have hG_root : G.eval pQ = 0 := by rwa [toLastPoly_eval]
  obtain ⟨r, hr_lt, hHr_root, hHr'_nz⟩ := exists_simple_root_hasseDeriv G hG_nz hG_deg pQ hG_root
  -- Step 2: Build Vandermonde-interpolated `RatCircuit (m + 1)` for `H = hasseDeriv r G` and `H' = derivative H`
  obtain ⟨α, hα⟩ := vandermonde_hasseDeriv_coeffs d r (le_of_lt hr_lt)
  obtain ⟨β, hβ⟩ := vandermonde_hasseDeriv_coeffs d (r + 1) hr_lt
  let shiftJ : Fin (d + 1) → RatCircuit (m + 1) :=
    fun j => shiftVarsCircuit C_g (Fin.lastCases (j.val : ℚ) (fun _ => 0))
  have hshiftJ_size : ∀ j, (shiftJ j).size ≤ 3 * g_circ.size := fun _ => le_refl _
  have hB_pos : 1 ≤ 3 * g_circ.size := by have := g_circ.size_pos; omega
  let C_H : RatCircuit (m + 1) := linCombCircuit (d + 1) (by omega) (3 * g_circ.size) hB_pos α shiftJ hshiftJ_size
  let C_H' : RatCircuit (m + 1) :=
    linCombCircuit (d + 1) (by omega) (3 * g_circ.size) hB_pos (fun j => ((r + 1 : ℕ) : ℚ) * β j) shiftJ hshiftJ_size
  have htoC : ∀ q : ℚ, toLastPoly m (MvPolynomial.C q) = Polynomial.C (MvPolynomial.C q) := by
    intro q; dsimp [toLastPoly]; rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_C, MvPolynomial.optionEquivLeft_C]
  have hCH_poly : toLastPoly m C_H.evalPoly = Polynomial.hasseDeriv r G := by
    rw [linCombCircuit_evalPoly, map_sum, hα m G hG_deg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, htoC, shiftVarsCircuit_evalPoly, hCg_eval, toLastPoly_shiftLast, Polynomial.smul_eq_C_mul]
  have hCH'_poly : toLastPoly m C_H'.evalPoly = Polynomial.derivative (Polynomial.hasseDeriv r G) := by
    rw [linCombCircuit_evalPoly, map_sum, derivative_hasseDeriv, hβ m G hG_deg, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, htoC, shiftVarsCircuit_evalPoly, hCg_eval, toLastPoly_shiftLast]
    simp only [Polynomial.smul_eq_C_mul, map_mul, map_natCast]
    ring
  -- Step 3: Pick origin `a₀ : Fin m → ℚ` where `H'(a₀, pQ(a₀)) ≠ 0`
  have hH'_at_p_nz : MvPolynomial.bind₁ (Fin.lastCases pQ MvPolynomial.X) C_H'.evalPoly ≠ 0 := by
    rwa [← toLastPoly_eval, hCH'_poly]
  let Sgrid : Finset ℚ := (Finset.range ((MvPolynomial.bind₁ (Fin.lastCases pQ MvPolynomial.X) C_H'.evalPoly).totalDegree + 1)).image (fun i : ℕ => (i : ℚ))
  have hSgrid_card : (MvPolynomial.bind₁ (Fin.lastCases pQ MvPolynomial.X) C_H'.evalPoly).totalDegree < Sgrid.card := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]; omega
  obtain ⟨a0, _, ha0_nz⟩ :=
    ExactMatching.Proofs.step_2_2_nonvanishing_proved _ hH'_at_p_nz Sgrid hSgrid_card
  -- Shift origin by `a0`: `p̃(z) = pQ(z + a0)`, `H̃(z, y) = H(z + a0, y)`, `H̃'(z, y) = H'(z + a0, y)`
  let shiftA0 : MvPolynomial (Fin m) ℚ →ₐ[ℚ] MvPolynomial (Fin m) ℚ :=
    MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (a0 i))
  let pTilde : MvPolynomial (Fin m) ℚ := MvPolynomial.bind₁ (fun i => MvPolynomial.X i + MvPolynomial.C (a0 i)) pQ
  let C_Ht : RatCircuit (m + 1) := shiftVarsCircuit C_H (Fin.lastCases 0 a0)
  let C_Ht' : RatCircuit (m + 1) := shiftVarsCircuit C_H' (Fin.lastCases 0 a0)
  have hHt_poly : toLastPoly m C_Ht.evalPoly =
      (toLastPoly m C_H.evalPoly).map (MvPolynomial.bind₁ (fun i => MvPolynomial.X i + MvPolynomial.C (a0 i))) := by
    rw [shiftVarsCircuit_evalPoly, toLastPoly_shiftBase]
  have hHt'_poly : toLastPoly m C_Ht'.evalPoly = Polynomial.derivative (toLastPoly m C_Ht.evalPoly) := by
    rw [shiftVarsCircuit_evalPoly, toLastPoly_shiftBase, hCH'_poly, ← hCH_poly, hHt_poly,
        Polynomial.derivative_map]
  have hHt_root : MvPolynomial.bind₁ (Fin.lastCases pTilde MvPolynomial.X) C_Ht.evalPoly = 0 := by
    rw [← toLastPoly_eval, hHt_poly, Polynomial.eval_map]
    change Polynomial.eval₂ (MvPolynomial.bind₁ (fun i => MvPolynomial.X i + MvPolynomial.C (a0 i))).toRingHom
      ((MvPolynomial.bind₁ (fun i => MvPolynomial.X i + MvPolynomial.C (a0 i))).toRingHom pQ) (toLastPoly m C_H.evalPoly) = 0
    rw [Polynomial.eval₂_hom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hCH_poly, hHr_root, map_zero]
  have hHt'_unit : MvPolynomial.eval 0 (MvPolynomial.bind₁ (Fin.lastCases pTilde MvPolynomial.X) C_Ht'.evalPoly) ≠ 0 := by
    have hcomp : MvPolynomial.bind₁ (Fin.lastCases pTilde MvPolynomial.X) C_Ht'.evalPoly =
        MvPolynomial.bind₁ (fun i => MvPolynomial.X i + MvPolynomial.C (a0 i))
          (MvPolynomial.bind₁ (Fin.lastCases pQ MvPolynomial.X) C_H'.evalPoly) := by
      rw [← toLastPoly_eval, shiftVarsCircuit_evalPoly, toLastPoly_shiftBase, Polynomial.eval_map]
      change Polynomial.eval₂ (MvPolynomial.bind₁ (fun i => MvPolynomial.X i + MvPolynomial.C (a0 i))).toRingHom
        ((MvPolynomial.bind₁ (fun i => MvPolynomial.X i + MvPolynomial.C (a0 i))).toRingHom pQ) (toLastPoly m C_H'.evalPoly) = _
      rw [Polynomial.eval₂_hom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, toLastPoly_eval]
    rw [hcomp, eval_bind₁_eq]
    have hev : (fun i => MvPolynomial.eval (0 : Fin m → ℚ) (MvPolynomial.X i + MvPolynomial.C (a0 i))) = a0 := by
      ext i; simp
    rwa [hev]
  have hpTilde_deg : pTilde.totalDegree ≤ d := by
    have hdeg_bind : ∀ (f : MvPolynomial (Fin m) ℚ),
        (MvPolynomial.bind₁ (fun i => MvPolynomial.X i + MvPolynomial.C (a0 i)) f).totalDegree ≤ f.totalDegree := by
      intro f
      conv_lhs => rw [MvPolynomial.as_sum f]
      rw [map_sum]
      refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) (Finset.sup_le fun s hs => ?_)
      rw [MvPolynomial.monomial_eq, map_mul, MvPolynomial.bind₁_C_right, Finsupp.prod, map_prod]
      have h1 : (MvPolynomial.C (f.coeff s) * ∏ i ∈ s.support, (MvPolynomial.bind₁ (fun j => MvPolynomial.X j + MvPolynomial.C (a0 j)) (MvPolynomial.X i ^ s i))).totalDegree ≤
          (∏ i ∈ s.support, (MvPolynomial.X i + MvPolynomial.C (a0 i)) ^ s i).totalDegree := by
        refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
        simp only [MvPolynomial.totalDegree_C, zero_add, map_pow, MvPolynomial.bind₁_X_right, le_refl]
      refine le_trans h1 (le_trans (MvPolynomial.totalDegree_finsetProd _ _) ?_)
      have h2 : ∑ i ∈ s.support, ((MvPolynomial.X i + MvPolynomial.C (a0 i)) ^ s i).totalDegree ≤
          ∑ i ∈ s.support, s i := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hlin : (MvPolynomial.X i + MvPolynomial.C (a0 i)).totalDegree ≤ 1 :=
          le_trans (MvPolynomial.totalDegree_add _ _) (by simp)
        calc
          ((MvPolynomial.X i + MvPolynomial.C (a0 i)) ^ s i).totalDegree
              ≤ s i * (MvPolynomial.X i + MvPolynomial.C (a0 i)).totalDegree := MvPolynomial.totalDegree_pow _ _
          _ ≤ s i * 1 := Nat.mul_le_mul_left _ hlin
          _ = s i := mul_one _
      exact le_trans h2 (MvPolynomial.le_totalDegree hs)
    exact le_trans (hdeg_bind pQ) hpQ_deg
  -- Step 4: Coupled quadratic Newton iteration circuit `C_Y`
  let K := Nat.clog 2 (d + 1)
  let y0 := MvPolynomial.eval 0 pTilde
  let u0 := (MvPolynomial.eval 0 (MvPolynomial.bind₁ (Fin.lastCases pTilde MvPolynomial.X) C_Ht'.evalPoly))⁻¹
  let C_Y : RatCircuit m := newtonCircuit C_Ht C_Ht' y0 u0 K
  have hY_mod : ZeroMod (d + 1) (C_Y.evalPoly - pTilde) := by
    have h1 := (newtonIter_zeroMod C_Ht.evalPoly C_Ht'.evalPoly hHt'_poly pTilde hHt_root hHt'_unit K).1
    have hpow : d + 1 ≤ 2 ^ K := Nat.le_pow_clog (by omega) (d + 1)
    have h2 : ZeroMod (d + 1) (pTilde - C_Y.evalPoly) := by
      rw [newtonCircuit_evalPoly]; exact zeroMod_mono hpow h1
    simpa [neg_sub] using zeroMod_neg h2
  -- Step 5: Strassen homogenization up to degree `d` + unshift `z_i ↦ x_i - a0 i`
  obtain ⟨C_hom, hChom_size, hChom_eval⟩ := hrat_homog C_Y d
  have hChom_eq : C_hom.evalPoly = pTilde := by
    rw [hChom_eval, hsum_homog C_Y.evalPoly pTilde hpTilde_deg hY_mod]
  let C_p : RatCircuit m := shiftVarsCircuit C_hom (fun i => -a0 i)
  have hCp_eval : C_p.evalPoly = pQ := by
    rw [shiftVarsCircuit_evalPoly, hChom_eq]
    dsimp [pTilde]
    rw [MvPolynomial.bind₁_bind₁]
    have hid : (fun i => MvPolynomial.bind₁ (fun v => MvPolynomial.X v + MvPolynomial.C (-a0 v))
        (MvPolynomial.X i + MvPolynomial.C (a0 i))) = MvPolynomial.X := by
      ext i; simp [map_add, MvPolynomial.bind₁_X_right]
    rw [hid, MvPolynomial.bind₁_X_left]
    rfl
  -- Step 6: Clean polynomial size bound `C_p.size ≤ 1000 * (s + d + a + 2) ^ 6`
  refine ⟨C_p, ?_, fun x => by rw [hCp_eval]⟩
  have hK_le : K ≤ d + 1 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)
  have hCY_size : C_Y.size = 3 + K * newtonBlockSize (3 * ((d + 1) * (3 * g_circ.size) + (d + 1) + (d + 1))) := by
    have h1 : C_Ht.size = 3 * ((d + 1) * (3 * g_circ.size) + (d + 1) + (d + 1)) := rfl
    have h2 : C_Ht'.size = 3 * ((d + 1) * (3 * g_circ.size) + (d + 1) + (d + 1)) := rfl
    change 3 + K * newtonBlockSize (max C_Ht.size C_Ht'.size) = _
    rw [h1, h2, max_self]
  rw [hCY_size] at hChom_size
  exact ki04_size_arith s d a g_circ.size K C_hom.size hs_ge hK_le hChom_size

/-- **Unconditional Proof of `KI04_Cor_7_4`** from Lean's three standard axioms alone. -/
theorem ki04_cor_7_4_proved : KI04_Cor_7_4 :=
  ki04_cor_7_4_of_strassen
    ⟨fun Y p hp hmod => ExactMatching.Proofs.sum_homogeneousComponent_eq_of_zeroMod Y p hp hmod,
     fun C d => ExactMatching.Proofs.ratCircuit_homog_trunc C d⟩

end ExactMatching.Proofs.KI04Newton
