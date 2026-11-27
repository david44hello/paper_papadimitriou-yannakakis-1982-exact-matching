/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Rat.Defs
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.LinearAlgebra.Matrix.Permanent

@[expose] public section

/-!
# Arithmetic circuits over `ℚ` and `ℤ`, permanent polynomials, and Hypothesis `H(c)`

Defines:
- `expTwo`: base-2 exponential `2 ^ t`.
- `Computes`, `perm`, `hc`, `Beyond`: copied token-for-token from `[A26]` `Statement.lean` (p. 11).
- `paperPerm`: the permanent polynomial `∑ σ, ∏ i, X (i, σ i)` as printed in the paper.
- `HypothesisH`: Hypothesis `H(c)` parameterized by `c > 0` and threshold `μ₀ ≥ 1`, stated using
  the paper's `paperPerm`.
- `O26ExactComputes`: exact arithmetic circuit model of `[O26]` (p. 2), with binary `+`, `-`, `×`
  gates and free variables and scalars.
- `IntGate`, `IntCircuit`: division-free arithmetic circuits over `ℤ` with binary gates `+`, `-`,
  `×`, integer constants written in binary, and explicit binary encoding length.
- `RatGate`, `RatCircuit`: strictly division-free arithmetic circuits over `ℚ` matching `[KI04]`
  Section 2.3 (p. 12): binary `+`, `-`, `×`, rational constants, and multiplication by constants.
-/

namespace ExactMatching

open MvPolynomial
open scoped BigOperators

universe u

/-- Base-2 exponential `exp₂(t) = 2 ^ t`. -/
noncomputable def expTwo (t : ℝ) : ℝ := (2 : ℝ) ^ t

/-- `f` has an arithmetic circuit with at most `s` gates: a list of `s` polynomials contains `f`, and each of
them is a variable, a constant, or the sum or product of two earlier ones (possibly the same one). Variables and
constants count as gates. -/
def Computes {R : Type u} {V : Type} [CommSemiring R] (f : MvPolynomial V R) (s : ℕ) : Prop :=
  ∃ l : ℕ → MvPolynomial V R,
    (∀ k < s, (∃ v : V, l k = X v) ∨ (∃ a : R, l k = C a) ∨
      (∃ i < k, ∃ j < k, l k = l i + l j) ∨ (∃ i < k, ∃ j < k, l k = l i * l j)) ∧
    ∃ k < s, l k = f

/-- The permanent of the generic `m × m` matrix. -/
noncomputable def perm (F : Type u) [CommSemiring F] (m : ℕ) : MvPolynomial (Fin m × Fin m) F :=
  ∑ σ : Equiv.Perm (Fin m), ∏ i, X (σ i, i)

open Classical in
/-- The Hamiltonian cycle polynomial: the sum over the permutations with a single cycle through all points. -/
noncomputable def hc (F : Type u) [CommSemiring F] (m : ℕ) : MvPolynomial (Fin m × Fin m) F :=
  ∑ σ : Equiv.Perm (Fin m) with σ.IsCycleOn Set.univ, ∏ i, X (i, σ i)

/-- More than `m ^ (c * (log₂ m) ^ (1/3))` gates. -/
def Beyond (c : ℝ) (m s : ℕ) : Prop := (m : ℝ) ^ (c * Real.logb 2 m ^ (1 / 3 : ℝ)) < s

/-- The `μ × μ` permanent polynomial as printed in the paper:
`PERM_μ(X) = ∑_{σ ∈ S_μ} ∏_{i=1}^μ X_{i, σ(i)}`. -/
noncomputable def paperPerm (R : Type u) [CommSemiring R] (μ : ℕ) :
    MvPolynomial (Fin μ × Fin μ) R :=
  ∑ σ : Equiv.Perm (Fin μ), ∏ i : Fin μ, MvPolynomial.X (i, σ i)

/-- Hypothesis `H(c)` with explicit constant `c > 0` and threshold `μ₀ ≥ 1`:
for every `μ ≥ μ₀`, every arithmetic circuit over `ℚ` computing `paperPerm ℚ μ` has
strictly more than `μ ^ (c * (log₂ μ) ^ (1/3))` gates. -/
def HypothesisH (c : ℝ) (μ₀ : ℕ) : Prop :=
  0 < c ∧ 1 ≤ μ₀ ∧ ∀ μ ≥ μ₀, ∀ s : ℕ, Computes (paperPerm ℚ μ) s → Beyond c μ s

/-- `[O26]` exact arithmetic circuit model (p. 2): at most `s` binary gates (`+`, `-`, `×`),
with variables and scalar inputs free (not counted toward `s`). -/
def O26ExactComputes {R : Type u} {V : Type} [CommRing R] (f : MvPolynomial V R) (s : ℕ) : Prop :=
  ∃ (n : ℕ) (l : ℕ → MvPolynomial V R) (isBin : ℕ → Bool),
    (∀ k < n,
      if isBin k then
        (∃ i < k, ∃ j < k, l k = l i + l j) ∨
        (∃ i < k, ∃ j < k, l k = l i - l j) ∨
        (∃ i < k, ∃ j < k, l k = l i * l j)
      else
        (∃ v : V, l k = MvPolynomial.X v) ∨ (∃ a : R, l k = MvPolynomial.C a)) ∧
    ((Finset.range n).filter (fun k => isBin k = true)).card ≤ s ∧
    ∃ k < n, l k = f

/-- A polynomial `p` is multilinear if every variable has degree at most `1` in every
monomial in its support. -/
def IsMultilinear {V : Type*} {R : Type*} [CommSemiring R] (p : MvPolynomial V R) : Prop :=
  ∀ d ∈ p.support, ∀ v : V, d v ≤ 1

/-- Every integer coefficient of `f` has magnitude at most `2 ^ b` (bit-length at most `b`). -/
def CoeffBitBound {V : Type*} (f : MvPolynomial V ℤ) (b : ℕ) : Prop :=
  ∀ d : V →₀ ℕ, (f.coeff d).natAbs ≤ 2 ^ b

/-- Binary bit-length of an integer constant (at least `1`). -/
def intBitLen (a : ℤ) : ℕ :=
  Nat.clog 2 (a.natAbs + 1) + 1

/-- A single gate of an arithmetic circuit over `ℤ` in `n` input variables. -/
inductive IntGate (n : ℕ) where
  | var (v : Fin n)
  | const (a : ℤ)
  | add (i j : ℕ)
  | sub (i j : ℕ)
  | mul (i j : ℕ)
  deriving DecidableEq

/-- Well-formedness of gate `k`: binary inputs reference strictly earlier gates. -/
def IntGate.WF {n : ℕ} (k : ℕ) : IntGate n → Prop
  | .var _ => True
  | .const _ => True
  | .add i j => i < k ∧ j < k
  | .sub i j => i < k ∧ j < k
  | .mul i j => i < k ∧ j < k

/-- Encoding bit-cost of a single gate (tag + variable/gate indices or binary constant). -/
def IntGate.bitCost {n : ℕ} : IntGate n → ℕ
  | .var v => Nat.clog 2 (v.val + 2) + 1
  | .const a => intBitLen a + 1
  | .add i j => Nat.clog 2 (i + 2) + Nat.clog 2 (j + 2) + 2
  | .sub i j => Nat.clog 2 (i + 2) + Nat.clog 2 (j + 2) + 2
  | .mul i j => Nat.clog 2 (i + 2) + Nat.clog 2 (j + 2) + 2

/-- A division-free arithmetic circuit over `ℤ` in `n` variables with binary gates `+`, `-`, `×`
and integer constants written in binary. -/
structure IntCircuit (n : ℕ) where
  size : ℕ
  size_pos : 0 < size
  gate : Fin size → IntGate n
  wf : ∀ k : Fin size, (gate k).WF k.val
  out : Fin size

namespace IntCircuit

/-- Total binary encoding length of an integer arithmetic circuit (bounds both gate count
and total bit-length of all integer constants inside the circuit). -/
def encodingLength {n : ℕ} (C : IntCircuit n) : ℕ :=
  ∑ k : Fin C.size, (C.gate k).bitCost

/-- Every integer constant in `C` belongs to `{-1, 0, 1}`. -/
def UsesOnlyUnitConstants {n : ℕ} (C : IntCircuit n) : Prop :=
  ∀ k : Fin C.size, ∀ a : ℤ, C.gate k = .const a → a = 0 ∨ a = 1 ∨ a = -1

/-- Value of gate `k` when evaluated in any commutative ring `R` at input assignment `x`. -/
def evalGateAt {n : ℕ} {R : Type*} [CommRing R] (C : IntCircuit n) (x : Fin n → R) :
    Fin C.size → R :=
  fun k =>
    WellFounded.fix (InvImage.wf Fin.val Nat.lt_wfRel.wf)
      (fun k rec =>
        match h : C.gate k with
        | .var v => x v
        | .const a => (a : R)
        | .add i j =>
          have hwf := C.wf k
          have hi : i < k.val := by rw [h] at hwf; exact hwf.1
          have hj : j < k.val := by rw [h] at hwf; exact hwf.2
          rec ⟨i, Nat.lt_trans hi k.isLt⟩ hi + rec ⟨j, Nat.lt_trans hj k.isLt⟩ hj
        | .sub i j =>
          have hwf := C.wf k
          have hi : i < k.val := by rw [h] at hwf; exact hwf.1
          have hj : j < k.val := by rw [h] at hwf; exact hwf.2
          rec ⟨i, Nat.lt_trans hi k.isLt⟩ hi - rec ⟨j, Nat.lt_trans hj k.isLt⟩ hj
        | .mul i j =>
          have hwf := C.wf k
          have hi : i < k.val := by rw [h] at hwf; exact hwf.1
          have hj : j < k.val := by rw [h] at hwf; exact hwf.2
          rec ⟨i, Nat.lt_trans hi k.isLt⟩ hi * rec ⟨j, Nat.lt_trans hj k.isLt⟩ hj)
      k

/-- Output value of circuit `C` evaluated in commutative ring `R` at input `x`. -/
def evalAt {n : ℕ} (R : Type*) [CommRing R] (C : IntCircuit n) (x : Fin n → R) : R :=
  C.evalGateAt x C.out

/-- Formal polynomial in `ℤ[y_1, ..., y_n]` computed by circuit `C`. -/
noncomputable def evalPoly {n : ℕ} (C : IntCircuit n) : MvPolynomial (Fin n) ℤ :=
  C.evalAt (MvPolynomial (Fin n) ℤ) MvPolynomial.X

end IntCircuit

/-- A strictly division-free arithmetic gate over `ℚ` in `n` variables, matching `[KI04]`
Section 2.3 (p. 12): `+`, `-`, `×`, rational constants, and scalar multiplication by constants. -/
inductive RatGate (n : ℕ) where
  | var (v : Fin n)
  | const (a : ℚ)
  | add (i j : ℕ)
  | sub (i j : ℕ)
  | mul (i j : ℕ)
  | smul (a : ℚ) (i : ℕ)
  deriving DecidableEq

/-- Well-formedness of a `RatGate` at index `k`. -/
def RatGate.WF {n : ℕ} (k : ℕ) : RatGate n → Prop
  | .var _ => True
  | .const _ => True
  | .add i j => i < k ∧ j < k
  | .sub i j => i < k ∧ j < k
  | .mul i j => i < k ∧ j < k
  | .smul _ i => i < k

/-- Strictly division-free arithmetic circuit over `ℚ` (`[KI04]` Section 2.3). -/
structure RatCircuit (n : ℕ) where
  size : ℕ
  size_pos : 0 < size
  gate : Fin size → RatGate n
  wf : ∀ k : Fin size, (gate k).WF k.val
  out : Fin size

namespace RatCircuit

/-- Formal polynomial computed by gate `k` of a `RatCircuit`. -/
noncomputable def evalGatePoly {n : ℕ} (C : RatCircuit n) :
    Fin C.size → MvPolynomial (Fin n) ℚ :=
  fun k =>
    WellFounded.fix (InvImage.wf Fin.val Nat.lt_wfRel.wf)
      (fun k rec =>
        match h : C.gate k with
        | .var v => MvPolynomial.X v
        | .const a => MvPolynomial.C a
        | .add i j =>
          have hwf := C.wf k
          have hi : i < k.val := by rw [h] at hwf; exact hwf.1
          have hj : j < k.val := by rw [h] at hwf; exact hwf.2
          rec ⟨i, Nat.lt_trans hi k.isLt⟩ hi + rec ⟨j, Nat.lt_trans hj k.isLt⟩ hj
        | .sub i j =>
          have hwf := C.wf k
          have hi : i < k.val := by rw [h] at hwf; exact hwf.1
          have hj : j < k.val := by rw [h] at hwf; exact hwf.2
          rec ⟨i, Nat.lt_trans hi k.isLt⟩ hi - rec ⟨j, Nat.lt_trans hj k.isLt⟩ hj
        | .mul i j =>
          have hwf := C.wf k
          have hi : i < k.val := by rw [h] at hwf; exact hwf.1
          have hj : j < k.val := by rw [h] at hwf; exact hwf.2
          rec ⟨i, Nat.lt_trans hi k.isLt⟩ hi * rec ⟨j, Nat.lt_trans hj k.isLt⟩ hj
        | .smul a i =>
          have hwf := C.wf k
          have hi : i < k.val := by rw [h] at hwf; exact hwf
          MvPolynomial.C a * rec ⟨i, Nat.lt_trans hi k.isLt⟩ hi)
      k

/-- Output formal polynomial in `ℚ[x_1, ..., x_n]` computed by a `RatCircuit`. -/
noncomputable def evalPoly {n : ℕ} (C : RatCircuit n) : MvPolynomial (Fin n) ℚ :=
  C.evalGatePoly C.out

end RatCircuit

end ExactMatching
