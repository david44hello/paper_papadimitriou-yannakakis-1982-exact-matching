/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import ExactMatching.Defs.Circuits
public import ExactMatching.Defs.Design
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Permanent

@[expose] public section

/-!
# Explicit quantitative PIT parameters, Ryser's formula, and hitting-set tests (Theorem 1 & Remark 1)

Defines the paper's exact-integer parameters and explicit PIT tests:
- `pitL s = ⌈log₂ s⌉`
- `pitT A s`: least integer `t ≥ 1` satisfying `t^4 ≥ (A * pitL s)^3`
- `pitMu A μ₀ s = max μ₀ (2 ^ pitT A s)`, `pitM A μ₀ s = (pitMu A μ₀ s)^2`
- `pitB0 s = 3 * s + s * ⌈log₂ s⌉ + 2`
- `pitB A μ₀ s = 3 * s + s * μ * ⌈log₂(s * μ^2)⌉ + 2`
- `ryserPerm`: Ryser's formula for the `μ × μ` permanent
- `pitSmallTest`, `pitLargeTest`, `pitEvalPointCount`: explicit modular evaluation tests and count
- `o26T`, `o26Mu`, `o26M`, `o26B`, `o26LargeTest`, `o26EvalPointCount`: Remark 1 parameters and test
-/

namespace ExactMatching

open scoped BigOperators

/-- `L = ⌈log₂ s⌉`, the bit-length of `s - 1` for `s ≥ 2`. -/
def pitL (s : ℕ) : ℕ := Nat.clog 2 s

/-- Existence of `t ≥ 1` with `t ^ 4 ≥ (A * pitL s) ^ 3`. -/
theorem pitT_exists (A s : ℕ) : ∃ t : ℕ, 1 ≤ t ∧ (A * pitL s) ^ 3 ≤ t ^ 4 := by
  refine ⟨A * pitL s + 1, Nat.succ_pos _, ?_⟩
  have h1 : A * pitL s ≤ A * pitL s + 1 := Nat.le_succ _
  calc
    (A * pitL s) ^ 3 ≤ (A * pitL s + 1) ^ 3 := Nat.pow_le_pow_left h1 3
    _ = (A * pitL s + 1) ^ 3 * 1 := (Nat.mul_one _).symm
    _ ≤ (A * pitL s + 1) ^ 3 * (A * pitL s + 1) :=
      Nat.mul_le_mul_left _ (Nat.succ_pos _)
    _ = (A * pitL s + 1) ^ 4 := by ring

/-- Least integer `t ≥ 1` satisfying `t ^ 4 ≥ (A * pitL s) ^ 3`. -/
def pitT (A s : ℕ) : ℕ := Nat.find (pitT_exists A s)

/-- Exact-integer parameter `μ = max(μ₀, 2 ^ t)`. -/
def pitMu (A μ₀ s : ℕ) : ℕ := max μ₀ (2 ^ pitT A s)

/-- Number of variables `m = μ ^ 2` of `PERM_μ`. -/
def pitM (A μ₀ s : ℕ) : ℕ := (pitMu A μ₀ s) ^ 2

/-- Small-input modulus exponent `B₀ = 3s + s⌈log₂ s⌉ + 2`. -/
def pitB0 (s : ℕ) : ℕ := 3 * s + s * Nat.clog 2 s + 2

/-- Large-input modulus exponent `B = 3s + s μ ⌈log₂(s μ²)⌉ + 2`. -/
def pitB (A μ₀ s : ℕ) : ℕ :=
  let μ := pitMu A μ₀ s
  3 * s + s * μ * Nat.clog 2 (s * μ ^ 2) + 2

/-- Ryser's formula for the `μ × μ` permanent over any commutative ring `R`:
`(-1)^μ ∑_{T ⊆ [μ]} (-1)^|T| ∏_{r=1}^μ ∑_{j ∈ T} M_{r, j}`. -/
def ryserPerm {μ : ℕ} {R : Type*} [CommRing R] (M : Matrix (Fin μ) (Fin μ) R) : R :=
  (-1 : R) ^ μ * ∑ T : Finset (Fin μ), (-1 : R) ^ T.card * ∏ r : Fin μ, ∑ j ∈ T, M r j

/-- Reshape a vector of length `μ ^ 2` into a `μ × μ` matrix in row-major order. -/
def matrixOfVec {μ : ℕ} {R : Type*} (v : Fin (μ ^ 2) → R) : Matrix (Fin μ) (Fin μ) R :=
  fun r c =>
    v ⟨r.val * μ + c.val, by
      have hμ : 0 < μ := Nat.pos_of_ne_zero (fun h => by subst h; exact Fin.elim0 r)
      calc
        r.val * μ + c.val < r.val * μ + μ := Nat.add_lt_add_left c.isLt _
        _ = (r.val + 1) * μ := by ring
        _ ≤ μ * μ := Nat.mul_le_mul_right _ r.isLt
        _ = μ ^ 2 := by ring⟩

/-- Canonical bijection `Fin μ × Fin μ ≃ Fin (μ ^ 2)` matching `matrixOfVec`. -/
def finPairEquivSq (μ : ℕ) : Fin μ × Fin μ ≃ Fin (μ ^ 2) where
  toFun p := ⟨p.1.val * μ + p.2.val, by
    have hμ : 0 < μ := Nat.pos_of_ne_zero (fun h => by subst h; exact Fin.elim0 p.1)
    calc
      p.1.val * μ + p.2.val < p.1.val * μ + μ := Nat.add_lt_add_left p.2.isLt _
      _ = (p.1.val + 1) * μ := by ring
      _ ≤ μ * μ := Nat.mul_le_mul_right _ p.1.isLt
      _ = μ ^ 2 := by ring⟩
  invFun k :=
    have hμ : 0 < μ := by
      by_contra h
      push Not at h
      have h0 : μ = 0 := Nat.le_zero.mp h
      subst h0
      exact Fin.elim0 k
    (⟨k.val / μ, Nat.div_lt_of_lt_mul (by simpa [sq] using k.isLt)⟩,
     ⟨k.val % μ, Nat.mod_lt k.val hμ⟩)
  left_inv p := by
    have hμ : 0 < μ := Nat.pos_of_ne_zero (fun h => by subst h; exact Fin.elim0 p.1)
    ext
    · simp only
      rw [Nat.mul_comm p.1.val μ, Nat.mul_add_div hμ, Nat.div_eq_of_lt p.2.isLt, Nat.add_zero]
    · simp only
      rw [Nat.mul_comm p.1.val μ, Nat.mul_add_mod, Nat.mod_eq_of_lt p.2.isLt]
  right_inv k := by
    have hμ : 0 < μ := by
      by_contra h
      push Not at h
      have h0 : μ = 0 := Nat.le_zero.mp h
      subst h0
      exact Fin.elim0 k
    ext
    simp only
    rw [Nat.mul_comm, Nat.div_add_mod]

/-- Small-input PIT test (`s < s₀`): `C` evaluates to `0 (mod 2^{B₀})` on every grid point
`a ∈ {0, 1, ..., s}^s`. -/
def pitSmallTest (s : ℕ) (C : IntCircuit s) : Prop :=
  ∀ a : Fin s → Fin (s + 1),
    C.evalAt (ZMod (2 ^ pitB0 s)) (fun i => ((a i).val : ZMod (2 ^ pitB0 s))) = 0

/-- Generic large-input NW-permanent modular test for parameter `μ` (`m = μ² ≥ 2`) and
modulus exponent `B`: `C` evaluates to `0 (mod 2^B)` at `v_i = ryserPerm(a|_{S_i})` for
every `a ∈ {0, 1, ..., s μ}^l`. -/
def nwPermModTest (μ B s : ℕ) (hm : 2 ≤ μ ^ 2)
    (hcard : ∀ i : Fin s, (designSets (μ ^ 2) s hm i).card = μ ^ 2)
    (C : IntCircuit s) : Prop :=
  let m := μ ^ 2
  let l := designL m
  let S := designSets m s hm
  ∀ a : Fin l → Fin (s * μ + 1),
    C.evalAt (ZMod (2 ^ B))
      (fun i =>
        let sub : Fin (μ ^ 2) → ℤ := fun j => ((a ((S i).orderEmbOfFin (hcard i) j)).val : ℤ)
        ((ryserPerm (R := ℤ) (matrixOfVec sub) : ℤ) : ZMod (2 ^ B))) = 0

/-- Large-input PIT test (`s ≥ s₀`): `C` evaluates to `0 (mod 2^B)` at
`v_i = ryserPerm(a|_{S_i})` for every `a ∈ {0, 1, ..., s μ}^l`, where `S₁, ..., S_s`
is the explicit polynomial-graph design of Lemma 2.1. -/
def pitLargeTest (A μ₀ s : ℕ) (hm : 2 ≤ pitM A μ₀ s)
    (hcard : ∀ i : Fin s, (designSets (pitM A μ₀ s) s hm i).card = pitM A μ₀ s)
    (C : IntCircuit s) : Prop :=
  nwPermModTest (pitMu A μ₀ s) (pitB A μ₀ s) s hm hcard C

/-- Exact count of evaluation points tested by the PIT algorithm on parameter `s`. -/
def pitEvalPointCount (A μ₀ s₀ s : ℕ) : ℕ :=
  if s < s₀ then (s + 1) ^ s
  else (s * pitMu A μ₀ s + 1) ^ designL (pitM A μ₀ s)

/-- Existence of `t ≥ 1` with `t ^ 2 ≥ C₁ ^ 2 * ⌈log₂ s⌉ * ⌈log₂ log₂(s + 2)⌉ ^ 2`
(Remark 1 exact-integer parameter). -/
theorem o26T_exists (C₁ s : ℕ) :
    ∃ t : ℕ, 1 ≤ t ∧
      C₁ ^ 2 * Nat.clog 2 s * (Nat.clog 2 (Nat.clog 2 (s + 2))) ^ 2 ≤ t ^ 2 := by
  let b := C₁ * Nat.clog 2 s * Nat.clog 2 (Nat.clog 2 (s + 2)) + 1
  refine ⟨b, Nat.succ_pos _, ?_⟩
  have h1 : C₁ * Nat.clog 2 s * Nat.clog 2 (Nat.clog 2 (s + 2)) ≤ b := Nat.le_succ _
  have h2 : C₁ ^ 2 * Nat.clog 2 s * (Nat.clog 2 (Nat.clog 2 (s + 2))) ^ 2 ≤
      (C₁ * Nat.clog 2 s * Nat.clog 2 (Nat.clog 2 (s + 2))) ^ 2 := by
    have hL : Nat.clog 2 s ≤ (Nat.clog 2 s) ^ 2 := by
      simpa [sq] using Nat.le_mul_self (Nat.clog 2 s)
    calc
      C₁ ^ 2 * Nat.clog 2 s * (Nat.clog 2 (Nat.clog 2 (s + 2))) ^ 2
          = C₁ ^ 2 * (Nat.clog 2 (Nat.clog 2 (s + 2))) ^ 2 * Nat.clog 2 s := by ring
      _ ≤ C₁ ^ 2 * (Nat.clog 2 (Nat.clog 2 (s + 2))) ^ 2 * (Nat.clog 2 s) ^ 2 :=
          Nat.mul_le_mul_left _ hL
      _ = (C₁ * Nat.clog 2 s * Nat.clog 2 (Nat.clog 2 (s + 2))) ^ 2 := by ring
  exact le_trans h2 (Nat.pow_le_pow_left h1 2)

/-- Least integer `t ≥ 1` for Remark 1's `[O26]` tradeoff. -/
def o26T (C₁ s : ℕ) : ℕ := Nat.find (o26T_exists C₁ s)

/-- Exact-integer parameter `μ = max(N₀, 2 ^ t)` for Remark 1. -/
def o26Mu (C₁ N₀ s : ℕ) : ℕ := max N₀ (2 ^ o26T C₁ s)

/-- Number of variables `m = μ ^ 2` for Remark 1. -/
def o26M (C₁ N₀ s : ℕ) : ℕ := (o26Mu C₁ N₀ s) ^ 2

/-- Large-input modulus exponent `B = 3s + s μ ⌈log₂(s μ²)⌉ + 2` for Remark 1. -/
def o26B (C₁ N₀ s : ℕ) : ℕ :=
  let μ := o26Mu C₁ N₀ s
  3 * s + s * μ * Nat.clog 2 (s * μ ^ 2) + 2

/-- Large-input PIT test for Remark 1 (`[O26]` parameters). -/
def o26LargeTest (C₁ N₀ s : ℕ) (hm : 2 ≤ o26M C₁ N₀ s)
    (hcard : ∀ i : Fin s, (designSets (o26M C₁ N₀ s) s hm i).card = o26M C₁ N₀ s)
    (C : IntCircuit s) : Prop :=
  nwPermModTest (o26Mu C₁ N₀ s) (o26B C₁ N₀ s) s hm hcard C

/-- Exact count of evaluation points for Remark 1 (`[O26]` parameters). -/
def o26EvalPointCount (C₁ N₀ s₀ s : ℕ) : ℕ :=
  if s < s₀ then (s + 1) ^ s
  else (s * o26Mu C₁ N₀ s + 1) ^ designL (o26M C₁ N₀ s)

end ExactMatching
