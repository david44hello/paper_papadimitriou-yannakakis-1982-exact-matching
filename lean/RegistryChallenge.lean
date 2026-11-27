-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Mathlib

@[expose] public section

/-! # Exact Matching from permanent lower bounds
The five statements cover test correctness, evaluation counts, matching decision and witness recovery. -/

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
end ExactMatching

namespace ExactMatching

open scoped BigOperators

/-- Exponent `r = ⌈log₂ m⌉` so that `q = 2 ^ r` is the least power of `2` with `q ≥ m`. -/
def designR (m : ℕ) : ℕ := Nat.clog 2 m

/-- Field size `q = 2 ^ r` (least power of `2` with `q ≥ m`). -/
def designQ (m : ℕ) : ℕ := 2 ^ designR m

/-- Ambient universe size `l = m * q`. -/
def designL (m : ℕ) : ℕ := m * designQ m

/-- Polynomial degree bound `t = ⌈log₂ n / log₂ q⌉ = Nat.clog q n`. -/
def designT (m n : ℕ) : ℕ := Nat.clog (designQ m) n

theorem designR_ne_zero_of_two_le {m : ℕ} (hm : 2 ≤ m) : designR m ≠ 0 :=
  Nat.ne_of_gt (Nat.clog_pos (Nat.lt_succ_self 1) hm)

theorem le_designQ (m : ℕ) : m ≤ designQ m :=
  (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp le_rfl

theorem designQ_gt_one_of_two_le {m : ℕ} (hm : 2 ≤ m) : 1 < designQ m :=
  lt_of_lt_of_le (show 1 < m from hm) (le_designQ m)

theorem n_le_designQ_pow_designT {m n : ℕ} (hm : 2 ≤ m) :
    n ≤ designQ m ^ designT m n :=
  (Nat.clog_le_iff_le_pow (designQ_gt_one_of_two_le hm)).mp le_rfl

/-- Canonical finite field `𝔽_q` of order `q = designQ m` (for `m ≥ 2`). -/
abbrev DesignField (m : ℕ) := GaloisField 2 (designR m)

noncomputable instance instFintypeDesignField (m : ℕ) : Fintype (DesignField m) :=
  Fintype.ofFinite (DesignField m)

/-- Cardinality of `DesignField m` equals `designQ m` for `m ≥ 2`. -/
theorem card_designField {m : ℕ} (hm : 2 ≤ m) :
    Fintype.card (DesignField m) = designQ m := by
  rw [← Nat.card_eq_fintype_card]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact GaloisField.card 2 (designR m) (designR_ne_zero_of_two_le hm)

/-- Canonical bijection `DesignField m ≃ Fin (designQ m)` for `m ≥ 2`. -/
noncomputable def designFieldEquiv {m : ℕ} (hm : 2 ≤ m) :
    DesignField m ≃ Fin (designQ m) :=
  Fintype.equivFinOfCardEq (card_designField hm)

/-- Univariate polynomial `h ∈ 𝔽_q[z]` of degree `< t` from its coefficient vector. -/
noncomputable def polyOfCoeffs {m t : ℕ} (c : Fin t → DesignField m) :
    Polynomial (DesignField m) :=
  ∑ j : Fin t, Polynomial.C (c j) * Polynomial.X ^ j.val

/-- Graph set `S_h = {(u, h(u)) : u ∈ A} ⊆ A × 𝔽_q ≃ Fin (designL m)` of a polynomial `h`,
where `A` consists of the first `m` elements of `𝔽_q`. -/
noncomputable def polyGraphSet {m t : ℕ} (hm : 2 ≤ m) (c : Fin t → DesignField m) :
    Finset (Fin (designL m)) :=
  let e := designFieldEquiv hm
  let h := polyOfCoeffs c
  Finset.univ.image fun u : Fin m =>
    let uF : DesignField m := e.symm ⟨u.val, Nat.lt_of_lt_of_le u.isLt (le_designQ m)⟩
    let y : Fin (designQ m) := e (h.eval uF)
    ⟨u.val * designQ m + y.val, by
      have hq : 0 < designQ m := Nat.lt_trans Nat.zero_lt_one (designQ_gt_one_of_two_le hm)
      calc
        u.val * designQ m + y.val < u.val * designQ m + designQ m := Nat.add_lt_add_left y.isLt _
        _ = (u.val + 1) * designQ m := by ring
        _ ≤ m * designQ m := Nat.mul_le_mul_right _ u.isLt⟩

/-- Canonical enumeration of coefficient vectors `Fin t → DesignField m` into `Fin (q ^ t)`. -/
noncomputable def coeffVecEquiv {m t : ℕ} (hm : 2 ≤ m) :
    (Fin t → DesignField m) ≃ Fin (designQ m ^ t) :=
  Fintype.equivFinOfCardEq (by
    rw [Fintype.card_fun, card_designField hm, Fintype.card_fin])

/-- Explicit family `S₁, ..., Sₙ ⊆ Fin (designL m)` of Lemma 2.1: the graph sets of the
first `n` polynomials of degree `< designT m n` over `𝔽_{designQ m}`. -/
noncomputable def designSets (m n : ℕ) (hm : 2 ≤ m) :
    Fin n → Finset (Fin (designL m)) :=
  fun i =>
    let idx : Fin (designQ m ^ designT m n) :=
      ⟨i.val, Nat.lt_of_lt_of_le i.isLt (n_le_designQ_pow_designT hm)⟩
    polyGraphSet hm ((coeffVecEquiv hm).symm idx)

end ExactMatching

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

end ExactMatching

namespace ExactMatching

open scoped BigOperators

/-- Ordered pairs `(u, v)` with `u < v` in `Fin n` (upper-triangular entries). -/
abbrev UpperPair (n : ℕ) := { p : Fin n × Fin n // p.1 < p.2 }

/-- A set of undirected edges `M` is a perfect matching of `G` if every edge belongs to `G`
and every vertex is incident to a unique edge in `M`. -/
def IsPerfectMatching {n : ℕ} (G : SimpleGraph (Fin n)) (M : Finset (Sym2 (Fin n))) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧ ∀ v : Fin n, (M.filter (fun e => v ∈ e)).card = 1

/-- The first slot of pair `i` is an index of the full permutation. -/
theorem pairingEvenIndexLt {k : ℕ} (i : Fin k) : 2 * i.val < 2 * k :=
  Nat.mul_lt_mul_of_pos_left i.isLt (Nat.zero_lt_succ 1)

/-- The second slot of pair `i` is also an index of the full permutation. -/
theorem pairingOddIndexLt {k : ℕ} (i : Fin k) : 2 * i.val + 1 < 2 * k := by
  calc
    2 * i.val + 1 < 2 * i.val + 2 := Nat.lt_succ_self _
    _ = 2 * (i.val + 1) := (Nat.mul_succ 2 i.val).symm
    _ ≤ 2 * k := Nat.mul_le_mul_left 2 i.isLt

/-- A canonical pairing of `Fin (2 * k)` into `k` disjoint ordered pairs
`(u_0, v_0), ..., (u_{k-1}, v_{k-1})` with `u_i < v_i` and `u_0 < u_1 < ... < u_{k-1}`. -/
structure OrderedPairing (k : ℕ) where
  perm : Equiv.Perm (Fin (2 * k))
  pair_lt : ∀ i : Fin k,
    perm ⟨2 * i.val, pairingEvenIndexLt i⟩ < perm ⟨2 * i.val + 1, pairingOddIndexLt i⟩
  fst_mono : ∀ i j : Fin k, i < j →
    perm ⟨2 * i.val, pairingEvenIndexLt i⟩ < perm ⟨2 * j.val, pairingEvenIndexLt j⟩

instance instDecidableEqOrderedPairing (k : ℕ) : DecidableEq (OrderedPairing k) :=
  fun a b =>
    if h : a.perm = b.perm then
      isTrue (by cases a; cases b; cases h; rfl)
    else
      isFalse (fun hab => h (by cases hab; rfl))

/-- `OrderedPairing k` embeds into `Equiv.Perm (Fin (2 * k))`, hence is finite. -/
noncomputable instance instFintypeOrderedPairing (k : ℕ) : Fintype (OrderedPairing k) :=
  Fintype.ofInjective (fun m : OrderedPairing k => m.perm) (fun a b h => by
    cases a; cases b; cases h; rfl)

/-- Sign `sgn(M) ∈ {-1, 1}` of an ordered perfect matching of `K_{2k}`. -/
def OrderedPairing.sign {k : ℕ} (m : OrderedPairing k) : ℤ :=
  (Equiv.Perm.sign m.perm : ℤ)

/-- Underlying edge finset of an ordered pairing of `K_{2k}`. -/
def OrderedPairing.edgeFinset {k : ℕ} (m : OrderedPairing k) : Finset (Sym2 (Fin (2 * k))) :=
  Finset.univ.image fun i : Fin k =>
    s(m.perm ⟨2 * i.val, pairingEvenIndexLt i⟩, m.perm ⟨2 * i.val + 1, pairingOddIndexLt i⟩)

/-- The Pfaffian of a `(2k) × (2k)` matrix `M` over any commutative ring `R`, defined by its
universal matching sum `∑_M sgn(M) ∏_{{u,v} ∈ M, u < v} M_{u, v}`. -/
noncomputable def pfaffian {k : ℕ} {R : Type*} [CommRing R]
    (M : Matrix (Fin (2 * k)) (Fin (2 * k)) R) : R :=
  ∑ m : OrderedPairing k,
    (m.sign : R) * ∏ i : Fin k, M (m.perm ⟨2 * i.val, pairingEvenIndexLt i⟩) (m.perm ⟨2 * i.val + 1, pairingOddIndexLt i⟩)

/-- Upper-triangular edges of a graph `G` on `Fin n`. -/
abbrev UpperEdge {n : ℕ} (G : SimpleGraph (Fin n)) :=
  { p : UpperPair n // G.Adj p.val.1 p.val.2 }

/-- The Tutte matrix `T` of `(G, w)` over `ℤ[Γ][{x_e : e ∈ E(G)}]`:
for `u < v` with `{u, v} ∈ E`, `T_{uv} = x_e · e_{w(e)}`, `T_{vu} = -T_{uv}`, and `0` otherwise. -/
noncomputable def tutteMatrix {n : ℕ} {Γ : Type*} [AddCommGroup Γ] [DecidableEq Γ]
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : UpperEdge G → Γ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (UpperEdge G) (AddMonoidAlgebra ℤ Γ)) :=
  fun u v =>
    if hlt : u < v then
      if hadj : G.Adj u v then
        MvPolynomial.C (AddMonoidAlgebra.single (w ⟨⟨(u, v), hlt⟩, hadj⟩) 1) *
          MvPolynomial.X ⟨⟨(u, v), hlt⟩, hadj⟩
      else 0
    else if hgt : v < u then
      if hadj : G.Adj v u then
        -(MvPolynomial.C (AddMonoidAlgebra.single (w ⟨⟨(v, u), hgt⟩, hadj⟩) 1) *
          MvPolynomial.X ⟨⟨(v, u), hgt⟩, hadj⟩)
      else 0
    else 0

/-- Extract the `e_γ`-coordinate polynomial `P_γ(x) ∈ ℤ[x]` from a polynomial
`F ∈ (ℤ[Γ])[x]`. -/
noncomputable def extractGroupCoeff {E Γ : Type*} [AddCommGroup Γ] [DecidableEq Γ]
    (γ : Γ) (F : MvPolynomial E (AddMonoidAlgebra ℤ Γ)) : MvPolynomial E ℤ :=
  ∑ d ∈ F.support, MvPolynomial.monomial d ((AddMonoidAlgebra.coeffAddEquiv (F.coeff d)) γ)

/-- The polynomial `P_{γ*}(x) ∈ ℤ[{x_e : e ∈ E(G)}]` extracted from `Pf(T)` at `e_{γ*}`. -/
noncomputable def groupRingPoly {k : ℕ} {Γ : Type*} [AddCommGroup Γ] [DecidableEq Γ]
    (G : SimpleGraph (Fin (2 * k))) [DecidableRel G.Adj]
    (w : UpperEdge G → Γ) (γstar : Γ) : MvPolynomial (UpperEdge G) ℤ :=
  extractGroupCoeff γstar (pfaffian (tutteMatrix G w))

/-- Delete a single edge `e` from a simple graph `H`. -/
def deleteEdge {n : ℕ} (H : SimpleGraph (Fin n)) (e : Sym2 (Fin n)) : SimpleGraph (Fin n) where
  Adj u v := H.Adj u v ∧ s(u, v) ≠ e
  symm := ⟨fun _ _ h => ⟨H.symm.symm _ _ h.1, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun _ h => H.loopless.irrefl _ h.1⟩

/-- Explicit edge-deletion self-reduction of Theorem 2(c): starting from `H = G`,
iterates over `edges`, deleting `e` whenever `oracle (deleteEdge H e) = true`. -/
def selfReduce {n : ℕ} (oracle : SimpleGraph (Fin n) → Bool)
    (G : SimpleGraph (Fin n)) (edges : List (Sym2 (Fin n))) : SimpleGraph (Fin n) :=
  edges.foldl
    (fun H e =>
      let H' := deleteEdge H e
      if oracle H' then H' else H)
    G

/-- Exact Matching cyclic-group labeling into `ZMod (k + 1)` for `n = 2 * k` vertices
(red edges get `1`, blue edges get `0`). -/
def exactMatchingLabel {k : ℕ} (G : SimpleGraph (Fin (2 * k)))
    (R : Finset (Sym2 (Fin (2 * k)))) (e : UpperEdge G) : ZMod (k + 1) :=
  if s(e.val.val.1, e.val.val.2) ∈ R then 1 else 0

/-- Bounded integer-weight shifted cyclic-group labeling into `ZMod (2 * k * W + 1)`
for `n = 2 * k` vertices and `w : UpperEdge G → ℤ` with `|w(e)| ≤ W`. -/
def boundedWeightLabel {k : ℕ} (W : ℕ) (G : SimpleGraph (Fin (2 * k)))
    (w : UpperEdge G → ℤ) (e : UpperEdge G) : ZMod (2 * k * W + 1) :=
  ((w e + (W : ℤ)) : ZMod (2 * k * W + 1))

/-- Embed `UpperEdge H` into `Fin s` (adding dummy variables up to `s`) when `|E(H)| ≤ s`. -/
noncomputable def upperEdgeEmbed {n s : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hle : Fintype.card (UpperEdge H) ≤ s) : UpperEdge H → Fin s :=
  fun e => ⟨(Fintype.equivFin (UpperEdge H) e).val,
    Nat.lt_of_lt_of_le (Fintype.equivFin (UpperEdge H) e).isLt hle⟩

/-- Restrict a symmetric edge weight `w : Sym2 (Fin n) → α` to `UpperEdge H`. -/
def restrictEdgeWeight {n : ℕ} {α : Type*} (H : SimpleGraph (Fin n))
    (w : Sym2 (Fin n) → α) : UpperEdge H → α :=
  fun e => w s(e.val.val.1, e.val.val.2)

end ExactMatching

namespace ExactMatching.Paper

open scoped BigOperators

universe u

/-- Polynomial identity testing under the permanent lower bound. -/
theorem thm_1_test_correct (c : ℝ) (μ₀ : ℕ) (hH : HypothesisH c μ₀) :
    ∃ (A s₀ : ℕ) (K : ℝ), 1 ≤ A ∧ 4 ≤ s₀ ∧ 0 < K ∧
      (∀ s ≥ s₀,
        Real.logb 2 s < (pitM A μ₀ s : ℝ) ∧
        pitM A μ₀ s < s ∧
        2 ≤ pitM A μ₀ s ∧
        s * pitMu A μ₀ s + 1 ≤ s ^ 2) ∧
      (∀ (s : ℕ) (hs : 2 ≤ s) (C : IntCircuit s),
        C.encodingLength ≤ s →
        C.evalPoly.totalDegree ≤ s →
        CoeffBitBound C.evalPoly s →
        (s < s₀ → (pitSmallTest s C ↔ C.evalPoly = 0)) ∧
        (∀ (hge : s₀ ≤ s) (hm : 2 ≤ pitM A μ₀ s)
           (hcard : ∀ i : Fin s, (designSets (pitM A μ₀ s) s hm i).card = pitM A μ₀ s),
           pitLargeTest A μ₀ s hm hcard C ↔ C.evalPoly = 0)) ∧
      (∀ s ≥ 2,
        (pitEvalPointCount A μ₀ s₀ s : ℝ) * ((2 : ℝ) ^ pitMu A μ₀ s) * ((s : ℝ) ^ 4) ≤
          expTwo (expTwo (K * (Real.logb 2 s) ^ (3 / 4 : ℝ)))) := by
  sorry

/-- The evaluation-count bound for the explicit test parameters. -/
theorem thm_1_eval_points (A μ₀ s₀ d : ℕ) (hA : 1 ≤ A) (hμ₀ : 1 ≤ μ₀) (hs₀ : 4 ≤ s₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ s ≥ 2,
      (pitEvalPointCount A μ₀ s₀ s : ℝ) * ((2 : ℝ) ^ pitMu A μ₀ s) * ((s : ℝ) ^ d) ≤
        expTwo (expTwo (K * (Real.logb 2 s) ^ (3 / 4 : ℝ))) := by
  sorry

/-- Decision and witness recovery for a prescribed number of red edges. -/
theorem thm_2a_decision_witness (c : ℝ) (μ₀ : ℕ) (hH : HypothesisH c μ₀) :
    ∃ (A s₀ C_0 : ℕ) (K' : ℝ), 1 ≤ A ∧ 4 ≤ s₀ ∧ 1 ≤ C_0 ∧ 0 < K' ∧
      (∀ s ≥ s₀,
        Real.logb 2 s < (pitM A μ₀ s : ℝ) ∧
        pitM A μ₀ s < s ∧
        2 ≤ pitM A μ₀ s ∧
        s * pitMu A μ₀ s + 1 ≤ s ^ 2) ∧
      ∀ (k : ℕ) (_hk : 1 ≤ k)
        (G : SimpleGraph (Fin (2 * k))) [DecidableRel G.Adj]
        (R : Finset (Sym2 (Fin (2 * k)))) (target : ℕ) (htarget : target ≤ k),
        let s := max (2 * k) (C_0 * (2 * k + (k + 1)) ^ 8)
        (∀ H : SimpleGraph (Fin (2 * k)), [DecidableRel H.Adj] →
          ∃ (hle : Fintype.card (UpperEdge H) ≤ s) (C_H : IntCircuit s),
            C_H.UsesOnlyUnitConstants ∧
            C_H.encodingLength ≤ s ∧
            C_H.evalPoly =
              MvPolynomial.rename (upperEdgeEmbed H hle)
                (groupRingPoly H (exactMatchingLabel H R) (target : ZMod (k + 1))) ∧
            C_H.evalPoly.totalDegree ≤ s ∧
            CoeffBitBound C_H.evalPoly s ∧
            ((s < s₀ → (¬ pitSmallTest s C_H ↔
              ∃ M : Finset (Sym2 (Fin (2 * k))),
                IsPerfectMatching H M ∧ (M ∩ R).card = target)) ∧
             (∀ (hge : s₀ ≤ s) (hm : 2 ≤ pitM A μ₀ s)
                (hcard : ∀ i : Fin s, (designSets (pitM A μ₀ s) s hm i).card = pitM A μ₀ s),
                ¬ pitLargeTest A μ₀ s hm hcard C_H ↔
                  ∃ M : Finset (Sym2 (Fin (2 * k))),
                    IsPerfectMatching H M ∧ (M ∩ R).card = target))) ∧
        (∀ (oracle : SimpleGraph (Fin (2 * k)) → Bool)
           (horacle : ∀ H, oracle H = true ↔
             ∃ M : Finset (Sym2 (Fin (2 * k))),
               IsPerfectMatching H M ∧ (M ∩ R).card = target)
           (edges : List (Sym2 (Fin (2 * k))))
           (hedges : ∀ e, e ∈ edges ↔ e ∈ G.edgeFinset)
           (hnodup : edges.Nodup)
           (hex : ∃ M : Finset (Sym2 (Fin (2 * k))),
             IsPerfectMatching G M ∧ (M ∩ R).card = target),
          let H := selfReduce oracle G edges
          ∃ M : Finset (Sym2 (Fin (2 * k))),
            (∀ e, e ∈ H.edgeSet ↔ e ∈ M) ∧
            IsPerfectMatching G M ∧
            (M ∩ R).card = target ∧
            edges.length + 1 ≤ (2 * k) ^ 2) ∧
        (((2 * k : ℝ) ^ 2) * (pitEvalPointCount A μ₀ s₀ s : ℝ) *
          ((2 : ℝ) ^ pitMu A μ₀ s) * ((s : ℝ) ^ 4) ≤
            expTwo (expTwo (K' * (Real.logb 2 ((2 * k : ℕ) : ℝ)) ^ (3 / 4 : ℝ)))) := by
  sorry

/-- Decision and witness recovery for a bounded integer target weight. -/
theorem thm_2b_decision_witness (c : ℝ) (μ₀ : ℕ) (hH : HypothesisH c μ₀) :
    ∃ (A s₀ C_0 : ℕ) (K' : ℝ), 1 ≤ A ∧ 4 ≤ s₀ ∧ 1 ≤ C_0 ∧ 0 < K' ∧
      (∀ s ≥ s₀,
        Real.logb 2 s < (pitM A μ₀ s : ℝ) ∧
        pitM A μ₀ s < s ∧
        2 ≤ pitM A μ₀ s ∧
        s * pitMu A μ₀ s + 1 ≤ s ^ 2) ∧
      (∀ (k : ℕ) (_hk : 1 ≤ k) (W : ℕ)
        (G : SimpleGraph (Fin (2 * k))) [DecidableRel G.Adj]
        (w : Sym2 (Fin (2 * k)) → ℤ) (hw : ∀ e, -(W : ℤ) ≤ w e ∧ w e ≤ (W : ℤ))
        (target : ℤ) (htarget : -(k * W : ℤ) ≤ target ∧ target ≤ (k * W : ℤ)),
        let s := max (2 * k) (C_0 * (2 * k + (2 * k * W + 1)) ^ 8)
        (∀ H : SimpleGraph (Fin (2 * k)), [DecidableRel H.Adj] →
          ∃ (hle : Fintype.card (UpperEdge H) ≤ s) (C_H : IntCircuit s),
            C_H.UsesOnlyUnitConstants ∧
            C_H.encodingLength ≤ s ∧
            C_H.evalPoly =
              MvPolynomial.rename (upperEdgeEmbed H hle)
                (groupRingPoly H (boundedWeightLabel W H (restrictEdgeWeight H w))
                  ((target + (k * W : ℤ)) : ZMod (2 * k * W + 1))) ∧
            C_H.evalPoly.totalDegree ≤ s ∧
            CoeffBitBound C_H.evalPoly s ∧
            ((s < s₀ → (¬ pitSmallTest s C_H ↔
              ∃ M : Finset (Sym2 (Fin (2 * k))),
                IsPerfectMatching H M ∧ ∑ e ∈ M, w e = target)) ∧
             (∀ (hge : s₀ ≤ s) (hm : 2 ≤ pitM A μ₀ s)
                (hcard : ∀ i : Fin s, (designSets (pitM A μ₀ s) s hm i).card = pitM A μ₀ s),
                ¬ pitLargeTest A μ₀ s hm hcard C_H ↔
                  ∃ M : Finset (Sym2 (Fin (2 * k))),
                    IsPerfectMatching H M ∧ ∑ e ∈ M, w e = target))) ∧
        (∀ (oracle : SimpleGraph (Fin (2 * k)) → Bool)
           (horacle : ∀ H, oracle H = true ↔
             ∃ M : Finset (Sym2 (Fin (2 * k))),
               IsPerfectMatching H M ∧ ∑ e ∈ M, w e = target)
           (edges : List (Sym2 (Fin (2 * k))))
           (hedges : ∀ e, e ∈ edges ↔ e ∈ G.edgeFinset)
           (hnodup : edges.Nodup)
           (hex : ∃ M : Finset (Sym2 (Fin (2 * k))),
             IsPerfectMatching G M ∧ ∑ e ∈ M, w e = target),
          let H := selfReduce oracle G edges
          ∃ M : Finset (Sym2 (Fin (2 * k))),
            (∀ e, e ∈ H.edgeSet ↔ e ∈ M) ∧
            IsPerfectMatching G M ∧
            ∑ e ∈ M, w e = target ∧
            edges.length + 1 ≤ (2 * k) ^ 2) ∧
        (((2 * k : ℝ) ^ 2) * (pitEvalPointCount A μ₀ s₀ s : ℝ) *
          ((2 : ℝ) ^ pitMu A μ₀ s) * ((s : ℝ) ^ 4) ≤
            expTwo (expTwo (K' * (Real.logb 2 ((2 * k + W : ℕ) : ℝ)) ^ (3 / 4 : ℝ))))) ∧
      (∀ (C : ℝ), 0 < C → ∃ K'_C : ℝ, 0 < K'_C ∧
        ∀ (k : ℕ) (_hk : 1 ≤ k) (W : ℕ),
          (W : ℝ) ≤ ((2 * k : ℕ) : ℝ) ^ C →
          let s := max (2 * k) (C_0 * (2 * k + (2 * k * W + 1)) ^ 8)
          ((2 * k : ℝ) ^ 2) * (pitEvalPointCount A μ₀ s₀ s : ℝ) *
            ((2 : ℝ) ^ pitMu A μ₀ s) * ((s : ℝ) ^ 4) ≤
              expTwo (expTwo (K'_C * (Real.logb 2 ((2 * k : ℕ) : ℝ)) ^ (3 / 4 : ℝ)))) := by
  sorry

/-- Decision and witness recovery for a prescribed finite abelian group sum. -/
theorem thm_2c_decision_witness (c : ℝ) (μ₀ : ℕ) (hH : HypothesisH c μ₀) :
    ∃ (A s₀ C_0 : ℕ) (K' : ℝ), 1 ≤ A ∧ 4 ≤ s₀ ∧ 1 ≤ C_0 ∧ 0 < K' ∧
      (∀ s ≥ s₀,
        Real.logb 2 s < (pitM A μ₀ s : ℝ) ∧
        pitM A μ₀ s < s ∧
        2 ≤ pitM A μ₀ s ∧
        s * pitMu A μ₀ s + 1 ≤ s ^ 2) ∧
      (∀ (k : ℕ) (_hk : 1 ≤ k)
        (Γ : Type) [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
        (G : SimpleGraph (Fin (2 * k))) [DecidableRel G.Adj]
        (w : Sym2 (Fin (2 * k)) → Γ) (γstar : Γ),
        let s := max (2 * k) (C_0 * (2 * k + Fintype.card Γ) ^ 8)
        (∀ H : SimpleGraph (Fin (2 * k)), [DecidableRel H.Adj] →
          ∃ (hle : Fintype.card (UpperEdge H) ≤ s) (C_H : IntCircuit s),
            C_H.UsesOnlyUnitConstants ∧
            C_H.encodingLength ≤ s ∧
            C_H.evalPoly =
              MvPolynomial.rename (upperEdgeEmbed H hle)
                (groupRingPoly H (restrictEdgeWeight H w) γstar) ∧
            C_H.evalPoly.totalDegree ≤ s ∧
            CoeffBitBound C_H.evalPoly s ∧
            ((s < s₀ → (¬ pitSmallTest s C_H ↔
              ∃ M : Finset (Sym2 (Fin (2 * k))),
                IsPerfectMatching H M ∧ ∑ e ∈ M, w e = γstar)) ∧
             (∀ (hge : s₀ ≤ s) (hm : 2 ≤ pitM A μ₀ s)
                (hcard : ∀ i : Fin s, (designSets (pitM A μ₀ s) s hm i).card = pitM A μ₀ s),
                ¬ pitLargeTest A μ₀ s hm hcard C_H ↔
                  ∃ M : Finset (Sym2 (Fin (2 * k))),
                    IsPerfectMatching H M ∧ ∑ e ∈ M, w e = γstar))) ∧
        (∀ (oracle : SimpleGraph (Fin (2 * k)) → Bool)
           (horacle : ∀ H, oracle H = true ↔
             ∃ M : Finset (Sym2 (Fin (2 * k))),
               IsPerfectMatching H M ∧ ∑ e ∈ M, w e = γstar)
           (edges : List (Sym2 (Fin (2 * k))))
           (hedges : ∀ e, e ∈ edges ↔ e ∈ G.edgeFinset)
           (hnodup : edges.Nodup)
           (hex : ∃ M : Finset (Sym2 (Fin (2 * k))),
             IsPerfectMatching G M ∧ ∑ e ∈ M, w e = γstar),
          let H := selfReduce oracle G edges
          ∃ M : Finset (Sym2 (Fin (2 * k))),
            (∀ e, e ∈ H.edgeSet ↔ e ∈ M) ∧
            IsPerfectMatching G M ∧
            ∑ e ∈ M, w e = γstar ∧
            edges.length + 1 ≤ (2 * k) ^ 2) ∧
        (((2 * k : ℝ) ^ 2) * (pitEvalPointCount A μ₀ s₀ s : ℝ) *
          ((2 : ℝ) ^ pitMu A μ₀ s) * ((s : ℝ) ^ 4) ≤
            expTwo (expTwo (K' * (Real.logb 2 ((2 * k + Fintype.card Γ : ℕ) : ℝ)) ^ (3 / 4 : ℝ))))) ∧
      (∀ (C : ℝ), 0 < C → ∃ K'_C : ℝ, 0 < K'_C ∧
        ∀ (k : ℕ) (_hk : 1 ≤ k) (gCard : ℕ), 1 ≤ gCard →
          (gCard : ℝ) ≤ ((2 * k : ℕ) : ℝ) ^ C →
          let s := max (2 * k) (C_0 * (2 * k + gCard) ^ 8)
          ((2 * k : ℝ) ^ 2) * (pitEvalPointCount A μ₀ s₀ s : ℝ) *
            ((2 : ℝ) ^ pitMu A μ₀ s) * ((s : ℝ) ^ 4) ≤
              expTwo (expTwo (K'_C * (Real.logb 2 ((2 * k : ℕ) : ℝ)) ^ (3 / 4 : ℝ)))) := by
  sorry

end ExactMatching.Paper
