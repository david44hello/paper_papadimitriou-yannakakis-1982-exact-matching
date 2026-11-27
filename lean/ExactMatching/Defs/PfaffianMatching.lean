/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import ExactMatching.Defs.Circuits
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Perm.Sign

@[expose] public section

/-!
# Perfect matchings, Pfaffian over `ℤ[Γ][x]`, circuit wire-expansion, and self-reduction

Defines:
- `IsPerfectMatching`, `perfectMatchings`: perfect matchings as edge finsets of a graph on `Fin n`.
- `UpperPair n`, `pfaffian`, `universalPfaffian`: the Pfaffian of an `n × n` skew-symmetric
  matrix over any commutative ring `R`, defined directly by its universal matching expansion.
- `tutteMatrix`, `groupRingPoly`: the Tutte matrix over `ℤ[Γ][x]` (`AddMonoidAlgebra ℤ Γ`)
  and the extracted polynomial `P_{γ*}(x) ∈ ℤ[x]`.
- `expandGroupRingCircuit`: explicit wire-expansion converting a division-free `ℤ`-circuit
  for `universalPfaffian n` into a `{0, ±1}`-constant `ℤ`-circuit for `P_{γ*}(x)`.
- `selfReduce`: explicit edge-deletion self-reduction given a decision oracle.
- Cyclic-group embeddings for Exact Matching (`ZMod (n/2 + 1)`) and bounded integer weights
  (`ZMod (n * W + 1)`), and Remark 2's interpolation matrix.
-/

namespace ExactMatching

open scoped BigOperators

/-- Ordered pairs `(u, v)` with `u < v` in `Fin n` (upper-triangular entries). -/
abbrev UpperPair (n : ℕ) := { p : Fin n × Fin n // p.1 < p.2 }

/-- A set of undirected edges `M` is a perfect matching of `G` if every edge belongs to `G`
and every vertex is incident to a unique edge in `M`. -/
def IsPerfectMatching {n : ℕ} (G : SimpleGraph (Fin n)) (M : Finset (Sym2 (Fin n))) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧ ∀ v : Fin n, (M.filter (fun e => v ∈ e)).card = 1

/-- The finset of all perfect matchings of `G`. -/
noncomputable def perfectMatchings {n : ℕ} (G : SimpleGraph (Fin n)) :
    Finset (Finset (Sym2 (Fin n))) :=
  open Classical in Finset.univ.filter (IsPerfectMatching G)

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

/-- The universal integer Pfaffian polynomial `Pf(Z) ∈ ℤ[{Z_{u,v} : u < v}]`. -/
noncomputable def universalPfaffian (k : ℕ) : MvPolynomial (UpperPair (2 * k)) ℤ :=
  ∑ m : OrderedPairing k,
    MvPolynomial.C m.sign *
      ∏ i : Fin k,
        MvPolynomial.X ⟨(m.perm ⟨2 * i.val, by omega⟩, m.perm ⟨2 * i.val + 1, by omega⟩),
          m.pair_lt i⟩

/-- Canonical enumeration of upper-triangular pairs `UpperPair n` into `Fin (Fintype.card (UpperPair n))`. -/
noncomputable def upperPairEquiv (n : ℕ) :
    UpperPair n ≃ Fin (Fintype.card (UpperPair n)) :=
  Fintype.equivFin (UpperPair n)

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

/-- Label sum `w(M) = ∑_{e ∈ M} w(e) ∈ Γ` of a perfect matching `M` of `G`. -/
def matchingLabelSum {n : ℕ} {Γ : Type*} [AddCommGroup Γ]
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : UpperEdge G → Γ) (M : Finset (Sym2 (Fin n))) : Γ :=
  ∑ e : UpperEdge G, if s(e.val.val.1, e.val.val.2) ∈ M then w e else 0

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

/-- Remark 2: Tutte matrix over `ℤ[x]` evaluated at `y = j` with shifted nonnegative
integer weights `w'(e) = w(e) + W ∈ {0, ..., 2W}`. -/
noncomputable def interpMatrix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w' : UpperEdge G → ℕ) (j : ℤ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (UpperEdge G) ℤ) :=
  fun u v =>
    if hlt : u < v then
      if hadj : G.Adj u v then
        MvPolynomial.C (j ^ (w' ⟨⟨(u, v), hlt⟩, hadj⟩)) *
          MvPolynomial.X ⟨⟨(u, v), hlt⟩, hadj⟩
      else 0
    else if hgt : v < u then
      if hadj : G.Adj v u then
        -(MvPolynomial.C (j ^ (w' ⟨⟨(v, u), hgt⟩, hadj⟩)) *
          MvPolynomial.X ⟨⟨(v, u), hgt⟩, hadj⟩)
      else 0
    else 0

/-- The exact polynomial `P_{k'}(x) ∈ ℤ[x]` summing signed matching monomials with
shifted weight sum `w'(M) = k'`. -/
noncomputable def weightFiberPoly {k : ℕ} (G : SimpleGraph (Fin (2 * k))) [DecidableRel G.Adj]
    (w' : UpperEdge G → ℕ) (k' : ℕ) : MvPolynomial (UpperEdge G) ℤ :=
  ∑ m : OrderedPairing k,
    if hsub : ∀ i : Fin k, G.Adj (m.perm ⟨2 * i.val, by omega⟩) (m.perm ⟨2 * i.val + 1, by omega⟩)
    then
      let wt : ℕ :=
        ∑ i : Fin k,
          w' ⟨⟨(m.perm ⟨2 * i.val, by omega⟩, m.perm ⟨2 * i.val + 1, by omega⟩), m.pair_lt i⟩,
            hsub i⟩
      if wt = k' then
        MvPolynomial.C m.sign *
          ∏ i : Fin k,
            MvPolynomial.X
              ⟨⟨(m.perm ⟨2 * i.val, by omega⟩, m.perm ⟨2 * i.val + 1, by omega⟩), m.pair_lt i⟩,
                hsub i⟩
      else 0
    else 0

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
