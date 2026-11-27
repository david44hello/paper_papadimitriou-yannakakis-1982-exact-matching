/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Nat.Log
public import Mathlib.FieldTheory.Finite.GaloisField

@[expose] public section

/-!
# Explicit polynomial-graph design (Lemma 2.1) and Nisan–Wigderson polynomial map

Defines:
- `designR m`, `designQ m`, `designL m`, `designT m n`: exact integer parameters of
  Lemma 2.1 (`q = 2^r` least power of 2 with `q ≥ m`, `l = m * q`, `t = ⌈log₂ n / log₂ q⌉`).
- `designSets`: the explicit family of sets `S₁, ..., Sₙ ⊆ Fin (designL m)` constructed
  as graphs `{(u, h(u)) : u ∈ A}` of the first `n` polynomials `h ∈ 𝔽_q[z]` of degree `< t`.
- `nwMap`: the Nisan–Wigderson polynomial map `NW^p(a) = (p(a|_{S₁}), ..., p(a|_{Sₙ}))`
  where `a|_{S_i}` lists coordinates of `a` indexed by `S_i` in increasing order.
-/

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

/-- The Nisan–Wigderson polynomial map `NW^p : R^l → R^n`,
`NW^p(a)_i = p(a|_{S_i})`, where `a|_{S_i}` lists the coordinates of `a`
indexed by `S_i` in strictly increasing order. -/
noncomputable def nwMap {m n l : ℕ} {R : Type*} [CommSemiring R]
    (S : Fin n → Finset (Fin l)) (hcard : ∀ i, (S i).card = m)
    (p : MvPolynomial (Fin m) R) (a : Fin l → R) : Fin n → R :=
  fun i => MvPolynomial.eval (fun j : Fin m => a ((S i).orderEmbOfFin (hcard i) j)) p

end ExactMatching
