/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import ExactMatching.Defs.Circuits
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Explicit cited hypotheses (NO `axiom` declarations)

All prior results used by conditional theorems enter strictly as named `Prop` hypotheses:
1. `KI04_Cor_7_4` (**REFEREED**): Kabanets & Impagliazzo (2004), Corollary 7.4 (p. 34), via
   Kaltofen (1989, Theorem 7.2, p. 33) and Section 2.3 (pp. 12–13).
2. `A26_MainTheorem` (**UNREFEREED**): Claude (Anthropic), Nov 23, 2026, Theorem 1.1
   (`Statement.MainTheorem`, p. 11), copied token-for-token. Used ONLY in Corollary 1.
3. `O26_Thm_1_1` (**UNREFEREED**): OpenAI, Nov 24, 2026, Theorem 1.1 (pp. 1–2), exact-circuit
   specialization over `ℚ`. Used ONLY in Remark 1.

No Lean project of `[A26]` or `[O26]` is imported.
-/

namespace ExactMatching

open MvPolynomial

universe u

/-- Cited result (**REFEREED**): V. Kabanets and R. Impagliazzo,
*Derandomizing polynomial identity tests means proving circuit lower bounds*,
Comput. Complexity 13 (2004), 1–46, Corollary 7.4 (p. 34) via Kaltofen (1989, Theorem 7.2,
p. 33) and Definition 7.1 (p. 33), specialized to `𝔽 = ℚ` and integer-coefficient inputs.

Plain-word interface notes:
1. The source states a probabilistic polynomial-time algorithm for root finding; we use only
   that its output circuit exists with the polynomial size bound given by Theorem 7.2
   (`poly(s, d, a)` over `ℚ`, where `a` is the maximum coefficient bit-length).
2. "Division-free" (`+`, `-`, `×`, rational constants, and multiplication by constants,
   represented by `RatCircuit`) is the source's own arithmetic-circuit model of Section 2.3
   (p. 12).
3. Because Section 2.3's model is already division-free, the paper's fallback sentence on
   Strassen's division elimination (`[Str73]`) is not used. -/
def KI04_Cor_7_4 : Prop :=
  ∃ (c_ki e_ki : ℕ), 1 ≤ c_ki ∧ 1 ≤ e_ki ∧
    ∀ (m : ℕ) (g_circ : IntCircuit (m + 1)) (d a : ℕ)
      (p : MvPolynomial (Fin m) ℤ),
      let g : MvPolynomial (Fin (m + 1)) ℤ := g_circ.evalPoly
      g ≠ 0 →
      g.totalDegree ≤ d →
      CoeffBitBound g a →
      MvPolynomial.bind₁
        (Fin.lastCases p (fun i => MvPolynomial.X i)) g = 0 →
      ∃ C_p : RatCircuit m,
        C_p.size ≤ c_ki * (g_circ.encodingLength + d + a + 2) ^ e_ki ∧
        ∀ x : Fin m → ℚ,
          MvPolynomial.eval x C_p.evalPoly =
            MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℚ) p)

/-- Cited result (**UNREFEREED**): Claude (Anthropic), *`VP ≠ VNP` over every field*,
preprint and Lean 4 formalization, November 23, 2026, Theorem 1.1 (`Statement.MainTheorem`,
p. 11), copied token-for-token.
**UNREFEREED:** machine-checked in Lean 4, not yet human-refereed. Used ONLY in Corollary 1. -/
def A26_MainTheorem : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ p : ℕ, ∃ m₀ : ℕ, ∀ (F : Type u) [Field F] [CharP F p], ∀ m ≥ m₀, ∀ s : ℕ,
    (Computes (hc F m) s → Beyond c m s) ∧ (p ≠ 2 → Computes (perm F m) s → Beyond c m s)

/-- Cited result (**UNREFEREED**): OpenAI, *Circuit lower bounds for Hamiltonian cycle and
the permanent*, preprint, November 24, 2026, Theorem 1.1 (pp. 1–2), exact-circuit
specialization over `ℚ` (characteristic `χ = 0 ≠ 2`, natural logarithm `Real.log`).
**UNREFEREED:** not yet human-refereed; its accompanying Lean 4 files formalize only the
qualitative superpolynomial statement, not this explicit quantitative rate.
Used ONLY in Remark 1. -/
def O26_Thm_1_1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧
    ∀ N ≥ N₀, ∀ s : ℕ,
      O26ExactComputes (perm ℚ N) s →
      Real.exp (c * (Real.log N) ^ 2 / (Real.log (Real.log N)) ^ 2) ≤ (s : ℝ)

end ExactMatching
