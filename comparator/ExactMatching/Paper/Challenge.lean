/-
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
import ExactMatching.Defs.Circuits
import ExactMatching.Defs.Design
import ExactMatching.Defs.PitAlgorithm
import ExactMatching.Defs.PfaffianMatching
import ExactMatching.Defs.CitedHypotheses

/-!
# Formal statements of all formalized claims of the paper

Single-writer statement surface (`ExactMatching.Paper`). Every theorem speaks of the explicit
constructions in `ExactMatching.Defs` (no bare existence shortcuts). Deterministic running-time
clauses and randomized/parallel complexity remarks are not formalized (`no time-bounded
computation / randomized or parallel complexity in Lean's library`).
-/

namespace ExactMatching.Paper

open scoped BigOperators

universe u

/-! ### Permanent convention agreement (paper vs. `[A26]`) -/

/-- The paper's permanent `∑ σ, ∏ i, X (i, σ i)` equals `[A26]`'s `perm` `∑ σ, ∏ i, X (σ i, i)`. -/
theorem paperPerm_eq_perm (R : Type*) [CommSemiring R] (μ : ℕ) :
    paperPerm R μ = perm R μ := by
  sorry

/-! ### Lemma 2.1 — Explicit polynomial-graph design (unconditional) -/

/-- Lemma 2.1 (field existence): for every `m ≥ 2`, there exists a monic irreducible
polynomial of degree `r = designR m` over `ZMod 2`. -/
theorem lem_2_1_irred_exists (m : ℕ) (hm : 2 ≤ m) :
    ∃ f : Polynomial (ZMod 2), f.Monic ∧ Irreducible f ∧ f.natDegree = designR m := by
  sorry

/-- Lemma 2.1 (explicit polynomial-graph design): for `m, n ≥ 1` with `log₂ n < m ≤ n` and
`n ≥ 2`, `l = m * q < 2 * m^2`, every set `S_i = designSets m n _ i` has cardinality `m`,
and for all `i ≠ j`, `|S_i ∩ S_j| < log₂ n`. -/
theorem lem_2_1_design (m n : ℕ) (hn : 2 ≤ n) (hm_gt : Real.logb 2 n < (m : ℝ)) (hmn : m ≤ n) :
    have hm2 : 2 ≤ m := by
      have h1 : (1 : ℝ) ≤ Real.logb 2 n := by
        rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
        exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by exact_mod_cast hn)
      have h2 : (1 : ℝ) < (m : ℝ) := lt_of_le_of_lt h1 hm_gt
      exact_mod_cast Nat.succ_le_of_lt (by exact_mod_cast h2)
    designL m < 2 * m ^ 2 ∧
    (∀ i : Fin n, (designSets m n hm2 i).card = m) ∧
    (∀ i j : Fin n, i ≠ j →
      ((designSets m n hm2 i ∩ designSets m n hm2 j).card : ℝ) < Real.logb 2 n) := by
  sorry

/-! ### Lemma 2.2 — Reconstruction and circuit-model transfer -/

/-- Multivariate polynomial nonvanishing on a grid `S^l` (`[KI04]` Lemma 2.18). -/
theorem step_2_2_nonvanishing {l : ℕ} (f : MvPolynomial (Fin l) ℚ) (hf : f ≠ 0)
    (S : Finset ℚ) (hS : f.totalDegree < S.card) :
    ∃ a : Fin l → ℚ, (∀ i, a i ∈ S) ∧ MvPolynomial.eval a f ≠ 0 := by
  sorry

/-- Strictly division-free `RatCircuit` translates into `Computes` with at most `3 * C.size`
gates; and functional agreement on `ℚ^m` implies formal equality in `ℚ[x_1, ..., x_m]`. -/
theorem step_2_2_model_transfer {m : ℕ} (C : RatCircuit m) :
    Computes C.evalPoly (3 * C.size) ∧
    ∀ q : MvPolynomial (Fin m) ℚ,
      (∀ x : Fin m → ℚ, MvPolynomial.eval x C.evalPoly = MvPolynomial.eval x q) →
      C.evalPoly = q := by
  sorry

/-- Lemma 2.2 (full statement): given `KI04_Cor_7_4`, there exists an absolute constant `κ ≥ 1`
such that if `f ∈ ℤ[y_1,...,y_n]` (nonzero, degree `d_f`, computable by an `IntCircuit` of
encoding length `≤ s`) and multilinear `p ∈ ℤ[x_1,...,x_m]` (nonzero, degree `d_p`, `n ≥ 2`,
`log₂ n < m ≤ n`, `max(m, n, d_f, d_p, s, b) ≤ s`, `s ≥ 2`) satisfy `f(NW^p(a)) = 0` on
`S^l` with `|S| > d_f * d_p` for the explicit sets `designSets m n _`, then `p` is computable
in the `[A26]` `ℚ`-circuit model (`Computes`) with at most `s ^ κ` gates. -/
theorem lem_2_2_reconstruction (hKI : KI04_Cor_7_4) :
    ∃ κ : ℕ, 1 ≤ κ ∧
      ∀ (s m n d_f d_p b : ℕ) (hs : 2 ≤ s) (hn : 2 ≤ n)
        (hm_gt : Real.logb 2 n < (m : ℝ)) (hmn : m ≤ n)
        (hmax : m ≤ s ∧ n ≤ s ∧ d_f ≤ s ∧ d_p ≤ s ∧ b ≤ s)
        (C_f : IntCircuit n) (hC_len : C_f.encodingLength ≤ s)
        (hf_nz : C_f.evalPoly ≠ 0) (hf_deg : C_f.evalPoly.totalDegree ≤ d_f)
        (hf_bit : CoeffBitBound C_f.evalPoly b)
        (p : MvPolynomial (Fin m) ℤ) (hp_nz : p ≠ 0) (hp_ml : IsMultilinear p)
        (hp_deg : p.totalDegree ≤ d_p) (hp_bit : CoeffBitBound p b)
        (S_grid : Finset ℚ) (hS_card : d_f * d_p < S_grid.card),
        have hm2 : 2 ≤ m := by
          have h1 : (1 : ℝ) ≤ Real.logb 2 n := by
            rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
            exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by exact_mod_cast hn)
          exact_mod_cast Nat.succ_le_of_lt (by exact_mod_cast lt_of_le_of_lt h1 hm_gt)
        ∀ (hcard : ∀ i : Fin n, (designSets m n hm2 i).card = m),
        (∀ a : Fin (designL m) → ℚ, (∀ j, a j ∈ S_grid) →
          MvPolynomial.eval
            (nwMap (designSets m n hm2) hcard (MvPolynomial.map (Int.castRingHom ℚ) p) a)
            (MvPolynomial.map (Int.castRingHom ℚ) C_f.evalPoly) = 0) →
        Computes (MvPolynomial.map (Int.castRingHom ℚ) p) (s ^ κ) := by
  sorry

/-! ### Theorem 1 ingredients — Quantitative PIT over `ℤ` -/

/-- Equation (1) of Theorem 1: `μ ≥ μ₀` and `μ ^ (c * (log₂ μ)^(1/3)) = exp₂(c * (log₂ μ)^(4/3)) ≥ s^κ`. -/
theorem step_thm1_eq1 (c : ℝ) (hc : 0 < c) (κ μ₀ s : ℕ) (hκ : 1 ≤ κ) (hs : 2 ≤ s) :
    let A := Nat.ceil ((κ : ℝ) / c)
    let μ := pitMu A μ₀ s
    μ₀ ≤ μ ∧
    (μ : ℝ) ^ (c * (Real.logb 2 μ) ^ (1 / 3 : ℝ)) = expTwo (c * (Real.logb 2 μ) ^ (4 / 3 : ℝ)) ∧
    ((s : ℝ) ^ κ) ≤ (μ : ℝ) ^ (c * (Real.logb 2 μ) ^ (1 / 3 : ℝ)) := by
  sorry

/-- Threshold `s₀ = s₀(A, μ₀) ≥ 4` with `log₂ s < m < s` and `s * μ + 1 ≤ s^2` for all `s ≥ s₀`. -/
theorem step_thm1_threshold (A μ₀ : ℕ) (hA : 1 ≤ A) (hμ₀ : 1 ≤ μ₀) :
    ∃ s₀ : ℕ, 4 ≤ s₀ ∧ ∀ s ≥ s₀,
      Real.logb 2 s < (pitM A μ₀ s : ℝ) ∧
      pitM A μ₀ s < s ∧
      s * pitMu A μ₀ s + 1 ≤ s ^ 2 := by
  sorry

/-- Ryser's formula equals `Matrix.permanent` over every commutative ring `R`. -/
theorem step_thm1_ryser {μ : ℕ} {R : Type*} [CommRing R] (M : Matrix (Fin μ) (Fin μ) R) :
    ryserPerm M = M.permanent := by
  sorry

/-- Small-input mod-`2^{B₀}` grid test exactness: `pitSmallTest s C ↔ C.evalPoly = 0`. -/
theorem step_thm1_small_inputs (s : ℕ) (hs : 2 ≤ s) (C : IntCircuit s)
    (hdeg : C.evalPoly.totalDegree ≤ s) (hcoeff : CoeffBitBound C.evalPoly s) :
    pitSmallTest s C ↔ C.evalPoly = 0 := by
  sorry

/-- Large-input modulus `2^B` exactness at every NW-permanent evaluation point. -/
theorem step_thm1_modulus_exact (A μ₀ s : ℕ) (hs : 2 ≤ s) (hm : 2 ≤ pitM A μ₀ s)
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
  sorry

/-- Modulus bit-length bound `B ≤ 10 * s^{3/2} * log₂ s` once `m < s`. -/
theorem step_thm1_B_bound (A μ₀ s : ℕ) (hs : 2 ≤ s) (hms : pitM A μ₀ s < s) :
    (pitB A μ₀ s : ℝ) ≤ 10 * (s : ℝ) ^ (3 / 2 : ℝ) * Real.logb 2 s := by
  sorry

/-- Theorem 1 ingredient: the number of evaluation points (times `2^μ * s^d`) is bounded by
`exp₂(exp₂(K * (log₂ s)^(3/4)))`. -/
theorem thm_1_eval_points (A μ₀ s₀ d : ℕ) (hA : 1 ≤ A) (hμ₀ : 1 ≤ μ₀) (hs₀ : 4 ≤ s₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ s ≥ 2,
      (pitEvalPointCount A μ₀ s₀ s : ℝ) * ((2 : ℝ) ^ pitMu A μ₀ s) * ((s : ℝ) ^ d) ≤
        expTwo (expTwo (K * (Real.logb 2 s) ^ (3 / 4 : ℝ))) := by
  sorry

/-- Theorem 1 ingredient: the test is correct (and its evaluation-point count satisfies the
`exp₂(exp₂(K (log₂ s)^(3/4)))` bound).
Under `HypothesisH c μ₀` and `KI04_Cor_7_4`, there exist fixed integer constants `A ≥ 1`, `s₀ ≥ 4`,
and `K > 0` (depending only on `c, μ₀` and the universal constant of `KI04_Cor_7_4`) such that
for every `s ≥ 2` and every `C : IntCircuit s` of encoding length `≤ s`, degree `≤ s`, and
coefficient bit-length `≤ s`:
- if `s < s₀`, `pitSmallTest s C ↔ C.evalPoly = 0`;
- if `s ≥ s₀`, `pitLargeTest A μ₀ s _ _ C ↔ C.evalPoly = 0`;
- and `pitEvalPointCount A μ₀ s₀ s * 2^{pitMu A μ₀ s} * s^4 ≤ exp₂(exp₂(K (log₂ s)^(3/4)))`. -/
theorem thm_1_test_correct (hKI : KI04_Cor_7_4) (c : ℝ) (μ₀ : ℕ) (hH : HypothesisH c μ₀) :
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

/-- In-text asymptotic identity and comparisons (`2^{polylog(s)} < exp₂(exp₂(K (log₂ s)^(3/4))) < 2^{s^ε}`). -/
theorem cov_asymptotic_between (K : ℝ) (hK : 0 < K) :
    (∀ s : ℕ, 2 ≤ s →
      expTwo (expTwo (K * (Real.logb 2 s) ^ (3 / 4 : ℝ))) =
        (2 : ℝ) ^ ((s : ℝ) ^ (K / (Real.logb 2 s) ^ (1 / 4 : ℝ)))) ∧
    (∀ (d : ℕ) (ε : ℝ), 0 < ε → ∃ S₀ : ℕ, ∀ s ≥ S₀,
      (2 : ℝ) ^ ((Real.logb 2 s) ^ d) < expTwo (expTwo (K * (Real.logb 2 s) ^ (3 / 4 : ℝ))) ∧
      expTwo (expTwo (K * (Real.logb 2 s) ^ (3 / 4 : ℝ))) < (2 : ℝ) ^ ((s : ℝ) ^ ε)) := by
  sorry

/-- Table 1 naive grid evaluation size `(s + 1)^s ≤ 2^(2 * s * log₂ s)` for `s ≥ 2`. -/
theorem cov_grid_prior_pit (s : ℕ) (hs : 2 ≤ s) :
    ((s + 1 : ℕ) ^ s : ℝ) ≤ (2 : ℝ) ^ (2 * (s : ℝ) * Real.logb 2 s) := by
  sorry

/-! ### Proposition 3.1 — Group-ring Pfaffian identity and circuit construction (unconditional) -/

/-- Proposition 3.1 (algebraic Pfaffian identity over `ℤ[Γ][x]`). -/
theorem prop_3_1_pfaffian_identity {k : ℕ} (hk : 1 ≤ k)
    {Γ : Type*} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (G : SimpleGraph (Fin (2 * k))) [DecidableRel G.Adj]
    (w : UpperEdge G → Γ) (γstar : Γ) :
    let P := groupRingPoly G w γstar
    (∀ d, P.coeff d = -1 ∨ P.coeff d = 0 ∨ P.coeff d = 1) ∧
    P.totalDegree ≤ k ∧
    (∀ d ∈ P.support, d.sum (fun _ e => e) = k) ∧
    (P ≠ 0 ↔ ∃ M : Finset (Sym2 (Fin (2 * k))),
      IsPerfectMatching G M ∧ matchingLabelSum G w M = γstar) := by
  sorry

/-- Proposition 3.1 (cyclic factor rank bound): `r ≤ max(1, log₂ |Γ|)`. -/
theorem prop_3_1_cyclic_rank_bound (r : ℕ) (q : Fin r → ℕ)
    (hq : (∀ i, 2 ≤ q i) ∨ (∃ hr : r = 1, q ⟨0, by omega⟩ = 1)) :
    (r : ℝ) ≤ max (1 : ℝ) (Real.logb 2 ((∏ i : Fin r, q i : ℕ) : ℝ)) := by
  sorry

/-- Internal unconditional division-free Pfaffian circuit construction (alternating-clow-sequence
DP): for every `k ≥ 1`, there exists an explicit division-free `{0, ±1}`-constant `IntCircuit`
of size `O(k^4)` computing `universalPfaffian k`. -/
theorem pfaffian_clow_circuit_exists :
    ∃ C_const : ℕ, 1 ≤ C_const ∧ ∀ (k : ℕ), 1 ≤ k →
      ∃ C_pf : IntCircuit (Fintype.card (UpperPair (2 * k))),
        C_pf.UsesOnlyUnitConstants ∧
        C_pf.size ≤ C_const * k ^ 4 ∧
        C_pf.evalPoly = MvPolynomial.rename (upperPairEquiv (2 * k)) (universalPfaffian k) := by
  sorry

/-- Proposition 3.1 (wire-expansion theorem, parametrized by any `{0, ±1}`-constant circuit `C_pf`
computing `universalPfaffian k`). -/
theorem prop_3_1_wire_expansion {k : ℕ} (hk : 1 ≤ k)
    {Γ : Type*} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (G : SimpleGraph (Fin (2 * k))) [DecidableRel G.Adj]
    (w : UpperEdge G → Γ) (γstar : Γ)
    (C_pf : IntCircuit (Fintype.card (UpperPair (2 * k))))
    (hunit : C_pf.UsesOnlyUnitConstants)
    (hpf : C_pf.evalPoly = MvPolynomial.rename (upperPairEquiv (2 * k)) (universalPfaffian k)) :
    let M := 2 * (Fintype.card Γ) ^ 2 * C_pf.size + Fintype.card Γ
    ∃ C_out : IntCircuit (Fintype.card (UpperEdge G)),
      C_out.UsesOnlyUnitConstants ∧
      C_out.size ≤ M ∧
      C_out.encodingLength ≤ M * (2 * Nat.clog 2 (M + (2 * k) ^ 2 + 2) + 4) ∧
      C_out.evalPoly =
        MvPolynomial.rename (Fintype.equivFin (UpperEdge G)) (groupRingPoly G w γstar) := by
  sorry

/-- Proposition 3.1 (combined algebraic + circuit construction core, unconditional):
there exists a universal polynomial bound `C_0 * (n + |Γ|)^8` such that for every even
`n = 2k ≥ 2`, finite abelian group `Γ`, graph `G`, labeling `w`, and target `γ*`, there is a
`{0, ±1}`-constant `IntCircuit` `C_{γ*}` of encoding length `≤ C_0 * (2k + |Γ|)^8` computing
`P_{γ*}(x)` of degree `≤ k` with coefficients in `{-1, 0, 1}` and `P_{γ*} ≠ 0 ↔ ∃ M, w(M) = γ*`. -/
theorem prop_3_1_pfaffian_circuit :
    ∃ C_0 : ℕ, 1 ≤ C_0 ∧
      ∀ (k : ℕ) (_hk : 1 ≤ k)
        (Γ : Type) [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
        (G : SimpleGraph (Fin (2 * k))) [DecidableRel G.Adj]
        (w : UpperEdge G → Γ) (γstar : Γ),
        let P := groupRingPoly G w γstar
        ∃ C_out : IntCircuit (Fintype.card (UpperEdge G)),
          C_out.UsesOnlyUnitConstants ∧
          C_out.encodingLength ≤ C_0 * (2 * k + Fintype.card Γ) ^ 8 ∧
          C_out.evalPoly = MvPolynomial.rename (Fintype.equivFin (UpperEdge G)) P ∧
          (∀ d, P.coeff d = -1 ∨ P.coeff d = 0 ∨ P.coeff d = 1) ∧
          P.totalDegree ≤ k ∧
          (∀ d ∈ P.support, d.sum (fun _ e => e) = k) ∧
          (P ≠ 0 ↔ ∃ M : Finset (Sym2 (Fin (2 * k))),
            IsPerfectMatching G M ∧ matchingLabelSum G w M = γstar) := by
  sorry

/-! ### Theorem 2 ingredients — Exact Matching, bounded integer weights, and abelian group labels -/

/-- Odd-vertex graphs have no perfect matching. -/
theorem step_thm2_odd_n {n : ℕ} (hodd : Odd n) (G : SimpleGraph (Fin n))
    (M : Finset (Sym2 (Fin n))) : ¬ IsPerfectMatching G M := by
  sorry

/-- Theorem 2(c) edge-deletion self-reduction recovers a valid `γ*`-matching in at most
`|E(G)| + 1 ≤ n^2` oracle calls (`n ≥ 2`). -/
theorem step_thm2c_self_reduction {n : ℕ} (hn : 2 ≤ n)
    {Γ : Type*} [AddCommGroup Γ]
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → Γ) (γstar : Γ)
    (oracle : SimpleGraph (Fin n) → Bool)
    (horacle : ∀ H : SimpleGraph (Fin n),
      oracle H = true ↔
        ∃ M : Finset (Sym2 (Fin n)), IsPerfectMatching H M ∧ ∑ e ∈ M, w e = γstar)
    (edges : List (Sym2 (Fin n))) (hedges : ∀ e, e ∈ edges ↔ e ∈ G.edgeFinset)
    (hnodup : edges.Nodup)
    (hex : ∃ M : Finset (Sym2 (Fin n)), IsPerfectMatching G M ∧ ∑ e ∈ M, w e = γstar) :
    let H := selfReduce oracle G edges
    ∃ M : Finset (Sym2 (Fin n)),
      (∀ e, e ∈ H.edgeSet ↔ e ∈ M) ∧
      IsPerfectMatching G M ∧
      ∑ e ∈ M, w e = γstar ∧
      edges.length + 1 ≤ n ^ 2 := by
  sorry

/-- Theorem 2(a) Exact Matching cyclic-group embedding into `ZMod (k + 1)` (`n = 2k ≥ 2`). -/
theorem step_thm2a_embedding {k : ℕ} (hk : 1 ≤ k)
    (G : SimpleGraph (Fin (2 * k))) [DecidableRel G.Adj]
    (R : Finset (Sym2 (Fin (2 * k)))) (target : ℕ) (htarget : target ≤ k) :
    (∀ M : Finset (Sym2 (Fin (2 * k))), IsPerfectMatching G M →
      ((M ∩ R).card = target ↔
        matchingLabelSum G (exactMatchingLabel G R) M = (target : ZMod (k + 1)))) ∧
    2 * k + (k + 1) ≤ (2 * k) ^ 2 := by
  sorry

/-- Theorem 2(b) bounded integer-weight shifted cyclic-group embedding into `ZMod (2kW + 1)`. -/
theorem step_thm2b_embedding {k : ℕ} (hk : 1 ≤ k) (W : ℕ)
    (G : SimpleGraph (Fin (2 * k))) [DecidableRel G.Adj]
    (w : UpperEdge G → ℤ) (hw : ∀ e, -(W : ℤ) ≤ w e ∧ w e ≤ (W : ℤ))
    (target : ℤ) (htarget : -(k * W : ℤ) ≤ target ∧ target ≤ (k * W : ℤ)) :
    (∀ M : Finset (Sym2 (Fin (2 * k))), IsPerfectMatching G M →
      ((∑ e : UpperEdge G, if s(e.val.val.1, e.val.val.2) ∈ M then w e else 0) = target ↔
        matchingLabelSum G (boundedWeightLabel W G w) M =
          ((target + (k * W : ℤ)) : ZMod (2 * k * W + 1)))) ∧
    2 * k + (2 * k * W + 1) ≤ (2 * k + W) ^ 2 := by
  sorry

/-- Theorem 2(c) ingredient (finite abelian group labels): under `HypothesisH c μ₀` and
`KI04_Cor_7_4`, there exist uniform `A, s₀, C_0, K' > 0` (and `K'_C > 0` for each `C > 0`) such
that on every even-vertex graph `G` (`n = 2k ≥ 2`) with edge labels `w : Sym2 (Fin (2k)) → Γ`
and target `γ* ∈ Γ`, setting `s := max (2*k) (C_0 * (2*k + |Γ|)^8)` yields:
1. the explicit group-ring Pfaffian circuit `C_pad : IntCircuit s` tested by `pitSmallTest` /
   `pitLargeTest` decides existence of a `γ*`-sum perfect matching;
2. `selfReduce` with that exact decision predicate recovers a valid `γ*`-sum perfect matching
   whenever one exists, in at most `|E(G)| + 1 ≤ (2k)^2` calls;
3. total evaluation points `(2k)^2 * pitEvalPointCount A μ₀ s₀ s * 2^{pitMu A μ₀ s} * s^4` is
   at most `exp₂(exp₂(K' (log₂(2k + |Γ|))^(3/4)))`, and at most `exp₂(exp₂(K'_C (log₂(2k))^(3/4)))`
   whenever `|Γ| ≤ (2k)^C`. -/
theorem thm_2c_decision_witness (hKI : KI04_Cor_7_4) (c : ℝ) (μ₀ : ℕ) (hH : HypothesisH c μ₀) :
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

/-- Theorem 2(a) ingredient (Exact Matching via `ZMod (k + 1)`): under `HypothesisH c μ₀` and
`KI04_Cor_7_4`, the explicit `ZMod (k + 1)` Pfaffian circuit + PIT test + `selfReduce` decides
and recovers a `target`-red perfect matching on any even-vertex graph (`n = 2k ≥ 2`) with total
evaluation count bounded by `exp₂(exp₂(K' (log₂(2k))^(3/4)))`. -/
theorem thm_2a_decision_witness (hKI : KI04_Cor_7_4) (c : ℝ) (μ₀ : ℕ) (hH : HypothesisH c μ₀) :
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

/-- Theorem 2(b) ingredient (bounded integer weights via shifted `ZMod (2kW + 1)`): under
`HypothesisH c μ₀` and `KI04_Cor_7_4`, the explicit shifted `ZMod (2kW + 1)` Pfaffian circuit +
PIT test + `selfReduce` decides and recovers a weight-`target` perfect matching with total
evaluation count bounded by `exp₂(exp₂(K' (log₂(2k + W))^(3/4)))` (and `K'_C` whenever
`W ≤ (2k)^C`). -/
theorem thm_2b_decision_witness (hKI : KI04_Cor_7_4) (c : ℝ) (μ₀ : ℕ) (hH : HypothesisH c μ₀) :
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

/-! ### Corollary 1 — Instantiation via `[A26]` Theorem 1.1 (**UNREFEREED**) -/

/-- Corollary 1 (unconditional implication): `[A26]` `MainTheorem` over `ℚ` implies `HypothesisH c μ₀`. -/
theorem cor_1_a26_implies_H (hA26 : A26_MainTheorem.{0}) :
    ∃ (c : ℝ) (μ₀ : ℕ), HypothesisH c μ₀ := by
  sorry

/-- Corollary 1 ingredient: conditional on `A26_MainTheorem` (**UNREFEREED**) and `KI04_Cor_7_4`,
`HypothesisH c μ₀` holds and yields the PIT test correctness and evaluation-point bounds. -/
theorem cor_1_implication (hA26 : A26_MainTheorem.{0}) (hKI : KI04_Cor_7_4) :
    ∃ (c : ℝ) (μ₀ : ℕ), HypothesisH c μ₀ ∧
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

/-! ### Remark 1 — Stronger permanent lower bound via `[O26]` Theorem 1.1 (**UNREFEREED**) -/

/-- Remark 1 logarithm inequality: `(ln μ)^2 / (ln ln μ)^2 > (log₂ μ)^2 / (log₂ log₂ μ)^2` for `μ ≥ 3`. -/
theorem step_rem1_ln_vs_log2 (μ : ℕ) (hμ : 3 ≤ μ) :
    (Real.logb 2 μ) ^ 2 / (Real.logb 2 (Real.logb 2 μ)) ^ 2 <
      (Real.log μ) ^ 2 / (Real.log (Real.log μ)) ^ 2 := by
  sorry

/-- Model inclusion: any `[A26]` circuit (`Computes f s`) is an `[O26]` exact circuit
(`O26ExactComputes f s`) with at most `s` binary gates. -/
theorem step_rem1_computes_to_o26 {R : Type u} {V : Type} [CommRing R]
    (f : MvPolynomial V R) (s : ℕ) (h : Computes f s) :
    O26ExactComputes f s := by
  sorry

/-- Remark 1 ingredient: conditional on `O26_Thm_1_1` (**UNREFEREED**) and `KI04_Cor_7_4`,
fixing `C₁ ≥ 4` and taking `μ = o26Mu C₁ N₀ s` yields explicit test correctness for
`pitSmallTest` / `o26LargeTest` and sharpened evaluation-point bound
`exp₂(exp₂(K'' (log₂ s)^(1/2) log₂ log₂(s + 2)))` (and `K'''`, `K'''_C` for matching sizes). -/
theorem rem_1_tradeoff (hO26 : O26_Thm_1_1) (hKI : KI04_Cor_7_4) :
    ∃ (C₁ N₀ s₀ : ℕ) (K'' : ℝ), 4 ≤ C₁ ∧ 3 ≤ N₀ ∧ 4 ≤ s₀ ∧ 0 < K'' ∧
      (∀ s ≥ s₀,
        Real.logb 2 s < (o26M C₁ N₀ s : ℝ) ∧
        o26M C₁ N₀ s < s ∧
        2 ≤ o26M C₁ N₀ s ∧
        s * o26Mu C₁ N₀ s + 1 ≤ s ^ 2) ∧
      (∀ (s : ℕ) (hs : 2 ≤ s) (C : IntCircuit s),
        C.encodingLength ≤ s →
        C.evalPoly.totalDegree ≤ s →
        CoeffBitBound C.evalPoly s →
        (s < s₀ → (pitSmallTest s C ↔ C.evalPoly = 0)) ∧
        (∀ (hge : s₀ ≤ s) (hm : 2 ≤ o26M C₁ N₀ s)
           (hcard : ∀ i : Fin s, (designSets (o26M C₁ N₀ s) s hm i).card = o26M C₁ N₀ s),
           o26LargeTest C₁ N₀ s hm hcard C ↔ C.evalPoly = 0)) ∧
      (∀ s ≥ 2,
        (o26EvalPointCount C₁ N₀ s₀ s : ℝ) * ((2 : ℝ) ^ o26Mu C₁ N₀ s) * ((s : ℝ) ^ 4) ≤
          expTwo (expTwo (K'' * (Real.logb 2 s) ^ (1 / 2 : ℝ) * Real.logb 2 (Real.logb 2 (s + 2))))) ∧
      (∀ (C_0 d_poly : ℕ), 1 ≤ C_0 → 1 ≤ d_poly → ∃ K''' : ℝ, 0 < K''' ∧
        ∀ (N : ℕ), 2 ≤ N →
          let s := max N (C_0 * N ^ d_poly)
          ((N : ℝ) ^ 2) * (o26EvalPointCount C₁ N₀ s₀ s : ℝ) *
            ((2 : ℝ) ^ o26Mu C₁ N₀ s) * ((s : ℝ) ^ 4) ≤
              expTwo (expTwo (K''' * (Real.logb 2 N) ^ (1 / 2 : ℝ) *
                Real.logb 2 (Real.logb 2 (N + 2))))) ∧
      (∀ (C_0 d_poly : ℕ) (C : ℝ), 1 ≤ C_0 → 1 ≤ d_poly → 0 < C → ∃ K'''_C : ℝ, 0 < K'''_C ∧
        ∀ (n M : ℕ), 2 ≤ n → (M : ℝ) ≤ (n : ℝ) ^ C →
          let s := max n (C_0 * (n + M) ^ d_poly)
          ((n : ℝ) ^ 2) * (o26EvalPointCount C₁ N₀ s₀ s : ℝ) *
            ((2 : ℝ) ^ o26Mu C₁ N₀ s) * ((s : ℝ) ^ 4) ≤
              expTwo (expTwo (K'''_C * (Real.logb 2 n) ^ (1 / 2 : ℝ) *
                Real.logb 2 (Real.logb 2 (n + 2))))) := by
  sorry

/-! ### Remark 2 — Alternative Lagrange interpolation identity (unconditional, tightened) -/

/-- Remark 2: there exist graph-independent integer Lagrange multipliers `coeff` of magnitude
at most `(2*(2kW) + 2)^(2kW)` (hence `O(nW log(nW))` bits) such that for every even-vertex
graph `G` (`n = 2k ≥ 2`) and shifted weights `w'(e) ≤ 2W`,
`∑_{j=0}^{2kW} coeff j * Pf(interpMatrix G w' j) = (2kW)! * weightFiberPoly G w' k'`. -/
theorem rem_2_interpolation {k : ℕ} (hk : 1 ≤ k) (W : ℕ) (k' : ℕ) (hk' : k' ≤ 2 * k * W) :
    ∃ coeff : Fin (2 * k * W + 1) → ℤ,
      (∀ j, (coeff j).natAbs ≤ (2 * (2 * k * W) + 2) ^ (2 * k * W)) ∧
      ∀ (G : SimpleGraph (Fin (2 * k))) [DecidableRel G.Adj]
        (w' : UpperEdge G → ℕ), (∀ e, w' e ≤ 2 * W) →
        ∑ j : Fin (2 * k * W + 1),
          MvPolynomial.C (coeff j) * pfaffian (interpMatrix G w' (j.val : ℤ)) =
        MvPolynomial.C (((2 * k * W).factorial : ℤ)) * weightFiberPoly G w' k' := by
  sorry

end ExactMatching.Paper
