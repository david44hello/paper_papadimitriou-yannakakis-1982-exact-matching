# Guide to the Lean 4 formalization

This guide summarizes the Lean 4 formalization of *Exact Matching (Papadimitriou–Yannakakis, 1982) in Deterministic Time $2^{n^{o(1)}}$ from Permanent Lower Bounds*, its definitions, its explicit cited hypotheses, its proof architecture, and its verification record.

## 1. Definitions and trust surface

All definitions and cited hypothesis types appearing in the theorem statements live in `ExactMatching/Defs/` (zero custom `axiom` declarations):

- `ExactMatching/Defs/Circuits.lean`: integer arithmetic circuits (`IntCircuit n`), strictly division-free rational circuits (`RatCircuit m`), `[A26]` circuit evaluation (`Computes`), `[O26]` exact circuit evaluation (`O26ExactComputes`), permanent polynomials (`paperPerm`, `perm`), `IsMultilinear`, `CoeffBitBound`, and `expTwo`.
- `ExactMatching/Defs/Design.lean`: explicit finite-field polynomial-graph design parameters (`designR`, `designQ`, `designL`, `designT`), explicit sets `designSets`, and the Nisan–Wigderson polynomial map `nwMap`.
- `ExactMatching/Defs/PitAlgorithm.lean`: Ryser's permanent formula (`ryserPerm`), Theorem 1 parameters (`pitMu`, `pitM`, `pitB`, `pitEvalPointCount`), explicit small-input (`pitSmallTest`) and large-input (`pitLargeTest`) mod-$2^B$ PIT tests, and Remark 1 `[O26]` parameters (`o26Mu`, `o26M`, `o26LargeTest`, `o26EvalPointCount`).
- `ExactMatching/Defs/PfaffianMatching.lean`: ordered pairings (`OrderedPairing k`), Pfaffian (`pfaffian`), universal skew-symmetric Pfaffian (`universalPfaffian`), perfect matchings (`IsPerfectMatching`), integral group-ring Tutte matrix (`tutteMatrix`, `groupRingPoly`), edge-deletion self-reduction (`selfReduce`), Exact Matching and bounded-weight cyclic embeddings (`exactMatchingLabel`, `boundedWeightLabel`), and Remark 2 interpolation matrix (`interpMatrix`, `weightFiberPoly`).
- `ExactMatching/Defs/CitedHypotheses.lean`: Hypothesis `HypothesisH c μ₀`, the now-proved `KI04_Cor_7_4` proposition, and the two remaining unrefereed hypothesis propositions (`A26_MainTheorem`, `O26_Thm_1_1`).

## 2. Axioms and explicit cited hypotheses

Zero custom `axiom` declarations and zero `sorry`s exist anywhere in the project. Every checked declaration in `ExactMatching/Paper/Statements.lean` depends strictly on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

- **32 of 35 declarations** are PROVED from Lean's three standard axioms alone, with zero external hypotheses remaining — including Lemma 2.1, Lemma 2.2, Theorem 1 (test correctness, evaluation-point bound, and all supporting steps), Proposition 3.1 (including `pfaffian_clow_circuit_exists`, removing `[MSV04]`), Theorem 2(a)–(c) (decision, witness recovery, self-reduction, and embeddings), Remark 2, and `ki04_cor_7_4 : KI04_Cor_7_4` (removing `[KI04]` Corollary 7.4).
- **3 of 35 declarations** take one of the following two unrefereed external results as an explicit named hypothesis, verified mechanically by `scripts/audit.py`:
  1. **`A26_MainTheorem`** (**UNREFEREED**): Claude (Anthropic), *$\mathrm{VP} \neq \mathrm{VNP}$ over every field*, preprint and Lean 4 formalization, November 23, 2026, Theorem 1.1 (`Statement.lean`, p. 11). Token-for-token identical to the source statement. `HypothesisH` uses the paper's row-indexed permanent `paperPerm`, and `[A26]`'s column-indexed `perm` is proved equal to `paperPerm` by `ExactMatching.Paper.paperPerm_eq_perm`. Explicit hypothesis of `cor_1_a26_implies_H` and `cor_1_implication`.
  2. **`O26_Thm_1_1`** (**UNREFEREED**): OpenAI, *Circuit lower bounds for Hamiltonian cycle and the permanent*, preprint and Lean 4 formalization, November 24, 2026, Theorem 1.1 (pp. 1–2). Explicit hypothesis of `rem_1_tradeoff`.

## 3. Main statements and scope

All 35 formalized declarations live in `ExactMatching/Paper/Statements.lean` and are indexed in `CLAIM_MAP.tsv` and `AUDIT.md`:

- **Lemma 2.1** (`lem_2_1_irred_exists`, `lem_2_1_design`): PROVED.
- **Root-finding circuit existence** (`ki04_cor_7_4 : KI04_Cor_7_4`): PROVED.
- **Lemma 2.2** (`lem_2_2_reconstruction`, `step_2_2_nonvanishing`, `step_2_2_model_transfer`): PROVED.
- **Theorem 1** (`thm_1_test_correct`, `thm_1_eval_points`, plus all 6 supporting steps): PROVED (under the paper's own stated `HypothesisH c μ₀`).
- **Proposition 3.1** (`prop_3_1_pfaffian_identity`, `prop_3_1_cyclic_rank_bound`, `pfaffian_clow_circuit_exists`, `prop_3_1_wire_expansion`, `prop_3_1_pfaffian_circuit`): PROVED.
- **Theorem 2(a)–(c)** (`thm_2a_decision_witness`, `thm_2b_decision_witness`, `thm_2c_decision_witness`, plus all 4 reduction/embedding steps): PROVED (under the paper's own stated `HypothesisH c μ₀`).
- **Corollary 1** (`cor_1_a26_implies_H`, `cor_1_implication`): PROVED GIVEN `A26_MainTheorem` (UNREFEREED).
- **Remark 1** (`rem_1_tradeoff`, plus `step_rem1_ln_vs_log2`, `step_rem1_computes_to_o26`): tradeoff PROVED GIVEN `O26_Thm_1_1` (UNREFEREED); both supporting steps PROVED.
- **Remark 2** (`rem_2_interpolation`): PROVED.

**Items not formalized:** Deterministic Turing-machine running-time bounds (`thm_1_time`, `thm_2a_time`, `thm_2b_time`, `thm_2c_time`, `cor_1_time`, `rem_1_time`, `lem_2_1_time`, `prop_3_1_time`: no time-bounded computation in Lean's library) and randomized/parallel complexity remarks (`cov_tab1_rnc_rp`: `RNC`, `RP`, `coRP` in Table 1: no randomized or parallel complexity in Lean's library).

## 4. Route differences

- Proposition 3.1's division-free $\{0, \pm 1\}$-constant Pfaffian circuit (`pfaffian_clow_circuit_exists`) is proved from Lean's three standard axioms alone in `ExactMatching/Proofs/PfaffianClowAlgebra.lean` and `ExactMatching/Proofs/PfaffianClowDP.lean` via the 3-index alternating-clow-sequence dynamic program and an explicit 3-case sign-reversing involution (`dpCircuit` of size at most $27 k^4$), rather than taking Mahajan–Subramanya–Vinay (2004) as an external hypothesis.
- `[KI04]` Corollary 7.4 (`ki04_cor_7_4 : KI04_Cor_7_4`) is proved from Lean's three standard axioms alone in `ExactMatching/Proofs/StrassenHomog.lean` and `ExactMatching/Proofs/KI04Newton.lean` via Vandermonde Hasse-derivative extraction, coupled division-free quadratic Newton iteration modulo `(z_1, ..., z_m)^{2^k}`, and Strassen homogenization up to degree `d` (`O((s + d + a + 2)^6)` gates), rather than invoking Kaltofen's probabilistic factoring algorithm.

## 5. Verification

Verification procedure (Lean `v4.35.0`, Mathlib `v4.35.0`):

- **Build and axiom audit (`./scripts/check.sh`):** Builds all 22 Lean modules with zero `sorry`s and zero custom `axiom` declarations, and runs `python3 scripts/audit.py` to verify all 35 declarations depend strictly on `[propext, Classical.choice, Quot.sound]` (32 declarations with zero external hypotheses; 3 declarations with explicit unrefereed hypotheses `A26_MainTheorem` / `O26_Thm_1_1`).
- **Independent kernel replay (`./scripts/kernel_replay.sh`):** Replays all exported proof terms through the bundled independent checkers (`leanchecker`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`).
- **Statement comparison (`comparator/README.md`):** Runs `lake --no-cache comparator --config=comparator.json --paranoid` against the minimal-mode `Challenge.lean` across all 35 target declarations.

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see [LICENSE](../LICENSE).
