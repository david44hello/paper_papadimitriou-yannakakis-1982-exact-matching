# Audit notes

This document records the scope, explicit cited hypotheses, proof architecture, and route differences for the Lean 4 formalization of *Exact Matching (Papadimitriou–Yannakakis, 1982) in Deterministic Time $2^{n^{o(1)}}$ from Permanent Lower Bounds*.

## Axioms and cited external results (zero custom `axiom` declarations, zero refereed hypotheses remaining)

Every one of the 35 checked declarations in `ExactMatching/Paper/Statements.lean` depends strictly on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), with zero custom `axiom` declarations and zero `sorry`s.

- **32 declarations** are PROVED from Lean's three standard axioms alone, with zero external hypotheses — including Lemma 2.1, Lemma 2.2, Theorem 1 (test correctness, evaluation-point bound, and all six supporting steps), Proposition 3.1 (group-ring Tutte–Pfaffian identity, wire expansion, and the division-free alternating-clow-sequence Pfaffian circuit construction `pfaffian_clow_circuit_exists`, removing `[MSV04]`), Theorem 2(a)–(c) (decision, witness recovery, self-reduction, and cyclic embeddings), Remark 2, and `ki04_cor_7_4 : KI04_Cor_7_4` (proved via coupled division-free quadratic Newton iteration and Strassen homogenization, removing `[KI04]` Corollary 7.4 as an external hypothesis completely).
- **3 declarations** take one of the following two unrefereed external results as an explicit named hypothesis (`ExactMatching/Defs/CitedHypotheses.lean`), verified mechanically by `scripts/audit.py`:
  1. **`A26_MainTheorem`** (**UNREFEREED**): Claude (Anthropic), *$\mathrm{VP} \neq \mathrm{VNP}$ over every field*, preprint and Lean 4 formalization, November 23, 2026, Theorem 1.1 (`Statement.lean`, p. 11). Token-for-token identical to the source statement; bridged to `paperPerm` via `paperPerm_eq_perm`. Used as an explicit hypothesis in `cor_1_a26_implies_H` and `cor_1_implication`.
  2. **`O26_Thm_1_1`** (**UNREFEREED**): OpenAI, *Circuit lower bounds for Hamiltonian cycle and the permanent*, preprint and Lean 4 formalization, November 24, 2026, Theorem 1.1 (pp. 1–2). Used as an explicit hypothesis in `rem_1_tradeoff`.

## Scope (items not formalized)

- **Deterministic Turing-machine running-time clauses** (`thm_1_time`, `thm_2a_time`, `thm_2b_time`, `thm_2c_time`, `cor_1_time`, `rem_1_time`, `lem_2_1_time`, `prop_3_1_time`): not formalized (no time-bounded computation in Lean's library).
- **Randomized and parallel complexity classes** (`cov_tab1_rnc_rp`: `RNC`, `RP`, `coRP` in Table 1): not formalized (no randomized or parallel complexity in Lean's library).

## Proof modules

- `ExactMatching/Defs/{Circuits,Design,PitAlgorithm,PfaffianMatching,CitedHypotheses}.lean`: trust surface (all definitions and explicit hypothesis types).
- `ExactMatching/Proofs/Design.lean`: Lemma 2.1 (`lem_2_1_irred_exists`, `lem_2_1_design`).
- `ExactMatching/Proofs/CircuitsTransfer.lean`: `paperPerm_eq_perm`, `step_2_2_nonvanishing`, `step_2_2_model_transfer`, `step_rem1_computes_to_o26`.
- `ExactMatching/Proofs/StrassenHomog.lean`, `KI04Newton.lean`: unconditional proof of `KI04_Cor_7_4` (`ki04_cor_7_4`) via Vandermonde Hasse-derivative extraction, coupled division-free quadratic Newton iteration modulo `(z_1, ..., z_m)^{2^k}`, and Strassen homogenization up to degree `d`.
- `ExactMatching/Proofs/Reconstruction.lean`: hybrid argument, coefficient bit-length bounds, and Lemma 2.2 (`lem_2_2_reconstruction`).
- `ExactMatching/Proofs/PitBounds.lean`, `PitMain.lean`, `Remark1O26.lean`: Theorem 1, Corollary 1, Remark 1, and all quantitative PIT bounds.
- `ExactMatching/Proofs/PfaffianPairingHelpers.lean`, `PfaffianClowAlgebra.lean`, `PfaffianClowDP.lean`: unconditional `[MSV04]` alternating-clow-sequence Pfaffian algebra and $O(k^4)$ division-free $\{0, \pm 1\}$-constant circuit (`pfaffian_clow_circuit_exists`).
- `ExactMatching/Proofs/PfaffianIdentity.lean`, `WireExpansion.lean`, `MatchingReductions.lean`, `MatchingMain.lean`: Proposition 3.1, Theorem 2(a)–(c), and Remark 2.

## Route differences

- Proposition 3.1's division-free Pfaffian circuit (`pfaffian_clow_circuit_exists`) is proved from Lean's three standard axioms alone via the 3-index alternating-clow-sequence DP and sign-reversing involution (`dpCircuit` of size $\le 27 k^4$), rather than taking Mahajan–Subramanya–Vinay (2004) as an external hypothesis.
- `[KI04]` Corollary 7.4 (`ki04_cor_7_4 : KI04_Cor_7_4`) is proved from Lean's three standard axioms alone via Vandermonde-interpolated Hasse derivatives, coupled division-free quadratic Newton iteration, and Strassen homogenization (`O((s + d + a + 2)^6)` gates), rather than invoking Kaltofen's probabilistic factoring algorithm.

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see [LICENSE](../LICENSE).
