# Audit notes

This document records the scope, explicit cited hypotheses, proof architecture, and route differences for the Lean 4 formalization of *Exact Matching (Papadimitriou–Yannakakis, 1982) in Deterministic Time $2^{n^{o(1)}}$ from Permanent Lower Bounds*.

## Axioms and cited external results (zero custom `axiom` declarations)

Every one of the 34 checked declarations in `ExactMatching/Paper/Statements.lean` depends strictly on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), with zero custom `axiom` declarations and zero `sorry`s.

- **26 declarations** are proved unconditionally from Lean's three standard axioms alone, including Lemma 2.1 (explicit polynomial-graph design), Proposition 3.1 (group-ring Tutte–Pfaffian identity, wire expansion, and the unconditional division-free alternating-clow-sequence Pfaffian circuit construction `pfaffian_clow_circuit_exists`, removing the `[MSV04]` assumption entirely), Remark 2 (Lagrange interpolation identity), and all algebraic, combinatorial, and quantitative parameter/evaluation-count ingredients.
- **8 declarations** take one or two of the following three cited external results as explicit named hypotheses (`ExactMatching/Defs/CitedHypotheses.lean`), verified mechanically by `scripts/audit.py`:
  1. **`KI04_Cor_7_4`** (**REFEREED**): V. Kabanets and R. Impagliazzo, *Derandomizing polynomial identity tests means proving circuit lower bounds*, Comput. Complexity 13 (2004), 1–46, Corollary 7.4 (p. 34; circuit model pp. 12, 33). Used as an explicit hypothesis in `lem_2_2_reconstruction`, `thm_1_test_correct`, `thm_2a_decision_witness`, `thm_2b_decision_witness`, `thm_2c_decision_witness`, `cor_1_implication`, and `rem_1_tradeoff`.
  2. **`A26_MainTheorem`** (**UNREFEREED**): Claude (Anthropic), *$\mathrm{VP} \neq \mathrm{VNP}$ over every field*, preprint and Lean 4 formalization, November 23, 2026, Theorem 1.1 (`Statement.lean`, p. 11). Token-for-token identical to the source statement. Used as an explicit hypothesis in `cor_1_a26_implies_H` and `cor_1_implication`.
  3. **`O26_Thm_1_1`** (**UNREFEREED**): OpenAI, *Circuit lower bounds for Hamiltonian cycle and the permanent*, preprint and Lean 4 formalization, November 24, 2026, Theorem 1.1 (pp. 1–2). Used as an explicit hypothesis in `rem_1_tradeoff`.

## Scope (items not formalized)

- **Deterministic Turing-machine running-time clauses** (`thm_1_time`, `thm_2a_time`, `thm_2b_time`, `thm_2c_time`, `cor_1_time`, `rem_1_time`, `lem_2_1_time`, `prop_3_1_time`): not formalized (no time-bounded computation in Lean's library). All mathematical ingredients (test correctness, evaluation-point counts, modulus bit-length bounds, explicit circuit constructions and encoding-length bounds, self-reduction query counts, and group embeddings) are proved as separate theorems.
- **Randomized and parallel complexity classes** (`cov_tab1_rnc_rp`: `RNC`, `RP`, `coRP` in Table 1): not formalized (no randomized or parallel complexity in Lean's library).

## Proof modules

- `ExactMatching/Defs/Circuits.lean`, `Design.lean`, `PitAlgorithm.lean`, `PfaffianMatching.lean`, `CitedHypotheses.lean`: trust surface (all definitions and explicit hypothesis types).
- `ExactMatching/Proofs/Design.lean`: Lemma 2.1 (`lem_2_1_irred_exists`, `lem_2_1_design`).
- `ExactMatching/Proofs/CircuitsTransfer.lean`: permanent row/column equivalence (`paperPerm_eq_perm`), multivariate grid nonvanishing (`step_2_2_nonvanishing`), `RatCircuit`-to-`Computes` model transfer and functional-to-formal lift (`step_2_2_model_transfer`), and `Computes`-to-`O26ExactComputes` inclusion (`step_rem1_computes_to_o26`).
- `ExactMatching/Proofs/Reconstruction.lean`: hybrid argument, polynomial coefficient bit-length bounds, and Lemma 2.2 (`lem_2_2_reconstruction`).
- `ExactMatching/Proofs/PitBounds.lean`: Ryser's formula (`step_thm1_ryser`), small-input and large-input mod-$2^B$ exactness (`step_thm1_small_inputs`, `step_thm1_modulus_exact`), parameter inequalities (`step_thm1_eq1`, `step_thm1_threshold`, `step_thm1_B_bound`, `thm_1_eval_points`), asymptotic comparisons (`cov_asymptotic_between`, `cov_grid_prior_pit`), and Remark 1 log inequality (`step_rem1_ln_vs_log2`).
- `ExactMatching/Proofs/PitMain.lean`: Theorem 1 test correctness (`thm_1_test_correct`) and Corollary 1 (`cor_1_a26_implies_H`, `cor_1_implication`).
- `ExactMatching/Proofs/Remark1O26.lean`: Remark 1 parameter tradeoff and test correctness (`rem_1_tradeoff`).
- `ExactMatching/Proofs/PfaffianPairingHelpers.lean`, `PfaffianClowAlgebra.lean`, `PfaffianClowDP.lean`: unconditional Mahajan–Subramanya–Vinay alternating-clow-sequence Pfaffian algebra (`dpAns A = pfaffian A` via sign-reversing involution) and explicit $O(k^4)$ division-free $\{0, \pm 1\}$-constant circuit (`pfaffian_clow_circuit_exists`).
- `ExactMatching/Proofs/PfaffianIdentity.lean`: group-ring Tutte–Pfaffian identity (`prop_3_1_pfaffian_identity`), cyclic rank bound (`prop_3_1_cyclic_rank_bound`), and Remark 2 Lagrange interpolation identity (`rem_2_interpolation`).
- `ExactMatching/Proofs/WireExpansion.lean`: uniform $\mathbb{Z}[\Gamma]$ wire expansion (`prop_3_1_wire_expansion`).
- `ExactMatching/Proofs/MatchingReductions.lean`: odd-$n$ impossibility (`step_thm2_odd_n`), edge-deletion self-reduction (`step_thm2c_self_reduction`), and cyclic-group embeddings (`step_thm2a_embedding`, `step_thm2b_embedding`).
- `ExactMatching/Proofs/MatchingMain.lean`: combined Proposition 3.1 circuit (`prop_3_1_pfaffian_circuit`) and Theorem 2(a)–(c) decision and witness-recovery theorems (`thm_2a_decision_witness`, `thm_2b_decision_witness`, `thm_2c_decision_witness`).

## Route differences

- Proposition 3.1's division-free Pfaffian circuit (`pfaffian_clow_circuit_exists`) is proved unconditionally from Lean's three standard axioms alone via the 3-index alternating-clow-sequence DP and sign-reversing involution (`dpCircuit` of size $\le 27 k^4$), rather than taking Mahajan–Subramanya–Vinay (2004) as an external hypothesis.

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see [LICENSE](../LICENSE).
