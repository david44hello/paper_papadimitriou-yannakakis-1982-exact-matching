# Guide to the Lean 4 formalization

This guide summarizes the Lean 4 formalization of *Exact Matching (Papadimitriou–Yannakakis, 1982) in Deterministic Time $2^{n^{o(1)}}$ from Permanent Lower Bounds*, its definitions, its explicit cited hypotheses, its proof architecture, and its verification record.

## 1. Definitions and trust surface

All definitions and cited hypothesis types appearing in the theorem statements live in `ExactMatching/Defs/` (zero custom `axiom` declarations):

- `ExactMatching/Defs/Circuits.lean`: integer arithmetic circuits (`IntCircuit n`, binary gates `+`, `-`, `×`, integer constants, `UsesOnlyUnitConstants`, `encodingLength`, `evalAt`, `evalPoly`), strictly division-free rational circuits (`RatCircuit m`), `[A26]` circuit evaluation (`Computes`), `[O26]` exact circuit evaluation (`O26ExactComputes`), permanent polynomials (`paperPerm`, `perm`), `IsMultilinear`, `CoeffBitBound`, and `expTwo`.
- `ExactMatching/Defs/Design.lean`: explicit finite-field polynomial-graph design parameters (`designR`, `designQ`, `designL`, `designT`), explicit sets `designSets`, and the Nisan–Wigderson polynomial map `nwMap`.
- `ExactMatching/Defs/PitAlgorithm.lean`: Ryser's permanent formula (`ryserPerm`), Theorem 1 parameters (`pitMu`, `pitM`, `pitB`, `pitEvalPointCount`), explicit small-input (`pitSmallTest`) and large-input (`pitLargeTest`) mod-$2^B$ PIT tests, and Remark 1 `[O26]` parameters (`o26Mu`, `o26M`, `o26LargeTest`, `o26EvalPointCount`).
- `ExactMatching/Defs/PfaffianMatching.lean`: ordered pairings (`OrderedPairing k`), Pfaffian (`pfaffian`), universal skew-symmetric Pfaffian (`universalPfaffian`), perfect matchings (`IsPerfectMatching`), integral group-ring Tutte matrix (`tutteMatrix`, `groupRingPoly`), edge-deletion self-reduction (`selfReduce`), Exact Matching and bounded-weight cyclic embeddings (`exactMatchingLabel`, `boundedWeightLabel`), and Remark 2 interpolation matrix (`interpMatrix`, `weightFiberPoly`).
- `ExactMatching/Defs/CitedHypotheses.lean`: Hypothesis `HypothesisH c μ₀` and the three explicit cited hypothesis propositions (`KI04_Cor_7_4`, `A26_MainTheorem`, `O26_Thm_1_1`).

## 2. Axioms and explicit cited hypotheses

Zero custom `axiom` declarations and zero `sorry`s exist anywhere in the project. Every checked declaration in `ExactMatching/Paper/Statements.lean` depends strictly on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

- **26 of 34 declarations** are proved unconditionally from Lean's three standard axioms alone, including Lemma 2.1, Proposition 3.1 (together with the unconditional division-free alternating-clow-sequence Pfaffian circuit construction `pfaffian_clow_circuit_exists`, which removes the `[MSV04]` assumption entirely), Remark 2, and all algebraic, combinatorial, and parameter/evaluation-count ingredients.
- **8 of 34 declarations** take one or two of the following three external results as explicit named hypotheses, verified mechanically by `scripts/audit.py`:
  1. **`KI04_Cor_7_4`** (**REFEREED**): V. Kabanets and R. Impagliazzo, *Derandomizing polynomial identity tests means proving circuit lower bounds*, Comput. Complexity 13 (2004), 1–46, Corollary 7.4 (p. 34; via Kaltofen 1989, Theorem 7.2, p. 33, and Section 2.3, pp. 12–13). Explicit hypothesis of `lem_2_2_reconstruction`, `thm_1_test_correct`, `thm_2a_decision_witness`, `thm_2b_decision_witness`, `thm_2c_decision_witness`, `cor_1_implication`, and `rem_1_tradeoff`.
     - The source states a probabilistic polynomial-time algorithm for root finding; the formalization uses only that its output circuit exists with the polynomial size bound given by Theorem 7.2 (`poly(s, d, a)` over `ℚ`, where `a` is the maximum coefficient bit-length).
     - "Division-free" (`+`, `-`, `×`, rational constants, and multiplication by constants, represented by `RatCircuit`) is the source's own arithmetic-circuit model of Section 2.3 (p. 12).
     - Because Section 2.3's model is already division-free, the paper's fallback sentence on Strassen's division elimination (`[Str73]`) is not used.
  2. **`A26_MainTheorem`** (**UNREFEREED**): Claude (Anthropic), *$\mathrm{VP} \neq \mathrm{VNP}$ over every field*, preprint and Lean 4 formalization, November 23, 2026, Theorem 1.1 (`Statement.lean`, p. 11). Token-for-token identical to the source statement. `HypothesisH` uses the paper's row-indexed permanent `paperPerm`, and `[A26]`'s column-indexed `perm` is proved equal to `paperPerm` unconditionally by `ExactMatching.Paper.paperPerm_eq_perm`. Explicit hypothesis of `cor_1_a26_implies_H` and `cor_1_implication`.
  3. **`O26_Thm_1_1`** (**UNREFEREED**): OpenAI, *Circuit lower bounds for Hamiltonian cycle and the permanent*, preprint and Lean 4 formalization, November 24, 2026, Theorem 1.1 (pp. 1–2). Explicit hypothesis of `rem_1_tradeoff`.

## 3. Main statements and scope

All 34 formalized declarations live in `ExactMatching/Paper/Statements.lean` and are indexed in `CLAIM_MAP.tsv` and `AUDIT.md`:

- **Lemma 2.1** (`lem_2_1_irred_exists`, `lem_2_1_design`): proved unconditionally.
- **Lemma 2.2** (`lem_2_2_reconstruction`, plus `step_2_2_nonvanishing`, `step_2_2_model_transfer`): full statement proved given `KI04_Cor_7_4` (both supporting steps proved unconditionally).
- **Theorem 1** (`thm_1_test_correct`, `thm_1_eval_points`, plus `step_thm1_eq1`, `step_thm1_threshold`, `step_thm1_ryser`, `step_thm1_small_inputs`, `step_thm1_modulus_exact`, `step_thm1_B_bound`): test correctness proved given `KI04_Cor_7_4`; evaluation-point bound and all six supporting steps proved unconditionally.
- **Proposition 3.1** (`prop_3_1_pfaffian_identity`, `prop_3_1_cyclic_rank_bound`, `pfaffian_clow_circuit_exists`, `prop_3_1_wire_expansion`, `prop_3_1_pfaffian_circuit`): all five declarations proved unconditionally.
- **Theorem 2(a)–(c)** (`thm_2a_decision_witness`, `thm_2b_decision_witness`, `thm_2c_decision_witness`, plus `step_thm2_odd_n`, `step_thm2c_self_reduction`, `step_thm2a_embedding`, `step_thm2b_embedding`): decision and witness-recovery ingredients proved given `KI04_Cor_7_4`; all four reduction/embedding steps proved unconditionally.
- **Corollary 1** (`cor_1_a26_implies_H`, `cor_1_implication`): proved given `A26_MainTheorem` (UNREFEREED) and `KI04_Cor_7_4`.
- **Remark 1** (`rem_1_tradeoff`, plus `step_rem1_ln_vs_log2`, `step_rem1_computes_to_o26`): tradeoff and test correctness proved given `O26_Thm_1_1` (UNREFEREED) and `KI04_Cor_7_4`; both supporting steps proved unconditionally.
- **Remark 2** (`rem_2_interpolation`): proved unconditionally with explicit graph-independent integer multipliers of magnitude at most $(2(2kW)+2)^{2kW}$.

**Items not formalized:** Deterministic Turing-machine running-time bounds (`thm_1_time`, `thm_2a_time`, `thm_2b_time`, `thm_2c_time`, `cor_1_time`, `rem_1_time`, `lem_2_1_time`, `prop_3_1_time`: no time-bounded computation in Lean's library) and randomized/parallel complexity remarks (`cov_tab1_rnc_rp`: `RNC`, `RP`, `coRP` in Table 1: no randomized or parallel complexity in Lean's library).

## 4. Route differences

- Proposition 3.1's division-free $\{0, \pm 1\}$-constant Pfaffian circuit (`pfaffian_clow_circuit_exists`) is proved unconditionally from Lean's three standard axioms alone in `ExactMatching/Proofs/PfaffianClowAlgebra.lean` and `ExactMatching/Proofs/PfaffianClowDP.lean` via the 3-index alternating-clow-sequence dynamic program and an explicit 3-case sign-reversing involution (`dpCircuit` of size at most $27 k^4$), rather than taking Mahajan–Subramanya–Vinay (2004) as an external hypothesis.

## 5. Verification record

All checks below ran on the exact Lean sources (`ExactMatching.lean`, `ExactMatching/**/*.lean`, `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, Lean `v4.35.0`, Mathlib `v4.35.0`) and comparator inputs (`comparator/ExactMatching/Paper/Challenge.lean`, `comparator/comparator.json`):

- **Clean build from empty and audit (`./scripts/check.sh`):** All 20 modules (`ExactMatching`, `ExactMatching.Defs.*`, `ExactMatching.Proofs.*`, `ExactMatching.Paper.Statements`) built cleanly from an empty build directory (`656 s`, peak RSS `3.49 GB`), ending with `Checked 34 Lean declarations against the three permitted standard axioms.`
- **Independent `#print axioms` probe:** Confirmed all 34 public declarations in `ExactMatching/Paper/Statements.lean` depend strictly on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), with zero custom `axiom` declarations and zero `sorry`s (`34 = 34 standard-only + 0 custom`, `6 s`).
- **Per-module kernel replay and whole-library export (`scripts/kernel_replay.sh`, `965 s`):**
  - Per-module `leanchecker` replay on all 19 declaration-bearing modules: **PASS** (`241 s`, peak RSS `2.8 GB`).
  - Whole-library `leanexport`: `2,213` safe project constants plus transitive core and Mathlib dependencies (`43,643` declaration records, `311 MB`, `39 s`, peak RSS `3.3 GB`, export SHA-256 `face64e02d8c4e8ddad83d30e1b539c06a8610a9189b6f3606bd812bfef2ec83`; declared axioms strictly `propext`, `Quot.sound`, `Classical.choice`; `11` unsafe/partial compiler helpers replayed in per-module `leanchecker` only).
  - Independent export checkers (from an empty environment, `0` failures, `0` skips): `leanchecker --from-export` (**PASS**, `43,643` records, `131 s`), `leanchecker-paranoid --from-export` (**PASS**, `43,643` records, `164 s`), `lean4lean --import` (**PASS**, `43,640` declarations, `191 s`), `nanoda` (**PASS**, `45,442` declarations, `63 s`), `con-leche --verified` (**PASS**, `43,643` declarations, `82 s`), and `con-ron --verified` (**PASS**, `43,643` declarations, `39 s`).
- **Statement comparison (`lake comparator --config comparator.json`):**
  - Minimal-mode challenge `comparator/ExactMatching/Paper/Challenge.lean` imports strictly `ExactMatching.Defs.*` (zero `ExactMatching.Proofs.*` imports) and matches all 34 theorem signatures verbatim against `ExactMatching/Paper/Statements.lean` with every proof body replaced by `sorry`.
  - Standard mode (`230 s` active): accepted by Lean's default kernel (`Your solution is okay!`).
  - Paranoid mode (`--paranoid`, `872 s`): accepted by all six kernels (`leanchecker`, `leanchecker-paranoid`, `lean4lean` `43,244` declarations, `nanoda`, `con-leche --verified` `43,247` declarations, `con-ron --verified` `43,247` declarations, `Your solution is okay!`).

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see [LICENSE](../LICENSE).
