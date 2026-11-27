# Paper claim audit

Every formalized declaration below depends strictly on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), with zero custom `axiom` declarations. Cited external results (`KI04_Cor_7_4`, `A26_MainTheorem`, `O26_Thm_1_1`) enter solely as explicit hypotheses of the theorems that use them, verified mechanically below.

| Claim ID | Paper ref | Plain name | Status | Lean declaration | Cited hypotheses |
|---|---|---|---|---|---|
| `thm_1_time` | Theorem 1 (L172-174, L280-321) | Theorem 1 (deterministic time bound) | not formalized: no time-bounded computation in Lean's library | — | NONE |
| `thm_1_test_correct` | Theorem 1 (L172-174, L293-314) | Theorem 1 ingredient: the test is correct | PROVED GIVEN [KI04] Corollary 7.4 | `ExactMatching.Paper.thm_1_test_correct` | KI04_Cor_7_4 (refereed) |
| `thm_1_eval_points` | Theorem 1 (L172-174, L316-320) | Theorem 1 ingredient: the number of evaluation points | PROVED | `ExactMatching.Paper.thm_1_eval_points` | NONE |
| `thm_2a_time` | Theorem 2(a) (L178-181, L398, L402) | Theorem 2(a) (Exact Matching deterministic time bound) | not formalized: no time-bounded computation in Lean's library | — | NONE |
| `thm_2a_decision_witness` | Theorem 2(a) (L178-181, L398, L402) | Theorem 2(a) ingredient: Exact Matching decision and witness recovery | PROVED GIVEN [KI04] Corollary 7.4 | `ExactMatching.Paper.thm_2a_decision_witness` | KI04_Cor_7_4 (refereed) |
| `thm_2b_time` | Theorem 2(b) (L178-179, L182, L400, L402) | Theorem 2(b) (bounded integer weights deterministic time bound) | not formalized: no time-bounded computation in Lean's library | — | NONE |
| `thm_2b_decision_witness` | Theorem 2(b) (L178-179, L182, L400, L402) | Theorem 2(b) ingredient: bounded integer-weight decision and witness recovery | PROVED GIVEN [KI04] Corollary 7.4 | `ExactMatching.Paper.thm_2b_decision_witness` | KI04_Cor_7_4 (refereed) |
| `thm_2c_time` | Theorem 2(c) (L178-179, L183, L390-396, L402) | Theorem 2(c) (abelian-group labels deterministic time bound) | not formalized: no time-bounded computation in Lean's library | — | NONE |
| `thm_2c_decision_witness` | Theorem 2(c) (L178-179, L183, L390-396, L402) | Theorem 2(c) ingredient: abelian-group decision and witness recovery | PROVED GIVEN [KI04] Corollary 7.4 | `ExactMatching.Paper.thm_2c_decision_witness` | KI04_Cor_7_4 (refereed) |
| `cor_1_time` | Corollary 1 (L187-189) | Corollary 1 (deterministic time bound from [A26]) | not formalized: no time-bounded computation in Lean's library | — | NONE |
| `cor_1_a26_implies_H` | Corollary 1 (L170, L188) | Corollary 1 ingredient: [A26] Theorem 1.1 implies Hypothesis H(c) | PROVED GIVEN [A26] Theorem 1.1 (UNREFEREED) | `ExactMatching.Paper.cor_1_a26_implies_H` | A26_MainTheorem (UNREFEREED) |
| `cor_1_implication` | Corollary 1 (L187-189) | Corollary 1 ingredient: [A26] Theorem 1.1 yields PIT test and evaluation bounds | PROVED GIVEN [A26] Theorem 1.1 (UNREFEREED), [KI04] Corollary 7.4 | `ExactMatching.Paper.cor_1_implication` | A26_MainTheorem (UNREFEREED); KI04_Cor_7_4 (refereed) |
| `rem_1_time` | Remark 1 (L191-193) | Remark 1 (deterministic time bound from [O26]) | not formalized: no time-bounded computation in Lean's library | — | NONE |
| `rem_1_tradeoff` | Remark 1 (L191-193) | Remark 1 ingredient: [O26] parameter tradeoff, test correctness, and evaluation-point bound | PROVED GIVEN [O26] Theorem 1.1 (UNREFEREED), [KI04] Corollary 7.4 | `ExactMatching.Paper.rem_1_tradeoff` | O26_Thm_1_1 (UNREFEREED); KI04_Cor_7_4 (refereed) |
| `lem_2_1_irred_exists` | Lemma 2.1 proof (L223) | Lemma 2.1 ingredient: irreducible polynomial over F_2 | PROVED | `ExactMatching.Paper.lem_2_1_irred_exists` | NONE |
| `lem_2_1_design` | Lemma 2.1 (L218-224) | Lemma 2.1 (explicit polynomial-graph design) | PROVED | `ExactMatching.Paper.lem_2_1_design` | NONE |
| `lem_2_1_time` | Lemma 2.1 (L219, L223) | Lemma 2.1 (deterministic poly(n)-time constructibility) | not formalized: no time-bounded computation in Lean's library | — | NONE |
| `lem_2_2_reconstruction` | Lemma 2.2 (L232-248) | Lemma 2.2 (reconstruction and circuit-model transfer) | PROVED GIVEN [KI04] Corollary 7.4 | `ExactMatching.Paper.lem_2_2_reconstruction` | KI04_Cor_7_4 (refereed) |
| `step_2_2_nonvanishing` | Lemma 2.2 proof (L239, L243) | Multivariate polynomial nonvanishing on a grid | PROVED | `ExactMatching.Paper.step_2_2_nonvanishing` | NONE |
| `step_2_2_model_transfer` | Lemma 2.2 proof (L247) | Circuit-model transfer and functional-to-formal lift | PROVED | `ExactMatching.Paper.step_2_2_model_transfer` | NONE |
| `prop_3_1_pfaffian_identity` | Proposition 3.1 (L328-350) | Proposition 3.1 ingredient: group-ring Tutte-Pfaffian identity | PROVED | `ExactMatching.Paper.prop_3_1_pfaffian_identity` | NONE |
| `prop_3_1_cyclic_rank_bound` | Proposition 3.1 proof (L361) | Proposition 3.1 ingredient: cyclic factor rank bound | PROVED | `ExactMatching.Paper.prop_3_1_cyclic_rank_bound` | NONE |
| `pfaffian_clow_circuit_exists` | Proposition 3.1 proof (L352) | Unconditional division-free {0, +-1}-constant Pfaffian circuit | PROVED | `ExactMatching.Paper.pfaffian_clow_circuit_exists` | NONE |
| `prop_3_1_wire_expansion` | Proposition 3.1 proof (L354-361) | Proposition 3.1 ingredient: Z[Gamma] wire expansion | PROVED | `ExactMatching.Paper.prop_3_1_wire_expansion` | NONE |
| `prop_3_1_pfaffian_circuit` | Proposition 3.1 (L328-362) | Proposition 3.1 (group-ring Pfaffian identity and circuit construction) | PROVED | `ExactMatching.Paper.prop_3_1_pfaffian_circuit` | NONE |
| `prop_3_1_time` | Proposition 3.1 (L329, L352, L361) | Proposition 3.1 (deterministic poly(n, |Gamma|)-time constructibility) | not formalized: no time-bounded computation in Lean's library | — | NONE |
| `rem_2_interpolation` | Remark 2 (L405-407) | Remark 2 (alternative Lagrange interpolation identity) | PROVED | `ExactMatching.Paper.rem_2_interpolation` | NONE |
| `paperPerm_eq_perm` | Sec 1 (L164, L170) | Permanent row/column convention agreement | PROVED | `ExactMatching.Paper.paperPerm_eq_perm` | NONE |
| `cov_asymptotic_between` | Intro L73, Fig 1 L159, L176 | Asymptotic rate identity and comparisons | PROVED | `ExactMatching.Paper.cov_asymptotic_between` | NONE |
| `cov_grid_prior_pit` | Theorem 1 proof (L293) | Small-input grid evaluation size bound | PROVED | `ExactMatching.Paper.cov_grid_prior_pit` | NONE |
| `cov_tab1_rnc_rp` | Table 1 caption (L209) | Table 1 RNC/RP/coRP randomized parallel complexity | not formalized: no randomized or parallel complexity in Lean's library | — | NONE |
| `step_thm1_eq1` | Theorem 1 eq. (1) (L287-290) | Theorem 1 parameter lower bound eq. (1) | PROVED | `ExactMatching.Paper.step_thm1_eq1` | NONE |
| `step_thm1_threshold` | Theorem 1 proof (L291) | Theorem 1 threshold s_0 | PROVED | `ExactMatching.Paper.step_thm1_threshold` | NONE |
| `step_thm1_ryser` | Theorem 1 proof (L301-304) | Ryser's formula for the permanent | PROVED | `ExactMatching.Paper.step_thm1_ryser` | NONE |
| `step_thm1_small_inputs` | Theorem 1 proof (L293) | Small-input mod-2^{B_0} grid test exactness | PROVED | `ExactMatching.Paper.step_thm1_small_inputs` | NONE |
| `step_thm1_modulus_exact` | Theorem 1 proof (L310-314) | Large-input mod-2^B exactness | PROVED | `ExactMatching.Paper.step_thm1_modulus_exact` | NONE |
| `step_thm1_B_bound` | Theorem 1 proof (L297, Fig 2 L262) | Modulus bit-length bound B = O(s^{3/2} log s) | PROVED | `ExactMatching.Paper.step_thm1_B_bound` | NONE |
| `step_rem1_ln_vs_log2` | Remark 1 (L192) | Natural vs base-2 double-log comparison | PROVED | `ExactMatching.Paper.step_rem1_ln_vs_log2` | NONE |
| `step_rem1_computes_to_o26` | Remark 1 (L192) | [A26] Computes implies [O26] O26ExactComputes | PROVED | `ExactMatching.Paper.step_rem1_computes_to_o26` | NONE |
| `step_thm2_odd_n` | Theorem 2 proof (L388) | Odd-vertex graphs have no perfect matching | PROVED | `ExactMatching.Paper.step_thm2_odd_n` | NONE |
| `step_thm2c_self_reduction` | Theorem 2(c) proof (L396) | Edge-deletion self-reduction | PROVED | `ExactMatching.Paper.step_thm2c_self_reduction` | NONE |
| `step_thm2a_embedding` | Theorem 2(a) proof (L398) | Exact Matching cyclic embedding Z_{n/2+1} | PROVED | `ExactMatching.Paper.step_thm2a_embedding` | NONE |
| `step_thm2b_embedding` | Theorem 2(b) proof (L400) | Bounded integer weights shifted cyclic embedding Z_{nW+1} | PROVED | `ExactMatching.Paper.step_thm2b_embedding` | NONE |
| `nonclaim_history_defs_disc` | Abstract L58, Sec 1 L66-73, Figs 1-3, Table 1 lit cols, Discussion L409-419, Ack L421-422 | Historical background, definitions, schematic figures, open directions | NOT COUNTED | — | NONE |
