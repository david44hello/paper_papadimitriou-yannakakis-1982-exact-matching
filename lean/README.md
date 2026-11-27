# Exact Matching from permanent lower bounds: formalization in Lean 4

The paper's link is on the [front page of this repository](https://github.com/david44hello/paper_papadimitriou-yannakakis-1982-exact-matching).

This directory contains a Lean 4 formalization of the mathematical claims of the paper (35 declarations in `ExactMatching.Paper`): Lemma 2.1, Lemma 2.2, Theorem 1's test correctness and evaluation-point bounds, Proposition 3.1 (including an unconditional alternating-clow-sequence Pfaffian circuit construction), Theorem 2(a)–(c)'s decision and witness-recovery ingredients, Remark 2, and the cited root-finding circuit existence result (`KI04_Cor_7_4`) — 32 declarations in total — are proved from Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) alone, with zero refereed literature hypotheses remaining. Corollary 1's two declarations are proved given `[A26]` Theorem 1.1 (`A26_MainTheorem`, UNREFEREED), and Remark 1's tradeoff is proved given `[O26]` Theorem 1.1 (`O26_Thm_1_1`, UNREFEREED). There are zero custom `axiom` declarations. Deterministic Turing-machine running-time bounds and randomized/parallel complexity remarks (`RNC`, `RP`, `coRP`) are not formalized.

See [WHAT_TO_READ.md](WHAT_TO_READ.md) for the statement guide, cited hypotheses with sources, proof architecture, and verification record.

## How to verify

Install [elan](https://github.com/leanprover/elan) (the toolchain is pinned in `lean-toolchain`), then from this directory run:

```bash
./scripts/check.sh
```

A successful run ends with:

```text
Checked 35 Lean declarations against the three permitted standard axioms.
```

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see [LICENSE](../LICENSE).
