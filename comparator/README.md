# Comparing the Lean statements

The challenge states all 35 formalized claims and supporting ingredients of the paper in `ExactMatching/Paper/Statements.lean`: Theorem 1, Theorem 2(a)–(c), Corollary 1, Remark 1, Lemma 2.1, Lemma 2.2 (including the unconditional root-finding circuit existence theorem `ki04_cor_7_4`), Proposition 3.1 (including the unconditional alternating-clow-sequence Pfaffian circuit construction), Remark 2, and all supporting proof steps and coverage links. Each challenge theorem has an open proof (`sorry`), and the challenge module imports strictly `ExactMatching.Defs.*` (no proof modules). The solution in the Lean directory supplies proofs depending strictly on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), with 32 declarations proved from Lean's three standard axioms alone (zero refereed literature hypotheses remaining) and only the two unrefereed external results (`A26_MainTheorem`, `O26_Thm_1_1`) entering as explicit hypotheses of the three declarations that use them.

To run the comparison on Linux with Git, elan, and bubblewrap, start at the root of the checked-out repository:

```sh
set -eu
comparison_dir=$(mktemp -d)
git archive HEAD:lean | tar -xf - -C "$comparison_dir"
cp comparator/ExactMatching/Paper/Challenge.lean "$comparison_dir/ExactMatching/Paper/Challenge.lean"
cp comparator/comparator.json "$comparison_dir/comparator.json"
cd "$comparison_dir"
lake exe cache get
lake --no-cache comparator --config=comparator.json --paranoid
```

Lake compares all 35 declarations and checks the solution across all bundled kernels. A successful run ends with `Your solution is okay!`.

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see [LICENSE](../LICENSE).
