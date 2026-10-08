/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
-- One import per file proving a headline result of formalization.yaml.
import Ito2026Adversarial.ILMTW2026.Theorem1
import Ito2026Adversarial.ILMTW2026.Theorem2
import Ito2026Adversarial.ILMTW2026.Theorem4
import Ito2026Adversarial.ILMTW2026.Theorem5
import Ito2026Adversarial.ILMTW2026.Theorem6
import Ito2026Adversarial.ILMTW2026.Lemma7
import Ito2026Adversarial.ILMTW2026.Lemma8
import Ito2026Adversarial.ILMTW2026.Lemma9
import Ito2026Adversarial.ILMTW2026.Lemma10
import Ito2026Adversarial.ILMTW2026.Lemma11
import Ito2026Adversarial.ILMTW2026.Theorem12
import Ito2026Adversarial.ILMTW2026.Lemma13

/-! # Comparator solution module

The solution side of the [comparator](https://github.com/leanprover/comparator) setup in
`comparator/`: this module imports the project files proving the headline results listed in
`formalization.yaml`, so its environment contains, at the exact names stated (with `sorry`) in
the `comparator/Challenge_*.lean` files, the headline theorems of the paper (see
`comparator/README.md`). -/
