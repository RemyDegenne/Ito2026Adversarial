# Comparator setup

Machine-checkable verification, with [leanprover/comparator](https://github.com/leanprover/comparator),
that this repository proves the headline results claimed in [`formalization.yaml`](../formalization.yaml)
without having to read or trust the Lean development in `Ito2026Adversarial/`.

**Status.** Every challenge is proved. The challenges were regenerated on 2026-11-09, when the project
moved to LMLExplore; `scripts/comparator-verify.sh` has to be run again on them (it has not been run
on this project yet).

Each challenge is one file that imports LML and Mathlib modules only (the project does not use
LMLExplore's definitions yet), no project modules and no sibling helpers.

## The trust story

For each headline theorem `Ito2026Adversarial.<name>` there is a challenge file `Challenge_<name>.lean` and a
config `<name>.json`; the list is `targets.txt`:

| paper result | challenge(s) |
|---|---|
| Theorem 1 (Tsallis-INF) | `exists_psmr_tsallisINFHalf_le` |
| Theorem 2 (lower bound) | `exists_forall_psmr_ge` |
| Theorem 4 (Maximin-UCB) | `exists_psmr_maximinUCB_le` |
| Theorem 5 (Tsallis-FTRL-SPM) | `forall_exists_psmr_tsallisSPMPaper_le` |
| Theorem 6 (Maximin-LinUCB, informal) | `exists_forall_exists_psmr_maximinLinUCB_le` |
| Lemma 7 | `sqrt_mul_sub_mul_le` |
| Lemma 8 (self-bounding) | `le_add_sqrt_add_of_le_sqrt_add` |
| Lemma 9 (KL of two-point laws) | `klDiv_twoPoint_le` |
| Lemma 10 | `sq_entryGap_div_four_le_mixGap` |
| Lemma 11 (anytime confidence bounds) | `probReal_forall_abs_sub_div_le_ge` |
| Theorem 12 (Maximin-LinUCB) | `exists_psmr_maximinLinUCB_le` |
| Lemma 13 (confidence ellipsoid) | `probReal_forall_sqrt_mahalanobisSq_le_ge` |

Each challenge states the theorem with `sorry`, with every definition of the project that the
statement rests on copied verbatim from its source by
[challenge-gen](https://github.com/LeanTrustBuilders/challenge-gen); the definitions of
LMLExplore, LML, Tau Ceti and Mathlib that it uses are imported. A reader checks the *statement*
(the challenge file) by hand and lets comparator check that the project proves exactly it, with
no axioms beyond `propext`, `Classical.choice` and `Quot.sound`, the proofs replayed through the
kernel. The config also lists the lemmas the definitions use, left `sorry` in the challenge and
proved by the project, and the theorems Lean makes of the proofs inside definitions.

## Regenerating and running

`scripts/make-challenges.py` regenerates every challenge and config from `targets.txt`;
`lake build Comparator` checks that they compile; `scripts/comparator-verify.sh [--insecure]`
runs comparator on every config (see the script header for the sandbox requirements).

## Auxiliary theorems

Lean reuses, within a module, an auxiliary theorem `foo._proof_n` made earlier for a proof of the
same statement; a challenge, which holds the definitions of many modules in one file, would then
differ from the project, and challenge-gen refuses it. The definitions in the closure of the
headline statements therefore avoid the numeral `2` (the source of the only such shared
statement, `(1 + 1).AtLeastTwo`): see `notes/blueprint-outline.md`, section 6.
