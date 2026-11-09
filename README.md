# Ito2026Adversarial

A Lean 4 formalization of *Adversarial Learning in Games with Bandit Feedback: Logarithmic
Pure-Strategy Maximin Regret* (Shinji Ito, Haipeng Luo, Arnab Maiti, Taira Tsuchiya and Yue Wu,
COLT 2026, [arXiv:2602.06348](https://arxiv.org/abs/2602.06348)), on top of
[LMLExplore](https://github.com/LeanMachineLearning/LMLExplore), and so of
[LML](https://github.com/LeanMachineLearning/LML), [Tau Ceti](https://github.com/TauCetiProject/TauCeti)
and [Mathlib](https://github.com/leanprover-community/mathlib4). It follows the layout of
[lml-paper-template](https://github.com/LeanMachineLearning/lml-paper-template).

It formalizes the pure-strategy maximin regret bounds of the paper for a learner playing a
zero-sum game against an adaptive adversary with bandit feedback: Tsallis-INF (Theorem 1) and its
matching lower bound (Theorem 2), Maximin-UCB (Theorem 4), Tsallis-FTRL-SPM and Maximin-LinUCB in
bilinear games (Theorems 5, 6 and 12), and Lemmas 7–11 and 13, together with the analyses that the
paper cites (Tsallis-INF, Tsallis-FTRL with stability-penalty matching, the self-normalized
confidence ellipsoid, the elliptical potential lemma). Theorems 1, 4 and 5 and Lemma 10 are stated
in a corrected form: see the errata. Every headline result is proved, with no `sorry`.

- Website: https://RemyDegenne.github.io/Ito2026Adversarial/, with the blueprint, the referee site
  and the literature links (which declarations formalize which results of the paper). CI builds it
  on each push to `main`. `scripts/formalize.sh` also commits the literature links, as
  `literature/annotations.jsonl`, when the paper is formalized and after the final bump.
- The paper: `source/`. Errors found in it, with their corrections: `notes/paper-errata.md`.
- The paper's results: `Ito2026Adversarial/ILMTW2026/`, one file per result, listed with their
  status in `formalization.yaml`; comparator challenges in `comparator/`.
- Library-shaped material: `Ito2026Adversarial/ForLMLExplore/`, which Tau Ceti workers port to
  LMLExplore; `PAPER_ROADMAP.md` says where each item goes.
- The blueprint outline, the phase-2 plan and the upstreaming candidates: `notes/`.

## Results of the paper

| Result | Lean declaration | Notes |
|---|---|---|
| Theorem 1 (Tsallis-INF, uninformed) | `exists_psmr_tsallisINFHalf_le` | errata E1, E2 |
| Theorem 2 (lower bound) | `exists_forall_psmr_ge` | |
| Theorem 4 (Maximin-UCB, informed) | `exists_psmr_maximinUCB_le` | errata E4 |
| Theorem 5 (Tsallis-FTRL-SPM, bilinear) | `forall_exists_psmr_tsallisSPMPaper_le` | errata E1–E3 |
| Theorem 6 (Maximin-LinUCB, informal) | `exists_forall_exists_psmr_maximinLinUCB_le` | |
| Lemma 7 | `sqrt_mul_sub_mul_le` | |
| Lemma 8 (self-bounding) | `le_add_sqrt_add_of_le_sqrt_add` | |
| Lemma 9 (KL of two-point laws) | `klDiv_twoPoint_le` | |
| Lemma 10 (`Δ^mix ≥ Δ_M² / 4`) | `sq_entryGap_div_four_le_mixGap` | errata E7 |
| Lemma 11 (anytime confidence bounds) | `probReal_forall_abs_sub_div_le_ge` | without the implied `u ∈ [-1, 1]` |
| Theorem 12 (Maximin-LinUCB) | `exists_psmr_maximinLinUCB_le` | |
| Lemma 13 (confidence ellipsoid) | `probReal_forall_sqrt_mahalanobisSq_le_ge` | |

## Building

```bash
scripts/build.sh
```

The script fetches Mathlib's and Tau Ceti's prebuilt files, then runs `lake build`; its arguments go
to `lake build`.

## Working on it

The workflow is the `formalize-paper` skill of the `lml` Claude Code plugin
([lml-claude](https://github.com/LeanMachineLearning/lml-claude)). The paper is formalized; what is
left is to contribute its library-shaped part. `scripts/formalize.sh`, in a terminal or tmux, tags
`PAPER_ROADMAP.md`, sends the reusable parts to LMLExplore, and once they are merged moves the paper
to the current LMLExplore.
