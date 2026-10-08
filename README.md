# Ito2026Adversarial

Lean 4 formalization of the paper

> Shinji Ito, Haipeng Luo, Arnab Maiti, Taira Tsuchiya, Yue Wu, *Adversarial Learning in Games
> with Bandit Feedback: Logarithmic Pure-Strategy Maximin Regret*, COLT 2026,
> [arXiv:2602.06348](https://arxiv.org/abs/2602.06348),

built on Mathlib and the [Lean Machine Learning](https://github.com/LeanMachineLearning/LML)
library (LML, branch `rename`). The development is blueprint-driven:
[blueprint](https://remydegenne.github.io/Ito2026Adversarial/blueprint/),
[dependency graph](https://remydegenne.github.io/Ito2026Adversarial/blueprint/dep_graph_document.html).

**Status: phase 1 (statements).** The 12 results of the paper are stated in Lean with `sorry`.
They are listed in [`formalization.yaml`](formalization.yaml) and are standalone challenges for
[comparator](https://github.com/leanprover/comparator) in [`comparator/`](comparator/).

## Layout

* `Ito2026Adversarial/ILMTW2026/`: the paper, one file per result (`Theorem1.lean`, …,
  `Lemma13.lean`), namespace `Ito2026Adversarial`; the algorithms and bilinear games are in
  `Setting.lean`.
* `Ito2026Adversarial/LeanMachineLearning/`: material for LML (from `LMLPapers`): repeated
  zero-sum games with bandit feedback (`Game/`), Tsallis-INF and FTRL on the simplex, importance
  weighting, the ridge regression state of linear bandits, online learners and regret.
* `Ito2026Adversarial/Mathlib/`: material for Mathlib (from `LMLPapers`): two-point laws, the
  Bernoulli KL divergence and Pinsker's inequality, Mahalanobis norms, the simplex, Fenchel
  conjugates, matrices.
* `blueprint/src/`: the blueprint (Part I follows the paper, Part II the prerequisites, including
  the regret analyses the paper cites); `notes/blueprint-outline.md`: the outline it was written
  from (labels, corrections, proof routes); `source/`: the paper's LaTeX source.

## Results of the paper

| Result | Lean declaration | Notes |
|---|---|---|
| Theorem 1 (Tsallis-INF, uninformed) | `exists_psmr_tsallisINFHalf_le` | strict-PSNE bound in the proof's form; `Δ^mix > 0` instead of "no PSNE" |
| Theorem 2 (lower bound) | `exists_forall_psmr_ge` | |
| Remark 3 | — | remark |
| Theorem 4 (Maximin-UCB, informed) | `exists_psmr_maximinUCB_le` | additive `m_x m_y` in the instance-dependent bound |
| Theorem 5 (Tsallis-FTRL-SPM, bilinear) | `forall_exists_psmr_tsallisSPMPaper_le` | as Theorem 1; variance ratio with `S(p₀) ≻ 0` |
| Theorem 6 (Maximin-LinUCB, informal) | `exists_forall_exists_psmr_maximinLinUCB_le` | |
| Lemma 7 | `sqrt_mul_sub_mul_le` | |
| Lemma 8 (self-bounding) | `le_add_sqrt_add_of_le_sqrt_add` | |
| Lemma 9 (KL of two-point laws) | `klDiv_twoPoint_le` | |
| Lemma 10 (`Δ^mix ≥ Δ_M² / 4`) | `sq_entryGap_div_four_le_mixGap` | no PSNE instead of a unique equilibrium |
| Lemma 11 (anytime confidence bounds) | `probReal_forall_abs_sub_div_le_ge` | |
| Theorem 12 (Maximin-LinUCB) | `exists_psmr_maximinLinUCB_le` | |
| Lemma 13 (confidence ellipsoid) | `probReal_forall_sqrt_mahalanobisSq_le_ge` | |

The corrections and the proof routes are explained in the blueprint and in
`notes/blueprint-outline.md` (sections 3 and 4).

## Building and checking

```
lake exe cache get
lake build Ito2026Adversarial
lake exe runLinter Ito2026Adversarial
python3 scripts/check-blueprint.py && leanblueprint pdf && leanblueprint web
lake exe checkdecls blueprint/lean_decls
python3 scripts/make-challenges.py && lake build Comparator
```
