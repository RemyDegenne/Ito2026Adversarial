# Phase 2 plan: work packages and briefs

Every package proves the lemmas of one blueprint area against interfaces that are already stated
(with `sorry`) in the repository, so that all packages can run in parallel: a package that uses
another one's interface or headline theorem relies on its statement only.

Interface files and headline theorems (statements fixed; their owner replaces the `sorry`):

| File | Declarations | Owner |
|---|---|---|
| `Ito2026Adversarial/LeanMachineLearning/Game/RegretRelations.lean` | `nashRegret_eq_psmr_add`, `nashRegret_le_externalRegret`, `IsStrictPSNE.colGapMin_mul_le`, `IsPSNE.integral_sum_rowGap_sub_le` | E |
| `ILMTW2026/Lemma7.lean`, `Lemma8.lean`, `Lemma9.lean`, `Lemma10.lean` (frozen) | `sqrt_mul_sub_mul_le`, `le_add_sqrt_add_of_le_sqrt_add`, `klDiv_twoPoint_le`, `sq_entryGap_div_four_le_mixGap` | E |
| `ILMTW2026/Theorem2.lean` (frozen) | `exists_forall_psmr_ge` | L |
| `ILMTW2026/Theorem1.lean` (frozen) | `exists_psmr_tsallisINFHalf_le` | T |
| `ILMTW2026/Theorem5.lean` (frozen) | `forall_exists_psmr_tsallisSPMPaper_le` | S |
| `ILMTW2026/Lemma11.lean`, `Lemma13.lean` (frozen) | `probReal_forall_abs_sub_div_le_ge`, `probReal_forall_sqrt_mahalanobisSq_le_ge` | C1 |
| `ILMTW2026/Theorem4.lean`, `Theorem12.lean`, `Theorem6.lean` (frozen) | `exists_psmr_maximinUCB_le`, `exists_psmr_maximinLinUCB_le`, `exists_forall_exists_psmr_maximinLinUCB_le` | C2 |

(`ILMTW2026/` is `Ito2026Adversarial/ILMTW2026/`.)

Correction during phase 2: package E found the four `RegretRelations.lean` interfaces false as
stated in phase 1 (the regrets are integrals of the actions' utilities, which need the actions to
be measurable functions to a space with measurable singletons). They now assume
`MeasurableSingletonClass 𝒳`, `MeasurableSingletonClass 𝒴` (and `Finite` for the PSNE ones);
the headline statements were not affected.

## Rules for every package

* Read `notes/blueprint-outline.md` (sections 3, 4 and 6: corrections, proof routes, the numeral
  `2`), the blueprint chapters of your package (`blueprint/src/chapters/*.tex`),
  `Ito2026Adversarial/ILMTW2026/Setting.lean`, `Ito2026Adversarial/LeanMachineLearning/Game/*.lean`
  and the files you build on. Lean conventions: every file `module` + `public import …` + module
  docstring + `@[expose] public section`, copyright header `Rémy Degenne` (as the existing files),
  every declaration with a docstring, `lemma` (never `theorem`, except the headline results already
  stated), Mathlib naming, lines ≤ 100 chars, no `sorry` left in your files at the end.
* **Never change** the statements of the headline theorems in `Ito2026Adversarial/ILMTW2026/`
  (frozen by the comparator challenges), the definitions in `Setting.lean`, the definitions and
  statements of the library files copied from LMLPapers, nor the statements of the interface
  lemmas above. You replace the `sorry` of what you own; for anything else, add new files (or new
  lemmas in your own files). If a statement you must prove looks false or unprovable, stop and
  report instead of changing it. If a hypothesis of a frozen headline statement ends up unused,
  keep it, put `@[nolint unusedArguments]` on the theorem (with
  `set_option linter.unusedVariables false in` if needed) and report it.
* **No numeral `2` in the values of new definitions** that a headline statement could depend on
  (outline, section 6): write `((2 : ℕ) : ℝ)` and `WithLp.toLp _`. In lemmas and proofs numerals
  are fine.
* Prove the general statement and derive the specialization; drop hypotheses the proof does not
  use from *new* lemmas. New library-shaped material goes to `Ito2026Adversarial/Mathlib/` (Mathlib
  path and namespaces) or `Ito2026Adversarial/LeanMachineLearning/` (LML path, namespaces `Learning`
  or `Bandits`); paper-specific material to `Ito2026Adversarial/ILMTW2026/` (namespace
  `Ito2026Adversarial`). State laws as `HasLaw`/`HasCondDistrib` rather than `Measure.map`
  equations. No structures bundling a function with its measurability.
* Only edit your own files and, in the blueprint, the environments of your package. Re-read a
  blueprint chapter right before editing it. After adding a Lean file run
  `lake exe mk_all --lib Ito2026Adversarial` (concurrent runs are harmless). Do not run
  `leanblueprint`, do not commit.
* Blueprint: add `\lean{Full.Name}` and `\leanok` to each statement the moment its declaration
  compiles, and `\leanok` inside the `proof` environment when its proof is complete; keep labels
  unchanged; add a lemma (label, `\uses`) for any new intermediate step that deserves one. Run
  `python3 scripts/check-blueprint.py`.
* Check before reporting: `lake build Ito2026Adversarial` with no warnings in your files other than
  `declaration uses 'sorry'` coming from *other* packages, `lake exe runLinter Ito2026Adversarial`
  (fix what it reports in your files), `grep -n sorry` on your files. Concurrent `lake build` calls
  in this checkout are fine.
* Look up APIs by grepping `.lake/packages/mathlib/Mathlib` and
  `.lake/packages/LeanMachineLearning/LeanMachineLearning`; test in scratch files with
  `lake env lean File.lean` in your scratchpad directory. `~/Documents/Lean/LMLPapers` has more
  library material (read-only for you): copy what you need into this repository, mapping
  `LMLPapers.LeanMachineLearning.ForMathlib.X` to `Ito2026Adversarial.Mathlib.X` and
  `LMLPapers.LeanMachineLearning.X` to `Ito2026Adversarial.LeanMachineLearning.X`; if two packages
  need the same LMLPapers file, the first to copy it owns it, the other imports it (check before
  copying).
* Report: what was proved (names, files), any deviation from the plan, anything left.

## E. Elementary lemmas and regret relations (`games.tex`)

Prove the four interfaces of `RegretRelations.lean` (pathwise identities and bounds, then
integrals of bounded functions; `nashRegret_le_externalRegret` needs a maximin mixed strategy, i.e.
that the supremum defining `nashValue` is attained, `lem:maximin_attained`, by compactness of the
simplex), and the frozen Lemmas 7, 8 (elementary real analysis), 9 (KL of two-point laws: the
library has `twoPoint` in `Mathlib/Probability/Distributions/TwoPoint.lean` and the Bernoulli KL
in `Mathlib/InformationTheory/KullbackLeibler/Bernoulli.lean`; the paper's derivative argument)
and 10 (`lem:two_by_two_value`: the explicit value of a `2 × 2` game without PSNE, with a symmetry
lemma for row/column swaps).

## L. Lower bound (`lower_bound.tex`; `prereq_information.tex`)

Prove the frozen `exists_forall_psmr_ge` (Theorem 2), using Lemma 9 (`klDiv_twoPoint_le`) by its
statement. Route (blueprint, outline section 4): the two games `A`, `B`, two-point rewards
(`stationaryReward` of `twoPoint`), the oblivious adversary (a `Player` whose policy ignores the
history: `(1 - ε, ε)` before `T'`, `y*` after); the observations `(x_t, r_t)` of the uninformed
learner form a run of it against the non-stationary bandit `t ↦ (x ↦ twoPoint(u(x, q_t)))`
(`lem:uninformed_oblivious`: identify the conditional laws, using that a mixture of two-point laws
is the two-point law of the mixed mean); the divergence decomposition for non-stationary bandits
(LMLPapers `SequentialLearning/DivergenceDecomposition.lean`, `klDiv_map_history_banditSeq…`) and
Bretagnolle–Huber (LMLPapers `ForMathlib/InformationTheory/KullbackLeibler/BretagnolleHuber.lean`);
the two cases of the paper with `Δ₀ = 1/13`, `T₀ = 169`, `T' = ⌊(13 Δʳ Δᶜ)⁻²⌋` (rounding down
changes the constant).

## T. Tsallis-INF (`tsallis_inf.tex`, `prereq_ftrl.tex`: `lem:ftrl_decomposition` to `lem:tsallis_inf_self_bound`)

Prove the frozen `exists_psmr_tsallisINFHalf_le` (Theorem 1), using the interfaces of
`RegretRelations.lean` and Lemmas 7, 8 by their statements. The bulk is the regret analysis of
Tsallis-INF for rewards in `[-1, 1]` against adaptive adversaries (`lem:tsallis_inf_worst`,
`lem:tsallis_inf_self_bound`), with any universal constants. First write the generic FTRL
decomposition (penalty and stability terms for time-varying regularizers, telescoping of the
value function `ftrlValue` of `Online/Bandit/SimplexFTRL.lean`) in a library file
`Ito2026Adversarial/LeanMachineLearning/Online/Bandit/FTRLRegret.lean`, which package S may import;
then the stability bound of the Tsallis-1/2 regularizer for the reduced-variance estimate
(`lem:tsallis_stability`; the classical route of Zimmert–Seldin 2021 / Ito et al. 2025: the
conjugate of the Tsallis entropy and its local norms), the conditional unbiasedness of the
estimates in a run against an adaptive adversary (`lem:uninformed_run`: Tsallis-INF draws `x_t`
from `p_t`, a function of the past, independently of `y_t`), then Theorem 1 as in the blueprint.

## S. Tsallis-FTRL-SPM (`bilinear.tex`: `thm:tsallis_bilinear`; `prereq_ftrl.tex`: `lem:tsallis_spm_regret`)

Prove the frozen `forall_exists_psmr_tsallisSPMPaper_le` (Theorem 5), using the interfaces of
`RegretRelations.lean` and Lemmas 7, 8 by their statements. The bulk is the regret bound of
Tsallis-FTRL-SPM (Ito, Tsuchiya, Honda 2024, Eq. (26) with the parameters of their Section 4.3,
`lem:tsallis_spm_regret`): FTRL with the hybrid regularizer, stability-penalty matching learning
rates, exploration with variance ratio `c`, linear estimates. For the generic FTRL decomposition,
use `LeanMachineLearning/Online/Bandit/FTRLRegret.lean` if package T has written it (do not edit
it), otherwise write what you need in your own files. This is the largest package; if it cannot
be finished, report precisely which sublemmas are proved and which remain (with statements).

## C1. Confidence bounds (`maximin_ucb.tex`: `lem:ucb_ucb`; `bilinear.tex`: `lem:conf_ellipsoid`; `prereq_concentration.tex`)

Prove the frozen `probReal_forall_abs_sub_div_le_ge` (Lemma 11) and
`probReal_forall_sqrt_mahalanobisSq_le_ge` (Lemma 13). Route: bounded noise is conditionally
`1`-sub-Gaussian (Hoeffding's lemma, `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`, applied to
the reward kernel at each history and action pair, `lem:bounded_noise_subgaussian`); Ville's
inequality and mixtures of supermartingales (LMLPapers
`ForMathlib/Probability/Martingale/Ville.lean`, `Mixture.lean`); the one-dimensional Gaussian
mixture for Lemma 11 (`lem:mixture_supermartingale`) and the `d`-dimensional one for the
self-normalized bound (`lem:self_normalized`, Abbasi-Yadkori et al. 2011, Theorem 1: Gaussian
integral of a quadratic form, `det`), the determinant bound (`lem:log_det_le`, AM–GM on the
eigenvalues or the trace bound for positive definite matrices) and `‖vec A‖ ≤ √(d_x d_y)`.

## C2. UCB algorithms (`maximin_ucb.tex`: `thm:pureucb`; `bilinear.tex`: `thm:purelinucb`, `thm:purelinucb_informal`; `prereq_concentration.tex`: `lem:elliptical_potential`)

Prove the frozen `exists_psmr_maximinUCB_le` (Theorem 4), `exists_psmr_maximinLinUCB_le`
(Theorem 12) and `exists_forall_exists_psmr_maximinLinUCB_le` (Theorem 6), using Lemmas 11 and 13 by
their statements. Routes in the blueprint: the optimism `v* ≤ U_t(x_t, y_t)` on the good event
(Maximin-UCB and Maximin-LinUCB are `Algorithm.index`/`Algorithm.statefulIndex`: the action of a run
is the argmax of the index), the counts of pairs with a positive gap (Theorem 4, with the additive
`m_x m_y` of the failure event and the threshold argument for the worst case), the elliptical
potential (`lem:elliptical_potential`: matrix determinant lemma, Mathlib's
`Matrix.det_add_col_mul_row`, and `x ≤ 2 log(1 + x)` on `[0, 1]`), Cauchy–Schwarz, and the failure
events with `δ = 1/T` (`PSMR` at most `2T`). Theorem 6 from Theorem 12.
