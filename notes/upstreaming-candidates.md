# Upstreaming candidates

Library-shaped material written in phase 2 (2026-10-08/09), by destination, after the review
against the Mathlib guidelines (2026-10-09). Paths are under `Ito2026Adversarial/`. The library
files copied from `LMLPapers` in phase 1 are listed only where the review added to them.

The review organized the files by topic:
- `Game/UninformedRun.lean` and `UninformedRunIntegral.lean` were merged into `Game/Run.lean`;
- `Game/Optimism.lean` was split between `Game/Maximin.lean` (values),
  `Game/RepeatedGame.lean` (pair counts) and `Game/Regret.lean` (the renamed `RegretRelations.lean`,
  regret bounds);
- the Tsallis-entropy lemmas of `HybridTsallis.lean` and `TsallisHalf.lean` were gathered in
  `TsallisEntropy.lean`, and the real-power inequalities in
  `Mathlib/Analysis/Convex/SpecificFunctions/Pow.lean`;
- the `regGram` API moved to `DesignMatrix.lean`, the simplex lemmas to `Simplex.lean`, the
  `estimate` API to `TsallisINF.lean`, and `Linear/Optimism.lean` was merged into
  `Linear/ConfidenceEllipsoid.lean`.

Other review changes:
- FTRL lemmas take `IsMaxOn` hypotheses;
- two wrappers of the phase-1 interfaces were deleted (one with an unused hypothesis);
- lemmas about runs use `IsAlgEnvSeq.` dot notation;
- `rexp` became `exp` in the names;
- `## Tags` sections were added.

Still open:
- `IsCondSubgaussianNoise` (`SelfNormalized.lean`) is a lower-integral form of conditional
  sub-Gaussianity. It should be connected to Mathlib's `HasCondSubgaussianMGF`, as the moment
  bound of `SubgaussianSum.lean` in Wang2026Almost does.
- The SPM lemma names (`spm_pos`, …) could live in a namespace.

Definitions changed in phase 1 to avoid the numeral `2` (challenge-gen, outline section 6) stay in
this repository. In `LMLPapers` the original forms are kept, and the ported proofs are adapted where
needed. The definitions are `twoPoint`, `ridgeEstimate`, `TsallisINF.estimate`, `banditPolicy`,
`uniformVec`, `pinvMahalanobisSq`, and a private definition in Pinsker.

## Mathlib

| File | Content |
|---|---|
| `Mathlib/Analysis/Convex/Simplex.lean` (additions) | norm and inner products of points of the simplex, moving mass between two coordinates |
| `Mathlib/Analysis/Convex/SpecificFunctions/Pow.lean` | inequalities for `x ^ a`, `a ∈ [0, 1]`: tangent line, quadratic lower bound on the Bregman divergence (`Real.sq_le_rpow_bregman`), `K ^ (-a) ≤ 1 - a (1 - 1 / K)`, subadditivity over finite sums, the power mean inequality |
| `Mathlib/Analysis/Matrix/LogDet.lean` | `log det A ≤ d log(tr A / d)` for positive definite `A` (AM–GM for the eigenvalues) |
| `Mathlib/Analysis/SpecialFunctions/Gaussian/QuadraticForm.lean` | the real Gaussian integral with a linear term, its version for the quadratic form of a positive definite matrix (`Matrix.PosDef.lintegral_exp_inner_sub_mahalanobisSq`), `Matrix.PosDef.det_sqrt` |
| `Mathlib/Analysis/SpecialFunctions/Log/OneAdd.lean` | `min(1, w) ≤ 2 log(1 + w)` |
| `Mathlib/InformationTheory/KullbackLeibler/TwoPoint.lean` | divergence between two-point laws on `{-1, 1}` as a binary divergence, quadratic upper bound away from the boundary |
| `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` | `Integrable.of_ae_abs_le`, integrals equal when the lower integrals of `ofReal` are |
| `Mathlib/MeasureTheory/Measure/Weighted.lean` (addition) | `lintegral_weightedMeasure_eq_sum` |
| `Mathlib/Probability/Distributions/TwoPoint.lean` (additions) | mean and support of the two-point law, mixtures of two-point laws |
| `Mathlib/Probability/HasCondDistrib.lean` | `HasCondDistrib.lintegral_prodMk` (already in LMLPapers) |
| `Mathlib/Probability/Martingale/Ville.lean` | Ville's inequality for `ℝ≥0∞`-valued supermartingales in the lower-integral sense (no integrability hypothesis) |

## LML

| File | Content |
|---|---|
| `LeanMachineLearning/DesignMatrix.lean` (additions) | determinant and trace of the regularized Gram matrix, matrix determinant lemma, `‖v‖²_{V⁻¹} ≤ ‖v‖² / λ` |
| `LeanMachineLearning/EllipticalPotential.lean` | `log det V_t` bound and the elliptical potential lemma |
| `LeanMachineLearning/SelfNormalized.lean` | conditionally sub-Gaussian noise (`IsCondSubgaussianNoise`), the Gaussian mixture supermartingale, and the self-normalized bound of Abbasi-Yadkori, Pál, Szepesvári (2011, Theorem 1) for a general filtration with predictable features |
| `LeanMachineLearning/Online/Bandit/Linear/ConfidenceEllipsoid.lean` | `‖θ - θ̂_t‖_{V_t} ≤ ‖S_t‖_{V_t⁻¹} + √λ ‖θ‖` for ridge regression; optimism of the linear UCB index |
| `LeanMachineLearning/Online/Bandit/FTRLRegret.lean` | FTRL on the simplex with time-varying regularizers: Fenchel–Young, the regret decomposition (`sum_inner_sub_le_ftrl`), the value function's gradient is the maximizer (Danskin, `ftrlSimplex_eq`) |
| `LeanMachineLearning/Online/Bandit/TsallisEntropy.lean` | Tsallis entropies on the simplex: bounds (uniform, self-bounding, `q*` lower bound, `φ_a(r) ≤ c φ_a(p)` for `r ≤ c p`), the case `a = 1/2` |
| `LeanMachineLearning/Online/Bandit/TsallisHalf.lean` | Tsallis-1/2 FTRL: explicit maximizer, exact objective identity, stability of the importance-weighted estimate |
| `LeanMachineLearning/Online/Bandit/TsallisINF.lean` (additions) | coordinates and inner products of the importance-weighted estimate |
| `LeanMachineLearning/Online/Bandit/HybridTsallis.lean` | FTRL with the hybrid regularizer `β φ_α + βbar φ_{1-α}`: maximizer, first-order conditions, joint differentiability of the value function in `(β, G)`, stability, multiplicative stability, coordinate lower bounds |
| `LeanMachineLearning/Online/StabilityPenaltyMatching.lean` | the stability-penalty matching learning rates of Ito, Tsuchiya, Honda (2024): sum bounds `spm_sum_le_sqrt` and `spm_sum_le_levels` (dyadic levels) |
| `LeanMachineLearning/SequentialLearning/BretagnolleHuber.lean` | Bretagnolle–Huber for the actions of two sequences of rounds |
| `LeanMachineLearning/Game/Maximin.lean` | pure maximin value: attained, optimism of upper bounds; the mixed maximin value is attained; closed form for `2 × 2` games without PSNE |
| `LeanMachineLearning/Game/RepeatedGame.lean` (additions) | counts of action pairs and their measurability |
| `LeanMachineLearning/Game/Regret.lean` | `NR_T = PSMR_T + Δ^mix T`, `NR_T ≤ ER_T`, PSNE relations between `ER_T(x*)` and `PSMR_T`, failure-event bound on `PSMR_T` |
| `LeanMachineLearning/Game/Run.lean` | the law of a round of a run against `gameEnv` given the history (conditional law of the actions, reward mean), lower-integral and signed versions |
| `LeanMachineLearning/Game/Oblivious.lean` | an oblivious opponent turns an uninformed learner's problem into a non-stationary bandit; two-point noise mixtures |
| `LeanMachineLearning/Game/Concentration.lean` | the reward noise is conditionally 1-sub-Gaussian for the pre-reward filtration; the self-normalized bound for runs of the repeated game |
