# Upstreaming candidates

Library-shaped material written in phase 2 (2026-10-08/09), by destination. Paths are under
`Ito2026Adversarial/`. The library files copied from `LMLPapers` in phase 1 are not listed, except
where phase 2 added to them. None of this has been reviewed against the Mathlib guidelines yet, and
none of it is in `LMLPapers`.

Definitions changed in phase 1 to avoid the numeral `2` (challenge-gen, outline section 6) must be
carried over with the material when porting back to `LMLPapers`: `twoPoint`, `ridgeEstimate`,
`TsallisINF.estimate`, `banditPolicy`, `uniformVec`, `pinvMahalanobisSq`, and a private definition
in Pinsker.

## Mathlib

| File | Content |
|---|---|
| `Mathlib/Analysis/Matrix/LogDet.lean` | `log det A ≤ d log(tr A / d)` for positive definite `A` (AM–GM for the eigenvalues) |
| `Mathlib/Analysis/SpecialFunctions/Gaussian/QuadraticForm.lean` | the real Gaussian integral with a linear term, and its version for the quadratic form of a positive definite matrix (`Matrix.PosDef.lintegral_exp_inner_sub_mahalanobisSq`), `Matrix.PosDef.det_sqrt` |
| `Mathlib/Analysis/SpecialFunctions/Pow/Tangent.lean` | tangent-line inequality for `x ^ a`, `a ∈ [0, 1]`, and a quadratic lower bound on the Bregman divergence of `-x ^ a` (`Real.sq_le_rpow_bregman`) |
| `Mathlib/Probability/Martingale/VilleLintegral.lean` | Ville's inequality for `ℝ≥0∞`-valued supermartingales in the lower-integral sense (no integrability hypothesis) |
| `Mathlib/InformationTheory/KullbackLeibler/TwoPoint.lean` | divergence between two-point laws on `{-1, 1}` as a binary divergence, quadratic upper bound away from the boundary |
| `Mathlib/Probability/Distributions/TwoPointMixture.lean` | mean and support of the two-point law, mixtures of two-point laws |
| `Mathlib/InformationTheory/KullbackLeibler/BretagnolleHuber.lean` | copied from LMLPapers |

## LML

| File | Content |
|---|---|
| `LeanMachineLearning/SelfNormalized.lean` | conditionally sub-Gaussian noise (`IsCondSubgaussianNoise`), the Gaussian mixture supermartingale, and the self-normalized bound of Abbasi-Yadkori, Pál, Szepesvári (2011, Theorem 1) for a general filtration with predictable features |
| `LeanMachineLearning/EllipticalPotential.lean` | matrix determinant lemma for the regularized Gram matrix, `log det V_t` bound, the elliptical potential lemma |
| `LeanMachineLearning/Online/Bandit/Linear/ConfidenceEllipsoid.lean` | `‖θ - θ̂_t‖_{V_t} ≤ ‖S_t‖_{V_t⁻¹} + √λ ‖θ‖` for ridge regression |
| `LeanMachineLearning/Online/Bandit/Linear/Optimism.lean` | the linear UCB index is optimistic and exceeds the mean by at most `2 β' ‖v‖_{V⁻¹}` |
| `LeanMachineLearning/Online/Bandit/FTRLRegret.lean` | FTRL on the simplex with time-varying regularizers: Fenchel–Young, the regret decomposition (`sum_inner_sub_le_ftrl`), the value function's gradient is the maximizer (Danskin, `ftrlSimplex_eq`) |
| `LeanMachineLearning/Online/Bandit/TsallisHalf.lean` | Tsallis-1/2 FTRL: explicit maximizer, exact objective identity, stability of the importance-weighted estimate |
| `LeanMachineLearning/Online/Bandit/HybridTsallis.lean` | FTRL with the hybrid regularizer `β φ_α + βbar φ_{1-α}`: maximizer, first-order conditions, joint differentiability of the value function in `(β, G)`, stability, multiplicative stability, coordinate lower bounds |
| `LeanMachineLearning/Online/StabilityPenaltyMatching.lean` | the stability-penalty matching learning rates of Ito, Tsuchiya, Honda (2024): sum bounds `spm_sum_le_sqrt` and `spm_sum_le_levels` (dyadic levels) |
| `LeanMachineLearning/SequentialLearning/BretagnolleHuber.lean` | Bretagnolle–Huber for the actions of two sequences of rounds |
| `LeanMachineLearning/SequentialLearning/DivergenceDecomposition.lean` | divergence decomposition for non-stationary bandits (the `NonstationaryBandit` section of the LMLPapers file) |
| `LeanMachineLearning/Game/Maximin.lean` | the mixed maximin value is attained; closed form for `2 × 2` games without PSNE |
| `LeanMachineLearning/Game/RegretRelations.lean` | `NR_T = PSMR_T + Δ^mix T`, `NR_T ≤ ER_T`, strict-PSNE relations between `ER_T(x*)` and `PSMR_T` |
| `LeanMachineLearning/Game/Optimism.lean` | optimism of the pure maximin action of upper confidence bounds |
| `LeanMachineLearning/Game/Oblivious.lean` | an oblivious opponent turns an uninformed learner's problem into a non-stationary bandit; two-point noise mixtures |
| `LeanMachineLearning/Game/UninformedRun.lean`, `UninformedRunIntegral.lean` | the law of a round of a run against `gameEnv` given the history (conditional law of the actions, reward mean), lower-integral and signed versions |
| `LeanMachineLearning/Game/Concentration.lean` | the reward noise is conditionally 1-sub-Gaussian for the pre-reward filtration; the self-normalized bound for runs of the repeated game |
