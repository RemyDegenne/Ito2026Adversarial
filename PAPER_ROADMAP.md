# Paper roadmap: Adversarial Learning in Games with Bandit Feedback: Logarithmic Pure-Strategy Maximin Regret

Paper: RemyDegenne/Ito2026Adversarial · LMLExplore afd365492580 · LMLRoadmaps d01bdd6b89ce · Refreshed 2026-11-09

## Items

| Id | Item | Tag | Link | Status | Files |
|---|---|---|---|---|---|
| R1 | Measurability of the gradient | exists | `TauCeti.measurable_gradient` | – | `ForLMLExplore/Analysis/Calculus/Gradient/Measurable.lean` |
| R2 | Compactness of the convex hull of a compact set in finite dimension | exists | `IsCompact.convexHull` | – | `ForLMLExplore/Analysis/Convex/CompactHull.lean` |
| R3 | Fenchel conjugate of a function restricted to a set | exists | `TauCeti.fenchelConjugate` | – | `ForLMLExplore/Analysis/Convex/FenchelConjugate.lean` |
| R4 | Probability simplex: topology, uniform point, moving mass between coordinates | exists | `LMLExplore.simplex` | – | `ForLMLExplore/Analysis/Convex/Simplex.lean` |
| R5 | Finite weighted sums of Dirac masses | exists | `LMLExplore.weightedMeasure` | – | `ForLMLExplore/MeasureTheory/Measure/Weighted.lean` |
| R6 | Gaussian integrals of quadratic forms with a linear term | exists | `LMLExplore.integral_exp_inner_sub_inner_apply` | – | `ForLMLExplore/Analysis/SpecialFunctions/Gaussian/QuadraticForm.lean` |
| R7 | Regularized Gram matrices: rank-one updates, determinant, trace, log-determinant bound | exists | `LMLExplore.designOp` | – | `ForLMLExplore/Analysis/Matrix/DesignMatrix.lean`, `ForLMLExplore/Analysis/Matrix/LogDet.lean`, `ForLMLExplore/Analysis/Matrix/SchurComplement.lean` |
| R8 | Elliptical potential lemma | exists | `LMLExplore.sum_min_one_inner_inverse_designOp_le_log_det` | – | `ForLMLExplore/Analysis/Matrix/EllipticalPotential.lean`, `ForLMLExplore/Analysis/SpecialFunctions/Log/OneAdd.lean` |
| R9 | Weighted norms of positive definite matrices, Loewner order and square roots | exists | `ContinuousLinearMap.IsPositive.abs_inner_le_sqrt_mul_sqrt_ringInverse` | – | `ForLMLExplore/Analysis/InnerProductSpace/Mahalanobis.lean`, `ForLMLExplore/Analysis/Matrix/Order.lean`, `ForLMLExplore/Analysis/CStarAlgebra/Matrix.lean`, `ForLMLExplore/Analysis/Matrix/MeasurableSpace.lean` |
| R10 | Disintegration of a lower integral along a conditional law | exists | `ProbabilityTheory.HasCondDistrib.lintegral_comp_prodMk_eq_lintegral_lintegral` | – | `ForLMLExplore/Probability/HasCondDistrib.lean` |
| R11 | Binary relative entropy and Pinsker's inequality | exists | `LMLExplore.klBer` | – | `ForLMLExplore/InformationTheory/KullbackLeibler/Bernoulli.lean`, `ForLMLExplore/InformationTheory/KullbackLeibler/Pinsker.lean`, `ForLMLExplore/Analysis/SpecialFunctions/Log/Basic.lean` |
| R12 | Bretagnolle–Huber inequality | exists | `LMLExplore.exp_neg_klDiv_div_two_le` | – | `ForLMLExplore/InformationTheory/KullbackLeibler/BretagnolleHuber.lean` |
| R13 | Bretagnolle–Huber for the histories of two algorithm–environment pairs | exists | `LMLExplore.exp_neg_klDiv_map_history_div_two_le` | – | `ForLMLExplore/SequentialLearning/BretagnolleHuber.lean` |
| R14 | Index algorithms and their run lemmas | exists | `LMLExplore.Bandits.indexAlgorithm` | – | `ForLMLExplore/SequentialLearning/Algorithms/Index.lean` |
| R15 | Importance-weighted estimator and sampling from weights in the simplex | exists | `LMLExplore.Bandits.iwEstimator` | – | `ForLMLExplore/Bandits/ImportanceWeighting.lean`, `ForLMLExplore/MeasureTheory/MeasurableSpace/Constructions.lean` |
| R16 | Tsallis-INF and its loss estimates | exists | `LMLExplore.Bandits.tsallisINF` | – | `ForLMLExplore/Bandits/TsallisINF.lean` |
| R17 | Confidence ellipsoid of ridge regression and optimism of the linear UCB index | exists | `LMLExplore.sqrt_inner_ridgeEstimate_sub_le` | – | `ForLMLExplore/Bandits/LinearBandit/ConfidenceEllipsoid.lean`, `ForLMLExplore/Bandits/LinearBandit/Ridge.lean` |
| R18 | Bernoulli laws on two arbitrary points: lower integrals, density, divergence | refactor | `LMLExplore.klDiv_bernoulliMeasure` | proved | `ForLMLExplore/Probability/Distributions/Bernoulli.lean`, `ForLMLExplore/InformationTheory/KullbackLeibler/Bernoulli.lean` |
| R19 | Two-point laws on {−1, 1} indexed by their mean: mixtures and divergence | refactor | `LMLExplore.bernoulliKernel` | proved | `ForLMLExplore/Probability/Distributions/TwoPoint.lean`, `ForLMLExplore/InformationTheory/KullbackLeibler/TwoPoint.lean` |
| R20 | Ville's inequality for ℝ≥0∞-valued supermartingales in lower-integral form | refactor | `MeasureTheory.Supermartingale.measure_exists_le_le` | proved | `ForLMLExplore/Probability/Martingale/Ville.lean` |
| R21 | Self-normalized bound under integrated conditional sub-Gaussianity, on any probability space | refactor | `LMLExplore.measure_exists_inner_ringInverse_designOp_ge_le` | proved | `ForLMLExplore/Probability/Martingale/SelfNormalized.lean` |
| R22 | Support of the feedback, and i.i.d. feedback, for every environment | refactor | `Learning.IsAlgEnvSeq.ae_forall_feedback_mem_bandit` | proved | `ForLMLExplore/SequentialLearning/ObliviousEnv.lean` |
| R23 | Regret of a sequence of plays against a fixed comparator, with its algebra | target | OnlineLearning 0.1 | proved | `ForLMLExplore/OnlineLearning/Regret.lean` |
| R24 | Stability of the ½-Tsallis FTRL step for shifted importance-weighted estimates | target | Bandits 7.5 | proved | `ForLMLExplore/OnlineLearning/TsallisHalf.lean` |
| R25 | Algorithms with a recursively updated state, and policies that read the history through a statistic | staged | S1 | proved | `ForLMLExplore/SequentialLearning/Algorithms/Stateful.lean`, `ForLMLExplore/SequentialLearning/FactorsThrough.lean`, `ForLMLExplore/SequentialLearning/Announce.lean` |
| R26 | Online learners as state machines, and their algorithms | staged | S1 | proved | `ForLMLExplore/OnlineLearning/OnlineLearner.lean` |
| R27 | Divergence decomposition for oblivious non-stationary bandits | staged | S2 | proved | `ForLMLExplore/SequentialLearning/DivergenceDecomposition.lean` |
| R28 | FTRL on the simplex through its value function: Danskin's theorem, measurable plays, regret decomposition | staged | S3 | proved | `ForLMLExplore/OnlineLearning/SimplexFTRL.lean`, `ForLMLExplore/OnlineLearning/FTRLRegret.lean`, `ForLMLExplore/MeasureTheory/MeasurableSpace/ToSet.lean` |
| R29 | Tsallis entropies on the simplex, and inequalities for real powers with exponent in [0, 1] | staged | S4 | proved | `ForLMLExplore/OnlineLearning/TsallisEntropy.lean`, `ForLMLExplore/Analysis/Convex/SpecificFunctions/Pow.lean` |
| R30 | FTRL with the hybrid Tsallis regularizer: maximizer, joint differentiability, stability | staged | S5 | proved | `ForLMLExplore/OnlineLearning/HybridTsallis.lean` |
| R31 | Stability–penalty-matching learning rates | staged | S5 | proved | `ForLMLExplore/OnlineLearning/StabilityPenaltyMatching.lean` |
| R32 | Zero-sum games in normal form: equilibria, pure and mixed maximin values, gaps | staged | S6 | proved | `ForLMLExplore/Game/ZeroSum.lean`, `ForLMLExplore/Game/Maximin.lean` |
| R33 | Repeated zero-sum games with noisy rewards against an adaptive opponent | staged | S7 | proved | `ForLMLExplore/Game/RepeatedGame.lean`, `ForLMLExplore/Game/Run.lean`, `ForLMLExplore/Game/Oblivious.lean`, `ForLMLExplore/Game/Concentration.lean`, `ForLMLExplore/MeasureTheory/Integral/Bochner/Basic.lean` |
| R34 | Setting of Section 3: gap thresholds, Algorithms 1–4, bilinear games | paper | | proved | `ILMTW2026/Setting.lean` |
| R35 | Pure-strategy maximin regret and Nash regret, and their relations with the external regret | paper | | proved | `ForLMLExplore/Game/Regret.lean` |
| R36 | Tsallis-INF in the uninformed game: worst-case and self-bounding regret bounds | paper | | proved | `ILMTW2026/TsallisINFRegret.lean` |
| R37 | Tsallis-FTRL-SPM in the uninformed game: its path, its regret, the paper's parameters | paper | | proved | `ILMTW2026/TsallisSPMPath.lean`, `ILMTW2026/TsallisSPMRegret.lean`, `ILMTW2026/TsallisSPMPaper.lean` |
| R38 | The two games and the oblivious opponent of the lower bound | paper | | proved | `ILMTW2026/LowerBound.lean` |
| R39 | Good events, optimism and pair counts of Maximin-UCB and Maximin-LinUCB | paper | | proved | `ILMTW2026/MaximinUCBAnalysis.lean`, `ILMTW2026/MaximinLinUCBAnalysis.lean` |

## Notes

- R1–R22: the library was written on LML before the project moved to LMLExplore, and imports
  no LMLExplore module yet. Five local declarations have the full name of an LMLExplore
  declaration and break the build as soon as the project imports the LMLExplore file: delete them
  at the bump. They are `IsCompact.convexHull` (R2), `Real.min_one_le_two_mul_log_one_add` (R8),
  `ProbabilityTheory.bernoulliMeasure_absolutelyContinuous` and
  `ProbabilityTheory.bernoulliMeasure_absolutelyContinuous_iff` (R18), and
  `Learning.Environment.ofSeq` (R22). Other names become ambiguous when both namespaces are open:
  - `MeasureTheory.weightedMeasure` and `LMLExplore.weightedMeasure` (R5);
  - `Learning.simplex` and `LMLExplore.simplex` (R4);
  - `Bandits.tsallisINF` and `LMLExplore.Bandits.tsallisINF` (R16);
  - `Bandits.Linear.ridgeEstimate` and `LMLExplore.ridgeEstimate` (R17);
  - `Learning.dyadicLevel` and `TauCeti.dyadicLevel`, which is unrelated (R31).
- R1–R17: the frozen headline statements use several local definitions. Their LMLExplore
  counterparts are equal only up to a change of carrier or form, so the bump keeps these
  definitions and proves the bridges instead of deleting them. They are:
  - `Learning.simplex` on `EuclideanSpace ℝ ι` (R4);
  - `regGram` and `Matrix.mahalanobisSq` (R7, R9);
  - `pinvMahalanobisSq` (R9);
  - `Bandits.tsallisINF` (R16);
  - `Algorithm.index` and `Algorithm.statefulIndex` (R14);
  - `twoPoint` (R19).

  Several of them avoid the numeral `2` on purpose (see `notes/upstreaming-candidates.md`).
- R4: `Learning.simplex ι` is the set of `EuclideanSpace ℝ ι` whose image under `WithLp.ofLp` is
  `LMLExplore.simplex ι`. The following are not in LMLExplore: re-prove them on
  `LMLExplore.simplex` at the bump.
  - `measurableSet_simplex`;
  - `simplex_eq_range_weights`, the identification with the weights of `Convexity.StdSimplex`
    that Bandits 8.6 asks for;
  - `openSimplex`, the Euclidean norm bound and `add_smul_single_sub_mem_simplex`.
- R6: the project's `Matrix.PosDef.lintegral_exp_inner_sub_mahalanobisSq` is the lower-integral,
  matrix form of `LMLExplore.integral_exp_inner_sub_inner_apply`, which R21 uses.
  `Matrix.PosDef.det_sqrt` is Mathlib's `Matrix.PosSemidef.det_sqrt`.
- R7: `regGram λ x t` is the matrix of `LMLExplore.designOp (λ • 1) x t`, and `gram` is the case
  `V₀ = 0`. The local lemmas correspond to LMLExplore declarations:
  - `det_regGram_succ` is `LMLExplore.det_designOp_succ`;
  - `trace_regGram` is `LMLExplore.trace_designOp`;
  - `Matrix.det_add_vecMulVec` is `LMLExplore.det_add_rankOne`;
  - `Matrix.PosDef.log_det_le_card_mul_log_trace_div` follows from
    `Matrix.PosSemidef.det_le_trace_div_card_pow`;
  - `designSet` is characterized by `LMLExplore.mem_convexHull_image_rankOne_iff`.
- R8: LMLExplore's elliptical potential lemma takes any positive invertible `V₀`, and its
  log-determinant bound is `LMLExplore.log_det_designOp_div_pow_le`.
- R9: LMLExplore and Mathlib have the operator forms (`Matrix.PosDef.dotProduct_mulVec_pos`,
  `CFC.sqrt_mul_sqrt_self`, `Matrix.ofLp_toLpLin`, `TauCeti.measurable_matrix_inv`). The following
  are not in the dependencies: they stay local.
  - the antitonicity of the inverse in the Loewner order for real positive definite matrices
    (`Matrix.PosDef.inv_le_inv`; Mathlib's `CStarAlgebra.inv_le_inv` needs a C⋆-algebra);
  - the variational form `pinvMahalanobisSq`;
  - the measurability of `mulVec` and `dotProduct`.
- R11: the local `InformationTheory.klBer` is not clamped, while `LMLExplore.klBer` clamps its
  arguments to `[0, 1]`. The two agree on `[0, 1] × [0, 1]`, so the move adds `p, q ∈ [0, 1]`
  hypotheses at the uses. Pinsker's inequality is `LMLExplore.two_mul_sq_le_klBerReal` and
  `TauCeti.two_mul_sq_measureReal_sub_le_klDiv`. Keep the lemmas that LMLExplore lacks,
  re-proved on its `klBer`:
  - `sub_log_two_le_klBerReal`, `mul_log_sub_log_two_le_klBerReal`, `exp_neg_le_of_klBer_le`
    and `abs_sub_le_sqrt_klDiv`;
  - the logarithm inequalities of `Log/Basic.lean`. `Real.neg_log_one_sub_le_add_sq`, for
    `|x| ≤ 1/2`, is the inequality `log(1 + x) ≥ x - x²` of OnlineLearning 1.7 after `x ↦ -x`, and
    a port of that target can take it.
- R14: `Algorithm.index` takes a real index, while `LMLExplore.Bandits.indexAlgorithm` takes an
  `EReal` one. Both play LML's `argmax`, so the bridge is a statement about `argmax` of the
  coerced index. `maximinUCB`, in the closure of Theorem 4, is built with `Algorithm.index`.
  `Algorithm.statefulIndex` and `factorsThrough_index`, the index read from a recursively updated
  state that Maximin-LinUCB uses, belong to R25. LMLExplore assumes `MeasurableSingletonClass`
  where the project assumes `MeasurableEq`.
- R15: `Learning.simplexKernel` is `LMLExplore.Bandits.weightKernel`, and
  `Bandits.importanceWeighted` is `LMLExplore.Bandits.iwEstimator`. The combinator that turns an
  online learner and an estimator into a bandit algorithm (`OnlineLearner.toBanditAlgorithm`,
  `banditPolicy`) is an instance of `LMLExplore.Bandits.weightAlgorithm` and belongs to R26.
  `Constructions.lean` holds measurability helpers that no dependency has (`Measurable.ite` as
  `fun_prop`, `measurable_decide`, `Measurable.eval_prod`). Their place in LMLExplore is
  `MeasureTheory/MeasurableSpace/Constructions.lean`.
- R16: `LMLExplore.Bandits.tsallisINF` is the algorithm of Theorem 1 (`α = 1/2`,
  `η_t = 1 / (2 √(t + 1))`, any observation type), and `LMLExplore.Bandits.lossIwEstimator` is
  its estimate. The local `Bandits.tsallisINF α η` takes any Tsallis parameter and learning rates,
  and its weights are the gradient-defined maximizer of R28. Theorem 1's `tsallisINFHalf` is built
  on it: the bump relates the two through `LMLExplore.tsallisWeights_add_const`.
- R17: `sqrt_mahalanobisSq_sub_ridgeEstimate_le` is `LMLExplore.sqrt_inner_ridgeEstimate_sub_le`,
  and the optimism lemmas are `LMLExplore.Bandits.inner_le_ofulIndex` and
  `LMLExplore.Bandits.ofulIndex_le_inner_add`. The incremental, measurable state of ridge
  regression (`Bandits.Linear.RidgeState`, `ridgeUpdate`) is not in LMLExplore. Maximin-LinUCB
  computes its index from it, and it is an instance of the stateful algorithms of R25.
- R18: LMLExplore's `klDiv_bernoulliMeasure` computes the divergence between Bernoulli laws on
  `{1, 0}`. The project computes it for Bernoulli laws on any two points `x ≠ y`
  (`klDiv_bernoulliMeasure` and `klDiv_bernoulliMeasure_eq_klBerReal` in
  `KullbackLeibler/Bernoulli.lean`). The proof uses `lintegral_bernoulliMeasure`,
  `bernoulliMeasure_eq_withDensity` and `rnDeriv_bernoulliMeasure`, which Mathlib and LMLExplore
  lack (Mathlib has only the Bochner `integral_bernoulliMeasure`). The refactor generalizes
  `klDiv_bernoulliMeasure` to any two points, updates its uses, and adds these lemmas to
  `LMLExplore/Probability/Distributions/Bernoulli.lean`.
- R19: LMLExplore's `bernoulliKernel` sends `x` to the law on `{0, 1}` of mean `x`, and
  `bernoulliKernel_comp` computes its mixtures. The paper's rewards follow `twoPoint x`, the law on
  `{−1, 1}` of mean `x`. A mixture of these laws is the law of the mixed mean
  (`sum_smul_twoPoint`). The refactor generalizes `bernoulliKernel` to the laws on two points
  `a ≠ b` indexed by their mean, with their mean, support and mixtures. `twoPoint` is then the
  case `{−1, 1}`. The following come with it:
  - `klDiv_twoPoint`, the divergence as `klBer` of the rescaled means;
  - `klBerReal_le_four_mul_sq` on `[1/4, 3/4]`, where LMLExplore's `klBerReal_le_sq_sub_div` gives
    the constant `16/3`.

  Do R19 after R18.
- R20: LMLExplore's `measure_exists_le_le` needs a real supermartingale, hence integrability, and
  a σ-finite filtration. `MeasureTheory.mul_measure_exists_le_le_lintegral` is Ville's inequality
  for `ℝ≥0∞`-valued processes whose lower integrals over the sets of the filtration decrease, with
  no integrability or finiteness hypothesis. R21 applies it to the Gaussian mixture, a lower
  integral, on a probability space with no Standard Borel structure. The refactor proves this form
  and derives `measure_exists_le_le` from it.
- R21: LMLExplore's self-normalized bound assumes `[StandardBorelSpace Ω]` and Mathlib's
  `HasCondSubgaussianMGF`, which is built on `condExpKernel`. This covers
  `measure_exists_inner_ringInverse_designOp_ge_le`,
  `le_measureReal_forall_inner_ringInverse_designOp_lt` and
  `supermartingale_integral_exp_inner_sum_smul_sub_designOp`. Lemma 13 and Theorems 6 and 12
  quantify over runs on any probability space, so the project assumes
  `Learning.IsCondSubgaussianNoise` instead. It is conditional sub-Gaussianity in integrated form:
  an exponential-moment inequality against every nonnegative `𝓕 n`-measurable function. The
  refactor states the supermartingale and both forms of the bound under that hypothesis, with a
  variance proxy `σ²` (the project has `σ² = 1`). It derives the current statements, since
  `HasCondSubgaussianMGF` implies the integrated form (compare the hypothesis of
  `LMLExplore.supermartingale_exp_sum_of_lintegral_mul_exp_le`). Do R21 after R20.
  Generalization 1.18 (a positive definite regularizer `V₀`) edits the same file: do one before
  the other. The matrix forms stay in the project (R7, R9).
- R22: the local `Learning.Environment.ofSeq y` is LMLExplore's
  `Learning.Environment.ofSeq (fun _ ↦ ()) (fun n _ ↦ y n) _`: delete it at the bump and use
  `Learning.IsAlgEnvSeq.feedback_ofSeq_ae_all_eq`. LMLExplore states the support of the feedback
  only for bandits. The project's `IsAlgEnvSeq.ae_feedback_mem` and `IsAlgEnvSeq.ae_obs_mem`
  hold for every environment whose feedback, or observation, laws lie in a set
  (`Environment.FeedbackIn`, `Environment.ObsIn`), by `ProbabilityTheory.HasCondDistrib.ae_mem`.
  The refactor states them for every environment and derives the bandit case. The rest of the
  file stays local unless it fits the same pull request:
  - `Environment.const μ`, which is `Environment.bandit (Kernel.const _ μ)`, and its i.i.d.
    feedback lemmas;
  - `Environment.FeedbackIgnoresAction` and its conditional-law lemmas.
- R23: OnlineLearning 0.1 asks for the regret `∑_{t<n} (ℓ_t(x_t) - ℓ_t(u))` of plays on an
  arbitrary type, which is `Learning.ocoRegret`, with the API later layers use (additivity in the
  losses, intervals). It also asks for the dynamic, interval, strongly adaptive and tracking
  regrets and the path length, which the project does not have. Port it to
  `LMLExplore/OnlineLearning/`, namespace `LMLExplore.OnlineLearning`.
  - The roadmaps take linear losses in the dual (OnlineLearning, Conventions). The project's
    `linRegret`, written with the inner product of a Hilbert space, is the case of the losses
    `InnerProductSpace.toDual ℝ E ℓ_t`.
  - `ocoRegret_le_sum_of_hasSubgradientWithinAt` is
    `LMLExplore.OnlineLearning.sum_sub_le_sum_apply_sub_of_hasSubgradientWithinAt`.
  - `expertRegret`, `LossesIn` and `IsBestCoord`, stated on `EuclideanSpace ℝ ι`, are not in 0.1.
- R24: Bandits 7.5 proves the adversarial regime of Tsallis-INF from three ingredients: the
  local-norm bound through the unconstrained step (OnlineLearning 6.1), the shift by the loss of
  the played arm, and the conditional moments of the estimates. The local-norm bound is
  LMLExplore's
  `LMLExplore.OnlineLearning.exists_mem_segment_apply_sub_sub_bregDiv_div_le_of_hasFDerivWithinAt`,
  whose docstring names the ½-Tsallis case but proves no instance. This item is the stability
  term. For the ½-Tsallis step and an estimate shifted by a constant `c`,
  `sq_sub_sq_mul_sub_le` and `inner_sub_sub_le_tsallisHalf` bound it by
  `2 η ∑_a √(p_a)³ (c - g_a)²` when `η √(p_a) (c - g_a) ≥ -1/2`.
  `Bandits.TsallisINF.inner_sub_estimate_sub_le` specializes it to the importance-weighted
  estimate.
  - The project works through the value function of R28 and the entropy of R29, on
    `Learning.simplex`, with gains.
  - The port restates it in LMLExplore's conventions: losses, `LMLExplore.simplex`, the
    closed-form weights `LMLExplore.tsallisWeights` with `tsallisNormalizer` and the objective
    identity `dotProduct_sub_mul_sum_sqrt_sub_eq_sum`. It keeps signed estimates: the paper's
    rewards lie in `[−1, 1]`, and 7.5's feedback in `[0, 1]` is a case of them.
  - The quadratic growth `sq_norm_sub_div_four_le` comes with it.
  - The `α = 1/2` part of R29 (`tsallisEntropy_half`, `sum_sqrt_le_sqrt_card`) is the penalty
    term of 7.5, and R36 is the rest of 7.5's proof, in the setting of the game.
- R25: the three files cover the following.
  - `Stateful.lean`: `Algorithm.stateful` and `Algorithm.detStateful` read their policy from a
    state that each round updates (`foldHist`, `stateProcess`), with their run lemmas. LML's
    `Algorithm.markov` is the case of a trivial state.
  - `FactorsThrough.lean`: `Algorithm.FactorsThrough`, a policy that reads the history only
    through a map, stable under `Algorithm.comap`. LML's `Algorithm.IsMarkov` is its case
    `Prod.snd`.
  - `Announce.lean`: algorithms that ignore what `Environment.comapAction` announces
    (`Algorithm.IgnoresAnnounced`, `IsAlgEnvSeq.isAlgEnvSeq_of_ignoresAnnounced`).

  R33 uses them to see a run of the game from either player's side.
- R26: `Learning.OnlineLearner` is a deterministic learner given by an initial state, a play from
  the state and a context, and an update from the feedback. It has iterates on sequences and an
  LML algorithm `toAlgorithm`, built with `Algorithm.detStateful`. With `toBanditAlgorithm` (R15)
  it gives the bandit algorithms of the paper. OnlineLearning 0.2 specifies causal learners as
  functions of the past, so a state machine is one way to build them, and a maintainer may move
  this item to 0.2.
- R27: LML's divergence decomposition (`Learning.IsAlgEnvSeq.klDiv_map_history_bandit`) and
  LMLExplore's `Learning.IsAlgEnvSeq.klDiv_map_history_eq_sum_pullCount` are stated for a
  stationary bandit. `klDiv_map_history_banditSeq` and `klDiv_map_history_banditSeq_eq_sum` are
  their forms for LML's `Environment.banditSeq`. The lower bound of Theorem 2 uses them: against an
  oblivious opponent, the uninformed learner faces such an environment
  (`IsAlgEnvSeq.isAlgEnvSeq_banditSeq_oblivious`, R33). The Bandits roadmap leaves non-stationary
  bandits out of its scope.
- R28: `LMLExplore.OnlineLearning.sum_apply_sub_le_ftrl` is the general FTRL decomposition, with
  stability terms that include the increments of the regularizer. The project's
  `sum_inner_sub_le_ftrl` has its stability terms at a fixed regularizer, and follows from it.
  Danskin's theorem here (`hasGradientAt_ftrlValue`) is the simplex case of the third bullet of
  OnlineLearning 1.4: a port should prove that bullet and derive this case from it. `ToSet.lean`
  is a measurability helper of this item.
- R29: LMLExplore has only the ½-Tsallis potential, written inline in
  `LMLExplore/Analysis/Convex/Tsallis.lean`. The inequalities of `Pow.lean` are not in Mathlib,
  which has the two-term `Real.rpow_add_le_add_rpow` and `Real.concaveOn_rpow`.
- R30: `powBregman` is LML's `bregDiv` of `x ↦ -x ^ a`. The multiplicative stability
  `le_eight_mul_of_kkt` has the constant `8` where Ito, Tsuchiya, Honda (2024) have `2`. The
  exploration rate only gives `|ℓ̂| ≤ (1 - α) β q*^(α - 1) / 4` (`notes/blueprint-outline.md`,
  section 3).
- R31: LMLExplore's only adaptive learning rate is AdaHedge's.
- R32: the equilibria are Mathlib saddle points with the players exchanged, since the first player
  of `IsSaddlePointOn` minimizes. `IsPSNE u x y` is
  `IsSaddlePointOn univ univ (fun y x ↦ u x y) y x`, and `IsMSNE` is the same on the simplices.
  `mixedUtility u p q` is `p ⬝ᵥ (Matrix.of u *ᵥ q)`. `nashValue` is real-valued, while
  `LMLExplore.iSup_simplex_iInf_ofReal_dotProduct` is von Neumann's theorem for
  `ENNReal.ofReal` payoffs. The item proves that a maximin mixed strategy exists, not von
  Neumann's identity. The gaps (`rowGap`, `colGap`, `pairGap`, `mixGap`) are the paper's
  `Δʳ`, `Δᶜ`, `Δ_{xy}`, `Δ^mix`.
- R33: several parts of the item are already in LML.
  - `Player 𝒳 𝒴` is LML's `Algorithm Unit 𝒳 (𝒴 × ℝ)`, and `Player.ofUninformed` is
    `Algorithm.comapFeedback Prod.snd`.
  - `pairCount` and `pairSum` are LML's `pullCount` and `sumRewards` of the process of action
    pairs: a port restates them so.
  - `Player.oblivious q` is LML's `Algorithm.markov` of constant kernels.

  `psmr` and `nashRegret`, defined in `RepeatedGame.lean`, belong to R35. In `Bochner/Basic.lean`,
  `Integrable.of_ae_abs_le` is Mathlib's `MeasureTheory.Integrable.of_bound`.
- R35: PSMR is the paper's measure of performance. This file should move to `ILMTW2026/`,
  together with the definitions of `psmr` and `nashRegret`, when R33 is ported.
- R36: `externalRegret_tsallisINFHalf_le` and `externalRegretAgainst_tsallisINFHalf_le` are the
  adversarial and self-bounding regimes of Bandits 7.5 for the uninformed learner of a game on
  `Fin m`, with rewards in `[−1, 1]`. Restated for runs against any `Environment 𝓞 α ℝ`, with
  `LMLExplore.Bandits.pseudoRegret`, they would be 7.5's statements, and the game forms their
  corollaries (S7).
- R37: the SPM regret bound `externalRegretAgainst_tsallisSPM_le` is the bound of Ito, Tsuchiya,
  Honda (2024, Eq. (26)) for linear estimates, with the parameters of their Section 4.3. It is
  stated for the uninformed learner of a game; its library core is S3–S5.

## Proposed targets

### S1. Algorithms that read the history through a statistic

In `LMLExplore/SequentialLearning/Algorithms/`, for LML's `Algorithm 𝓞 𝓐 𝓨` and its runs
`IsAlgEnvSeq`:

1. **Stateful algorithms.**
   - Data: a measurable state space `σ`, an initial state, measurable updates
     `σ → Round 𝓞 𝓐 𝓨 → σ` that may depend on the round, and a policy kernel from `σ × 𝓞`
     to `𝓐`.
   - Define the algorithm whose policy at round `t` is the policy at the state obtained by folding
     the updates over the history, and the state process along a run. Prove its measurability for
     the history filtration, and the run lemma: given the history and the observation, the
     conditional law of `A_t` is the policy at the current state.
   - Deterministic stateful algorithms are the case of Dirac policies, and LML's
     `Algorithm.markov` the case of a trivial state.
2. **Factorization through a statistic.** Define the predicate that the policy of round `t`
   depends on the history only through a measurable map `T_t`. Prove that it is stable under
   `Algorithm.comap`, and its consequence for runs: the conditional law of `A_t` given `T_t` of
   the history. LML's `Algorithm.IsMarkov` is the case of the last observation.
3. **Announcements.** For LML's `Environment.comapAction`: an algorithm that ignores the announced
   part of its observation has the same runs against the announcing environment as against the
   original one.
4. **Online learners as state machines.**
   - Define deterministic learners given by an initial state, a play from the state and a
     context, and an update from the feedback, with their LML algorithms.
   - For a learner with plays in LMLExplore's `simplex α` and an estimator of the full feedback
     from the bandit feedback, define the randomized bandit algorithm, as an instance of
     `LMLExplore.Bandits.weightAlgorithm`.
   - These learners are one way to build the causal learners of OnlineLearning 0.2.
5. **Instances.** The ridge-regression state of linear UCB algorithms (`designOp` and the
   response vector; Bandits 9.2), and the cumulative-estimate state of Tsallis-INF.

Generalization: any observation, action and feedback spaces, and updates that depend on the round.

### S2. Divergence decomposition for oblivious environments

For an algorithm run against LML's oblivious environments `Environment.banditSeq ν` and
`Environment.banditSeq ν'`, with `ν ν' : ℕ → Kernel 𝓐 𝓨`, prove the time-sum form of
[LS, Lemma 15.1] in `ℝ≥0∞`. The divergence between the laws of the histories of length `n` is
$\sum_{t<n}\mathbb E_\nu[D(\nu_t(A_t),\nu'_t(A_t))]$. The proof goes through LML's
`IsAlgEnvSeq.klDiv_map_history_stepKernel`. LML's `klDiv_map_history_bandit` is the case of
constant sequences. It applies to lower bounds against oblivious adversaries whose reward laws
change with the round.

### S3. Follow-the-regularized-leader on the simplex through its value function

Setting: a finite type `α`, a regularizer `ψ` continuous on `simplex α`, and the value function
$\Phi_\psi(G)=\max_{p\in\Delta}(\langle p,G\rangle-\psi(p))$. The value function is Tau Ceti's
`fenchelConjugate` of `ψ` plus the indicator of the simplex. Prove:

- **Danskin's theorem.** If `ψ` has quadratic growth at its maximizers, as an `m`-strongly convex
  `ψ` does, then $\Phi_\psi$ is differentiable, with gradient the unique maximizer. For a
  measurable family of regularizers, the maximizer is jointly measurable in the parameter and in
  `G`. This is the simplex case of OnlineLearning 1.4, and should be derived from it.
- **The FTRL decomposition** [Ora, Lemma 7.1] for time-varying regularizers $\psi_t$. The
  regret of the plays $p_t=\nabla\Phi_{\psi_t}(G_t)$ against $u\in\Delta$ is at most the sum of:
  - the penalty terms, $\psi_{t+1}-\psi_t$ at the plays and at `u`;
  - the stability terms at a fixed regularizer,
    $\Phi_{\psi_t}(G_{t+1})-\Phi_{\psi_t}(G_t)-\langle p_t,g_t\rangle$.

  Derive it from `sum_apply_sub_le_ftrl`.

Bandit analyses use this form: Tsallis-INF [ZS21], and FTRL with learning rates that adapt to the
data [ITH24].

### S4. Tsallis entropies on the simplex

For $0<a\le1$, define the Tsallis entropy $\varphi_a(p)=\frac1a\sum_i(p_i^a-p_i)$ on
`simplex α`. Prove the following [ZS21; ITH24, Lemma 23]:

- continuity;
- nonnegativity, with value `0` at the vertices;
- the maximum $(k^{1-a}-1)/a$, at the uniform point;
- the self-bounding bound $\varphi_a(p)\le k^{1-a}(1-p_x)^a/a$ for every `x`;
- the lower bound $(1-a)\,q^\ast(p)^a/(2a)\le\varphi_a(p)$, where
  $q^\ast(p)=\min(\|p\|_\infty,1-\|p\|_\infty)$;
- $\varphi_a(r)\le c\,\varphi_a(p)$ when $r\le c\,p$ coordinatewise and $c\ge1$;
- the case $a=\frac12$.

Prove the inequalities for $x^a$, $a\in[0,1]$, that these bounds use:

- the tangent-line bound;
- the quadratic lower bound on the Bregman divergence of $-x^a$;
- $K^{-a}\le1-a(1-1/K)$;
- subadditivity over finite sums;
- the power mean inequality for exponents at most `1`.

LMLExplore's ½-Tsallis weights (`tsallisWeights`) are the FTRL maximizer for $\varphi_{1/2}$.

### S5. Tsallis-FTRL with stability–penalty-matching learning rates

Setting: a finite type `α`, FTRL on `simplex α` with the hybrid regularizer
$\beta\varphi_a+\bar\beta\varphi_{1-a}$ of S4, $0<a<1$, $\beta>0$, $\bar\beta\ge0$ [ITH24].

1. **The regularizer.**
   - The maximizer exists and is unique, its coordinates are positive, and it satisfies the
     first-order conditions.
   - The objective has quadratic growth around the maximizer, through the Bregman divergences of
     the two entropies.
   - The value function is jointly differentiable in $(\beta,G)$, with the maximizer as gradient
     in `G`.
   - The stability bound for estimates bounded by $(1-a)\beta q^{\ast a-1}/4$, the multiplicative
     stability of the maximizer under a small increase of $\beta$ [ITH24, Lemma 24], and a lower
     bound on its coordinates.
2. **Stability–penalty-matching rates.** Given nonnegative stability coefficients $z_t$ and
   positive penalty coefficients $h_t$, the rates are $b_{t+1}=b_t+z_t/(b_th_t)$ from $b_0>0$.
   Prove both forms of [ITH24, Lemmas 9 and 10]:
   - the worst-case bound $\sum_{t<T}z_t/b_t\le2\sqrt{2H\sum_tz_t}+2z_{\max}/b_0$ for
     $h_t\le H$;
   - the bound by dyadic levels, which gives the logarithmic bound of the self-bounding analysis.
3. **The regret bound.** The bound of [ITH24, (26)] for the algorithm with exploration and
   linear estimates, against any environment.

### S6. Zero-sum games in normal form

For finite action types `𝒳`, `𝒴` and a payoff `u : 𝒳 → 𝒴 → ℝ` to the maximizing player, with
mixed strategies in LMLExplore's `simplex`:

- **Equilibria and values.**
  - Pure and mixed Nash equilibria, as Mathlib saddle points (`IsSaddlePointOn`).
  - The pure maximin value $v^\ast=\max_x\min_yu(x,y)$ and its attainment.
  - The mixed value $\max_p\min_q\,p^\top uq$, attained by a maximin mixed strategy. Build on
    OnlineLearning 15.3 for von Neumann's theorem on `simplex 𝒳 × simplex 𝒴` with real payoffs.
  - $v^\ast\le$ the mixed value, with equality at a pure equilibrium.
- **Strict equilibria and gaps.**
  - Strict pure equilibria.
  - The gaps of the actions against a pure equilibrium, the pair gaps $v^\ast-u(x,y)$, and the
    gap between the mixed and the pure value [ILTW25].
- **Optimism.** An upper bound $U\ge u$ gives $\max_x\min_yU\ge v^\ast$.
- **2 × 2 games** without pure equilibrium: the closed form of their value.

### S7. Repeated zero-sum games with noisy rewards

Setting: the learner and the opponent are LML algorithms on finite (or measurable) action types.
The opponent observes the history from its own side. The reward of round `t` is drawn from a
history-dependent kernel with conditional mean $u(x_t,y_t)$ [OLO21; MJR25; ILTW25].

1. **The environment.**
   - Construct the environment that the learner faces, for an opponent algorithm and reward
     kernels. The uninformed learner observes only the reward, so its feedback is in `ℝ`: an
     adaptive environment `Environment Unit 𝒳 ℝ`, to which the Bandits roadmap's bounds against
     any environment apply. The informed learner also observes the opponent's action.
   - The swap of the two players' views, through S1.
   - The law of a round given the history.
2. **Regrets.** The external regret against a fixed action and the Nash regret, related to
   LMLExplore's `pseudoRegret`, and the relations between them.
3. **Oblivious opponents.** Against an opponent whose actions do not depend on the history, the
   uninformed learner faces `Environment.banditSeq` (S2).
4. **Concentration.** The reward noise is conditionally sub-Gaussian for the filtration that
   contains both players' actions of the round. Deduce the self-normalized bound
   [AYPS11, Theorem 1] for runs of the game, from R21's form on any probability space.

Counts and sums of action pairs are LML's `pullCount` and `sumRewards` of the pair process.

References:
- [LS] T. Lattimore, Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020).
- [Ora] F. Orabona, *A Modern Introduction to Online Learning*, arXiv:1912.13213 (v10).
- [ZS21] J. Zimmert, Y. Seldin, *Tsallis-INF: an optimal algorithm for stochastic and adversarial
  bandits*, JMLR 22 (2021).
- [ITH24] S. Ito, T. Tsuchiya, J. Honda, *Adaptive learning rate for follow-the-regularized-leader:
  competitive analysis and best-of-both-worlds*, COLT 2024.
- [AYPS11] Y. Abbasi-Yadkori, D. Pál, Cs. Szepesvári, *Improved algorithms for linear stochastic
  bandits*, NeurIPS 2011.
- [OLO21] B. O'Donoghue, T. Lattimore, I. Osband, *Matrix games with bandit feedback*, UAI 2021.
- [MJR25] A. Maiti, K. Jamieson, L. J. Ratliff, *On the limitations and possibilities of Nash
  regret minimization in zero-sum matrix games under noisy feedback*, Algorithmic Game Theory
  (2025).
- [ILTW25] S. Ito, H. Luo, T. Tsuchiya, Y. Wu, *Instance-dependent regret bounds for learning
  two-player zero-sum games with bandit feedback*, COLT 2025.
