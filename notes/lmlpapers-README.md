# Ito, Luo, Maiti, Tsuchiya, Wu — Adversarial Learning in Games with Bandit Feedback: Logarithmic Pure-Strategy Maximin Regret

COLT 2026, paper #98 of the list. arXiv source (`main.tex`, sections in `sec/`).
Shinji Ito, Haipeng Luo, Arnab Maiti, Taira Tsuchiya, Yue Wu.

A learner repeatedly plays a zero-sum game `u : 𝒳 × 𝒴 → [-1, 1]` against an *adaptive* adversary,
with bandit feedback: *uninformed* (only the noisy reward `r_t` of the played pair is observed) or
*informed* (the adversary's action `y_t` is observed as well). The performance measure is the
*pure-strategy maximin regret* `PSMR_T = E[∑_t (v* - u(x_t, y_t))]` with `v* = max_x min_y u(x, y)`.
Tsallis-INF (uninformed) has game-dependent logarithmic PSMR (Theorem 1), with an unavoidable
`1 / (Δʳ_min Δᶜ_min)` dependence (Theorem 2); Maximin-UCB (informed) has another logarithmic bound
(Theorem 4); both extend to bilinear games with large action sets (Tsallis-FTRL-SPM, Theorem 5;
Maximin-LinUCB, Theorems 6 and 12).

The paper's `jmlr` class (with the `cleveref` option) numbers all environments with one counter:
Theorem 1 (`thm:tsallis`), Theorem 2 (`thm:uninformed-lb`), Remark 3, Theorem 4 (`thm:pureucb`),
Theorem 5 (`thm:tsallis-bilinear`), Theorem 6 (`thm:purelinucb-informal`), Lemmas 7–11
(appendix), Theorem 12 (`thm:purelinucb`), Lemma 13 (`lem:conf-ellipsoid`).

## Formalization choices

* **Repeated games** (library, `LMLPapers/LeanMachineLearning/Game/RepeatedGame.lean`, namespace
  `Learning.RepeatedGame`). A round of the learner is a `Round Unit 𝒳 (𝒴 × ℝ)`: action `x_t`,
  feedback `(y_t, r_t)`. An informed learner is a `Player 𝒳 𝒴 = Algorithm Unit 𝒳 (𝒴 × ℝ)`; an
  uninformed learner is an `Algorithm Unit 𝒳 ℝ`, lifted by `Player.ofUninformed`
  (`Algorithm.comapFeedback Prod.snd`: it ignores `y_t` in the feedback). The adaptive adversary is
  itself a player with the roles exchanged, `opp : Player 𝒴 𝒳`, acting on the swapped history
  (`Hist.swapPlayers`): it sees the past actions and rewards but not `x_t` (simultaneous moves).
  The reward noise is a reward kernel `R : RewardKernel 𝒳 𝒴` (a kernel from the past rounds and
  the two actions to `ℝ`, history-dependent), with the paper's assumptions `RewardKernel.HasMean R u`
  (conditional mean `u x_t y_t`, i.e. martingale-difference noise) and
  `RewardKernel.RewardsIn R (Icc (-1) 1)`. The environment of the learner is `gameEnv opp R`.
  "Against any adaptive adversary" quantifies over all `opp` and all such `R`.
  Regrets `psmr`, `externalRegret`, `nashRegret`; counts `histPairCount`/`histPairSum` on histories
  and `pairCount`/`pairSum` on runs.
* **Zero-sum games** (`Game/ZeroSum.lean`, namespace `Learning.ZeroSumGame`): `IsPSNE`,
  `IsStrictPSNE`, `HasPSNE`, `pureMaximin` (`v*`, equal to the value of any PSNE:
  `IsPSNE.pureMaximin_eq`), `mixedUtility`, `IsMSNE`, `nashValue` (`max_p min_q u(p, q) = v^Nash`),
  the gaps `rowGap`/`colGap` (`Δʳ_x`, `Δᶜ_y`), `rowGapMin`/`colGapMin`, `mixGap` (`Δ^mix`) and
  `pairGap` (`Δ_{xy}`).
* **FTRL on the simplex** (`Online/Bandit/SimplexFTRL.lean`): the FTRL maximizer
  `argmax_{p ∈ simplex} ⟪p, θ⟫ + φ(p)` is defined as the gradient of the value function
  `θ ↦ sup_p ⟪p, θ⟫ + φ(p)` (`ftrlSimplex`; `ftrlSimplexParam` for a regularizer depending on a
  real parameter, through the partial gradient of the joint value function), which makes it
  measurable for free; `tsallisEntropy`; `simplexKernel` (`Online/Bandit/ImportanceWeighting.lean`)
  samples an arm from a point of the simplex. **Tsallis-INF** (`Online/Bandit/TsallisINF.lean`,
  `Bandits.tsallisINF α η`) follows
  Algorithm 1 with the reward estimator `1 - (1 - r_t) / p_t(x_t)`; rounds are `0`-indexed, so
  `η_t = 1 / (2 √t)` is `fun n ↦ 1 / (2 √(n + 1))` (`tsallisINFHalf`).
* **Normal-form games** are `u : Fin mx → Fin my → ℝ` (`m_x = mx`, `m_y = my`).
* **Bilinear games** (`Setting.lean`): the action sets are finite types with features
  `φ : Fin mx → ℝ^{d_x}`, `ψ : Fin my → ℝ^{d_y}` (the paper's finite subsets of `ℝ^{d_x}`, `ℝ^{d_y}`)
  and `u x y = ⟪φ x, A ψ y⟫` (`bilinearGame φ ψ A`); `IsBilinearGame φ ψ A` collects the
  assumptions (features of norm at most `1` spanning the spaces, `‖A‖₂ ≤ 1`). Theorem 5's
  "suitable choice of `p₀`" is any exploration distribution with variance ratio `c`
  (`HasVarianceRatio φ p₀ c`), and the constant of the theorem may depend on `c`.
* **Algorithms of the paper**: `maximinUCB δ` (Algorithm 2) and `maximinLinUCB φ ψ λ β`
  (Algorithm 4) are deterministic algorithms (`Algorithm.deterministic`) playing
  `argmax_x min_y U_t(x, y)`, with ties broken by LML's measurable `argmax`; the ridge regression
  of Maximin-LinUCB works in the flattened space `ℝ^{d_x × d_y}` (`pairFeature x y = vec(x yᵀ)`,
  `vecMatrix A = vec(A)`) with the library's linear bandit ridge layer (`RidgeState`,
  `ridgeUpdate`, `ridgeEstimate`, `ucbIndex`, `Online/Bandit/Linear/Ridge.lean`) and its radii `β_t` are `linRadius (d_x d_y) λ δ t` with the paper's
  `1`-indexed `t`. Tsallis-FTRL-SPM (`tsallisSPM φ α β₁ β̄ p₀ c`, Algorithm 3) keeps the state
  `(G_t, β_t)`; the mixed distribution `(1 - γ_t) p̂_t + γ_t p₀` is clamped to the simplex
  (`toSet`), which is harmless when `γ_t ∈ [0, 1]`.
* **`O(·)`, `Ω(·)`** hide a universal constant `∃ C > 0` quantified before the game; the bounds in
  `log T` are stated for `T ≥ 2`. Theorem 2's "small enough gaps, large enough `T`" is
  `∃ Δ₀ > 0, ∃ T₀, ∀ Δʳ Δᶜ ∈ (0, Δ₀), ∀ T ≥ T₀`; its adversary and reward noise are existentially
  quantified (the paper's construction uses an oblivious adversary and two-point rewards, whose
  law is `ProbabilityTheory.twoPoint`, `ForMathlib/Probability/Distributions/TwoPoint.lean`).
* **Theorem 6** (informal version of Theorem 12) is stated as the existence, for each horizon, of
  parameters `(λ, β)` of Maximin-LinUCB achieving the two bounds.
* **Lemmas 11 and 13** are stated for a run of *any* informed player (the proofs only use that the
  counts are predictable), with probability over the run.
* **Lemma 10**: "unique mixed-strategy Nash equilibrium" is formalized as "no PSNE and a unique
  MSNE"; `entryGap u` is `Δ_M`.
* Library additions also include `Matrix.measurable_inv`, `Matrix.measurable_mulVec`
  (`ForMathlib/Analysis/Matrix/MeasurableSpace.lean`, moved from the Lévy et al. setting).

* **Measurability.** The three algorithms are instances of the library constructors
  `Algorithm.index` (Maximin-UCB), `Algorithm.stateful` (Tsallis-INF, Tsallis-FTRL-SPM) and
  `Algorithm.statefulIndex` (Maximin-LinUCB) of `LeanMachineLearning/SequentialLearning/Algorithms/`; the
  measurability side conditions are discharged by `fun_prop` from the tagged lemmas of the
  building blocks (`ucbIndex`, `spmEstimate`, `spmUpdate`, `linUpdate`, `linIndex`, …).

## Results

| Result | Status | File / declaration |
| --- | --- | --- |
| Theorem 1 (`thm:tsallis`, Tsallis-INF) | formalized | `Theorem1.lean`, `exists_psmr_tsallisINFHalf_le` |
| Theorem 2 (`thm:uninformed-lb`, lower bound) | formalized | `Theorem2.lean`, `exists_forall_psmr_ge` |
| Remark 3 (`rem:sqrt-t-lb`) | skipped | remark (an `Ω(√T)` lower bound with non-strict PSNE), not a numbered statement of the extraction |
| Theorem 4 (`thm:pureucb`, Maximin-UCB) | formalized | `Theorem4.lean`, `exists_psmr_maximinUCB_le` |
| Theorem 5 (`thm:tsallis-bilinear`, Tsallis-FTRL-SPM) | formalized | `Theorem5.lean`, `forall_exists_psmr_tsallisSPMPaper_le` |
| Theorem 6 (`thm:purelinucb-informal`) | formalized | `Theorem6.lean`, `exists_forall_exists_psmr_maximinLinUCB_le` |
| Lemma 7 (`lem:sqrt-func`) | formalized | `Lemma7.lean`, `sqrt_mul_sub_mul_le` |
| Lemma 8 (`lem:self-bound`) | formalized | `Lemma8.lean`, `le_add_sqrt_add_of_le_sqrt_add` |
| Lemma 9 (`lem:kl-bernoulli`) | formalized | `Lemma9.lean`, `klDiv_twoPoint_le` |
| Lemma 10 (`lem:delta-comparison`) | formalized | `Lemma10.lean`, `sq_entryGap_div_four_le_mixGap` |
| Lemma 11 (`lem:ucb-ucb`) | formalized | `Lemma11.lean`, `probReal_forall_abs_sub_div_le_ge` |
| Theorem 12 (`thm:purelinucb`, Maximin-LinUCB) | formalized | `Theorem12.lean`, `exists_psmr_maximinLinUCB_le` |
| Lemma 13 (`lem:conf-ellipsoid`) | formalized | `Lemma13.lean`, `probReal_forall_sqrt_mahalanobisSq_le_ge` |
