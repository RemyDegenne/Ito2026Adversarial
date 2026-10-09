# Blueprint outline — Ito, Luo, Maiti, Tsuchiya, Wu, *Adversarial Learning in Games with Bandit Feedback: Logarithmic Pure-Strategy Maximin Regret* (COLT 2026)

arXiv 2602.06348, source in `source/` (`main.tex`, sections in `sec/`, appendices in `sec/app/`).
Library `Ito2026Adversarial`, paper directory `Ito2026Adversarial/ILMTW2026/` (namespace
`Ito2026Adversarial`), LML branch `rename`. The statements start from the statement-only
formalization in `LMLPapers` (COLT2026/Ito2026Adversarial, its README is
`notes/lmlpapers-README.md`), checked against the paper and corrected where they were false.

## 1. Results of the paper

`jmlr` class: one counter for theorems, lemmas and remarks, not reset in the appendix; algorithms
have their own counter.

| Result | Label | Lean (`Ito2026Adversarial.`) | Status |
|---|---|---|---|
| Section 3 (game, PSNE, values, PSMR, feedback models) | `def:game`, `def:psne`, `def:values`, `def:regrets`, `def:repeated_game` | library `Learning.ZeroSumGame`, `Learning.RepeatedGame` | definitions |
| Algorithm 1 (Tsallis-INF) | `def:tsallis_inf` | `tsallisINFHalf`, library `Bandits.tsallisINF` | definition |
| Theorem 1 (Tsallis-INF, uninformed) | `thm:tsallis` | `exists_psmr_tsallisINFHalf_le` | headline |
| Theorem 2 (lower bound, uninformed) | `thm:uninformed_lb` | `exists_forall_psmr_ge` | headline |
| Remark 3 (`Ω(√T)` with a non-strict PSNE) | — | — | remark, not formalized |
| Algorithm 2 (Maximin-UCB) | `def:maximin_ucb` | `maximinUCB`, `ucbIndex` | definition |
| Theorem 4 (Maximin-UCB, informed) | `thm:pureucb` | `exists_psmr_maximinUCB_le` | headline |
| Algorithm 3 (Tsallis-FTRL-SPM) | `def:tsallis_spm` | `tsallisSPM`, `tsallisSPMPaper` | definition |
| Theorem 5 (Tsallis-FTRL-SPM, bilinear) | `thm:tsallis_bilinear` | `forall_exists_psmr_tsallisSPMPaper_le` | headline |
| Theorem 6 (Maximin-LinUCB, informal) | `thm:purelinucb_informal` | `exists_forall_exists_psmr_maximinLinUCB_le` | headline |
| Lemma 7 (`√(ax) - bx ≤ a / (4b)`) | `lem:sqrt_func` | `sqrt_mul_sub_mul_le` | headline |
| Lemma 8 (self-bounding) | `lem:self_bound` | `le_add_sqrt_add_of_le_sqrt_add` | headline |
| Lemma 9 (KL of two-point laws) | `lem:kl_bernoulli` | `klDiv_twoPoint_le` | headline |
| Lemma 10 (`Δ^mix ≥ Δ_M² / 4`) | `lem:delta_comparison` | `sq_entryGap_div_four_le_mixGap` | headline |
| Lemma 11 (anytime confidence bounds) | `lem:ucb_ucb` | `probReal_forall_abs_sub_div_le_ge` | headline |
| Algorithm 4 (Maximin-LinUCB) | `def:maximin_linucb` | `maximinLinUCB`, `linRadius`, `linState` | definition |
| Theorem 12 (Maximin-LinUCB, formal) | `thm:purelinucb` | `exists_psmr_maximinLinUCB_le` | headline |
| Lemma 13 (confidence ellipsoid) | `lem:conf_ellipsoid` | `probReal_forall_sqrt_mahalanobisSq_le_ge` | headline |

## 2. Modelling decisions

As in `LMLPapers` (see `notes/lmlpapers-README.md`, "Formalization choices"):

* **Repeated games** (`LeanMachineLearning/Game/RepeatedGame.lean`): a round of the learner is
  `Round Unit 𝒳 (𝒴 × ℝ)` (action `x_t`, feedback `(y_t, r_t)`); informed learners are
  `Player 𝒳 𝒴 = Algorithm Unit 𝒳 (𝒴 × ℝ)`, uninformed ones `Algorithm Unit 𝒳 ℝ` lifted by
  `Player.ofUninformed` (they ignore `y_t`). The adaptive adversary is a `Player 𝒴 𝒳` acting on the
  swapped history (it sees the past actions and rewards of the learner, not `x_t`). The reward is
  drawn from a history-dependent reward kernel `R` with conditional mean `u x_t y_t`
  (`RewardKernel.HasMean`) and values in `[-1, 1]` (`RewardKernel.RewardsIn`). "Against any
  adaptive adversary" quantifies over all `opp` and all such `R`, and over all runs.
* **Normal-form games** are `u : Fin mx → Fin my → ℝ`; **bilinear games** are finite action types
  with features `φ`, `ψ` and `u x y = ⟪φ x, A ψ y⟫`, under `IsBilinearGame`.
* **`O(·)`** is a universal constant `∃ C > 0` quantified before the game (for Theorem 5 after
  the variance ratio `c`).
* **Gaps** (`Learning.ZeroSumGame`): `rowGap`, `colGap`, `rowGapMin`, `colGapMin` (infima over the
  other actions: `0` when there is none), `pairGap`, `mixGap = v^Nash - v*` (`nashValue` is
  `sup_p inf_q u(p, q)`, no minimax theorem needed).

## 3. Corrections to the statements

Checked against the paper and the LMLPapers statements; the statements in this repository are
the corrected ones (frozen by the comparator challenges).

* **Theorem 1, strict-PSNE bound.** The paper's `O((1/Δᶜ_min) ∑_{x ≠ x*} log T / Δʳ_x)` is false
  in Lean for `m_y = 1`: `Δᶜ_min` is an infimum over no action, `0`, and `C / 0 = 0`, so the bound
  would claim `PSMR_T ≤ 0` for a stochastic bandit. Stated as the form the proof gives,
  `C (1 + 1/Δᶜ_min) ∑_{x ≠ x*} (1 + log T) / Δʳ_x` (no `T ≥ 2` needed); it implies the paper's for
  `m_y ≥ 2`, `T ≥ 2` since `Δᶜ_min ≤ 2`.
* **Theorems 1 and 5, no-PSNE bound.** The paper claims that a game without PSNE has
  `Δ^mix = v^Nash - v* > 0`. This is false: the `3 × 2` game with rows `(0, 0)`, `(1, -1)`,
  `(-1, 1)` has no PSNE and `v* = v^Nash = 0` (row 1 guarantees `0`, and every mixed row strategy
  gets `-|p_2 - p_3| ≤ 0` against the better column). With `Δ^mix = 0` the Lean bound `C m_x / 0 = 0`
  would be false. The proofs only use `Δ^mix > 0`, which is the hypothesis now (for `2 × 2` games
  no PSNE does imply `Δ^mix > 0`).
* **Theorem 5, strict-PSNE bound**: same issue as Theorem 1 for `m_y = 1`; stated as
  `C (d_x log m_x (1 + log T) (1 + 1/Δᶜ_min) / Δʳ_min + m_x log² m_x)`, the form of the proof.
* **Theorem 5, additive term (found in phase 2).** The paper's `m_x log m_x` is false for its
  parameters (`α = 1 - 1/(4 log m_x)`, `β₁ = 8 c d_x/(1-α)`, `β̄ = 32 d_x/((1-α)² β₁) = 16 log m_x / c`).
  The additive term of ITH24 (Eq. (24)/(26)) contains `β̄ h₀` with `h₀ = -ψ̄(q₁) ≤ m_x^α/(1-α)`,
  i.e. `64 m_x^α log² m_x / c`, which the paper evaluates as `m_x log m_x`. Counterexample:
  `d_x = 1`, `φ(x*) = 1`, `φ = -1` on the other `m_x - 1` actions, `A = 1`, `m_y = 1`, rewards
  deterministic, `p₀` uniform, `c = 1`. Then `S(p) = 1`, `g_t = φ`, the run is deterministic, the
  barrier `β̄ φ_{1-α}` keeps each bad action at `p̂_t(x) ≥ e⁻¹ β̄ / (4t + O(log m_x))` while
  `β_t = O(t)` and `γ_t ≤ 1/2`, so `PSMR_{m_x²} = Θ(m_x log² m_x)`, while the bound is
  `O(m_x log m_x)` there (the strict-PSNE bound too: `Δʳ_min = 2`, `Δᶜ_min = 0`). Exact simulation
  of the Lean algorithm: ratio PSMR / (`√(T log m_x) + m_x log m_x`) at `T = m_x²` is 19
  (`m_x = 100`), 37 (`m_x = 1000`), growing like `log m_x`. All three bounds of Theorem 5 are
  stated with `m_x log² m_x` (no change of parameters helps: ITH24 need `β̄ ≥ 32 d/((1-α)² β₁)`).
* **Theorem 5, variance ratio.** `HasVarianceRatio φ p₀ c` now requires `S(p₀)` positive
  definite; otherwise the inequality `⟪φ x, S(p₀)⁻¹ φ x⟫ ≤ c d_x` holds trivially for a singular
  `S(p₀)` (Lean's inverse being `0`), and the exploration gives no control of the variance.
* **Theorem 4, instance-dependent bound.** The proof bounds the contribution of the failure event
  of the confidence bounds (probability `≤ m_x m_y δ = m_x m_y / T`) by `2 m_x m_y`, and claims it is
  absorbed by `O(∑_{Δ_{xy} > 0} (Δ_{xy} + log T / Δ_{xy}))`; this is not the case when few pairs
  have a positive gap. Stated with the additive term: `C (∑_{Δ_{xy} > 0} (Δ_{xy} + log T / Δ_{xy})
  + m_x m_y)`. (The worst-case bound `C √(m_x m_y T log T)` holds as stated: the term `3 m_x m_y` is
  at most `C √(m_x m_y T log T)` when `m_x m_y ≤ T`, and `PSMR_T ≤ 2T` otherwise.)
* **Lemma 10.** The paper assumes a unique MSNE; the lemma is false for a unique *pure* equilibrium
  (`Δ^mix = 0`), and the proof uses the absence of PSNE. Stated with "no PSNE" only (a `2 × 2` game
  without PSNE has a unique MSNE).
* **Typos in the proofs (statements unaffected).** Theorem 2: "`ε = min{1, 1/(13 Δᶜ √T)} ≤ Δʳ`"
  should be `≥ Δʳ` (which is what `K ≤ Δʳ/ε ≤ 1` uses), and `T' = (13 Δʳ Δᶜ)^{-2}` must be rounded
  down to an integer (only the constant changes). Theorem 4: the last display should read
  `2 m_x m_y + 2 √(6 m_x m_y T log T)`.
* **Theorem 4, proof (found in phase 2).** At the last round a pair with `Δ_{xy} > 0` is played,
  the paper claims the confidence radius is at least `Δ_{xy}`; the confidence bounds only give
  twice the radius at least `Δ_{xy}` (the empirical mean is within the radius of `u(x, y)`, not
  below it), so the count bound is `N_T Δ_{xy}² ≤ Δ_{xy}² + 24 log T` (constant `24` instead of `6`);
  the statement, with a universal constant, is unaffected.

* **Lemmas 11 and 13 (library review, 2026-10-09).** The paper's hypothesis `u ∈ [-1, 1]` of
  Lemma 11 follows from the others (the utilities are the means of rewards in `[-1, 1]`); it is
  dropped, as are the instances `NeZero m_x`, `NeZero m_y` that neither proof uses. Both
  statements are strictly stronger than in phase 1.

## 4. Proof routes

### Elementary lemmas (Part I, `games.tex`)

* **Lemma 7**: `√(ax) - bx ≤ a/(4b)` is `0 ≤ (√(bx) - √a/(2√b))²`; equality at `x = a/(4b²)`.
* **Lemma 8**: as in the paper (if `x > c`, square and solve the quadratic inequality).
* **Lemma 10**: for a `2 × 2` game without PSNE, up to swapping rows and columns the entries are
  cyclically ordered (`a > b`, `d > b`, `d > c`, `a > c`); the maximin mixed strategy `p*` and the
  minimax `q*` of the paper give `nashValue = (ad - bc)/(a - b - c + d)` (`p*` gives `≥` through
  `inf_q`, `q*` gives `≤` for every `p`), `v* = max(b, c)`, and
  `Δ^mix = (a - b)(d - b)/(a - b - c + d) ≥ Δ_M²/4`. A general symmetry lemma (row/column swaps
  preserve `nashValue`, `pureMaximin`, `entryGap`, PSNE) handles the cases.

### Uninformed learning (Part I, `tsallis_inf.tex`; Part II, `prereq_ftrl.tex`)

* **Relations between regrets**: `NR_T = PSMR_T + Δ^mix T`; `NR_T ≤ ER_T` (a maximin mixed
  strategy `p*`, which exists by compactness, guarantees `v^Nash` against every `y`, so
  `E[∑ v^Nash - u(x_t, y_t)] ≤ ∑_x p*_x ER_T(x)`); for a strict PSNE `(x*, y*)`,
  `ER_T(x*) - PSMR_T = E[∑ 𝟙{y_t ≠ y*} Δᶜ_{y_t}] ≥ C Δᶜ_min` and
  `E[∑ ⟨Δʳ, p_t⟩] - ER_T(x*) ≤ 4 C`, `C = E[#{t : y_t ≠ y*}]` (the law of `x_t` given the past is
  `p_t`, independent of `y_t`).
* **Tsallis-INF regret bounds** (prerequisite, the bulk of the work): for `α = 1/2`,
  `η_t = 1/(2√t)`, rewards in `[-1, 1]` and any adaptive adversary, (a) `ER_T ≤ 8 √(m T) + 2`
  (Zimmert–Seldin 2021, Theorem 1, rescaled) and (b) the self-bounding form
  `ER_T(x*) ≤ C₀ E[∑_t t^{-1/2} ∑_{x ≠ x*} √p_{t,x}]` (Ito et al. 2025, Theorem 1; any universal
  `C₀`). Route: FTRL on the simplex with time-varying learning rates through the value function
  `ftrlValue` (Fenchel conjugate, `SimplexFTRL.lean`): regret against `e_x` = penalty
  `∑_t (1/η_{t+1} - 1/η_t)(φ(e_x) - φ(p_{t+1}))` + stability
  `∑_t (Φ_t(G_{t+1}) - Φ_t(G_t) - ⟨p_t, g_t⟩)`; the stability of the Tsallis-1/2 regularizer for
  the reduced-variance estimator `g_t x = 1 - (1 - r_t) 𝟙{x_t = x}/p_t x` is bounded by
  `η_t ∑_x p_{t,x}^{3/2} E[(g_t x - 1)²] ≤ 4 η_t ∑_x √p_{t,x}`, and excluding the best arm from the
  sum (shift of the estimates by a constant, which does not change `p_t`) gives (b); the penalty is
  `∑_x √p_{t,x} - 1 ≤ ∑_{x ≠ x*} √p_{t,x}` up to constants. Conditional expectations: the estimates
  are unbiased given the past and `y_t` (the reward has conditional mean `u x_t y_t` and `y_t` is
  independent of `x_t` given the past).
* **Theorem 1**: (a) gives the worst-case bound (`8√(mT) + 2 ≤ 10 √(mT)` for `T ≥ 1`); with
  `Δ^mix > 0`, `PSMR_T ≤ ER_T - Δ^mix T ≤ 2 + 8√(mT) - Δ^mix T ≤ 2 + 16 m/Δ^mix` (Lemma 7) and
  `2 ≤ 4m/Δ^mix`; with a strict PSNE, (b), Cauchy–Schwarz, the relations above, Lemma 8 and Lemma 7
  give `PSMR_T ≤ C (1 + 1/Δᶜ_min) ∑_{x ≠ x*} H_T/Δʳ_x`, `H_T ≤ 1 + log T`.
* **Theorem 2**: the two games `A = (0, Δᶜ; -Δʳ, K - Δʳ)`, `B` (rows swapped), two-point rewards
  (`twoPoint`), the oblivious adversary playing `(1 - ε, ε)` up to `T'` and `y*` after. The
  learner's observations `(x_t, r_t)` form a run of the uninformed algorithm against the
  non-stationary bandit `t ↦ (x ↦ twoPoint((A q_t)_x))` (marginalize `y_t`, independent of the
  past; two-point laws are linear in the mean), so the divergence decomposition for non-stationary
  bandits (in LMLPapers, `SequentialLearning/DivergenceDecomposition.lean`) and Lemma 9 bound the
  KL between the laws under `A` and `B` of the first `T'` rounds by `δ² T' ≤ 1`; Bretagnolle–Huber
  (LMLPapers) at each round, summed, and the two cases of the paper (`T' = ⌊(13 Δʳ Δᶜ)^{-2}⌋` or
  `T' = T`), with `Δ₀ = 1/13`, `T₀ = 169`, `c = 1/2028` (up to the rounding of `T'`).
* **Lemma 9**: the paper's derivative argument (`f_a(b) ≤ 0` with `f_a(a) = 0`, sign of `f_a'`),
  or monotonicity on `[a, b]` by the mean value theorem; `klDiv` of two-point laws computed from
  the Bernoulli KL in `ForMathlib/InformationTheory/KullbackLeibler/Bernoulli.lean`.

### Informed learning (Part I, `maximin_ucb.tex`, `bilinear.tex`; Part II, `prereq_concentration.tex`)

* **Lemma 11**: the paper's method of mixtures: for each `λ`, `Z_t(λ) = exp(λ M_t - λ² N_t/2)` is a
  supermartingale (the noise of a round in which `(x, y)` is played is conditionally
  `1`-sub-Gaussian by Hoeffding's lemma, rewards in `[-1, 1]`); the Gaussian mixture
  `Z̄_t = (1 + N_t)^{-1/2} exp(M_t²/(2(1 + N_t)))` is a nonnegative supermartingale with `Z̄_0 = 1`;
  Ville's inequality (LMLPapers, `ForMathlib/Probability/Martingale/Ville.lean`; mixtures of
  supermartingales: the Wang2026Almost material in LMLPapers). The counts are predictable for any
  informed player.
* **Theorem 4**: as in the paper with the additive `m_x m_y` (failure event, `δ = 1/T`); on the
  good event `v* ≤ U_t(x_t, y_t)` (`x_t` maximizes `min_y U_t`), so a pair with `Δ_{xy} > 0` is played
  at most `1 + 6 log T/Δ_{xy}²` times; the worst-case bound with the threshold
  `Δ = √(6 m_x m_y log T/T)`.
* **Lemma 13**: the vector self-normalized bound of Abbasi-Yadkori, Pál, Szepesvári (2011,
  Theorem 1) in dimension `d = d_x d_y`: Gaussian mixture `∫ exp(⟨θ, S_t⟩ - ‖θ‖²_{V̄_t}/2) dN(0, λ⁻¹I)`
  `= (det(λI)/det V_t)^{1/2} exp(‖S_t‖²_{V_t⁻¹}/2)`, Ville, then the ridge identity
  `vec(A) - V_t⁻¹ b_t = -V_t⁻¹(S_t - λ vec(A))` and `‖vec(A)‖ = ‖A‖_F ≤ √d` (`‖A‖₂ ≤ 1`, rank
  `≤ min(d_x, d_y)`), `log det V_t ≤ d log(λ + t/d)` (AM–GM on the eigenvalues, features of norm
  `≤ 1`).
* **Theorem 12**: as in the paper: on the event of Lemma 13 (radius `β_{t-1} ≤ β_t` for the state
  `V_{t-1}`), `v* ≤ U_t(x_t, y_t)` and `U_t - u ≤ 2 β_t ‖a_t‖_{V_{t-1}⁻¹}`; the elliptical potential
  `∑_t min(1, ‖a_t‖²_{V_{t-1}⁻¹}) ≤ 2 log(det V_T/det V_0)` (matrix determinant lemma
  `det(V + a aᵀ) = det V (1 + ‖a‖²_{V⁻¹})`, Mathlib's `Matrix.det_add_col_mul_row`; with `λ = 1` and
  `‖a_t‖ ≤ 1` the minimum is not needed); worst-case by Cauchy–Schwarz, instance-dependent through
  `v* - u ≤ (v* - u)²/Δ^lin` off `(0, Δ^lin)`; failure event `δ = 1/T` contributes `≤ 2`.
* **Theorem 6** from Theorem 12 (`λ = 1`, the radii of Theorem 12).
* **Theorem 5**: the relations of the uninformed case for bilinear games
  (`ER_T(x*) ≥ E[∑ ⟨p_t, Δʳ⟩] - 2C`), and the regret bound of Tsallis-FTRL-SPM of Ito, Tsuchiya,
  Honda (2024, Eq. (26) with the parameters of their Section 4.3): `ER_T(x*) ≤ O(E[min{√(d m^{1-α} T
  /(α(1-α))), √(d m^{1-α}/(α(1-α) Δʳ_min) ∑_t ⟨p_t, Δʳ⟩ log T)}] + m log m)`. This cited analysis
  (FTRL with the hybrid Tsallis regularizer, stability-penalty matching learning rates, exploration
  `p₀` with variance ratio `c`, linear estimates `r_t ⟨x_t, S(p_t)⁻¹ x⟩`) is the largest
  prerequisite of the project, a package of its own in phase 2.

## 5. Blueprint chapters

Part I: `setting.tex` (Section 3, Algorithms 1–4), `games.tex` (Lemmas 7, 8, 10 and the relations
between regrets), `tsallis_inf.tex` (Theorem 1), `lower_bound.tex` (Theorem 2, Lemma 9),
`maximin_ucb.tex` (Lemma 11, Theorem 4), `bilinear.tex` (Theorems 5, 6, 12, Lemma 13).
Part II: `prereq_ftrl.tex` (FTRL on the simplex, Tsallis-INF and Tsallis-FTRL-SPM regret bounds),
`prereq_concentration.tex` (Hoeffding's lemma, method of mixtures, Ville, self-normalized bounds,
elliptical potential), `prereq_information.tex` (Bretagnolle–Huber, divergence decomposition,
runs of uninformed learners against oblivious adversaries).

## 6. Comparator and auxiliary proofs (implementation note)

Lean turns the proofs inside a definition into auxiliary theorems `foo._proof_n`, and within a
module reuses an earlier auxiliary theorem for a later proof of the same statement. A comparator
challenge holds the definitions of many modules in one file, so it would reuse auxiliary theorems
that the project made apart, and challenge-gen refuses such a file. Here the only statement shared
across modules was `(1 + 1).AtLeastTwo`, made by the numeral `2` in a definition: the real `2` of
`2 * x` and the exponent of `WithLp.toLp 2`. The definitions in the closure of the headline
statements therefore write `((2 : ℕ) : ℝ)` for a real `2` and `WithLp.toLp _` (exponent inferred
from the type `EuclideanSpace`, whose `2` comes with Mathlib's own auxiliary theorem) or
`EuclideanSpace.equiv` for vectors: `twoPoint`, `ridgeEstimate`, `TsallisINF.estimate`,
`OnlineLearner.banditPolicy`, `uniformVec`, `pinvMahalanobisSq`, a private definition of
`Pinsker.lean`, and `tsallisINFHalf`, `ucbIndex`, `bilinearUtility` (as a dot product),
`pairFeature`, `vecMatrix`, `spmEstimate`, `linRadius` of `Setting.lean`. The definitions are
unchanged in meaning; these forms are to be kept (or the check redone with
`scripts/make-challenges.py`) when the library is ported back to LMLPapers.
