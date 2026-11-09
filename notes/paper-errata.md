# Errata of Adversarial Learning in Games with Bandit Feedback: Logarithmic Pure-Strategy Maximin Regret

Errors found in the paper while formalizing it, with their corrections. Each entry gives where the
error is (the revision of the paper, the result, the page or equation), the error, the correction,
the declarations that state the corrected form, the kind of error and when it was found. Entries
are numbered `E1`, `E2`, … and never renumbered.

## E1. Theorems 1 and 5: the strict-PSNE bounds fail when the adversary has a single action

- **Where:** arXiv:2602.06348v1, Theorem 1 (Section 3.1), second bullet, and Theorem 5
  (Section 5.1), second bullet.
- **Error:** the bounds `O((1/Δᶜ_min) ∑_{x ≠ x*} log T / Δʳ_x)` and
  `O(d_x log m_x log T / (Δʳ_min Δᶜ_min) + m_x log m_x)` divide by
  `Δᶜ_min = min_{y ≠ y*} Δᶜ_y`, a minimum over no action when `m_y = 1`. With the convention
  `min ∅ = +∞` the first bound claims `PSMR_T = 0` for Tsallis-INF on a stochastic bandit with at
  least two arms and a unique best arm, which is false, since Tsallis-INF plays every arm with
  positive probability; with any other convention the statement is undefined.
- **Correction:** the proofs give `C (1 + 1/Δᶜ_min) ∑_{x ≠ x*} (1 + log T) / Δʳ_x` (Theorem 1) and
  `C (d_x log m_x (1 + log T) (1 + 1/Δᶜ_min) / Δʳ_min + m_x log² m_x)` (Theorem 5, with the
  additive term of E3), with `1/Δᶜ_min` read as `0` when `m_y = 1`. They imply the paper's forms
  when `m_y ≥ 2` and `T ≥ 2`, since then `Δᶜ_min ≤ 2`.
- **Lean:** `Ito2026Adversarial.exists_psmr_tsallisINFHalf_le` and
  `Ito2026Adversarial.forall_exists_psmr_tsallisSPMPaper_le` state the corrected forms.
- **Kind:** false statement in a degenerate case (missing hypothesis `m_y ≥ 2`).
- **Found:** phase-1 statement check, 2026-10-08.

## E2. Theorems 1 and 5: a game without PSNE need not have `v^Nash > v*`

- **Where:** arXiv:2602.06348v1, Section 3.1, the paragraph before Theorem 1 ("if PSNEs do not
  exist, we know that the Nash value `v^Nash` is strictly higher than the pure-strategy maximin
  value `v*`"), and the third bullets of Theorems 1 and 5.
- **Error:** the claim is false. The `3 × 2` game with rows `(0, 0)`, `(1, -1)`, `(-1, 1)` has no
  PSNE, and `v* = v^Nash = 0`: the first row guarantees `0`, and every mixed row strategy `p` gets
  `-|p₂ - p₃| ≤ 0` against the better column. The no-PSNE bounds `O(m_x / Δ^mix)` and
  `O(d_x log m_x / Δ^mix + m_x log m_x)` are then meaningless.
- **Correction:** the proofs only use `Δ^mix = v^Nash - v* > 0`, which replaces "no PSNE" as the
  hypothesis of the third bullets. For `2 × 2` games, no PSNE does imply `Δ^mix > 0` (Lemma 10).
- **Lean:** `Ito2026Adversarial.exists_psmr_tsallisINFHalf_le` and
  `Ito2026Adversarial.forall_exists_psmr_tsallisSPMPaper_le` assume `0 < mixGap u`.
- **Kind:** false claim (wrong hypothesis).
- **Found:** phase-1 statement check, 2026-10-08.

## E3. Theorem 5: the additive term is `m_x log² m_x`, not `m_x log m_x`

- **Where:** arXiv:2602.06348v1, Theorem 5 (Section 5.1), all three bounds, and its proof in
  Appendix E.
- **Error:** for the parameters of the theorem (`α = 1 - 1/(4 log m_x)`, `β₁ = 8 c d_x/(1-α)`,
  `β̄ = 32 d_x/((1-α)² β₁) = 16 log m_x / c`), the penalty term `β̄ h₀` of the cited analysis
  (Ito, Tsuchiya, Honda 2024, Eq. (24)), with `h₀ = -ψ̄(q₁) ≤ m_x^α/(1-α)`, is of order
  `64 m_x^α log² m_x / c`, which the paper evaluates as `m_x log m_x`. The order is attained:
  take `d_x = 1`, `φ(x*) = 1` and `φ = -1` on the other `m_x - 1` actions, `A = 1`, `m_y = 1`,
  deterministic rewards, `p₀` uniform and `c = 1`. Then `S(p) = 1`, `g_t = φ`, the run is
  deterministic, and the barrier `β̄ φ_{1-α}` keeps each bad action at
  `p̂_t(x) ≥ e⁻¹ β̄ / (4t + O(log m_x))` while `β_t = O(t)`, so `PSMR_{m_x²}` is of order
  `m_x log² m_x`, while the stated bounds are `O(m_x log m_x)` there. An exact simulation of the
  algorithm gives the ratio of `PSMR_T` to `√(T log m_x) + m_x log m_x` at `T = m_x²` as `19` for
  `m_x = 100` and `37` for `m_x = 1000`, growing like `log m_x`.
- **Correction:** all three bounds of Theorem 5 hold with the additive term `m_x log² m_x`. No other
  choice of the parameters helps, since the cited analysis needs `β̄ ≥ 32 d/((1-α)² β₁)`.
- **Lean:** `Ito2026Adversarial.forall_exists_psmr_tsallisSPMPaper_le` states the bounds with
  `m_x log² m_x`.
- **Kind:** wrong order of a term (false statement).
- **Found:** phase 2, 2026-10-09.

## E4. Theorem 4: the instance-dependent bound misses the term `m_x m_y`

- **Where:** arXiv:2602.06348v1, Theorem 4 (Section 4), first bound, and the last paragraph of
  its proof in Appendix D.
- **Error:** the proof bounds the contribution of the failure event of the confidence bounds
  (probability at most `m_x m_y δ = m_x m_y / T`) by `m_x m_y`, and claims that this term is
  absorbed by `O(∑_{Δ_{xy} > 0} (Δ_{xy} + log T / Δ_{xy}))`. It is not when few action pairs have a
  positive gap.
- **Correction:** the instance-dependent bound is
  `C (∑_{Δ_{xy} > 0} (Δ_{xy} + log T / Δ_{xy}) + m_x m_y)`. The worst-case bound
  `C √(m_x m_y T log T)` holds as stated: the additive term is at most `C √(m_x m_y T log T)` when
  `m_x m_y ≤ T`, and `PSMR_T ≤ 2T` otherwise.
- **Lean:** `Ito2026Adversarial.exists_psmr_maximinUCB_le` states the bound with the additive
  `m_x m_y`.
- **Kind:** false statement (a term wrongly absorbed).
- **Found:** phase-1 statement check, 2026-10-08.

## E5. Theorem 4, proof: the confidence radius is only half the gap

- **Where:** arXiv:2602.06348v1, proof of Theorem 4 (Appendix D), the display after "At the last
  iteration this action pair is played".
- **Error:** the proof claims that, at the last round in which a pair `(x, y)` with
  `Δ_{xy} > 0` is played, the confidence radius `√((4 log(1/δ) + 2 log(1 + N))/N)` is at least
  `Δ_{xy}`. The confidence bounds only give `v* ≤ U_t(x, y) ≤ u(x, y) + 2 rad_t`, that is, twice the
  radius at least `Δ_{xy}`: the empirical mean is within the radius of `u(x, y)`, not below it.
- **Correction:** the count bound becomes `N_T(x, y) Δ_{xy}² ≤ Δ_{xy}² + 24 log T` instead of the
  paper's constant `6`. The statement, with a universal constant, is unaffected.
- **Lean:** `Ito2026Adversarial.pairCount_mul_sq_le_of_mem_ucbGoodEvent`.
- **Kind:** gap in the proof (wrong constant).
- **Found:** phase 2, 2026-10-09.

## E6. Theorem 4, proof: a missing factor `T` in the last display

- **Where:** arXiv:2602.06348v1, proof of Theorem 4 (Appendix D), the last display of the
  worst-case bound.
- **Error:** with `Δ = √(6 m_x m_y log T / T)`, `Δ T + m_x m_y (2 + 6 log T / Δ)` equals
  `2 m_x m_y + 2 √(6 m_x m_y T log T)`, not `2 m_x m_y + 2 √(6 m_x m_y log T)`.
- **Correction:** read `2 m_x m_y + 2 √(6 m_x m_y T log T)`, which is what the stated bound uses.
- **Lean:** `Ito2026Adversarial.exists_psmr_maximinUCB_le` (worst-case bound).
- **Kind:** typo.
- **Found:** phase-1 statement check, 2026-10-08.

## E7. Lemma 10: the lemma is false for a unique pure equilibrium

- **Where:** arXiv:2602.06348v1, Lemma 10 (Appendix B), hypothesis "Assume it has a unique
  mixed-strategy Nash equilibrium".
- **Error:** a `2 × 2` game whose unique Nash equilibrium is pure has a unique mixed-strategy Nash
  equilibrium and `Δ^mix = 0`, while its minimum entry gap may be positive. For the rows `(0, 1)`,
  `(-1, -1/2)` (the example after Theorem 4, with `ε = 1/2`), the first row strictly dominates, the
  unique equilibrium is the pure one `(1, 1)`, `Δ^mix = 0` and `Δ_M = 1/2`, so
  `Δ^mix ≥ Δ_M²/4` fails. The proof starts from "Since `A` does not have pure-strategy Nash
  equilibriums", which the hypothesis does not give.
- **Correction:** assume that the game has no PSNE (a `2 × 2` game without PSNE has a unique
  mixed-strategy Nash equilibrium, so uniqueness need not be assumed).
- **Lean:** `Ito2026Adversarial.sq_entryGap_div_four_le_mixGap` assumes `¬ HasPSNE u`.
- **Kind:** wrong hypothesis (false statement).
- **Found:** phase-1 statement check, 2026-10-08.

## E8. Theorem 2, proof: an inverted inequality and a horizon that is not an integer

- **Where:** arXiv:2602.06348v1, proof of Theorem 2 (Appendix C), the two cases of the
  construction of `(K, ε, T')`.
- **Error:** in the second case, `ε = min{1, 1/(13 Δᶜ √T)} ≤ Δʳ` should read `≥ Δʳ`, which is what
  `K ≤ Δʳ/ε ≤ 1` uses. In the first case, `T' = (13 Δʳ Δᶜ)^{-2}` need not be an integer.
- **Correction:** `ε ≥ Δʳ` in the second case, and `T' = ⌊(13 Δʳ Δᶜ)^{-2}⌋` in the first, which only
  changes the constant of the lower bound.
- **Lean:** `Ito2026Adversarial.exists_forall_psmr_ge` (the statement is unaffected).
- **Kind:** typo.
- **Found:** phase-1 statement check, 2026-10-08.
