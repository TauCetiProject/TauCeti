/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Probability.HasLaw
public import TauCeti.Analysis.Matrix.SampleSecondMoment
public import TauCeti.Probability.Moments.CenteredTruncation
import TauCeti.Analysis.Matrix.SampleCovariance.OperatorNorm
import TauCeti.Probability.RandomMatrix.ExtremeEigenvalues
import TauCeti.Probability.RandomMatrix.SampleCovariance.MarchenkoPastur
import TauCeti.Probability.RandomMatrix.SampleCovariance.Trace.Integrability
import TauCeti.Probability.RandomMatrix.SampleCovariance.Truncation
import TauCeti.Probability.RandomMatrix.SpectralMoment.Extremes

/-!
# Reduction of the sample covariance upper edge to a growing trace bound

Let `Xₙ` be the top-left `p(n) × n` corner of an array of independent complex entries with a
common centred law of unit second absolute moment and finite fourth moment, where
`p(n) / n → y > 0`. The largest eigenvalue of the sample covariance `Sₙ = XₙXₙᴴ/n` converges
almost surely to the upper edge `(1 + √y)²` of the Marchenko–Pastur law `MP_y`, provided that the
matrices `Tₙ` of centered truncations of the entries at `n^a`, with `a > 1/4`, satisfy a growing
trace bound: for each threshold `r > (1 + √y)²`, the expected real trace of the `2 kₙ`-th power of
the sample covariance of `Tₙ` is eventually at most `C (n + 1)^d t^(2 kₙ)` with `0 < t < r`, where
the orders satisfy `kₙ ≥ B log (n + 1)` eventually and `2 B log (r / t) > d + 1`.

The lower half, that the largest eigenvalue eventually exceeds every `c < (1 + √y)²`, is a
consequence of the almost-sure Marchenko–Pastur law `TauCeti.Probability.marchenkoPastur_ae`.
For the upper half, the trace bound and Borel–Cantelli give operator-norm bounds for the sample
covariance of the truncated corners. These transfer to `Xₙ / √n`, since the corners and their
truncations differ by `o(√n)` in operator norm, and the largest eigenvalue of `Sₙ` is
`‖Xₙ‖² / n`.

## References

* Y. Q. Yin, Z. D. Bai, P. R. Krishnaiah, *On the limit of the largest eigenvalue of the large
  dimensional sample covariance matrix*, Probab. Theory Related Fields 78 (1988).
* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), Theorem 2.15.
-/

public section

open Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology NNReal Matrix.Norms.L2Operator

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : ℕ → ℕ} [∀ n, NeZero (p n)]
  {y : ℝ≥0}

/-- Let the entries of an array indexed by `ℕ × ℕ` be independent with a common centred law `ν`
of unit second absolute moment and finite fourth moment, let `p(n) ≥ 1` with `p(n) / n → y > 0`,
and let `Xₙ` be the top-left `p(n) × n` corner. Then the largest eigenvalue of the sample
covariance `XₙXₙᴴ/n` converges almost surely to `(1 + √y)²`, provided the following trace bound
holds at each threshold `r > (1 + √y)²`. For all sufficiently large `n`, the expected real trace
of the `2 * k n`-th power of the sample covariance of the matrix of centered truncations of the
entries of `Xₙ` at `n ^ a`, with `a > 1/4`, is at most `C * (n + 1)^d * t^(2 * k n)`. The scale
`0 < t < r`, the constants `B`, `C`, `d` and the orders `k n` may depend on `r`; the orders
satisfy `k n ≥ B * log (n + 1)` eventually and `2 * B * log (r / t) > d + 1`. -/
theorem ae_tendsto_eigenvalues₀_zero_sampleCovariance_of_integral_re_trace_pow_two_mul_le
    {x : ℕ × ℕ → Ω → ℂ} {ν : Measure ℂ} (hx : ∀ ij, HasLaw (x ij) ν P)
    (hindep : iIndepFun x P) (hmean : ∫ z, z ∂ν = 0) (hvar : ∫ z, ‖z‖ ^ 2 ∂ν = 1)
    (h4 : MemLp id 4 ν) (hy : 0 < y) (hp : Tendsto (fun n ↦ (p n : ℝ) / n) atTop (𝓝 y))
    {a : ℝ} (ha : 1 / 4 < a)
    (htrace : ∀ r > (1 + √y) ^ 2, ∃ (t B C d : ℝ) (k : ℕ → ℕ), 0 < t ∧ t < r ∧
      d + 1 < 2 * B * Real.log (r / t) ∧
      (∀ᶠ n : ℕ in atTop, B * Real.log (n + 1) ≤ (k n : ℝ)) ∧
      (∀ᶠ n : ℕ in atTop, (∫ ω, RCLike.re ((sampleCovariance
        (Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦
          centeredTruncation (x (i, j)) P ((n : ℝ≥0) ^ a) ω)) ^ (2 * k n)).trace ∂P) ≤
        C * (n + 1 : ℝ) ^ d * t ^ (2 * k n))) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ (isHermitian_sampleCovariance
        (Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦ x (i, j) ω)).eigenvalues₀
        ⟨0, Fintype.card_pos⟩) atTop (𝓝 ((1 + √y) ^ 2)) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  let X (n : ℕ) (ω : Ω) := Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦ x (i, j) ω
  let T (n : ℕ) (ω : Ω) := Matrix.of fun (i : Fin (p n)) (j : Fin n) ↦
    centeredTruncation (x (i, j)) P ((n : ℝ≥0) ^ a) ω
  -- The aspect ratio bounds the row dimension linearly.
  have hK : ∀ᶠ n in atTop, (p n : ℝ) ≤ (y + 1) * n := by
    filter_upwards [hp.eventually (gt_mem_nhds (lt_add_one (y : ℝ))), eventually_gt_atTop 0]
      with n hn hn₀
    exact ((div_le_iff₀ (by exact_mod_cast hn₀)).1 hn.le)
  -- The trace bound controls the covariances of the truncated corners.
  have hnorm : ∀ᵐ ω ∂P, ∀ r > (1 + √y) ^ 2, ∀ᶠ n in atTop, ‖sampleCovariance (T n ω)‖ < r := by
    refine ae_eventually_l2_opNorm_lt_of_integral_re_trace_pow_two_mul_le
      (.of_forall fun n ↦ .of_forall fun ω ↦ isHermitian_sampleCovariance _) fun r hr ↦ ?_
    obtain ⟨t, B, C, d, k, ht, htr, hB, hk, hb⟩ := htrace r hr
    refine ⟨t, B, C, d, k, ht, htr, hB, hk, .of_forall fun n ↦ ?_, hb⟩
    exact (integrable_trace_pow_sampleCovariance (fun _ ↦ inferInstance) fun i j ↦
      (hx _).aemeasurable.aestronglyMeasurable.memLp_centeredTruncation _).re
  have happrox := SampleCovariance.ae_tendsto_l2_opNorm_sub_centeredTruncation_div_sqrt hx
    (fun i ↦ hindep.precomp (Prod.mk_right_injective i))
    (fun j ↦ hindep.precomp (Prod.mk_left_injective j)) h4 hmean hK ha
  filter_upwards [hnorm, happrox, marchenkoPastur_ae hx hindep hmean hvar hy hp]
    with ω hT hXT hMP
  -- By the global law, only the upper bound remains.
  refine (tendsto_eigenvalues₀_zero_iff_of_tendsto_marchenkoPastur hMP).2 fun c hc ↦ ?_
  have hc₀ : 0 ≤ c := (sq_nonneg _).trans hc.le
  have hs : 1 + √y < √c := (Real.lt_sqrt (by positivity)).2 hc
  let m := (1 + √y + √c) / 2
  filter_upwards [hT (m ^ 2) (pow_lt_pow_left₀ (by simp only [m]; linarith) (by positivity)
      two_ne_zero),
    hXT.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < (√c - (1 + √y)) / 2))] with n hTn hXTn
  rw [eigenvalues₀_zero_sampleCovariance, Fintype.card_fin]
  rw [l2_opNorm_sampleCovariance, Fintype.card_fin] at hTn
  -- Compare the normalized operator norms `‖X‖ / √n` and `‖T‖ / √n`.
  have hTm : ‖T n ω‖ / √n < m := by
    refine (pow_lt_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
    rwa [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hX : ‖X n ω‖ / √n < √c := calc
    _ ≤ ‖T n ω‖ / √n + ‖X n ω - T n ω‖ / √n := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (norm_le_norm_add_norm_sub' _ _) (Real.sqrt_nonneg _)
    _ < m + (√c - (1 + √y)) / 2 := add_lt_add hTm hXTn
    _ = √c := by ring
  calc
    _ = (‖X n ω‖ / √n) ^ 2 := by rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    _ < √c ^ 2 := pow_lt_pow_left₀ hX (by positivity) two_ne_zero
    _ = c := Real.sq_sqrt hc₀

end TauCeti.Probability
