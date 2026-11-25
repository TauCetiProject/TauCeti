/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Probability.Moments.SubGaussian.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import TauCeti.Analysis.Normed.Group.Real

/-!
# Sub-Gaussian random vectors

A random vector `x` in a real inner product space is sub-Gaussian with variance proxy `c` when
every linear form `⟪u, x⟫` satisfies a sub-Gaussian moment-generating function bound with
variance proxy `c * ‖u‖²`. A condition on the coordinates alone is weaker: for `g` standard
Gaussian, `(g, g)` has coordinates with proxy `1`, but its form along `(1, 1) / √2` is `√2 g`,
whose variance is `2`.

## Main definitions and results

* `TauCeti.IsSubgaussianVector x c μ`: every linear form `⟪u, x⟫` has variance proxy
  `c * ‖u‖₊ ^ 2`.
* `TauCeti.isSubgaussianVector_iff_forall_norm_eq_one`: for a measure of total mass at most `1`
  it suffices to test unit directions, with proxy `c`.
* `TauCeti.isSubgaussianVector_zero_iff`, `TauCeti.isSubgaussianVector_zero_measure`: the zero
  vector is sub-Gaussian exactly when the total mass is at most `1`, and every vector is
  sub-Gaussian under the zero measure.
* `TauCeti.IsSubgaussianVector.measure_univ_le_one`,
  `TauCeti.IsSubgaussianVector.isFiniteMeasure`: a sub-Gaussian vector forces the total mass to
  be at most `1`, so the measure is finite.
* `TauCeti.isSubgaussianVector_zero_proxy_iff`: in a separable space, the proxy `0` means that
  the vector vanishes almost everywhere and the total mass is at most `1`.
* `TauCeti.IsSubgaussianVector.integrable`: a sub-Gaussian vector in a finite-dimensional space
  is integrable.
* `TauCeti.IsSubgaussianVector.integral_eq_zero`: under a zero or probability measure, a
  sub-Gaussian vector has mean zero.
* `TauCeti.IsSubgaussianVector.continuousLinearMap_comp`: for a complete source space, the image
  under a continuous linear map `A` of a sub-Gaussian vector with proxy `c` has proxy
  `‖A‖₊ ^ 2 * c`.
* `TauCeti.isSubgaussianVector_iff_hasSubgaussianMGF_re_star_mul`: in `ℂ`, a sub-Gaussian vector
  is a directionally sub-Gaussian complex random variable, with every projection
  `(star u * Z).re` of proxy `‖u‖₊ ^ 2 * K`.

Independent coordinates are treated in `TauCeti.Probability.Moments.SubGaussian.LinearForms`
(`ProbabilityTheory.iIndepFun.isSubgaussianVector`).

Centred Gaussian vectors are treated in
`TauCeti.Probability.Moments.SubGaussian.Gaussian.Multivariate`
(`ProbabilityTheory.HasLaw.isSubgaussianVector`).

## References

* R. Vershynin, *High-Dimensional Probability* (2018), §3.4.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace

namespace TauCeti

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A random vector `x` in a real inner product space is sub-Gaussian with variance proxy `c`
if every linear form `⟪u, x⟫` has a sub-Gaussian moment-generating function with variance proxy
`c * ‖u‖₊ ^ 2`. -/
def IsSubgaussianVector (x : Ω → E) (c : ℝ≥0) (μ : Measure Ω) : Prop :=
  ∀ u : E, HasSubgaussianMGF (fun ω ↦ ⟪u, x ω⟫) (c * ‖u‖₊ ^ 2) μ

/-- Unfolding lemma for `IsSubgaussianVector`. -/
theorem isSubgaussianVector_def {x : Ω → E} {c : ℝ≥0} :
    IsSubgaussianVector x c μ ↔
      ∀ u : E, HasSubgaussianMGF (fun ω ↦ ⟪u, x ω⟫) (c * ‖u‖₊ ^ 2) μ := Iff.rfl

/-- A sub-Gaussian vector forces the total mass to be at most `1`. -/
theorem IsSubgaussianVector.measure_univ_le_one {x : Ω → E} {c : ℝ≥0}
    (h : IsSubgaussianVector x c μ) : μ Set.univ ≤ 1 :=
  (h 0).measure_univ_le_one

/-- A measure carrying a sub-Gaussian vector is finite. -/
theorem IsSubgaussianVector.isFiniteMeasure {x : Ω → E} {c : ℝ≥0}
    (h : IsSubgaussianVector x c μ) : IsFiniteMeasure μ :=
  (h 0).isFiniteMeasure

/-- Under a measure of total mass at most `1`, a random vector is sub-Gaussian with variance
proxy `c` if and only if its linear form along every unit vector has proxy `c`. -/
theorem isSubgaussianVector_iff_forall_norm_eq_one (hμ : μ Set.univ ≤ 1) {x : Ω → E}
    {c : ℝ≥0} :
    IsSubgaussianVector x c μ ↔
      ∀ u : E, ‖u‖ = 1 → HasSubgaussianMGF (fun ω ↦ ⟪u, x ω⟫) c μ := by
  refine ⟨fun h u hu ↦ ?_, fun h u ↦ ?_⟩
  · have hu' : ‖u‖₊ = 1 := NNReal.eq hu
    simpa [hu'] using h u
  rcases eq_or_ne u 0 with rfl | hu
  · simpa using hμ
  refine (((h _ (norm_smul_inv_norm (𝕜 := ℝ) hu)).const_mul ‖u‖).congr
    (ae_of_all _ fun ω ↦ ?_)).mono (le_of_eq ?_)
  · simp [real_inner_smul_left, hu]
  · rw [mul_comm, ← Real.nnNorm_sq, nnNorm_norm]

/-- The zero random vector is sub-Gaussian, with any variance proxy, exactly when the total mass
is at most `1`. -/
@[simp]
theorem isSubgaussianVector_zero_iff {c : ℝ≥0} :
    IsSubgaussianVector (0 : Ω → E) c μ ↔ μ Set.univ ≤ 1 := by
  simp [isSubgaussianVector_def]

/-- Every random vector is sub-Gaussian, with any variance proxy, under the zero measure. -/
@[simp]
theorem isSubgaussianVector_zero_measure {x : Ω → E} {c : ℝ≥0} :
    IsSubgaussianVector x c (0 : Measure Ω) :=
  fun _ ↦ by
    rw [HasSubgaussianMGF_iff_kernel, Kernel.const_zero]
    exact Kernel.HasSubgaussianMGF.zero_kernel

/-- In a separable space, a random vector is sub-Gaussian with variance proxy `0` exactly when it
vanishes almost everywhere and the total mass is at most `1`. -/
@[simp]
theorem isSubgaussianVector_zero_proxy_iff [SecondCountableTopology E] {x : Ω → E} :
    IsSubgaussianVector x 0 μ ↔ x =ᵐ[μ] 0 ∧ μ Set.univ ≤ 1 := by
  refine ⟨fun h ↦ ⟨ae_eq_zero_of_forall_inner (𝕜 := ℝ) fun u ↦ ?_, h.measure_univ_le_one⟩,
    fun ⟨hx, hμ⟩ ↦ ?_⟩
  · exact ((h u).mono (zero_mul _).le).ae_eq_zero_of_hasSubgaussianMGF_zero
  · exact fun u ↦ (isSubgaussianVector_zero_iff.2 hμ u).congr (hx.mono fun ω hω ↦ by simp [hω])

/-- A complex random variable is a sub-Gaussian vector of the real inner product space `ℂ` with
proxy `K` exactly when it is directionally `K`-sub-Gaussian: every projection `(star u * Z).re`
has proxy `‖u‖₊ ^ 2 * K`, since the real inner product `⟪u, z⟫` is `(star u * z).re`. -/
theorem isSubgaussianVector_iff_hasSubgaussianMGF_re_star_mul {Z : Ω → ℂ} {K : ℝ≥0} :
    IsSubgaussianVector Z K μ ↔
      ∀ u : ℂ, HasSubgaussianMGF (fun ω ↦ (star u * Z ω).re) (‖u‖₊ ^ 2 * K) μ := by
  simp only [isSubgaussianVector_def, Complex.inner, Complex.star_def, mul_comm]

namespace IsSubgaussianVector

variable {x : Ω → E} {c : ℝ≥0}

/-- The linear form `⟪u, x⟫` of a sub-Gaussian vector with proxy `c` has proxy
`c * ‖u‖₊ ^ 2`. -/
theorem hasSubgaussianMGF_inner (h : IsSubgaussianVector x c μ) (u : E) :
    HasSubgaussianMGF (fun ω ↦ ⟪u, x ω⟫) (c * ‖u‖₊ ^ 2) μ :=
  h u

/-- Monotonicity of `IsSubgaussianVector` in the variance proxy. -/
theorem mono (h : IsSubgaussianVector x c μ) {c' : ℝ≥0} (hc : c ≤ c') :
    IsSubgaussianVector x c' μ :=
  fun u ↦ (h u).mono (mul_le_mul_left hc _)

/-- `IsSubgaussianVector` is invariant under almost-everywhere equality of the random vector. -/
theorem congr (h : IsSubgaussianVector x c μ) {y : Ω → E} (hxy : x =ᵐ[μ] y) :
    IsSubgaussianVector y c μ :=
  fun u ↦ (h u).congr (hxy.mono fun ω hω ↦ by simp [hω])

/-- Each coordinate of a sub-Gaussian vector of `EuclideanSpace ℝ ι` with proxy `c` has proxy
`c`. -/
theorem hasSubgaussianMGF_eval {ι : Type*} [Fintype ι] {x : Ω → EuclideanSpace ℝ ι}
    (h : IsSubgaussianVector x c μ) (i : ι) : HasSubgaussianMGF (fun ω ↦ x ω i) c μ := by
  classical
  simpa [EuclideanSpace.inner_single_left] using h (EuclideanSpace.single i 1)

/-- A sub-Gaussian vector in a finite-dimensional space is integrable. -/
theorem integrable [FiniteDimensional ℝ E] (h : IsSubgaussianVector x c μ) : Integrable x μ := by
  let b := stdOrthonormalBasis ℝ E
  rw [funext fun ω ↦ (b.sum_repr' (x ω)).symm]
  exact integrable_finsetSum _ fun i _ ↦ (h (b i)).integrable.smul_const (b i)

/-- Under a zero or probability measure, a sub-Gaussian vector has mean zero. -/
theorem integral_eq_zero [IsZeroOrProbabilityMeasure μ] (h : IsSubgaussianVector x c μ) :
    ∫ ω, x ω ∂μ = 0 := by
  by_cases hE : CompleteSpace E; swap
  · exact integral_of_not_completeSpace hE
  by_cases hx : Integrable x μ
  · exact integral_eq_zero_of_forall_integral_inner_eq_zero ℝ x hx fun u ↦ (h u).integral_eq_zero
  · exact integral_undef hx

/-- Let `E` be complete. The image of a sub-Gaussian vector with proxy `c` under a continuous
linear map `A : E →L[ℝ] F` is a sub-Gaussian vector with proxy `‖A‖₊ ^ 2 * c`. -/
theorem continuousLinearMap_comp [CompleteSpace E] {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (h : IsSubgaussianVector x c μ) (A : E →L[ℝ] F) :
    IsSubgaussianVector (fun ω ↦ A (x ω)) (‖A‖₊ ^ 2 * c) μ := by
  intro v
  -- The Riesz representative `w` of the functional `⟪v, A ·⟫` has `‖w‖ ≤ ‖A‖ * ‖v‖`.
  set w := (InnerProductSpace.toDual ℝ E).symm (A.toSesqForm v)
  have hw : ‖w‖₊ ≤ ‖A‖₊ * ‖v‖₊ := by
    rw [← NNReal.coe_le_coe, coe_nnNorm, LinearIsometryEquiv.norm_map]
    exact ContinuousLinearMap.toSesqForm_apply_norm_le
  refine ((h w).congr (ae_of_all _ fun ω ↦ ?_)).mono ?_
  · simp [w, InnerProductSpace.toDual_symm_apply]
  · calc c * ‖w‖₊ ^ 2 ≤ c * (‖A‖₊ * ‖v‖₊) ^ 2 := by gcongr
      _ = ‖A‖₊ ^ 2 * c * ‖v‖₊ ^ 2 := by ring

end IsSubgaussianVector

end TauCeti
