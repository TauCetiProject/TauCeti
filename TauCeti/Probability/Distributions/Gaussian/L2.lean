/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import TauCeti.Probability.Distributions.Gaussian.Moments
public import TauCeti.Analysis.SpecialFunctions.Clipping
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The Gaussian embedding into `L²` and its clipping error

On a finite-dimensional real inner product space `E`, the random linear observable
`y ↦ ⟪x, y⟫` under the standard Gaussian measure has variance `‖x‖²` and fourth
moment `3 ‖x‖⁴`. Consequently these observables define a linear isometry from `E`
into `L²(stdGaussian E)`.

Clipping the observable at height `M > 0` gives a bounded `L²` function whose squared
error is at most `3 ‖x‖⁴ / (16 M²)`. For vectors in the unit ball this is the
`3 / (16 M²)` estimate used in the Gaussian truncation proof of Grothendieck's
inequality. The construction also works in dimension zero.

We use Mathlib's basis-independent `ProbabilityTheory.stdGaussian`,
`IsGaussian.memLp_dual`, and `variance_dual_stdGaussian`, rather than introducing
a second finite Gaussian probability space.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §8.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace TauCeti.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The second moment of a standard Gaussian linear observable. -/
theorem integral_sq_inner_stdGaussian (x : E) :
    (∫ y, ⟪x, y⟫_ℝ ^ 2 ∂stdGaussian E) = ‖x‖ ^ 2 := by
  have h := variance_of_integral_eq_zero
    (IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ x) 2 (by simp)).aemeasurable
    (integral_strongDual_stdGaussian (innerSL ℝ x))
  rw [variance_dual_stdGaussian, innerSL_apply_norm] at h
  exact h.symm

/-- The fourth moment of a standard Gaussian linear observable. -/
theorem integral_pow_four_inner_stdGaussian (x : E) :
    (∫ y, ⟪x, y⟫_ℝ ^ 4 ∂stdGaussian E) = 3 * ‖x‖ ^ 4 := by
  have hmap := IsGaussian.map_eq_gaussianReal (μ := stdGaussian E) (innerSL ℝ x)
  rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian, innerSL_apply_norm] at hmap
  have h := integral_sub_pow_two_mul_gaussianReal 0 (‖x‖ ^ 2).toNNReal 2
  rw [← hmap, integral_map (by fun_prop) (by fun_prop)] at h
  simp only [sub_zero, Real.coe_toNNReal _ (sq_nonneg _)] at h
  norm_num at h
  nlinarith only [h]

/-- A finite-dimensional real inner product space embeds isometrically into Gaussian `L²`
by sending a vector to its random linear observable. -/
def gaussianL2 : E →ₗᵢ[ℝ] Lp ℝ 2 (stdGaussian E) := by
  let g (x : E) : Lp ℝ 2 (stdGaussian E) :=
    (IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ x) 2 (by simp)).toLp
      (fun y ↦ ⟪x, y⟫_ℝ)
  have hg (x : E) : g x =ᵐ[stdGaussian E] fun y ↦ ⟪x, y⟫_ℝ := MemLp.coeFn_toLp _
  refine
    { toFun := g
      map_add' := ?_
      map_smul' := ?_
      norm_map' := ?_ }
  · intro x z
    apply Lp.ext
    filter_upwards [hg (x + z), Lp.coeFn_add (g x) (g z), hg x, hg z] with y h₁ h₂ h₃ h₄
    simp_all [inner_add_left]
  · intro c x
    apply Lp.ext
    filter_upwards [hg (c • x), Lp.coeFn_smul c (g x), hg x] with y h₁ h₂ h₃
    simp_all [real_inner_smul_left]
  · intro x
    have h : ‖g x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [← Lp.integral_norm_sq_eq_norm_sq]
      calc
        _ = ∫ y, ⟪x, y⟫_ℝ ^ 2 ∂stdGaussian E := by
          apply integral_congr_ae
          filter_upwards [hg x] with y hy
          simp [hy, Real.norm_eq_abs]
        _ = _ := integral_sq_inner_stdGaussian x
    have hn : ‖g x‖ = ‖x‖ := by nlinarith [norm_nonneg (g x), norm_nonneg x]
    exact hn

/-- A representative of the canonical Gaussian `L²` observable. -/
theorem gaussianL2_ae_eq (x : E) : gaussianL2 x =ᵐ[stdGaussian E] fun y ↦ ⟪x, y⟫_ℝ :=
  (IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ x) 2 (by simp)).coeFn_toLp

/-- A Gaussian observable clipped at height `M ≥ 0`, as an element of `L²`. -/
def clippedGaussianL2 (x : E) (M : ℝ) (hM : 0 ≤ M) : Lp ℝ 2 (stdGaussian E) :=
  ((IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ x) 2 (by simp)).max_min hM).toLp
    (fun y ↦ max (-M) (min M ⟪x, y⟫_ℝ))

/-- A bounded representative of the clipped Gaussian observable. -/
theorem clippedGaussianL2_ae_eq (x : E) (M : ℝ) (hM : 0 ≤ M) :
    clippedGaussianL2 x M hM =ᵐ[stdGaussian E] fun y ↦ max (-M) (min M ⟪x, y⟫_ℝ) :=
  MemLp.coeFn_toLp _

/-- The clipped observable is almost everywhere bounded by its clipping height. -/
theorem ae_abs_clippedGaussianL2_le (x : E) (M : ℝ) (hM : 0 ≤ M) :
    ∀ᵐ y ∂stdGaussian E, |clippedGaussianL2 x M hM y| ≤ M := by
  filter_upwards [clippedGaussianL2_ae_eq x M hM] with y hy
  rw [hy, abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- Clipping does not increase the `L²` norm of the Gaussian observable. -/
theorem norm_clippedGaussianL2_le (x : E) (M : ℝ) (hM : 0 ≤ M) :
    ‖clippedGaussianL2 x M hM‖ ≤ ‖x‖ := by
  calc
    _ ≤ ‖gaussianL2 x‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [clippedGaussianL2_ae_eq x M hM, gaussianL2_ae_eq x] with y h₁ h₂
      simpa only [h₁, h₂, Real.norm_eq_abs] using Real.abs_max_min_le_abs hM ⟪x, y⟫_ℝ
    _ = _ := gaussianL2.norm_map x

/-- Clipping a Gaussian linear observable has squared `L²` error at most
`3 ‖x‖⁴ / (16 M²)`. -/
theorem norm_sub_clippedGaussianL2_sq_le (x : E) {M : ℝ} (hM : 0 < M) :
    ‖gaussianL2 x - clippedGaussianL2 x M hM.le‖ ^ 2 ≤ 3 * ‖x‖ ^ 4 / (16 * M ^ 2) := by
  have hf := IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ x) 2 (by simp)
  have hf₄ : Integrable (fun y ↦ ⟪x, y⟫_ℝ ^ 4) (stdGaussian E) := by
    have h := (IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ x) 4 (by simp)).integrable_norm_rpow
      (by norm_num) (by norm_num)
    convert h using 1
    ext y
    norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat, innerSL_apply_apply]
    rw [Real.norm_eq_abs]
    convert (congrArg (fun t : ℝ ↦ t ^ 2) (sq_abs ⟪x, y⟫_ℝ)).symm using 1 <;> ring
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  calc
    _ = ∫ y, (⟪x, y⟫_ℝ - max (-M) (min M ⟪x, y⟫_ℝ)) ^ 2 ∂stdGaussian E := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (gaussianL2 x) (clippedGaussianL2 x M hM.le),
        gaussianL2_ae_eq x, clippedGaussianL2_ae_eq x M hM.le] with y h₁ h₂ h₃
      simp only [h₁, Pi.sub_apply, h₂, h₃, Real.norm_eq_abs, sq_abs]
    _ ≤ _ := by
      simpa only [innerSL_apply_apply, integral_pow_four_inner_stdGaussian] using
        hf.integral_sq_sub_max_min_le hf₄ hM

/-- The uniform clipping-error bound for Gaussian observables of unit-ball vectors. -/
theorem norm_sub_clippedGaussianL2_sq_le_of_norm_le_one {x : E} (hx : ‖x‖ ≤ 1)
    {M : ℝ} (hM : 0 < M) :
    ‖gaussianL2 x - clippedGaussianL2 x M hM.le‖ ^ 2 ≤ 3 / (16 * M ^ 2) := by
  refine (norm_sub_clippedGaussianL2_sq_le x hM).trans ?_
  have hx₄ : ‖x‖ ^ 4 ≤ 1 := by nlinarith [pow_le_pow_left₀ (norm_nonneg x) hx 4]
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

end TauCeti.Probability
