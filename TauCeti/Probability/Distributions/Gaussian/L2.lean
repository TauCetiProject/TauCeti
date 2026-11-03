/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Fernique
import TauCeti.Probability.Distributions.Gaussian.MixedMoments
public import TauCeti.MeasureTheory.Function.LpSeminorm.Clipping
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The Gaussian embedding into `L²` and its clipping error

On a finite-dimensional real inner product space `E`, the random linear observable
`y ↦ ⟪x, y⟫` under the standard Gaussian measure has variance `‖x‖²` and fourth
moment `3 ‖x‖⁴`. Consequently these observables define a linear isometry from `E`
into `L²(stdGaussian E)`.

Clipping the observable at height `M > 0` gives a bounded `L²` function whose squared
error is at most `3 ‖x‖⁴ / (16 M²)`. For vectors in the unit ball this is the
`3 / (16 M²)` estimate, or the norm bound `√3 / (4 M)`, used in the Gaussian truncation proof of
Grothendieck's inequality. The construction also works in dimension zero.

We use Mathlib's basis-independent `ProbabilityTheory.stdGaussian`,
`IsGaussian.memLp_dual`, and the real Gaussian even-moment formula, rather than introducing
a second finite Gaussian probability space.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §8.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace Nat

namespace TauCeti.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A standard Gaussian linear observable belongs to every finite `Lᵖ` space. -/
theorem memLp_inner_stdGaussian (x : E) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun y ↦ ⟪x, y⟫_ℝ) p (stdGaussian E) :=
  IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ x) p hp

/-- The even moments of a standard Gaussian linear observable. -/
theorem integral_pow_two_mul_inner_stdGaussian (x : E) (n : ℕ) :
    (∫ y, ⟪x, y⟫_ℝ ^ (2 * n) ∂stdGaussian E) =
      ‖x‖ ^ (2 * n) * (2 * n - 1 : ℕ)‼ := by
  have h := IsGaussian.integral_pow_two_mul_sub_dual (stdGaussian E) (innerSL ℝ x) n
  rw [covarianceBilinDual_self_eq_variance IsGaussian.memLp_two_id,
    variance_dual_stdGaussian, innerSL_apply_norm] at h
  simpa only [id_eq, integral_id_stdGaussian, sub_zero, innerSL_apply_apply, pow_mul] using h

/-- The second moment of a standard Gaussian linear observable. -/
theorem integral_sq_inner_stdGaussian (x : E) :
    (∫ y, ⟪x, y⟫_ℝ ^ 2 ∂stdGaussian E) = ‖x‖ ^ 2 := by
  simpa using integral_pow_two_mul_inner_stdGaussian x 1

/-- The fourth moment of a standard Gaussian linear observable. -/
theorem integral_pow_four_inner_stdGaussian (x : E) :
    (∫ y, ⟪x, y⟫_ℝ ^ 4 ∂stdGaussian E) = 3 * ‖x‖ ^ 4 := by
  simpa [Nat.doubleFactorial, mul_comm] using integral_pow_two_mul_inner_stdGaussian x 2

/-- A finite-dimensional real inner product space embeds isometrically into Gaussian `L²`
by sending a vector to its random linear observable. -/
def gaussianL2 : E →ₗᵢ[ℝ] Lp ℝ 2 (stdGaussian E) := by
  let g (x : E) : Lp ℝ 2 (stdGaussian E) :=
    (memLp_inner_stdGaussian x 2 (by simp)).toLp (fun y ↦ ⟪x, y⟫_ℝ)
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
  (memLp_inner_stdGaussian x 2 (by simp)).coeFn_toLp

/-- A Gaussian observable clipped to `[-M, M]` for `M ≥ 0`, as an element of `L²`.
For negative `M`, the max-min formula gives the constant `-M`. -/
def clippedGaussianL2 (x : E) (M : ℝ) : Lp ℝ 2 (stdGaussian E) :=
  (MemLp.of_bound (by fun_prop) |M| (Filter.Eventually.of_forall fun y ↦ by
    simpa only [Real.norm_eq_abs] using TauCeti.abs_max_min_le M ⟪x, y⟫_ℝ)).toLp
      (fun y ↦ max (-M) (min M ⟪x, y⟫_ℝ))

/-- A bounded representative of the clipped Gaussian observable. -/
theorem clippedGaussianL2_ae_eq (x : E) (M : ℝ) :
    clippedGaussianL2 x M =ᵐ[stdGaussian E] fun y ↦ max (-M) (min M ⟪x, y⟫_ℝ) :=
  MemLp.coeFn_toLp _

/-- The clipped observable is almost everywhere bounded by its clipping height. -/
theorem ae_abs_clippedGaussianL2_le (x : E) (M : ℝ) (hM : 0 ≤ M) :
    ∀ᵐ y ∂stdGaussian E, |clippedGaussianL2 x M y| ≤ M := by
  filter_upwards [clippedGaussianL2_ae_eq x M] with y hy
  simpa only [hy, abs_of_nonneg hM] using TauCeti.abs_max_min_le M ⟪x, y⟫_ℝ

/-- Clipping does not increase the `L²` norm of the Gaussian observable. -/
theorem norm_clippedGaussianL2_le (x : E) (M : ℝ) (hM : 0 ≤ M) :
    ‖clippedGaussianL2 x M‖ ≤ ‖x‖ := by
  calc
    _ ≤ ‖gaussianL2 x‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [clippedGaussianL2_ae_eq x M, gaussianL2_ae_eq x] with y h₁ h₂
      simpa only [h₁, h₂, Real.norm_eq_abs] using TauCeti.abs_max_min_le_abs hM ⟪x, y⟫_ℝ
    _ = _ := gaussianL2.norm_map x

/-- Clipping a Gaussian linear observable has squared `L²` error at most
`3 ‖x‖⁴ / (16 M²)`. -/
theorem norm_sub_clippedGaussianL2_sq_le (x : E) {M : ℝ} (hM : 0 < M) :
    ‖gaussianL2 x - clippedGaussianL2 x M‖ ^ 2 ≤ 3 * ‖x‖ ^ 4 / (16 * M ^ 2) := by
  have hf₄ : Integrable (fun y ↦ ⟪x, y⟫_ℝ ^ 4) (stdGaussian E) := by
    simpa only [Real.norm_eq_abs, (by decide : Even 4).pow_abs] using
      (memLp_inner_stdGaussian x 4 (by simp)).integrable_norm_pow (by norm_num)
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  calc
    _ = ∫ y, (⟪x, y⟫_ℝ - max (-M) (min M ⟪x, y⟫_ℝ)) ^ 2 ∂stdGaussian E := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (gaussianL2 x) (clippedGaussianL2 x M),
        gaussianL2_ae_eq x, clippedGaussianL2_ae_eq x M] with y h₁ h₂ h₃
      simp only [h₁, Pi.sub_apply, h₂, h₃, Real.norm_eq_abs, sq_abs]
    _ ≤ _ := by
      simpa only [innerSL_apply_apply, integral_pow_four_inner_stdGaussian] using
        hf₄.integral_sq_sub_max_min_le hM

/-- The uniform clipping-error bound for Gaussian observables of unit-ball vectors. -/
theorem norm_sub_clippedGaussianL2_sq_le_of_norm_le_one {x : E} (hx : ‖x‖ ≤ 1)
    {M : ℝ} (hM : 0 < M) :
    ‖gaussianL2 x - clippedGaussianL2 x M‖ ^ 2 ≤ 3 / (16 * M ^ 2) := by
  refine (norm_sub_clippedGaussianL2_sq_le x hM).trans ?_
  have hx₄ : ‖x‖ ^ 4 ≤ 1 := by nlinarith [pow_le_pow_left₀ (norm_nonneg x) hx 4]
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- The clipping error of the Gaussian observable of a unit-ball vector has `L²` norm at most
`√3 / (4 * M)`. -/
theorem norm_sub_clippedGaussianL2_le_of_norm_le_one {x : E} (hx : ‖x‖ ≤ 1) {M : ℝ}
    (hM : 0 < M) : ‖gaussianL2 x - clippedGaussianL2 x M‖ ≤ √3 / (4 * M) := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [div_pow, Real.sq_sqrt (by norm_num), mul_pow]
  exact (norm_sub_clippedGaussianL2_sq_le_of_norm_le_one hx hM).trans_eq (by ring)

end TauCeti.Probability
