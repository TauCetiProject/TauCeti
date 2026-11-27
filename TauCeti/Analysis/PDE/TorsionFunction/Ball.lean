/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import TauCeti.Analysis.Calculus.Morse.Linearization
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.Gradient

/-!
# The torsion function of the unit ball

On `ℝⁿ = EuclideanSpace ℝ ι`, let `v` be the torsion function of the unit ball, the concave
paraboloid

`v(x) = (1 - ‖x‖²) / (2n)` (`TauCeti.PDE.ballTorsionFunction`),

which solves `-Δv = 1` and vanishes on the unit sphere. This file computes its elementary
calculus. All declarations are in the `TauCeti.PDE` namespace.

* `v` is smooth (`contDiff_ballTorsionFunction`), vanishes on the unit sphere
  (`ballTorsionFunction_eq_zero_of_mem_sphere`) and attains its maximum `1 / (2n)` at the origin
  (`ballTorsionFunction_zero`, `ballTorsionFunction_le`).
* Its gradient is `∇v(x) = -x / n` (`gradient_ballTorsionFunction`).
* Its Hessian operator is `-1 / n` times the identity (`hessianOperator_ballTorsionFunction`), so
  `|det D²v| = n⁻ⁿ` (`abs_det_hessianOperator_ballTorsionFunction`) and, for `n ≥ 1`, `Δv = -1`
  (`sum_fderiv_fderiv_ballTorsionFunction`, `laplacian_ballTorsionFunction`).

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 9.1.
-/

public section

noncomputable section

open InnerProductSpace Laplacian Metric
open scoped Gradient RealInnerProductSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι]

/-- The **torsion function of the unit ball** of `ℝⁿ = EuclideanSpace ℝ ι`, `n = card ι`: the
concave paraboloid `v(x) = (1 - ‖x‖²) / (2n)`. It solves `-Δv = 1` and vanishes on the unit
sphere, and on the unit ball it attains equality in the Aleksandrov measure estimate. -/
def ballTorsionFunction (ι : Type*) [Fintype ι] (x : EuclideanSpace ℝ ι) : ℝ :=
  (1 - ‖x‖ ^ 2) / (2 * Fintype.card ι)

/-- The defining formula of the torsion function of the unit ball. -/
theorem ballTorsionFunction_apply (x : EuclideanSpace ℝ ι) :
    ballTorsionFunction ι x = (1 - ‖x‖ ^ 2) / (2 * Fintype.card ι) :=
  (rfl)

/-- The torsion function as a quadratic `(a / 2) ‖x‖² + c`, the form of
`TauCeti.gradient_mul_norm_sq_add`. -/
private theorem ballTorsionFunction_eq :
    ballTorsionFunction ι = fun x => -(Fintype.card ι : ℝ)⁻¹ / 2 * ‖x‖ ^ 2 +
      (2 * Fintype.card ι : ℝ)⁻¹ := by
  funext x
  rw [ballTorsionFunction_apply]
  ring

/-- The torsion function of the unit ball is smooth. -/
theorem contDiff_ballTorsionFunction {k : WithTop ℕ∞} :
    ContDiff ℝ k (ballTorsionFunction ι) := by
  rw [ballTorsionFunction_eq]
  exact (contDiff_const.mul (contDiff_norm_sq ℝ)).add contDiff_const

/-- The torsion function vanishes on the unit sphere. -/
theorem ballTorsionFunction_eq_zero_of_mem_sphere {x : EuclideanSpace ℝ ι}
    (hx : x ∈ sphere 0 1) : ballTorsionFunction ι x = 0 := by
  rw [mem_sphere_zero_iff_norm] at hx
  simp [ballTorsionFunction_apply, hx]

/-- The value of the torsion function at the origin is `1 / (2n)`. -/
theorem ballTorsionFunction_zero : ballTorsionFunction ι 0 = 1 / (2 * Fintype.card ι) := by
  simp [ballTorsionFunction_apply]

/-- The torsion function is at most its value `1 / (2n)` at the origin. -/
theorem ballTorsionFunction_le (x : EuclideanSpace ℝ ι) :
    ballTorsionFunction ι x ≤ 1 / (2 * Fintype.card ι) := by
  rw [ballTorsionFunction_apply]
  gcongr
  linarith [sq_nonneg ‖x‖]

/-- The gradient of the torsion function is `∇v(x) = -x / n`. -/
@[simp]
theorem gradient_ballTorsionFunction (x : EuclideanSpace ℝ ι) :
    ∇ (ballTorsionFunction ι) x = -(Fintype.card ι : ℝ)⁻¹ • x := by
  rw [ballTorsionFunction_eq]
  exact gradient_mul_norm_sq_add _ _ x

/-- The gradient of the torsion function, as a function: `∇v = fun x => -x / n`. -/
theorem gradient_ballTorsionFunction_eq :
    ∇ (ballTorsionFunction ι) = fun x => -(Fintype.card ι : ℝ)⁻¹ • x :=
  funext gradient_ballTorsionFunction

/-- The Hessian operator of the torsion function is `-1 / n` times the identity. -/
@[simp]
theorem hessianOperator_ballTorsionFunction (x : EuclideanSpace ℝ ι) :
    hessianOperator (ballTorsionFunction ι) x =
      -(Fintype.card ι : ℝ)⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι) := by
  rw [← fderiv_gradient, gradient_ballTorsionFunction_eq]
  exact ((hasFDerivAt_id x).const_smul (-(Fintype.card ι : ℝ)⁻¹)).fderiv

/-- The second derivatives of the torsion function: `D²v(x)(w₁, w₂) = -⟪w₁, w₂⟫ / n`. -/
@[simp]
theorem fderiv_fderiv_ballTorsionFunction (x w₁ w₂ : EuclideanSpace ℝ ι) :
    fderiv ℝ (fderiv ℝ (ballTorsionFunction ι)) x w₁ w₂ =
      -(Fintype.card ι : ℝ)⁻¹ * ⟪w₁, w₂⟫_ℝ := by
  rw [← inner_hessianOperator_left, hessianOperator_ballTorsionFunction]
  simp [real_inner_smul_left]

/-- **The torsion function solves `-Δv = 1`**, in every dimension `n ≥ 1`. -/
theorem sum_fderiv_fderiv_ballTorsionFunction [Nonempty ι] [DecidableEq ι]
    (x : EuclideanSpace ℝ ι) :
    ∑ i, fderiv ℝ (fderiv ℝ (ballTorsionFunction ι)) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single i 1) = -1 := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [fderiv_fderiv_ballTorsionFunction, EuclideanSpace.inner_single_left, map_one,
    PiLp.single_apply, ite_true, mul_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  field_simp

/-- **The Laplacian of the torsion function is `Δv = -1`**, in every dimension `n ≥ 1`. -/
@[simp]
theorem laplacian_ballTorsionFunction [Nonempty ι] (x : EuclideanSpace ℝ ι) :
    Δ (ballTorsionFunction ι) x = -1 := by
  classical
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun ι ℝ)]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    EuclideanSpace.basisFun_apply]
  exact sum_fderiv_fderiv_ballTorsionFunction x

/-- The determinant of the Hessian operator of the torsion function is `(-1 / n)ⁿ`. -/
theorem det_hessianOperator_ballTorsionFunction (x : EuclideanSpace ℝ ι) :
    (hessianOperator (ballTorsionFunction ι) x).det =
      (-(Fintype.card ι : ℝ)⁻¹) ^ Fintype.card ι := by
  simp [ContinuousLinearMap.det, LinearMap.det_smul, -neg_smul]

/-- The absolute value of the Hessian determinant of the torsion function is `n⁻ⁿ`. -/
theorem abs_det_hessianOperator_ballTorsionFunction (x : EuclideanSpace ℝ ι) :
    |(hessianOperator (ballTorsionFunction ι) x).det| =
      (Fintype.card ι : ℝ)⁻¹ ^ Fintype.card ι := by
  rw [det_hessianOperator_ballTorsionFunction, abs_pow, abs_neg, abs_of_nonneg (by positivity)]

end PDE

end TauCeti
