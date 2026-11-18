/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import TauCeti.Analysis.InnerProductSpace.Comass

/-!
# The norm determinant as the volume of a frame

For a linear map `L : U → E` between finite-dimensional real inner product spaces and an
orthonormal basis `b` of `U` indexed by `Fin k`, the Jacobian `LinearMap.normDet L` is the volume
`‖L b₁ ∧ ⋯ ∧ L bₖ‖` of the parallelepiped spanned by the images of the basis vectors, measured by
the Gram norm of the exterior power. Both sides are square roots of the Gram determinant of
`L ∘ b`.

Combined with the comass bound `ContinuousAlternatingMap.le_opNorm_mul_norm_ιMulti`, this gives
the linear calibration inequality in Jacobian form, `‖ω (L b₁, …, L bₖ)‖ ≤ ‖ω‖ · normDet L`. This
is the form in which a `k`-form is compared with the `k`-dimensional volume of a parametrized
piece of a submanifold, the integrand of the area formula.

## Main results

* `LinearMap.normDet_eq_norm_ιMulti`: `normDet L = ‖L b₁ ∧ ⋯ ∧ L bₖ‖`.
* `ContinuousAlternatingMap.le_opNorm_mul_normDet`: `‖ω (L ∘ b)‖ ≤ ‖ω‖ * normDet L`.

## References

* H. Federer, *Geometric Measure Theory*, §1.8.1.
* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. 148 (1982), Lemma II.3.5.
-/

public section

variable {U E : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {k : ℕ}

/-- The Jacobian `normDet L` of a linear map is the volume `‖L b₁ ∧ ⋯ ∧ L bₖ‖` of the image of
any orthonormal basis `b` of its domain. -/
theorem LinearMap.normDet_eq_norm_ιMulti (L : U →ₗ[ℝ] E) (b : OrthonormalBasis (Fin k) ℝ U) :
    L.normDet = ‖exteriorPower.ιMulti ℝ k (L ∘ b)‖ := by
  rw [← pow_left_inj₀ L.normDet_nonneg (norm_nonneg _) two_ne_zero, exteriorPower.norm_ιMulti_sq]
  simpa [Function.comp_def] using L.normDet_sq_eq_det_gram b

/-- **The linear calibration inequality** in Jacobian form: the value of a `k`-form on the image
of an orthonormal basis under `L` is at most its norm times the Jacobian of `L`. -/
theorem ContinuousAlternatingMap.le_opNorm_mul_normDet {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (ω : E [⋀^Fin k]→L[ℝ] F) (L : U →ₗ[ℝ] E)
    (b : OrthonormalBasis (Fin k) ℝ U) : ‖ω (L ∘ b)‖ ≤ ‖ω‖ * L.normDet := by
  rw [L.normDet_eq_norm_ιMulti b]
  exact ω.le_opNorm_mul_norm_ιMulti _
