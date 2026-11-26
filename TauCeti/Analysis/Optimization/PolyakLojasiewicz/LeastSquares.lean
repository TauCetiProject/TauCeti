/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Optimization.PolyakLojasiewicz.Basic
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import TauCeti.Analysis.Optimization.LeastSquares
import TauCeti.Analysis.InnerProductSpace.SingularValues.Range

/-!
# Gradient domination for least squares

For the objective `x ↦ ‖A x - b‖ ^ 2 / 2`, the component of `b` perpendicular to the range
contributes a constant to the loss. The objective gap is half the squared norm of the
remaining residual, and its gradient is the adjoint applied to that residual. Thus in
finite dimension the optimal Polyak–Łojasiewicz modulus for a nonzero map is the square
of its smallest nonzero singular value, for every right-hand side.

## References

* H. Karimi, J. Nutini and M. Schmidt, *Linear convergence of gradient and
  proximal-gradient methods under the Polyak–Łojasiewicz condition*, Appendix B.
-/

public section

open Set TauCeti InnerProductSpace
open scoped Gradient

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

namespace ContinuousLinearMap

variable [CompleteSpace E] [CompleteSpace F]

/-- A least-squares loss satisfies gradient domination exactly when the squared stretch
of the adjoint has the given lower bound on the range of the forward map. -/
theorem polyakLojasiewicz_leastSquares_iff (A : E →L[ℝ] F) [A.range.HasOrthogonalProjection]
    (b : F) {μ : ℝ} : PolyakLojasiewicz μ (fun x ↦ ‖A x - b‖ ^ 2 / 2) ↔
      ∀ y ∈ A.range, μ * ‖y‖ ^ 2 ≤ ‖A.adjoint y‖ ^ 2 := by
  have hb : A.adjoint b = A.adjoint (A.range.starProjection b) := by
    have h := A.range.sub_starProjection_mem_orthogonal b
    rwa [A.orthogonal_range, LinearMap.mem_ker, map_sub, sub_eq_zero] at h
  have pointwise (x : E) :
      2 * μ * (‖A x - b‖ ^ 2 / 2 - ⨅ y, ‖A y - b‖ ^ 2 / 2) ≤
          ‖∇ (fun y ↦ ‖A y - b‖ ^ 2 / 2) x‖ ^ 2 ↔
        μ * ‖A x - A.range.starProjection b‖ ^ 2 ≤
          ‖A.adjoint (A x - A.range.starProjection b)‖ ^ 2 := by
    have gap := A.toLinearMap.leastSquares_sub_iInf b x
    simp only [coe_coe] at gap
    rw [gap, (A.hasGradientAt_leastSquares b x).gradient, map_sub, hb, map_sub]
    ring_nf
  constructor
  · intro h y hy
    obtain ⟨x, hx⟩ := A.range.add_mem hy (A.range.starProjection_apply_mem b)
    simp only [coe_coe] at hx
    simpa only [hx, add_sub_cancel_right] using (pointwise x).mp (h.le x)
  · intro h
    exact ⟨⟨0, forall_mem_range.mpr fun x ↦ by positivity⟩, fun x ↦ (pointwise x).mpr <|
      h _ (A.range.sub_mem (A.mem_range_self x) (A.range.starProjection_apply_mem b))⟩

end ContinuousLinearMap

namespace LinearMap

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

private local instance : CompleteSpace E := FiniteDimensional.completeSpace ℝ E

/-- The admissible least-squares moduli are exactly the lower bounds of the nonzero
squared singular values. For the zero map every real modulus is admissible. -/
theorem polyakLojasiewicz_leastSquares_iff (A : E →ₗ[ℝ] F) (b : F) {μ : ℝ} :
    PolyakLojasiewicz μ (fun x ↦ ‖A x - b‖ ^ 2 / 2) ↔
      ∀ i, A.singularValues i ≠ 0 → μ ≤ A.singularValues i ^ 2 := by
  have := FiniteDimensional.completeSpace ℝ F
  have := FiniteDimensional.completeSpace ℝ A.range
  rw [← A.mul_norm_sq_le_norm_adjoint_sq_iff]
  simpa only [coe_toContinuousLinearMap, coe_toContinuousLinearMap', adjoint_eq_toCLM_adjoint,
    ContinuousLinearMap.coe_coe] using
    A.toContinuousLinearMap.polyakLojasiewicz_leastSquares_iff b (μ := μ)

/-- Any nonnegative lower bound for the nonzero singular values yields a least-squares
Polyak–Łojasiewicz modulus by squaring. -/
theorem polyakLojasiewicz_leastSquares (A : E →ₗ[ℝ] F) (b : F) {σ : ℝ} (hσ : 0 ≤ σ)
    (hmin : ∀ i, A.singularValues i ≠ 0 → σ ≤ A.singularValues i) :
    PolyakLojasiewicz (σ ^ 2) (fun x ↦ ‖A x - b‖ ^ 2 / 2) :=
  (A.polyakLojasiewicz_leastSquares_iff b).mpr fun i hi ↦ pow_le_pow_left₀ hσ (hmin i hi) 2

end LinearMap
