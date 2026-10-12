/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Disc
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Radial derivative of energy on a punctured disc

The real-direction energy used in the mean-value and boundary-energy estimates has
radial derivative equal to the circle integral of its density. Only `C¹` regularity
away from the puncture and square integrability of the full differential are required.
In particular, neither a holomorphic equation nor an extension at the puncture is
assumed. The formula supplies the boundary density in radial energy-decay arguments.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Section 4.5.
-/

public section

open Complex MeasureTheory Metric Set
open scoped Real

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The real-direction energy of a `C¹` map on a punctured disc has radial derivative
equal to the boundary integral of `‖∂ₛu‖²`. Square integrability of the operator norm
ensures that this is a genuine finite energy, including at the puncture. -/
theorem hasDerivAt_integral_norm_fderiv_one_sq_ball {u : ℂ → V} {z₀ : ℂ} {R r : ℝ}
    (hu : ContDiffOn ℝ 1 u (ball z₀ R \ {z₀}))
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z‖ ^ 2) (ball z₀ R))
    (hr : r ∈ Ioo 0 R) :
    HasDerivAt (fun t ↦ ∫ z in ball z₀ t, ‖fderiv ℝ u z 1‖ ^ 2)
      (r * ∫ θ in -π..π, ‖fderiv ℝ u (circleMap z₀ r θ) 1‖ ^ 2) r := by
  have hDu := hu.continuousOn_fderiv_of_isOpen
    (isOpen_ball.sdiff isClosed_singleton) le_rfl
  have hcont : ContinuousOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R \ {z₀}) :=
    (hDu.clm_apply continuousOn_const).norm.pow 2
  have hint : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ R) := by
    refine henergy.mono' ?_ (ae_of_all _ fun z ↦ ?_)
    · rw [← Measure.restrict_congr_set (sdiff_null_ae_eq_self (s := ball z₀ R)
        (measure_singleton z₀))]
      exact hcont.aestronglyMeasurable (measurableSet_ball.diff (measurableSet_singleton _))
    · rw [Real.norm_of_nonneg (sq_nonneg _)]
      have h := (fderiv ℝ u z).le_opNorm (1 : ℂ)
      simp only [norm_one, mul_one] at h
      gcongr
  exact hint.hasDerivAt_integral_ball hcont hr

end TauCeti
