/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex
public import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.MeasureTheory.Integral.DivergenceTheorem

/-!
# Symplectic area of a map on an annulus

For a constant symplectic form `ω`, the primitive `λₓ(v) = ½ ω(x, v)` identifies the
symplectic area of a `C²` map on a closed annulus with the difference of its boundary actions.
The outer and inner circles are both parametrized counterclockwise on `[-π, π]`, and the inner
action is subtracted. No extension across the inner disc is needed. Together with the
isoperimetric inequality for the boundary loops, this is the Stokes step used in energy decay
and removal of singularities for holomorphic curves.

The bilinear Green formula `ContinuousLinearMap.integral_bilinear_fderiv_sub_annulus` supplies
the identity, and alternation of `ω` supplies the factor `½`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 4.5.
-/

public section

open MeasureTheory Set Complex
open scoped Real

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Stokes' formula for symplectic area on an annulus.** The pullback area of a `C²` map is
the outer boundary action minus the inner boundary action for the primitive `λₓ(v) = ½ ω(x, v)`.
This identity does not require any regularity on the inner disc or a holomorphicity hypothesis. -/
theorem integral_fderiv_apply_annulus [FiniteDimensional ℝ V]
    (ω : SymplecticForm V) {u : ℂ → V} (z₀ : ℂ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hu : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ContDiffAt ℝ 2 u z) :
    ∫ z in {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b},
      ω (fderiv ℝ u z 1) (fderiv ℝ u z I) =
      (1 / 2 : ℝ) * ((∫ θ in -π..π, ω (u (circleMap z₀ b θ))
        (deriv (fun θ ↦ u (circleMap z₀ b θ)) θ)) -
      ∫ θ in -π..π, ω (u (circleMap z₀ a θ))
        (deriv (fun θ ↦ u (circleMap z₀ a θ)) θ)) := by
  let B : V →L[ℝ] V →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp ω.toBilinForm)
  have hB (x y : V) : B x y = ω x y := by simp [B]
  have hskew (x y : V) : B x y - B y x = 2 * ω x y := by
    rw [hB, hB, ← ω.neg_eq]
    ring
  have hcircle (r : ℝ) (hr : r ∈ Icc a b) (θ : ℝ) :
      deriv (fun θ ↦ u (circleMap z₀ r θ)) θ =
        fderiv ℝ u (circleMap z₀ r θ) (circleMap 0 r θ * I) := by
    have hm : circleMap z₀ r θ ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b} := by
      simpa only [mem_ofPred_eq, circleMap_sub_center, norm_circleMap_zero,
        abs_of_nonneg (le_trans ha.le hr.1)] using (mem_Icc.mp hr)
    exact (((hu _ hm).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt θ
      (hasDerivAt_circleMap z₀ r θ)).deriv
  have hgreen := B.integral_bilinear_fderiv_sub_annulus z₀ ha hab hu
  simp only [hskew, integral_const_mul] at hgreen
  simp only [hB, ← hcircle b ⟨hab, le_rfl⟩, ← hcircle a ⟨le_rfl, hab⟩] at hgreen
  linarith

end TauCeti.SymplecticForm
