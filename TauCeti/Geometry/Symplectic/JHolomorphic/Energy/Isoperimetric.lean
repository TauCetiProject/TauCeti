/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Isoperimetric
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

/-!
# Boundary control of energy on an annulus

A solution of `∂ₜu = J(u) ∂ₛu` on a closed annulus has its real-direction energy bounded by
its two boundary-loop energies, provided a constant symplectic form uniformly tames `J` along
its image. The norm is measured in a fixed compatible inner product, not a metric varying
with `J`. No regularity of `J` beyond the equation and the quantitative taming bound is needed.

The estimate combines the annular Stokes formula with the symplectic isoperimetric inequality.
It does not assume an extension over the inner disc. In a punctured-disc argument, sending the
inner radius to zero and controlling the inner boundary term gives the boundary-energy bound
used to prove energy decay. This file supplies the annular estimate, not that limiting argument
or removal of singularities.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Sections 4.4 and 4.5.
-/

public section

open Complex MeasureTheory Set
open scoped Real RealInnerProductSpace

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}

/-- For a uniformly tamed solution of `∂ₜu = J(u) ∂ₛu` on an annulus, the integral of
`‖∂ₛu‖²` is at most the sum of the two boundary-loop energies divided by twice the taming
constant. Both loops are parametrized counterclockwise on `[-π, π]`.

The inner product is the fixed compatible metric of `(ω, J₀)`, while `J` may vary with the
target point. Smoothness is required only near the closed annulus, not in its hole. -/
theorem integral_norm_fderiv_one_sq_annulus_le {u : ℂ → V} {J : V → V →L[ℝ] V}
    (z₀ : ℂ) {a b c : ℝ} (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫)
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c)
    (hu : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ContDiffAt ℝ 2 u z)
    (hCR : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b},
      fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (htame : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ∀ v : V,
      c * ‖v‖ ^ 2 ≤ ω v (J (u z) v)) :
    (∫ z in {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ‖fderiv ℝ u z 1‖ ^ 2) ≤
      ((∫ θ in -π..π, ‖deriv (fun θ ↦ u (circleMap z₀ b θ)) θ‖ ^ 2) +
        ∫ θ in -π..π, ‖deriv (fun θ ↦ u (circleMap z₀ a θ)) θ‖ ^ 2) / (2 * c) := by
  let A := {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}
  have hclosed : IsClosed A :=
    (isClosed_le continuous_const (continuous_id.sub continuous_const).norm).inter
      (isClosed_le (continuous_id.sub continuous_const).norm continuous_const)
  have hcompact : IsCompact A := (isCompact_closedBall z₀ b).of_isClosed_subset hclosed
    (fun z hz ↦ by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz.2)
  have hDu : ContinuousOn (fderiv ℝ u) A := fun z hz ↦
    ((hu z hz).continuousAt_fderiv (by norm_num)).continuousWithinAt
  have hE : IntegrableOn (fun z ↦ c * ‖fderiv ℝ u z 1‖ ^ 2) A :=
    (continuousOn_const.mul ((hDu.clm_apply continuousOn_const).norm.pow 2)).integrableOn_compact
      hcompact
  have harea : IntegrableOn (fun z ↦ ω (fderiv ℝ u z 1) (fderiv ℝ u z I)) A := by
    simpa only [Function.comp_apply, LinearMap.toContinuousBilinearMap_apply] using
      ((ω.toBilinForm.toContinuousBilinearMap.continuous.comp_continuousOn
        (hDu.clm_apply continuousOn_const)).clm_apply
        (hDu.clm_apply continuousOn_const)).integrableOn_compact hcompact
  have hmono := setIntegral_mono_on hE harea hclosed.measurableSet fun z hz ↦ by
    rw [hCR z hz]
    exact htame z hz (fderiv ℝ u z 1)
  rw [integral_const_mul] at hmono
  have hbound := ω.abs_integral_fderiv_apply_annulus_le z₀ hg ha hab hu
  have h := hmono.trans ((le_abs_self _).trans hbound)
  rw [le_div_iff₀ (by positivity)]
  linarith

end TauCeti.SymplecticForm
