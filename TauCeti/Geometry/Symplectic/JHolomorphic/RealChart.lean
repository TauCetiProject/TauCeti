/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Line
public import TauCeti.Analysis.Complex.RealChart
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Normed.Field.Inversion

/-!
# Holomorphic maps of the plane in real coordinates

A map `f : ℂ → ℂ` with a complex derivative becomes, read in the real coordinates `ℝ × ℝ` through
`TauCeti.Complex.realChart`, a map of the standard complex line whose real derivative is complex
linear for `AlmostComplexStructure.product ℝ`. This is the source-side holomorphicity used when a
holomorphic change of domain coordinates is applied to a `J`-holomorphic map or to its energy.

Precomposing a map `u` of the standard complex line by such a change of coordinates therefore
preserves the Cauchy–Riemann equation `du ∘ i = J ∘ du`. For the chart `w ↦ w⁻¹` at the point at
infinity of the Riemann sphere this says: a map that is `J`-holomorphic outside a disc of radius
`T` reads, in this chart, as a map `w` that is `J`-holomorphic on the punctured disc of radius
`T⁻¹`. If `w` extends `C¹` across the puncture, the equation holds there too, since complex
linearity of the derivative is a closed condition.

## Main results

* `TauCeti.isComplexLinearMap_fderiv_realChart`: a map of the plane with a complex derivative has
  complex-linear derivative in the real coordinates.
* `TauCeti.isComplexLinearMap_fderiv_of_forall_ne`: the Cauchy–Riemann equation for a `C¹` map
  extends across a point.
* `TauCeti.isComplexLinearMap_fderiv_of_eq_comp_inv`: a map `J`-holomorphic outside a disc,
  read in the chart `w ↦ w⁻¹` at infinity, is `J`-holomorphic on the inverted disc wherever this
  expression is `C¹`, the point at infinity included.
-/

public section

open Filter Set Metric Topology
open TauCeti.Complex (realChart fderiv_realChart_apply hasFDerivAt_realChart
  equivRealProdCLM_symm_realChart)

namespace TauCeti

/-- A map of the plane with a complex derivative is holomorphic in real coordinates: the derivative
of its real chart is complex linear. -/
theorem isComplexLinearMap_fderiv_realChart {f : ℂ → ℂ} {f' : ℂ} {z : ℝ × ℝ}
    (hf : HasDerivAt f f' (Complex.equivRealProdCLM.symm z)) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) (AlmostComplexStructure.product ℝ)
      (fderiv ℝ (realChart f) z : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) := by
  rw [isComplexLinearMap_iff_apply]
  intro v
  simp only [ContinuousLinearMap.coe_coe, fderiv_realChart_apply hf,
    AlmostComplexStructure.product_apply]
  apply Prod.ext <;>
    simp [Complex.equivRealProdCLM_symm_apply, Complex.mul_re, Complex.mul_im] <;> ring

section Extension

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {J : AlmostComplexStructure V}

/-- **The Cauchy–Riemann equation extends across a point.** If `w` is `C¹` on an open set `Ω` and
its derivative is complex linear at every point of `Ω` other than `y₀ ∈ Ω`, then it is complex
linear at `y₀` as well. -/
theorem isComplexLinearMap_fderiv_of_forall_ne {w : ℝ × ℝ → V} {Ω : Set (ℝ × ℝ)}
    (hΩ : IsOpen Ω) (hw : ContDiffOn ℝ 1 w Ω) {y₀ : ℝ × ℝ} (hy₀ : y₀ ∈ Ω)
    (h : ∀ y ∈ Ω, y ≠ y₀ → IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (fderiv ℝ w y : ℝ × ℝ →ₗ[ℝ] V)) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J (fderiv ℝ w y₀ : ℝ × ℝ →ₗ[ℝ] V) := by
  rw [isComplexLinearMap_stdComplexLine_iff]
  -- The defect `∂ₜw - J ∂ₛw` is continuous at `y₀` and vanishes on a punctured neighbourhood.
  have hc := (hw.continuousOn_fderiv_of_isOpen hΩ le_rfl).continuousAt (hΩ.mem_nhds hy₀)
  have hcont : ContinuousAt
      (fun y ↦ fderiv ℝ w y stdComplexLineImag - J (fderiv ℝ w y stdComplexLineReal)) y₀ :=
    (hc.clm_apply continuousAt_const).sub ((J.toLinearMap.continuous_of_finiteDimensional
      ).continuousAt.comp (hc.clm_apply continuousAt_const))
  have hev : ∀ᶠ y in 𝓝[≠] y₀,
      fderiv ℝ w y stdComplexLineImag - J (fderiv ℝ w y stdComplexLineReal) = 0 := by
    filter_upwards [nhdsWithin_le_nhds (hΩ.mem_nhds hy₀), self_mem_nhdsWithin] with y hy hne
    rw [sub_eq_zero]
    simpa using (isComplexLinearMap_stdComplexLine_iff _).1 (h y hy hne)
  simpa [sub_eq_zero] using tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_const_nhds.congr' (hev.mono fun y hy ↦ hy.symm))

/-- **Maps holomorphic near infinity, in the chart at infinity.** Let `u` be differentiable and
`J`-holomorphic at every point `z` with `‖z‖ > T` (in complex coordinates), and let `w` be `C¹` on
an open set `Ω` of the disc `‖y‖ < T⁻¹`, with `w y = u (y⁻¹)` for `y ≠ 0`. Then `w` is
`J`-holomorphic on all of `Ω`, including at `0`, the point at infinity. -/
theorem isComplexLinearMap_fderiv_of_eq_comp_inv {u w : ℝ × ℝ → V} {Ω : Set (ℝ × ℝ)} {T : ℝ}
    (hΩ : IsOpen Ω) (hΩT : Ω ⊆ Complex.equivRealProdCLM.symm ⁻¹' ball 0 T⁻¹)
    (hu : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ, DifferentiableAt ℝ u z)
    (hhol : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) J (fderiv ℝ u z : ℝ × ℝ →ₗ[ℝ] V))
    (hw : ContDiffOn ℝ 1 w Ω) (hwu : ∀ y ∈ Ω, y ≠ 0 → w y = u (realChart (fun ζ ↦ ζ⁻¹) y))
    {y : ℝ × ℝ} (hy : y ∈ Ω) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J (fderiv ℝ w y : ℝ × ℝ →ₗ[ℝ] V) := by
  -- Off `0`, `w` agrees near `y` with `u ∘ ι` for the holomorphic inversion `ι`, and `ι y` lies
  -- outside the disc of radius `T`.
  have hoff (y : ℝ × ℝ) (hy : y ∈ Ω) (hy0 : y ≠ 0) : IsComplexLinearMap
      (AlmostComplexStructure.product ℝ) J (fderiv ℝ w y : ℝ × ℝ →ₗ[ℝ] V) := by
    have hy0' : Complex.equivRealProdCLM.symm y ≠ 0 := by simpa using hy0
    have hfar : realChart (fun ζ ↦ ζ⁻¹) y ∈
        Complex.equivRealProdCLM.symm ⁻¹' (closedBall 0 T)ᶜ := by
      rw [mem_preimage, equivRealProdCLM_symm_realChart]
      exact mapsTo_inv_ball_diff_singleton_compl_closedBall T ⟨hΩT hy, hy0'⟩
    have hev : w =ᶠ[𝓝 y] u ∘ realChart (fun ζ ↦ ζ⁻¹) := by
      filter_upwards [(hΩ.sdiff isClosed_singleton).mem_nhds ⟨hy, hy0⟩] with y' hy'
        using hwu y' hy'.1 hy'.2
    have hι := hasDerivAt_inv hy0'
    rw [hev.fderiv_eq, fderiv_comp y (hu _ hfar) (hasFDerivAt_realChart hι).differentiableAt,
      ContinuousLinearMap.toLinearMap_comp]
    exact (hhol _ hfar).comp (isComplexLinearMap_fderiv_realChart hι)
  by_cases hy0 : y = 0
  · subst hy0
    exact isComplexLinearMap_fderiv_of_forall_ne hΩ hw hy fun y' hy' hne ↦ hoff y' hy' hne
  · exact hoff y hy hy0

end Extension

end TauCeti
