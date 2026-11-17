/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Isoperimetric
import TauCeti.Analysis.Complex.ClosedAnnulus
import TauCeti.Topology.MetricSpace.Annulus

/-!
# Boundary control of energy on annuli and half-annuli

A solution of `∂ₜu = J(u) ∂ₛu` on a closed annulus has its real-direction energy bounded by
its two boundary-loop energies, provided a constant symplectic form uniformly tames `J` along
its image. The norm is measured in a fixed compatible inner product, not a metric varying
with `J`. No regularity of `J` beyond the equation and the quantitative taming bound is needed.

The estimate combines the annular Stokes formula with the symplectic isoperimetric inequality.
It does not assume an extension over the inner disc. In a punctured-disc argument, sending the
inner radius to zero and controlling the inner boundary term gives the boundary-energy bound
used to prove energy decay. This file supplies the annular estimate, not that limiting argument
or removal of singularities.

The same holds on a closed upper half-annulus whose two straight boundary segments are mapped into
an isotropic subspace, as for a half-disc with Lagrangian boundary condition along the real axis,
with the energies of the two boundary half-circles in place of the boundary loops
(`TauCeti.SymplecticForm.integral_norm_fderiv_one_sq_halfAnnulus_le`). This is the corresponding
step for boundary punctures.

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

/-- On a compact set where `u` is `C²`, solves `∂ₜu = J(u) ∂ₛu` and has `ω` taming `J(u)` with
constant `c`, the real-direction energy times `c` is at most the symplectic area. -/
private theorem mul_integral_norm_fderiv_one_sq_le_integral_apply {u : ℂ → V}
    {J : V → V →L[ℝ] V} {A : Set ℂ} (hA : IsCompact A) {c : ℝ}
    (hu : ∀ z ∈ A, ContDiffAt ℝ 2 u z) (hCR : ∀ z ∈ A, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (htame : ∀ z ∈ A, ∀ v : V, c * ‖v‖ ^ 2 ≤ ω v (J (u z) v)) :
    c * ∫ z in A, ‖fderiv ℝ u z 1‖ ^ 2 ≤ ∫ z in A, ω (fderiv ℝ u z 1) (fderiv ℝ u z I) := by
  have hDu : ContinuousOn (fderiv ℝ u) A := fun z hz ↦
    ((hu z hz).continuousAt_fderiv (by norm_num)).continuousWithinAt
  have hE : IntegrableOn (fun z ↦ c * ‖fderiv ℝ u z 1‖ ^ 2) A :=
    (continuousOn_const.mul ((hDu.clm_apply continuousOn_const).norm.pow 2)).integrableOn_compact
      hA
  have harea := ω.integrableOn_fderiv_apply_of_contDiffAt hA fun z hz ↦ (hu z hz).of_le one_le_two
  have hmono := setIntegral_mono_on hE harea hA.measurableSet fun z hz ↦ by
    rw [hCR z hz]
    exact htame z hz (fderiv ℝ u z 1)
  rwa [integral_const_mul] at hmono

/-- For a uniformly tamed solution of `∂ₜu = J(u) ∂ₛu` on an annulus, the integral of
`‖∂ₛu‖²` is at most the sum of the two boundary-loop energies divided by twice the taming
constant. Both loops are parametrized counterclockwise on `[-π, π]`.

The inner product is the fixed compatible metric of `(ω, J₀)`, while `J` may vary with the
target point. Smoothness is required only near the closed annulus, not in its hole. -/
theorem integral_norm_fderiv_one_sq_annulus_le {u : ℂ → V} {J : V → V →L[ℝ] V}
    (z₀ : ℂ) {a b c : ℝ} (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫)
    (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 < c)
    (hu : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ContDiffAt ℝ 2 u z)
    (hCR : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b},
      fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (htame : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ∀ v : V,
      c * ‖v‖ ^ 2 ≤ ω v (J (u z) v)) :
    (∫ z in {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ‖fderiv ℝ u z 1‖ ^ 2) ≤
      ((∫ θ in -π..π, ‖deriv (fun θ ↦ u (circleMap z₀ b θ)) θ‖ ^ 2) +
        ∫ θ in -π..π, ‖deriv (fun θ ↦ u (circleMap z₀ a θ)) θ‖ ^ 2) / (2 * c) := by
  let A := {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}
  have hcompact : IsCompact A := isCompact_setOf_le_norm_sub_le z₀ a b
  have hmono := mul_integral_norm_fderiv_one_sq_le_integral_apply hcompact hu hCR htame
  have hbound := ω.abs_integral_fderiv_apply_annulus_le z₀ hg ha hab hu
  have h := hmono.trans ((le_abs_self _).trans hbound)
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- For a uniformly tamed solution of `∂ₜu = J(u) ∂ₛu` on a closed upper half-annulus whose two
straight boundary segments `z₀ ± r`, `a ≤ r ≤ b`, map into an isotropic subspace `L`, the
integral of `‖∂ₛu‖²` is at most `π / 4` times the sum of the energies of the two boundary
half-circles, parametrized counterclockwise on `[0, π]`, divided by the taming constant.

This is the boundary counterpart of `integral_norm_fderiv_one_sq_annulus_le`, for holomorphic
half-discs with Lagrangian boundary condition on the real axis. -/
theorem integral_norm_fderiv_one_sq_halfAnnulus_le {L : Submodule ℝ V} (hL : ω.IsIsotropic L)
    {u : ℂ → V} {J : V → V →L[ℝ] V} (z₀ : ℂ) {a b c : ℝ} (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫)
    (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 < c)
    (hu : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b ∧ 0 ≤ (z - z₀).im}, ContDiffAt ℝ 2 u z)
    (hCR : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b ∧ 0 ≤ (z - z₀).im},
      fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (htame : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b ∧ 0 ≤ (z - z₀).im}, ∀ v : V,
      c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (huL : ∀ r ∈ Icc a b, u (z₀ + r) ∈ L ∧ u (z₀ - r) ∈ L) :
    (∫ z in {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b ∧ 0 ≤ (z - z₀).im}, ‖fderiv ℝ u z 1‖ ^ 2) ≤
      π * ((∫ θ in 0..π, ‖deriv (fun θ ↦ u (circleMap z₀ b θ)) θ‖ ^ 2) +
        ∫ θ in 0..π, ‖deriv (fun θ ↦ u (circleMap z₀ a θ)) θ‖ ^ 2) / (4 * c) := by
  let A := {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b ∧ 0 ≤ (z - z₀).im}
  have hcompact : IsCompact A := isCompact_halfAnnulus z₀ a b
  have hmono := mul_integral_norm_fderiv_one_sq_le_integral_apply hcompact hu hCR htame
  have hbound := ω.abs_integral_fderiv_apply_halfAnnulus_le hL z₀ hg ha hab hu huL
  have h := hmono.trans ((le_abs_self _).trans hbound)
  rw [le_div_iff₀ (by positivity)]
  linarith

end TauCeti.SymplecticForm
