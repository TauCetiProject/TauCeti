/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Isoperimetric
import TauCeti.Analysis.RCLike.OperatorNorm
import TauCeti.Analysis.SpecialFunctions.Complex.CircleMap
import TauCeti.Topology.MetricSpace.Annulus

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

Along a circle, the equation and a bound `‖J(u)‖ ≤ M` bound the angular energy of the boundary
loop by `(1 + M)² r²` times the circle integral of `‖∂ₛu‖²`
(`TauCeti.integral_norm_deriv_comp_circleMap_sq_le`). Combined with the annular estimate, this
bounds the energy of the annulus by the boundary densities of its two circles
(`TauCeti.SymplecticForm.two_mul_mul_integral_norm_fderiv_one_sq_annulus_le`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Sections 4.4 and 4.5.
-/

public section

open Complex MeasureTheory Set
open scoped Real RealInnerProductSpace

namespace TauCeti

section Angular

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {u : ℂ → V} {J : V → V →L[ℝ] V} {z₀ : ℂ} {M : ℝ}

/-- The angular energy of the loop `θ ↦ u (z₀ + r e^{iθ})` is at most `(1 + M)² r²` times the
circle integral of `‖∂ₛu‖²`, for a solution of `∂ₜu = J(u) ∂ₛu` along the circle with
`‖J(u)‖ ≤ M`. This converts the boundary-loop energies of the isoperimetric estimates into the
boundary densities of radial energy integrals. -/
theorem integral_norm_deriv_comp_circleMap_sq_le {r : ℝ} (hr : 0 ≤ r)
    (hu : ∀ θ, ContDiffAt ℝ 1 u (circleMap z₀ r θ))
    (hCR : ∀ θ, fderiv ℝ u (circleMap z₀ r θ) I =
      J (u (circleMap z₀ r θ)) (fderiv ℝ u (circleMap z₀ r θ) 1))
    (hJ : ∀ θ, ‖J (u (circleMap z₀ r θ))‖ ≤ M) :
    (∫ θ in -π..π, ‖deriv (fun θ ↦ u (circleMap z₀ r θ)) θ‖ ^ 2) ≤
      (1 + M) ^ 2 * r ^ 2 *
        ∫ θ in -π..π, ‖fderiv ℝ u (circleMap z₀ r θ) 1‖ ^ 2 := by
  have hdu : Continuous (fun θ ↦ fderiv ℝ u (circleMap z₀ r θ)) :=
    continuous_iff_continuousAt.mpr fun θ ↦
      (hu θ).continuousAt_fderiv (by norm_num) |>.comp
        (continuous_circleMap z₀ r).continuousAt
  have hd (θ : ℝ) := ((hu θ).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt θ
    (hasDerivAt_circleMap z₀ r θ)
  have heq (θ : ℝ) : deriv (fun θ ↦ u (circleMap z₀ r θ)) θ =
      fderiv ℝ u (circleMap z₀ r θ) (circleMap 0 r θ * I) := hd θ |>.deriv
  have hcont : Continuous (fun θ ↦ ‖deriv (fun θ ↦ u (circleMap z₀ r θ)) θ‖ ^ 2) := by
    simp_rw [heq]
    exact (hdu.clm_apply ((continuous_circleMap 0 r).mul continuous_const)).norm.pow 2
  have hbcont : Continuous (fun θ ↦ ‖fderiv ℝ u (circleMap z₀ r θ) 1‖ ^ 2) :=
    (hdu.clm_apply continuous_const).norm.pow 2
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
    (hcont.intervalIntegrable _ _) ((hbcont.const_mul _).intervalIntegrable _ _)
  intro θ _
  have hs : ‖deriv (fun θ ↦ u (circleMap z₀ r θ)) θ‖ ≤
      (1 + M) * r * ‖fderiv ℝ u (circleMap z₀ r θ) 1‖ := by
    rw [heq]
    calc _ ≤ ‖fderiv ℝ u (circleMap z₀ r θ)‖ * ‖circleMap 0 r θ * I‖ :=
          (fderiv ℝ u (circleMap z₀ r θ)).le_opNorm _
      _ ≤ ((1 + M) * ‖fderiv ℝ u (circleMap z₀ r θ) 1‖) * r := by
          rw [norm_mul, norm_I, mul_one, norm_circleMap_zero, abs_of_nonneg hr]
          gcongr
          exact (fderiv ℝ u (circleMap z₀ r θ)).norm_le_of_apply_I_eq (hCR θ) (hJ θ) le_rfl
      _ = _ := by ring
  calc
    _ ≤ ((1 + M) * r * ‖fderiv ℝ u (circleMap z₀ r θ) 1‖) ^ 2 := by
      gcongr
    _ = _ := by ring

end Angular

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}

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
  have hDu : ContinuousOn (fderiv ℝ u) A := fun z hz ↦
    ((hu z hz).continuousAt_fderiv (by norm_num)).continuousWithinAt
  have hE : IntegrableOn (fun z ↦ c * ‖fderiv ℝ u z 1‖ ^ 2) A :=
    (continuousOn_const.mul ((hDu.clm_apply continuousOn_const).norm.pow 2)).integrableOn_compact
      hcompact
  have harea := ω.integrableOn_fderiv_apply_of_contDiffAt hcompact fun z hz ↦
    (hu z hz).of_le one_le_two
  have hmono := setIntegral_mono_on hE harea hcompact.measurableSet fun z hz ↦ by
    rw [hCR z hz]
    exact htame z hz (fderiv ℝ u z 1)
  rw [integral_const_mul] at hmono
  have hbound := ω.abs_integral_fderiv_apply_annulus_le z₀ hg ha hab hu
  have h := hmono.trans ((le_abs_self _).trans hbound)
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- **Boundary control of the energy of an annulus.** For a uniformly tamed solution of
`∂ₜu = J(u) ∂ₛu` on the annulus `a ≤ |z - z₀| ≤ b` with `‖J(u)‖ ≤ M`, twice the taming constant
times the energy `∫ ‖∂ₛu‖²` is at most `(1 + M)²` times the sum of the boundary densities
`r (r ∫ ‖∂ₛu(z₀ + r e^{iθ})‖² dθ)` of the two boundary circles. The inner product is the fixed
compatible metric of `(ω, J₀)`. -/
theorem two_mul_mul_integral_norm_fderiv_one_sq_annulus_le {u : ℂ → V} {J : V → V →L[ℝ] V}
    {z₀ : ℂ} {a b c M : ℝ} (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hc : 0 < c) (ha : 0 ≤ a) (hab : a ≤ b)
    (hu : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ContDiffAt ℝ 2 u z)
    (hCR : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b},
      fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (htame : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ∀ v : V,
      c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (hJ : ∀ z ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ‖J (u z)‖ ≤ M) :
    2 * c * (∫ z in {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, ‖fderiv ℝ u z 1‖ ^ 2) ≤
      (1 + M) ^ 2 * (b * (b * ∫ θ in -π..π, ‖fderiv ℝ u (circleMap z₀ b θ) 1‖ ^ 2) +
        a * (a * ∫ θ in -π..π, ‖fderiv ℝ u (circleMap z₀ a θ) 1‖ ^ 2)) := by
  have hmem (r : ℝ) (hr : r ∈ Icc a b) (θ : ℝ) :=
    circleMap_mem_setOf_le_norm_sub_le (z₀ := z₀) ha hr θ
  have hbound := ω.integral_norm_fderiv_one_sq_annulus_le z₀ hg ha hab hc hu hCR htame
  have hb := integral_norm_deriv_comp_circleMap_sq_le (ha.trans hab)
    (fun θ ↦ (hu _ (hmem b ⟨hab, le_rfl⟩ θ)).of_le one_le_two)
    (fun θ ↦ hCR _ (hmem b ⟨hab, le_rfl⟩ θ)) (fun θ ↦ hJ _ (hmem b ⟨hab, le_rfl⟩ θ))
  have ha' := integral_norm_deriv_comp_circleMap_sq_le ha
    (fun θ ↦ (hu _ (hmem a ⟨le_rfl, hab⟩ θ)).of_le one_le_two)
    (fun θ ↦ hCR _ (hmem a ⟨le_rfl, hab⟩ θ)) (fun θ ↦ hJ _ (hmem a ⟨le_rfl, hab⟩ θ))
  rw [le_div_iff₀ (by positivity)] at hbound
  nlinarith

end SymplecticForm

end TauCeti
