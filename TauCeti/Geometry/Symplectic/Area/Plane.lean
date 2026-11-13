/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Area.PuncturedDisc
public import TauCeti.Geometry.Symplectic.JHolomorphic.Line
import TauCeti.Analysis.Calculus.FDeriv.Integrable
import TauCeti.Analysis.Complex.Conformal.Area
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Finite-energy planes in a symplectic vector space have zero area

Let `(V, ω)` be a symplectic vector space and let `u : ℂ → V` be a `C²` map of finite energy, in
the sense that `‖du‖²` is integrable over the plane. Then the symplectic area of `u` vanishes:

`∫_ℂ ω(∂ₛu, ∂ₜu) = 0`

(`TauCeti.SymplecticForm.integral_fderiv_apply_eq_zero`). This is Stokes' formula on the sphere
`ℂ ∪ {∞}` for the exact form `ω = dλ`, `λₓ = ½ ω(x, ·)`, but no extension of `u` across `∞` is
assumed, and `u` need not be bounded. The area of the disc of radius `R` is the action of its
boundary circle for `λ`, that is half the integral of `ω(u, ∂_θ u)` along that circle
(`TauCeti.SymplecticForm.integral_fderiv_apply_closedBall`). In the coordinate `w = z⁻¹` at
infinity the map `w ↦ u w⁻¹` has finite energy on the punctured unit disc, because the inversion
is conformal (`TauCeti.integrableOn_norm_fderiv_comp_inv_sq_iff`), and its circle of radius `r` is
the circle of `u` of radius `r⁻¹` traversed backwards
(`TauCeti.SymplecticForm.integral_apply_deriv_comp_inv_circleMap`). Finite energy near the
puncture gives arbitrarily small circles with arbitrarily small action
(`TauCeti.SymplecticForm.exists_tendsto_integral_apply_circleMap_nhds_zero`). So `u` has
arbitrarily large circles with arbitrarily small action, and the areas of the discs they bound
converge to the total area.

The same holds in the real coordinates `ℝ × ℝ ≃ ℂ` used for Floer equations
(`TauCeti.SymplecticForm.integral_fderiv_stdComplexLine_eq_zero`). Since the area density of a
pseudoholomorphic map is nonnegative, it follows that finite-energy pseudoholomorphic planes in a
symplectic vector space are constant; this consequence is proved in
`TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Rigidity`.

## Main results

* `TauCeti.SymplecticForm.integral_apply_deriv_comp_inv_circleMap`: inversion reverses the
  boundary circles.
* `TauCeti.SymplecticForm.integral_fderiv_apply_eq_zero`: a `C²` finite-energy map `ℂ → V` has
  zero symplectic area.
* `TauCeti.SymplecticForm.integral_fderiv_stdComplexLine_eq_zero`: the same for maps
  `ℝ × ℝ → V`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 4.1
  (energy and area) and Section 4.5 (the end of a finite-energy plane).
-/

public section

open Complex Filter MeasureTheory Metric Set Topology
open scoped Real

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace SymplecticForm

variable [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- **Inversion reverses the boundary circles.** The circle of radius `r` of `w ↦ u w⁻¹` is the
circle of radius `r⁻¹` of `u` traversed backwards, so the integrals of `ω(u, ∂_θ u)` along them,
twice their actions for the primitive `λₓ = ½ ω(x, ·)`, are opposite. -/
theorem integral_apply_deriv_comp_inv_circleMap (ω : SymplecticForm V) (u : ℂ → V) (r : ℝ) :
    ∫ θ in -π..π, ω (u (circleMap 0 r θ)⁻¹) (deriv (fun θ ↦ u (circleMap 0 r θ)⁻¹) θ) =
      -∫ θ in -π..π, ω (u (circleMap 0 r⁻¹ θ)) (deriv (fun θ ↦ u (circleMap 0 r⁻¹ θ)) θ) := by
  simp_rw [circleMap_zero_inv]
  simp only [deriv_comp_neg (fun θ ↦ u (circleMap 0 r⁻¹ θ)), map_neg, intervalIntegral.integral_neg,
    intervalIntegral.integral_comp_neg (fun θ ↦ ω (u (circleMap 0 r⁻¹ θ))
      (deriv (fun θ ↦ u (circleMap 0 r⁻¹ θ)) θ)), neg_neg]

/-- **A finite-energy plane has zero symplectic area.** For a `C²` map `u : ℂ → V` into a
symplectic vector space with `‖du‖²` integrable over the plane, the integral of the area density
`ω(∂ₛu, ∂ₜu)` over the plane is zero. No boundedness of `u` and no extension across `∞` is
assumed. -/
theorem integral_fderiv_apply_eq_zero (ω : SymplecticForm V) {u : ℂ → V} (hu : ContDiff ℝ 2 u)
    (henergy : Integrable fun z ↦ ‖fderiv ℝ u z‖ ^ 2) :
    ∫ z, ω (fderiv ℝ u z 1) (fderiv ℝ u z I) = 0 := by
  let action (r : ℝ) := ∫ θ in -π..π, ω (u (circleMap 0 r θ))
    (deriv (fun θ ↦ u (circleMap 0 r θ)) θ)
  -- The map `w ↦ u w⁻¹` has finite energy on the punctured unit disc.
  have hv : ∀ w ∈ {w : ℂ | 0 < ‖w - 0‖ ∧ ‖w - 0‖ ≤ 1}, ContDiffAt ℝ 1 (fun w ↦ u w⁻¹) w :=
    fun w hw ↦ (hu.contDiffAt.of_le one_le_two).comp w
      (contDiffAt_inv ℝ (sub_ne_zero.1 (norm_pos_iff.1 hw.1)))
  have henergy' : IntegrableOn (fun w ↦ ‖fderiv ℝ (fun w ↦ u w⁻¹) w‖ ^ 2)
      {w : ℂ | 0 < ‖w - 0‖ ∧ ‖w - 0‖ ≤ 1} :=
    (integrableOn_norm_fderiv_comp_inv_sq_iff (measurableSet_puncturedClosedDisc 0 1)).2
      henergy.integrableOn
  -- So `u` has arbitrarily large circles of arbitrarily small action.
  obtain ⟨r, hr, hr0, hlim⟩ :=
    ω.exists_tendsto_integral_apply_circleMap_nhds_zero 0 one_pos hv henergy'
  have hR : Tendsto (fun n ↦ (r n)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp
      (tendsto_nhdsWithin_iff.2 ⟨hr0, Eventually.of_forall fun n ↦ (hr n).1⟩)
  have haction : Tendsto (fun n ↦ action (r n)⁻¹) atTop (𝓝 0) := by
    simpa only [integral_apply_deriv_comp_inv_circleMap, neg_neg, neg_zero] using hlim.neg
  -- The areas of the discs these circles bound converge to the total area.
  have harea : Integrable fun z ↦ ω (fderiv ℝ u z 1) (fderiv ℝ u z I) :=
    integrableOn_univ.1 (ω.integrableOn_fderiv_apply_of_integrableOn_norm_fderiv_sq 1 I
      henergy.integrableOn)
  have hdisc (n : ℕ) : ∫ z in closedBall (0 : ℂ) (r n)⁻¹, ω (fderiv ℝ u z 1) (fderiv ℝ u z I) =
      (1 / 2 : ℝ) * action (r n)⁻¹ :=
    ω.integral_fderiv_apply_closedBall 0 (inv_pos.2 (hr n).1) fun z _ ↦ hu.contDiffAt
  refine tendsto_nhds_unique
    ((aecover_closedBall (x := (0 : ℂ)) hR).integral_tendsto_of_countably_generated harea) ?_
  simpa only [hdisc, mul_zero] using haction.const_mul (1 / 2 : ℝ)

/-- **A finite-energy plane has zero symplectic area, in real coordinates.** For a `C²` map
`u : ℝ × ℝ → V` into a symplectic vector space with `‖du‖²` integrable over the plane, the
integral of `ω(∂ₛu, ∂ₜu)` over the plane is zero. -/
theorem integral_fderiv_stdComplexLine_eq_zero (ω : SymplecticForm V) {u : ℝ × ℝ → V}
    (hu : ContDiff ℝ 2 u) (henergy : Integrable fun z ↦ ‖fderiv ℝ u z‖ ^ 2) :
    ∫ z, ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) = 0 := by
  -- `equivRealProdCLM` and `measurableEquivRealProd` are the same map `z ↦ (z.re, z.im)`.
  have h := ω.integral_fderiv_apply_eq_zero (hu.comp equivRealProdCLM.contDiff)
    ((integrable_norm_fderiv_comp_sq_iff equivRealProdCLM volume_preserving_equiv_real_prod).2
      henergy)
  simp only [fderiv_comp_equivRealProdCLM_one, fderiv_comp_equivRealProdCLM_I] at h
  rwa [← volume_preserving_equiv_real_prod.integral_comp' fun z ↦
    ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)]

end SymplecticForm

end TauCeti
