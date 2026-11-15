/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Plane.Curvature
public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction.Capped
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
import TauCeti.LinearAlgebra.BilinearMap.Multilinear
import TauCeti.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.MeasureTheory.Integral.PolarCoord
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The energy of a PSS plane in a manifold in terms of the capped action of its end

Let `K` be the perturbation `TauCeti.Floer.PSSPlane.perturbation` of a PSS plane `p`, built from a
period-one Hamiltonian `H` on a finite-dimensional manifold `M` with a nondegenerate two-form `ω`,
such as a closed symplectic manifold, and let `ε = ±1` be the sign of the end of `p`. For a map `u`
of the plane and `R ∈ ℝ`, write `ℓ_R(t) = u(φ(ε R + i t))` for the loop of `u` along the circle
`ε s = R` of the end, where `φ(z) = exp (2π ε z)` is the end lift; this circle bounds the disc
`D_R = {‖w‖ ≤ exp (2πR)}`. The energy identity on discs
(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pssPlanePerturbation_closedBall`)
expresses the energy of `u` over `D_R` through its symplectic area over `D_R`. On a symplectic
vector space this area is `ε` times the loop area of `ℓ_R`
(`TauCeti.Geometry.Symplectic.Floer.Plane.Action`). On a manifold whose symplectic form does not
vanish on spheres, the area of a disc bounding a loop depends on the disc, and the action of a loop
is the capped action `A_H(γ, D) = ∫ D^* ω + ∫₀¹ H(t, γ(t)) dt` of the loop together with a disc
`D` bounding it (`TauCeti.cappedLoopAction`). The plane supplies such a disc for its own end loop.

**The end disc.** The cone `(r, t) ↦ r φ(ε R + i t)` over the circle `ε s = R`
(`TauCeti.Floer.PSSPlane.endDisc`) is, in polar coordinates, the map to radius `exp (2πR) r` and
angle `2π ε t` (`TauCeti.Floer.PSSPlane.endDisc_eq_polarCoord_symm`). For a `C²` map `u`, the map
`u ∘ endDisc R` is a disc in the sense of the capped action, from the constant loop at `u(0)` to
`ℓ_R` (`TauCeti.isLoopCylinder_comp_endDisc`), so the recapping laws of
`TauCeti.cappedLoopAction` apply to it.

**Its area.** The end disc multiplies area by the polar Jacobian `2π ε exp (2πR)² r`, so for every
continuous two-form `φ` and every `C¹` map `u`, the integral of `φ` over `u ∘ endDisc R` on the
unit square is `ε` times the integral of `u^* φ` over `D_R`
(`TauCeti.rectangleIntegral_comp_endDisc`). The sign records the direction in which
the angular coordinate of the end runs around the circle: counterclockwise on the positive plane,
clockwise on the negative plane.

**The energy.** Consequently, for a `C¹` map `u` and `R ≥ 2`,

`∫_{D_R} E = ε A_H(ℓ_R, u ∘ endDisc R) - ∫_ℂ R_K(u)`

(`integral_floerEnergyDensity_pssPlanePerturbation_closedBall_eq_endSign_mul_cappedLoopAction` in
`TauCeti.SmoothTwoForm.IsNondegenerate`). Against any other disc `D` bounding `ℓ_R`, the action
changes by the area of the sphere glued from `D` and `u ∘ endDisc R`
(`integral_floerEnergyDensity_pssPlanePerturbation_closedBall_of_isLoopCylinder`). If `|H| ≤ B`,
the curvature term is at most `B` in absolute value, uniformly in `R`. For a solution of the Floer
equation with almost complex structures tamed by `ω` the energy is nonnegative, which gives the
capped action bound
`-B ≤ ε A_H(ℓ_R, u ∘ endDisc R)`
(`SmoothTwoForm.IsNondegenerate.neg_le_endSign_mul_cappedLoopAction_pssPlanePerturbation`). If these
capped actions converge to `a` as `R → ∞`, then the energy of the solution over the whole plane is
`ε a - ∫_ℂ R_K(u)`, hence at most `ε a + B`, and `-B ≤ ε a`
(`SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_pssPlanePerturbation_eq` and the
results following it). These are the energy and action bounds of PSS planes in a manifold whose
asymptotic orbits carry the cap given by the plane itself: the capped output orbits of negative
planes have action at most `B`, and the energy of a plane is bounded by its capped end action. The
convergence of the capped actions is a hypothesis here; it is not derived from finite energy.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  energy of the perturbed planes of the PSS maps.
* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524, on the action of capped loops.
-/

public noncomputable section

open Set Real Function MeasureTheory Filter Manifold
open scoped Topology

namespace TauCeti

namespace Floer.PSSPlane

/-- The **end disc** of a PSS plane at the circle `ε s = R` of its end: the cone
`(r, t) ↦ r φ(ε R + i t)` over that circle, in the real coordinates `ℝ × ℝ ≃ ℂ` of the plane. Here
`φ(z) = exp (2π ε z)` is the end lift. For `r = 1` it runs once around the circle in the direction
of the angular coordinate `t` of the end, and for `r = 0` it is the pole `0`. -/
def endDisc (p : PSSPlane) (R : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  Complex.equivRealProdCLM (z.1 * p.cylindricalEndLift (↑(p.endSign * R) + ↑z.2 * Complex.I))

theorem endDisc_def (p : PSSPlane) (R : ℝ) (z : ℝ × ℝ) :
    p.endDisc R z =
      Complex.equivRealProdCLM (z.1 * p.cylindricalEndLift (↑(p.endSign * R) + ↑z.2 * Complex.I)) :=
  (rfl)

/-- The centre of the end disc is the pole. -/
@[simp]
theorem endDisc_mk_zero (p : PSSPlane) (R t : ℝ) : p.endDisc R (0, t) = 0 := by
  simp [endDisc_def]

/-- The boundary of the end disc is the circle `ε s = R` of the end, run through by the end lift. -/
@[simp]
theorem endDisc_mk_one (p : PSSPlane) (R t : ℝ) :
    p.endDisc R (1, t) =
      Complex.equivRealProdCLM (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)) := by
  simp [endDisc_def]

/-- The end disc is periodic with period one in the angular coordinate. -/
theorem endDisc_mk_add_one (p : PSSPlane) (R r t : ℝ) :
    p.endDisc R (r, t + 1) = p.endDisc R (r, t) := by
  have h := p.periodic_cylindricalEndLift (p.endSign * R) t
  simp only at h
  rw [endDisc_def, endDisc_def, h]

/-- The end disc runs through the circle of radius `exp (2πR) r` with angle `2π ε t`. -/
theorem endDisc_eq_circleMap (p : PSSPlane) (R : ℝ) (z : ℝ × ℝ) :
    p.endDisc R z = Complex.equivRealProdCLM
      (circleMap 0 (Real.exp (2 * π * R) * z.1) (2 * π * p.endSign * z.2)) := by
  rw [endDisc_def, cylindricalEndLift_eq_circleMap, circleMap_zero, circleMap_zero,
    show p.endSign * (2 * π * z.2) = 2 * π * p.endSign * z.2 by ring, ← mul_assoc,
    mul_comm (z.1 : ℂ), ← Complex.ofReal_mul (Real.exp (2 * π * R)) z.1]

/-- In polar coordinates the end disc is `(r, t) ↦ (exp (2πR) r, 2π ε t)`: radius
`exp (2πR) r` and angle `2π ε t`. -/
theorem endDisc_eq_polarCoord_symm (p : PSSPlane) (R : ℝ) (z : ℝ × ℝ) :
    p.endDisc R z = polarCoord.symm (Real.exp (2 * π * R) * z.1, 2 * π * p.endSign * z.2) := by
  rw [endDisc_eq_circleMap, circleMap_zero, polarCoord_symm_apply]
  ext
  · rw [Complex.equivRealProdCLM_apply, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  · rw [Complex.equivRealProdCLM_apply, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

/-- The end disc is smooth. -/
theorem contDiff_endDisc (p : PSSPlane) (R : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (p.endDisc R) := by
  have hr : ContDiff ℝ n fun z : ℝ × ℝ ↦ (z.1 : ℂ) := Complex.ofRealCLM.contDiff.comp contDiff_fst
  have ht : ContDiff ℝ n fun z : ℝ × ℝ ↦ (↑(p.endSign * R) : ℂ) + ↑z.2 * Complex.I :=
    contDiff_const.add ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const)
  exact Complex.equivRealProdCLM.contDiff.comp
    (hr.mul ((p.contDiff_cylindricalEndLift.restrict_scalars ℝ).comp ht))

/-- The derivative of the end disc, through polar coordinates: the end disc is the inverse polar
map after the linear map `(r, t) ↦ (exp (2πR) r, 2π ε t)`. -/
theorem hasFDerivAt_endDisc (p : PSSPlane) (R : ℝ) (z : ℝ × ℝ) :
    HasFDerivAt (p.endDisc R)
      ((fderivPolarCoordSymm (Real.exp (2 * π * R) * z.1, 2 * π * p.endSign * z.2)).comp
        ((Real.exp (2 * π * R) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
          ((2 * π * p.endSign) • ContinuousLinearMap.snd ℝ ℝ ℝ))) z := by
  have hA : HasFDerivAt (fun z : ℝ × ℝ ↦ (Real.exp (2 * π * R) * z.1, 2 * π * p.endSign * z.2))
      ((Real.exp (2 * π * R) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        ((2 * π * p.endSign) • ContinuousLinearMap.snd ℝ ℝ ℝ)) z :=
    (hasFDerivAt_fst.const_mul _).prodMk (hasFDerivAt_snd.const_mul _)
  rw [show p.endDisc R = _ from funext (endDisc_eq_polarCoord_symm p R)]
  exact (hasFDerivAt_polarCoord_symm _).comp z hA

end Floer.PSSPlane

open Floer Floer.PSSPlane

variable {E G M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {p : PSSPlane}

/-- **The end disc is a disc bounding the end loop.** For a `C²` map `u` of the plane, the
restriction `u ∘ endDisc R` of `u` to the disc `‖w‖ ≤ exp (2πR)` is a cylinder from the constant
loop at the value `u 0` at the pole to the loop `ℓ_R(t) = u(φ(ε R + i t))` along the circle
`ε s = R` of the end. So it caps `ℓ_R` in the convention of `TauCeti.cappedLoopAction`, and the
recapping laws of the capped action apply to it. -/
theorem isLoopCylinder_comp_endDisc {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (R : ℝ) :
    IsLoopCylinder I (u ∘ p.endDisc R) (fun _ ↦ u 0) fun t ↦
      u (Complex.equivRealProdCLM (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))) where
  contMDiff := hu.comp (p.contDiff_endDisc R).contMDiff
  apply_add_one z := by simp only [Function.comp_apply, endDisc_mk_add_one]
  apply_zero t := by simp
  apply_one t := by simp

/-- **The pullback of a two-form along the end disc.** At each point the end disc multiplies the
area element by its polar Jacobian `2π ε exp (2πR)² r`: the pullback of `φ` along `u ∘ endDisc R`,
evaluated on the coordinate vectors, is that Jacobian times the pullback along `u` at the image
point. -/
private theorem mpullback_comp_endDisc_apply (φ : RoughForm I M F 2) {u : ℝ × ℝ → M} (R : ℝ)
    (z : ℝ × ℝ) (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (p.endDisc R z)) :
    mpullback 𝓘(ℝ, ℝ × ℝ) I (u ∘ p.endDisc R) φ z ![(1, 0), (0, 1)] =
      (2 * π * p.endSign * Real.exp (2 * π * R) * (Real.exp (2 * π * R) * z.1)) •
        mpullback 𝓘(ℝ, ℝ × ℝ) I u φ (p.endDisc R z) ![(1, 0), (0, 1)] := by
  set q : ℝ × ℝ := (Real.exp (2 * π * R) * z.1, 2 * π * p.endSign * z.2)
  rw [mpullback_comp_apply_of_hasFDerivAt (p.hasFDerivAt_endDisc R z) hu]
  -- Read the pullback along `u` as a flat form on the plane, whose tangent spaces are `ℝ × ℝ`.
  let ψ : (ℝ × ℝ) [⋀^Fin 2]→L[ℝ] F := mpullback 𝓘(ℝ, ℝ × ℝ) I u φ (p.endDisc R z)
  refine (ContinuousAlternatingMap.compContinuousLinearMap_apply ψ _ _).trans ?_
  set B := ψ.toMultilinearMap.toBilinMap
  have hB (v w : ℝ × ℝ) : ψ ![v, w] = B v w := (MultilinearMap.toBilinMap_apply _ v w).symm
  have h2 (v w : ℝ × ℝ) : B v w - B w v = (2 : ℝ) • B v w := by
    rw [← ψ.toAlternatingMap.isAlt_toBilinMap.neg v w, sub_neg_eq_add, two_smul]
  -- The polar Jacobian identity, for `B` in the real coordinates of `ℂ`.
  have key := B.apply_exp_circleMap_sub_swap Complex.equivRealProdCLM.toLinearMap q.1 q.2
  rw [h2, h2, smul_comm] at key
  have key' := smul_right_injective F (two_ne_zero' ℝ) key
  have h₁ : fderivPolarCoordSymm q (1, 0) =
      Complex.equivRealProdCLM (Complex.exp (q.2 * Complex.I)) := by
    rw [← equivRealProd_symm_fderivPolarCoordSymm_apply_one_zero,
      ContinuousLinearEquiv.apply_symm_apply]
  have h₂ : fderivPolarCoordSymm q (0, 1) =
      Complex.equivRealProdCLM (circleMap 0 q.1 q.2 * Complex.I) := by
    rw [← equivRealProd_symm_fderivPolarCoordSymm_apply_zero_one,
      ContinuousLinearEquiv.apply_symm_apply]
  have he₁ : Complex.equivRealProdCLM 1 = ((1 : ℝ), (0 : ℝ)) := by simp
  have he₂ : Complex.equivRealProdCLM Complex.I = ((0 : ℝ), (1 : ℝ)) := by simp
  have hq : B (fderivPolarCoordSymm q (1, 0)) (fderivPolarCoordSymm q (0, 1)) =
      q.1 • B (1, 0) (0, 1) := by
    rw [h₁, h₂, ← he₁, ← he₂]
    exact key'
  have hv : (((fderivPolarCoordSymm q).comp
      ((Real.exp (2 * π * R) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        ((2 * π * p.endSign) • ContinuousLinearMap.snd ℝ ℝ ℝ))) ∘ ![(1, 0), (0, 1)]) =
      ![Real.exp (2 * π * R) • fderivPolarCoordSymm q (1, 0),
        (2 * π * p.endSign) • fderivPolarCoordSymm q (0, 1)] := by
    funext i
    fin_cases i <;> simp [← map_smul]
  refine (congrArg ψ hv).trans ((hB _ _).trans ?_)
  rw [map_smul, map_smul, LinearMap.smul_apply, hq, smul_smul, smul_smul]
  exact congrArg₂ (· • ·) (by ring) (hB _ _).symm

/-- Over the arc of angles `[0, 2π ε]`, a `2π`-periodic function integrates to `ε` times its
integral over one period. -/
private theorem intervalIntegral_zero_endSign {g : ℝ → F} (hg : Periodic g (2 * π)) :
    ∫ θ in (0 : ℝ)..2 * π * p.endSign, g θ = p.endSign • ∫ θ in -π..π, g θ := by
  cases p
  · have h := Function.Periodic.intervalIntegral_add_eq hg 0 (-π)
    simp only [zero_add] at h
    simp only [endSign_positive, mul_one, one_smul, h]
    ring_nf
  · have h := Function.Periodic.intervalIntegral_add_eq hg (-(2 * π)) (-π)
    simp only [neg_add_cancel] at h
    rw [endSign_negative, mul_neg_one, intervalIntegral.integral_symm, h, neg_one_smul]
    ring_nf

/-- **The area of the end disc of a PSS plane.** Let `φ` be a continuous two-form on `M` and `u` a
`C¹` map of the plane. The integral of `φ` over the end disc `u ∘ endDisc R` of the circle
`ε s = R`, on the unit square, is `ε` times the integral of `u^* φ` over the disc
`‖w‖ ≤ exp (2πR)` of the plane. The sign records the direction in which the angular coordinate of
the end runs around the circle: counterclockwise on the positive plane and clockwise on the
negative plane. -/
theorem rectangleIntegral_comp_endDisc [IsManifold I 1 M] {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 0 φ)
    {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (R : ℝ) :
    rectangleIntegral φ (u ∘ p.endDisc R) (0, 0) (1, 1) =
      p.endSign • ∫ z in Complex.equivRealProdCLM.symm ⁻¹'
          Metric.closedBall 0 (Real.exp (2 * π * R)),
        φ (u z) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (1, 0), mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (0, 1)] := by
  set ρ := Real.exp (2 * π * R)
  -- The pulled-back area density `f` of `u`, its values `g s` on the circles of radius `s`, and
  -- their integrals `A s` over the circles.
  set f : ℝ × ℝ → F := fun z ↦ mpullback 𝓘(ℝ, ℝ × ℝ) I u φ z ![(1, 0), (0, 1)]
  have hf : Continuous f := hφ.continuous_mpullback_apply hu ![(1, 0), (0, 1)]
  set g : ℝ → ℝ → F := fun s θ ↦ f (Complex.equivRealProdCLM (circleMap 0 s θ))
  have hg (s : ℝ) : Periodic (g s) (2 * π) := fun θ ↦ by
    simp only [g, periodic_circleMap 0 s θ]
  set A : ℝ → F := fun s ↦ ∫ θ in -π..π, g s θ
  -- On the square, the integrand is the polar Jacobian times the area density of `u`.
  have hint (r t : ℝ) : mpullback 𝓘(ℝ, ℝ × ℝ) I (u ∘ p.endDisc R) φ (r, t) ![(1, 0), (0, 1)] =
      (ρ * (ρ * r)) • ((2 * π * p.endSign) • g (ρ * r) (2 * π * p.endSign * t)) := by
    rw [mpullback_comp_endDisc_apply φ R (r, t) ((hu _).mdifferentiableAt one_ne_zero), smul_smul,
      endDisc_eq_circleMap]
    congr 1
    ring
  -- Integrating in the angle gives `ε` times the integral over the circle.
  have hangle (r : ℝ) : ∫ t in (0 : ℝ)..1,
      mpullback 𝓘(ℝ, ℝ × ℝ) I (u ∘ p.endDisc R) φ (r, t) ![(1, 0), (0, 1)] =
        p.endSign • (ρ • ((ρ * r) • A (ρ * r))) := by
    simp only [hint, intervalIntegral.integral_smul, intervalIntegral.smul_integral_comp_mul_left,
      mul_zero, mul_one, intervalIntegral_zero_endSign (hg _), A]
    module
  have hρ : 0 ≤ ρ := (Real.exp_pos _).le
  -- Integrating in the radius, rescaled to `[0, ρ]`.
  have hrect : rectangleIntegral φ (u ∘ p.endDisc R) (0, 0) (1, 1) =
      p.endSign • ∫ s in (0 : ℝ)..ρ, s • A s := by
    rw [rectangleIntegral_def]
    simp only [hangle, intervalIntegral.integral_smul]
    rw [intervalIntegral.smul_integral_comp_mul_left (fun s ↦ s • A s) ρ, mul_zero, mul_one]
  -- Polar coordinates on the disc.
  have hpre : Complex.measurableEquivRealProd ⁻¹' (Complex.equivRealProdCLM.symm ⁻¹'
      Metric.closedBall 0 ρ) = {w : ℂ | 0 ≤ ‖w - 0‖ ∧ ‖w - 0‖ ≤ ρ} := by
    ext w
    simp [Complex.measurableEquivRealProd]
  have hdisc : ∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 ρ, f z =
      ∫ s in (0 : ℝ)..ρ, s • A s := by
    rw [← Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding _ _, hpre]
    exact integral_annulus_eq_integral_circleMap le_rfl hρ
      (hf.comp Complex.equivRealProdCLM.continuous).continuousOn
  rw [hrect, ← hdisc]
  congr 1
  refine setIntegral_congr_fun ?_ fun z _ ↦ mpullback_apply_pair u φ z (1, 0) (0, 1)
  exact (Metric.isClosed_closedBall.preimage Complex.equivRealProdCLM.symm.continuous).measurableSet

namespace SmoothTwoForm

variable [IsManifold I ⊤ M] [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M} {H : ℝ → M → ℝ}

namespace IsNondegenerate

/-- **The energy identity on discs of a PSS plane, in terms of the capped action.** Let `K` be the
perturbation of a PSS plane given by a period-one `C¹` Hamiltonian `H` on a finite-dimensional
manifold with a nondegenerate two-form `ω`, with components `K_s(z) = K(z)(1)` and
`K_t(z) = K(z)(i)` in the global coordinate `z = s + i t` of `ℂ`, and let `u` be a `C¹` map. For
`R ≥ 2`, the Floer energy of `u` over the disc `‖w‖ ≤ exp (2πR)` is `ε` times the capped action of
the loop `ℓ_R(t) = u(φ(ε R + i t))` along its boundary circle, capped by the restriction
`u ∘ endDisc R` of `u` to the disc, minus the integrated curvature over the plane:

`∫_{D_R} E = ε A_H(ℓ_R, u ∘ endDisc R) - ∫_ℂ R_K(u)`.

Here `ε` is the sign of the end of the plane and `φ(z) = exp (2π ε z)` is the end lift. -/
theorem
    integral_floerEnergyDensity_pssPlanePerturbation_closedBall_eq_endSign_mul_cappedLoopAction
    (hω : ω.IsNondegenerate) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {u : ℝ × ℝ → M}
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) {R : ℝ} (hR : 2 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R)),
        ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      p.endSign * cappedLoopAction ω.1 H (fun t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) (u ∘ p.endDisc R) -
        ∫ z, ω.hamiltonianCurvature
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  -- The symplectic area over the disc is `ε` times the area of the end disc.
  have harea : ∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R)),
      (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) =
      p.endSign * rectangleIntegral ω.1 (u ∘ p.endDisc R) (0, 0) (1, 1) := by
    rw [rectangleIntegral_comp_endDisc (ω.isSmoothForm.of_le (by simp)) hu R, smul_eq_mul,
      ← mul_assoc, endSign_mul_endSign, one_mul]
    simp only [SmoothBundleForm.eval₂_apply, stdComplexLineReal, stdComplexLineImag]
  rw [hω.integral_floerEnergyDensity_pssPlanePerturbation_closedBall hH hHs hu (by linarith),
    harea, ω.setIntegral_hamiltonianCurvature_pssPlanePerturbation_closedBall hH hHs u hR,
    smoothTransition.one_of_one_le (by linarith : (1 : ℝ) ≤ R - 1),
    cappedLoopAction_def]
  ring

/-- **The energy identity on discs of a PSS plane, against an arbitrary cap.** Let `K` be the
perturbation of a PSS plane given by a period-one `C¹` Hamiltonian `H` on a finite-dimensional
manifold with a nondegenerate two-form `ω`, let `u` be a `C²` map, `R ≥ 2`, and let `D` be any
disc bounding the loop `ℓ_R(t) = u(φ(ε R + i t))`. Then

`∫_{D_R} E = ε (A_H(ℓ_R, D) - ω(D ⋆ (u ∘ endDisc R)⁻¹)) - ∫_ℂ R_K(u)`,

where `D ⋆ (u ∘ endDisc R)⁻¹` is the sphere obtained by gluing `D` to the restriction of `u` to
the disc run backwards (`TauCeti.rectangleTrans`). On the negative plane, `ε = -1`, this is the
energy identity `E = -A_H(ℓ_R, D) + ω(A) - ∫ R_K` of the plane with output cap `D`, in the class
`A` of the sphere formed by `D` and the plane. -/
theorem integral_floerEnergyDensity_pssPlanePerturbation_closedBall_of_isLoopCylinder
    (hω : ω.IsNondegenerate) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {u : ℝ × ℝ → M}
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u) {R : ℝ} (hR : 2 ≤ R) {D : ℝ × ℝ → M} {x : M}
    (hD : IsLoopCylinder I D (fun _ ↦ x) fun t ↦ u (Complex.equivRealProdCLM
      (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R)),
        ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      p.endSign * (cappedLoopAction ω.1 H (fun t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) D -
          rectangleIntegral ω.1
            (rectangleTrans D ((u ∘ p.endDisc R) ∘ Prod.map (fun s ↦ 1 - s) id)) (0, 0) (1, 1)) -
        ∫ z, ω.hamiltonianCurvature
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  rw [hω.integral_floerEnergyDensity_pssPlanePerturbation_closedBall_eq_endSign_mul_cappedLoopAction
      hH hHs (hu.of_le one_le_two) hR,
    ← cappedLoopAction_sub_cappedLoopAction (ω.isSmoothForm.of_le (by simp)) H
      (isLoopCylinder_comp_endDisc hu R) hD, sub_sub_cancel]

/-- **The energy and the capped action on discs of a PSS plane.** If `|H| ≤ B`, then for every
`R ≥ 2` the Floer energy of a `C¹` map over the disc `‖w‖ ≤ exp (2πR)` differs from `ε` times the
capped action of its boundary loop, capped by the disc, by at most `B`, uniformly in `R`. -/
theorem abs_integral_floerEnergyDensity_pssPlanePerturbation_closedBall_sub_le
    (hω : ω.IsNondegenerate) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {B : ℝ} (hB : ∀ t x, |H t x| ≤ B)
    {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) {R : ℝ} (hR : 2 ≤ R) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R)),
        ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) -
      p.endSign * cappedLoopAction ω.1 H (fun t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) (u ∘ p.endDisc R)| ≤ B := by
  rw [hω.integral_floerEnergyDensity_pssPlanePerturbation_closedBall_eq_endSign_mul_cappedLoopAction
      hH hHs hu hR, sub_sub_cancel_left, abs_neg]
  exact ω.abs_integral_hamiltonianCurvature_pssPlanePerturbation_le hH hHs hB u

/-- **The capped action bound on the circles of a PSS plane.** Let `K` be the perturbation of a
PSS plane given by a period-one `C¹` Hamiltonian `H` with `|H| ≤ B`, and let `u` be a `C¹` map
solving the Floer equation `(du - X_K)^{0,1} = 0` on the disc `‖w‖ ≤ exp (2πR)`, `R ≥ 2`, for
almost complex structures `J(z)` tamed by `ω`. Then the capped action of the loop
`ℓ_R(t) = u(φ(ε R + i t))` along its boundary circle, capped by the disc, satisfies
`-B ≤ ε A_H(ℓ_R, u ∘ endDisc R)`: on the negative plane `A_H(ℓ_R, u ∘ endDisc R) ≤ B`, and on the
positive plane `-B ≤ A_H(ℓ_R, u ∘ endDisc R)`. -/
theorem neg_le_endSign_mul_cappedLoopAction_pssPlanePerturbation
    (hω : ω.IsNondegenerate) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {B : ℝ} (hB : ∀ t x, |H t x| ≤ B)
    {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) {R : ℝ} (hR : 2 ≤ R)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R)),
      (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R)),
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap) :
    -B ≤ p.endSign * cappedLoopAction ω.1 H (fun t ↦ u (Complex.equivRealProdCLM
      (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) (u ∘ p.endDisc R) := by
  -- The energy over the disc is nonnegative.
  have hE := setIntegral_nonneg (μ := volume)
    ((Metric.isClosed_closedBall.preimage Complex.equivRealProdCLM.symm.continuous).measurableSet)
    fun z hz ↦ floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  have h := (abs_le.1
    (hω.abs_integral_floerEnergyDensity_pssPlanePerturbation_closedBall_sub_le (p := p) hH hHs hB
      hu hR)).2
  linarith

/-- **The energy of a PSS plane in a manifold.** Let `K` be the perturbation of a PSS plane given
by a period-one `C¹` Hamiltonian `H` on a finite-dimensional manifold with a nondegenerate two-form
`ω`, and let `u` be a `C¹` map solving the Floer equation `(du - X_K)^{0,1} = 0` on the whole plane
for almost complex structures `J(z)` tamed by `ω`. If the capped actions of the loops
`ℓ_R(t) = u(φ(ε R + i t))`, each capped by the disc `u ∘ endDisc R` of the plane that it bounds,
converge to `a` as `R → ∞`, then the energy of `u` is

`E(u) = ε a - ∫_ℂ R_K(u)`. -/
theorem lintegral_floerEnergyDensity_pssPlanePerturbation_eq
    (hω : ω.IsNondegenerate) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {u : ℝ × ℝ → M}
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedMFDeriv (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z).toLinearMap)
    {a : ℝ} (ha : Tendsto (fun R ↦ cappedLoopAction ω.1 H (fun t ↦ u (Complex.equivRealProdCLM
      (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) (u ∘ p.endDisc R)) atTop
        (𝓝 a)) :
    ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) =
      ENNReal.ofReal (p.endSign * a - ∫ z, ω.hamiltonianCurvature
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) := by
  -- Exhaust the plane by the discs `D_R`, on which the energy is `ε` times the capped action
  -- minus the integrated curvature.
  refine lintegral_ofReal_eq_of_tendsto_setIntegral_closedBall
    Complex.equivRealProdCLM.symm.continuous (r := fun R ↦ Real.exp (2 * π * R))
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop Real.two_pi_pos))
    (ae_of_all _ fun z ↦ floerEnergyDensity_nonneg hω (hJ z) (hfloer z)) (fun _ ↦
      hω.integrableOn_floerEnergyDensity isOpen_univ hu.contMDiffOn
        (contMDiff_uncurry_perturbation hH hHs 1).contMDiffOn
        (contMDiff_uncurry_perturbation hH hHs Complex.I).contMDiffOn
        (Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
          (isCompact_closedBall _ _)) (subset_univ _)
        (ω.integrableOn_hamiltonianCurvature_pssPlanePerturbation_closedBall hH hHs hu.continuous
          _)) <|
    ((ha.const_mul p.endSign).sub_const _).congr' <| (eventually_ge_atTop 2).mono fun _ hR ↦
      (integral_floerEnergyDensity_pssPlanePerturbation_closedBall_eq_endSign_mul_cappedLoopAction
        hω hH hHs hu hR).symm

/-- **The energy bound for a PSS plane in a manifold.** Under the hypotheses of
`SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_pssPlanePerturbation_eq`, if moreover
`|H| ≤ B`, then the energy of `u` is at most `ε a + B`. -/
theorem lintegral_floerEnergyDensity_pssPlanePerturbation_le
    (hω : ω.IsNondegenerate) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {B : ℝ} (hB : ∀ t x, |H t x| ≤ B)
    {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedMFDeriv (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z).toLinearMap)
    {a : ℝ} (ha : Tendsto (fun R ↦ cappedLoopAction ω.1 H (fun t ↦ u (Complex.equivRealProdCLM
      (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) (u ∘ p.endDisc R)) atTop
        (𝓝 a)) :
    ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≤
      ENNReal.ofReal (p.endSign * a + B) := by
  rw [hω.lintegral_floerEnergyDensity_pssPlanePerturbation_eq hH hHs hu hJ hfloer ha]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith [neg_abs_le (∫ z, ω.hamiltonianCurvature
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)),
    ω.abs_integral_hamiltonianCurvature_pssPlanePerturbation_le (p := p) hH hHs hB u]

/-- **The capped action bound for a PSS plane in a manifold.** Under the hypotheses of
`SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_pssPlanePerturbation_eq`, if moreover
`|H| ≤ B`, then the limiting capped action `a` of the end satisfies `-B ≤ ε a`: on the negative
plane `a ≤ B`, and on the positive plane `-B ≤ a`. This is the limit `R → ∞` of
`SmoothTwoForm.IsNondegenerate.neg_le_endSign_mul_cappedLoopAction_pssPlanePerturbation`. -/
theorem neg_le_endSign_mul_of_tendsto_cappedLoopAction_pssPlanePerturbation
    (hω : ω.IsNondegenerate) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {B : ℝ} (hB : ∀ t x, |H t x| ≤ B)
    {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedMFDeriv (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z).toLinearMap)
    {a : ℝ} (ha : Tendsto (fun R ↦ cappedLoopAction ω.1 H (fun t ↦ u (Complex.equivRealProdCLM
      (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) (u ∘ p.endDisc R)) atTop
        (𝓝 a)) :
    -B ≤ p.endSign * a :=
  ge_of_tendsto (ha.const_mul _) <| eventually_atTop.2 ⟨2, fun _ hR ↦
    hω.neg_le_endSign_mul_cappedLoopAction_pssPlanePerturbation hH hHs hB hu hR
      (fun z _ ↦ hJ z) fun z _ ↦ hfloer z⟩

end IsNondegenerate

end SmoothTwoForm

end TauCeti
