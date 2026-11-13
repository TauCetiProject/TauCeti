/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Action
public import TauCeti.Geometry.Symplectic.Floer.Plane.Curvature
import TauCeti.Geometry.Symplectic.Area.PuncturedDisc
import TauCeti.MeasureTheory.Integral.IntegralEqImproper

/-!
# The energy of a PSS plane in terms of the action of its end

Let `K` be the perturbation `TauCeti.Floer.PSSPlane.perturbation` of a PSS plane `p`, built from
a period-one Hamiltonian `H` on a symplectic vector space `(V, ω)`, and let `ε = ±1` be the sign
of the end of `p` at `∞`: `+1` for the positive plane, whose end is an input, and `-1` for the
negative plane, whose end is an output. For a map `u` from the plane and `R ∈ ℝ`, write `ℓ_R` for
the loop `t ↦ u(φ(ε R + i t))` along the circle `‖w‖ = exp (2πR)`, where `φ(z) = exp (2π ε z)` is
the end lift. This loop runs counterclockwise on the positive plane and clockwise on the negative
plane, so Stokes' formula on the disc `D_R = {‖w‖ ≤ exp (2πR)}` gives `∫_{D_R} u^*ω = ε a(ℓ_R)`
for the loop area `a`. With the energy identity on discs
(`TauCeti.SymplecticForm.integral_floerEnergyDensity_pssPlanePerturbation_closedBall`), and since
the curvature vanishes outside `D_2`, this gives, for a `C²` map and `R ≥ 2`,

`∫_{D_R} E = ε A_H(ℓ_R) - ∫_ℂ R_K(u)`

for the Hamiltonian action `A_H(x) = a(x) + ∫₀¹ H(t, x(t)) dt`
(`integral_floerEnergyDensity_pssPlanePerturbation_closedBall_eq_endSign_mul_hamiltonianAction`
in `TauCeti.SymplecticForm`).
The plane itself serves as the cap of its end loop. If `|H| ≤ B`, the curvature term is at most
`B` in absolute value, uniformly in `R`. For a solution of the Floer equation with tame almost
complex structures the energy density is nonnegative, which gives the action bound
`-B ≤ ε A_H(ℓ_R)` on every circle: the output action of a negative plane is at most `B`, and the
input action of a positive plane is at least `-B`
(`SymplecticForm.neg_le_endSign_mul_hamiltonianAction_pssPlanePerturbation`).

If the actions `A_H(ℓ_R)` converge to `a` as `R → ∞`, then the energy of such a solution over the
whole plane is `ε a - ∫_ℂ R_K(u)`
(`SymplecticForm.lintegral_floerEnergyDensity_pssPlanePerturbation_eq`), it is at most `ε a + B`
(`SymplecticForm.lintegral_floerEnergyDensity_pssPlanePerturbation_le`), and `-B ≤ ε a`
(`SymplecticForm.neg_le_endSign_mul_of_tendsto_hamiltonianAction_pssPlanePerturbation`). These are
the energy bound for PSS planes with prescribed end action, which compactness arguments start
from, and the one-sided action bound on the orbits that solutions on the planes can reach.

## Main results

* `integral_floerEnergyDensity_pssPlanePerturbation_closedBall_eq_endSign_mul_hamiltonianAction`
  in `TauCeti.SymplecticForm`: the energy over a disc in terms of the action of its boundary loop.
* `SymplecticForm.abs_integral_floerEnergyDensity_pssPlanePerturbation_closedBall_sub_le`: the
  resulting energy bound, uniform in the radius.
* `SymplecticForm.neg_le_endSign_mul_hamiltonianAction_pssPlanePerturbation`: the action bound on
  every circle.
* `SymplecticForm.lintegral_floerEnergyDensity_pssPlanePerturbation_eq`,
  `SymplecticForm.lintegral_floerEnergyDensity_pssPlanePerturbation_le`: the energy of a solution
  over the whole plane, and its bound.
* `SymplecticForm.neg_le_endSign_mul_of_tendsto_hamiltonianAction_pssPlanePerturbation`: the
  action bound for the limiting action.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  energy of the perturbed planes of the PSS maps.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  energy identity for Hamiltonian perturbations, and Chapter 12, on the PSS isomorphism.
-/

public section

open Set Real Function MeasureTheory Filter
open scoped Topology

namespace TauCeti

namespace SymplecticForm

open Floer Floer.PSSPlane

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {p : PSSPlane} {H : ℝ → V → ℝ}

/-- **The symplectic area of a disc of a PSS plane.** For a `C²` map `u`, the symplectic area over
the disc `‖w‖ ≤ exp (2πR)` is `ε` times the loop area of the loop `ℓ_R(t) = u(φ(ε R + i t))`
along its boundary circle. -/
private theorem integral_symplecticForm_fderiv_closedBall (ω : SymplecticForm V)
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 2 u) (R : ℝ) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R)),
        ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) =
      p.endSign * ω.loopArea (fun t ↦ u (Complex.equivRealProdCLM
        (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) := by
  rw [ω.integral_fderiv_apply_preimage_closedBall 0 (Real.exp_pos _) fun z _ ↦ hu.contDiffAt]
  -- The boundary loop runs once around the circle of radius `exp (2πR)`, in the direction `ε`.
  have hg : Periodic (fun θ ↦ u (Complex.equivRealProdCLM
      (circleMap 0 (Real.exp (2 * π * R)) θ))) (2 * π) := fun θ ↦ by
    simp only [periodic_circleMap 0 _ θ]
  simp only [cylindricalEndLift_eq_circleMap]
  cases p
  · have h := ω.loopArea_comp_add_mul hg 0
    simp only [zero_add] at h
    simp only [endSign_positive, one_mul, h]
  · have h := ω.loopArea_comp_sub_mul hg 0
    simp only [zero_sub] at h
    simp only [endSign_negative, neg_mul, one_mul, h, neg_neg]

/-- **The energy identity on discs of a PSS plane, in terms of the action.** Let `K` be the
perturbation of a PSS plane given by a period-one `C¹` Hamiltonian `H`, with components
`K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global coordinate `z = s + i t` of `ℂ`, and let
`u` be a `C²` map. For `R ≥ 2`, the Floer energy of `u` over the disc `‖w‖ ≤ exp (2πR)` is `ε`
times the Hamiltonian action of the loop `ℓ_R(t) = u(φ(ε R + i t))` along its boundary circle,
minus the integrated curvature over the plane:

`∫_{D_R} E = ε A_H(ℓ_R) - ∫_ℂ R_K(u)`.

Here `ε` is the sign of the end of the plane and `φ(z) = exp (2π ε z)` is the end lift. -/
theorem integral_floerEnergyDensity_pssPlanePerturbation_closedBall_eq_endSign_mul_hamiltonianAction
    (ω : SymplecticForm V) (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {u : ℝ × ℝ → V}
    (hu : ContDiff ℝ 2 u) {R : ℝ} (hR : 2 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R)),
        ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      p.endSign * ω.hamiltonianAction H (fun t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) -
        ∫ z, ω.hamiltonianCurvature
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  -- The curvature vanishes outside the disc, which contains the collar `1 ≤ ε s ≤ 2`.
  have hcurv :=
    ω.setIntegral_hamiltonianCurvature_pssPlanePerturbation_closedBall (p := p) hH hHs u hR
  rw [integral_floerEnergyDensity_pssPlanePerturbation_closedBall ω hH hHs (hu.of_le one_le_two)
      (by linarith), integral_symplecticForm_fderiv_closedBall ω hu R, hcurv,
    smoothTransition.one_of_one_le (by linarith : (1 : ℝ) ≤ R - 1), hamiltonianAction_def]
  ring

/-- **The energy and the action on discs of a PSS plane.** If `|H| ≤ B`, then for every `R ≥ 2`
the Floer energy of a `C²` map over the disc `‖w‖ ≤ exp (2πR)` differs from `ε` times the action
of its boundary loop by at most `B`, uniformly in `R`. -/
theorem abs_integral_floerEnergyDensity_pssPlanePerturbation_closedBall_sub_le
    (ω : SymplecticForm V) (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {B : ℝ}
    (hB : ∀ t x, |H t x| ≤ B) {u : ℝ × ℝ → V} (hu : ContDiff ℝ 2 u) {R : ℝ} (hR : 2 ≤ R) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R)),
        ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) -
      p.endSign * ω.hamiltonianAction H (fun t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))))| ≤ B := by
  rw [integral_floerEnergyDensity_pssPlanePerturbation_closedBall_eq_endSign_mul_hamiltonianAction
      ω hH hHs hu hR, sub_sub_cancel_left, abs_neg]
  exact ω.abs_integral_hamiltonianCurvature_pssPlanePerturbation_le hH hHs hB u

/-- **The action bound on the circles of a PSS plane.** Let `K` be the perturbation of a PSS plane
given by a period-one `C¹` Hamiltonian `H` with `|H| ≤ B`, and let `u` be a `C²` map solving the
Floer equation `(du - X_K)^{0,1} = 0` on the disc `‖w‖ ≤ exp (2πR)`, `R ≥ 2`, for almost complex
structures `J(z)` tamed by `ω`. Then the action of the loop `ℓ_R(t) = u(φ(ε R + i t))` along its
boundary circle satisfies `-B ≤ ε A_H(ℓ_R)`: on the negative plane `A_H(ℓ_R) ≤ B`, and on the
positive plane `-B ≤ A_H(ℓ_R)`. -/
theorem neg_le_endSign_mul_hamiltonianAction_pssPlanePerturbation (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {B : ℝ} (hB : ∀ t x, |H t x| ≤ B)
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 2 u) {R : ℝ} (hR : 2 ≤ R)
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R)),
      ω.Tames (J z))
    (hfloer : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R)),
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V)) :
    -B ≤ p.endSign * ω.hamiltonianAction H (fun t ↦ u (Complex.equivRealProdCLM
      (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) := by
  -- The energy over the disc is nonnegative.
  have hD : MeasurableSet
      (Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall (0 : ℂ) (Real.exp (2 * π * R))) :=
    Metric.isClosed_closedBall.measurableSet.preimage
      Complex.equivRealProdCLM.symm.continuous.measurable
  have hE := setIntegral_nonneg (μ := volume) hD fun z hz ↦
    ω.floerEnergyDensity_nonneg (hJ z hz) (hfloer z hz)
  have h := (abs_le.1
    (abs_integral_floerEnergyDensity_pssPlanePerturbation_closedBall_sub_le (p := p) ω hH hHs hB hu
      hR)).2
  linarith

/-- Under convergence of the actions of the boundary loops, the energy over the discs
`‖w‖ ≤ exp (2πR)` converges to `ε` times the limiting action minus the integrated curvature. -/
private theorem tendsto_integral_floerEnergyDensity_closedBall (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {u : ℝ × ℝ → V} (hu : ContDiff ℝ 2 u)
    {a : ℝ} (ha : Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u (Complex.equivRealProdCLM
      (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))))) atTop (𝓝 a)) :
    Tendsto (fun R : ℝ ↦ ∫ z in Complex.equivRealProdCLM.symm ⁻¹'
        Metric.closedBall 0 (Real.exp (2 * π * R)), ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) atTop
      (𝓝 (p.endSign * a - ∫ z, ω.hamiltonianCurvature
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))) :=
  ((ha.const_mul p.endSign).sub_const _).congr' <| (eventually_ge_atTop 2).mono fun _ hR ↦
    (integral_floerEnergyDensity_pssPlanePerturbation_closedBall_eq_endSign_mul_hamiltonianAction
      ω hH hHs hu hR).symm

/-- **The energy of a PSS plane.** Let `K` be the perturbation of a PSS plane given by a
period-one `C¹` Hamiltonian `H`, and let `u` be a `C²` map solving the Floer equation
`(du - X_K)^{0,1} = 0` on the whole plane for almost complex structures `J(z)` tamed by `ω`. If
the actions of the loops `ℓ_R(t) = u(φ(ε R + i t))` converge to `a` as `R → ∞`, then the energy
of `u` is

`E(u) = ε a - ∫_ℂ R_K(u)`. -/
theorem lintegral_floerEnergyDensity_pssPlanePerturbation_eq (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {u : ℝ × ℝ → V} (hu : ContDiff ℝ 2 u)
    {J : ℝ × ℝ → AlmostComplexStructure V} (hJ : ∀ z, ω.Tames (J z))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    {a : ℝ} (ha : Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u (Complex.equivRealProdCLM
      (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))))) atTop (𝓝 a)) :
    ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) =
      ENNReal.ofReal (p.endSign * a - ∫ z, ω.hamiltonianCurvature
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) := by
  -- Exhaust the plane by the discs `D_R`, on which the energy density is continuous.
  have hEc : Continuous (ω.floerEnergyDensity
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u) :=
    continuousOn_univ.1 (ω.continuousOn_floerEnergyDensity isOpen_univ
      (hu.of_le one_le_two).contDiffOn
      (by simpa using (contDiff_uncurry_perturbation (p := p) hH hHs 1).contDiffOn)
      (by simpa using (contDiff_uncurry_perturbation (p := p) hH hHs Complex.I).contDiffOn))
  exact lintegral_ofReal_eq_of_tendsto_setIntegral_closedBall
    Complex.equivRealProdCLM.symm.continuous (r := fun R ↦ Real.exp (2 * π * R))
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop Real.two_pi_pos))
    (ae_of_all _ fun z ↦ ω.floerEnergyDensity_nonneg (hJ z) (hfloer z))
    (fun _ ↦ hEc.continuousOn.integrableOn_compact
      (Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_closedBall _ _)))
    (tendsto_integral_floerEnergyDensity_closedBall ω hH hHs hu ha)

/-- **The energy bound for a PSS plane.** Under the hypotheses of
`SymplecticForm.lintegral_floerEnergyDensity_pssPlanePerturbation_eq`, if moreover `|H| ≤ B`, then
the energy of `u` is at most `ε a + B`. -/
theorem lintegral_floerEnergyDensity_pssPlanePerturbation_le (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {B : ℝ} (hB : ∀ t x, |H t x| ≤ B)
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 2 u)
    {J : ℝ × ℝ → AlmostComplexStructure V} (hJ : ∀ z, ω.Tames (J z))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    {a : ℝ} (ha : Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u (Complex.equivRealProdCLM
      (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))))) atTop (𝓝 a)) :
    ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≤
      ENNReal.ofReal (p.endSign * a + B) := by
  rw [lintegral_floerEnergyDensity_pssPlanePerturbation_eq ω hH hHs hu hJ hfloer ha]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith [neg_abs_le (∫ z, ω.hamiltonianCurvature
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)),
    ω.abs_integral_hamiltonianCurvature_pssPlanePerturbation_le (p := p) hH hHs hB u]

/-- **The action bound for a PSS plane.** Under the hypotheses of
`SymplecticForm.lintegral_floerEnergyDensity_pssPlanePerturbation_eq`, if moreover `|H| ≤ B`, then
the limiting action `a` of the end satisfies `-B ≤ ε a`: on the negative plane `a ≤ B`, and on the
positive plane `-B ≤ a`. This is the limit `R → ∞` of
`SymplecticForm.neg_le_endSign_mul_hamiltonianAction_pssPlanePerturbation`. -/
theorem neg_le_endSign_mul_of_tendsto_hamiltonianAction_pssPlanePerturbation
    (ω : SymplecticForm V) (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {B : ℝ}
    (hB : ∀ t x, |H t x| ≤ B) {u : ℝ × ℝ → V} (hu : ContDiff ℝ 2 u)
    {J : ℝ × ℝ → AlmostComplexStructure V} (hJ : ∀ z, ω.Tames (J z))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    {a : ℝ} (ha : Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u (Complex.equivRealProdCLM
      (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))))) atTop (𝓝 a)) :
    -B ≤ p.endSign * a :=
  ge_of_tendsto (ha.const_mul _) <| eventually_atTop.2 ⟨2, fun _ hR ↦
    neg_le_endSign_mul_hamiltonianAction_pssPlanePerturbation ω hH hHs hB hu hR
      (fun z _ ↦ hJ z) fun z _ ↦ hfloer z⟩

end SymplecticForm

end TauCeti
