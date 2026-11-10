/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Plane.Curvature
public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction.Capped
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Disc

/-!
# The energy of a PSS plane in a manifold in terms of the capped action of its end

Let `K` be the perturbation `TauCeti.Floer.PSSPlane.perturbation` of a PSS plane `p`, built from a
period-one Hamiltonian `H` on a finite-dimensional manifold `M` with a nondegenerate two-form `ω`,
such as a closed symplectic manifold, and let `ε = ±1` be the sign of the end of `p` at `∞`: `+1`
for the positive plane, whose end is an input, and `-1` for the negative plane, whose end is an
output. For a map `u` from the plane and `R ∈ ℝ`, write `ℓ_R(t) = u(φ(ε R + i t))` for its loop
along the circle `‖w‖ = exp (2πR)`, where `φ(z) = exp (2π ε z)` is the end lift.

On a manifold the action of a loop depends on a disc bounding it. The plane itself supplies one:
the *end disc* `D_R(r, t) = u(r φ(ε R + i t))` (`TauCeti.Floer.PSSPlane.endDisc`) sweeps out the
disc `‖w‖ ≤ exp (2πR)` of the plane radially, from the pole at `r = 0` to the loop `ℓ_R` at
`r = 1`. For a `C²` map it is a disc bounding `ℓ_R` in the sense of the capped action
(`TauCeti.Floer.PSSPlane.isLoopCylinder_endDisc`). Its area is `ε` times the symplectic area of `u`
over the disc of the plane (`TauCeti.SmoothTwoForm.rectangleIntegral_endDisc`), the sign recording
that `t` runs clockwise on the negative plane. So the energy identity on discs
(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pssPlanePerturbation_closedBall`)
reads, for a `C¹` map and `R ≥ 2`,

`∫_{D_R} E = ε A_H(ℓ_R, D_R) - ∫_ℂ R_K(u)`

for the capped action `A_H(γ, D) = ∫ D^* ω + ∫₀¹ H(t, γ(t)) dt` (`TauCeti.cappedLoopAction`); the
curvature vanishes outside the disc `‖w‖ ≤ exp (4π)`. This is the manifold counterpart of
`TauCeti.Geometry.Symplectic.Floer.Plane.Action`, where the plane caps its end loop by the cone
over it.

Measured against any other disc `D` of `ℓ_R`, the action changes by the area of the sphere
`D ⋆ D_R⁻¹` obtained by gluing `D` to the end disc run backwards, so

`∫_{D_R} E = ε (A_H(ℓ_R, D) - ω(D ⋆ D_R⁻¹)) - ∫_ℂ R_K(u)`.

For the negative plane this is the energy identity `E = -A_H(x, D) + ω(A) - ∫ R_K` of a plane
with output cap `D`, in the class `A` of the sphere it forms with `D`: the form in which the
energy bounds the classes of negative PSS planes with a given capped output.

If `|H| ≤ B`, the energy over every disc differs from `ε A_H(ℓ_R, D_R)` by at most `B`. For a
solution of the Floer equation with almost complex structures tamed by `ω`, the energy density is
nonnegative, which gives the action bound `-B ≤ ε A_H(ℓ_R, D_R)`. If the capped actions
`A_H(ℓ_R, D_R)` converge to `a` as `R → ∞`, the energy of such a solution over the whole plane is
`ε a - ∫_ℂ R_K(u)`, at most `ε a + B`, and `-B ≤ ε a`.

## Main definitions

* `TauCeti.Floer.PSSPlane.endDisc`: the disc of the plane bounding the end loop `ℓ_R`, swept out
  radially from the pole.

## Main results

* `TauCeti.SmoothTwoForm.rectangleIntegral_endDisc`: the area of the end disc is `ε` times the
  symplectic area of `u` over the disc of the plane.

In the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:

* `integral_floerEnergyDensity_pssPlanePerturbation_closedBall_eq_endSign_mul_cappedLoopAction`:
  the energy over a disc in terms of the capped action of its boundary loop.
* `integral_floerEnergyDensity_pssPlanePerturbation_closedBall_of_isLoopCylinder`: the same,
  measured against an arbitrary disc of the boundary loop.
* `abs_integral_floerEnergyDensity_pssPlanePerturbation_closedBall_sub_le`: the resulting energy
  bound, uniform in the radius.
* `neg_le_endSign_mul_cappedLoopAction_pssPlanePerturbation`: the action bound on every circle,
  for solutions of the Floer equation.
* `lintegral_floerEnergyDensity_pssPlanePerturbation_eq`,
  `lintegral_floerEnergyDensity_pssPlanePerturbation_le`: the energy of a solution over the whole
  plane, and its bound.
* `neg_le_endSign_mul_of_tendsto_cappedLoopAction_pssPlanePerturbation`: the action bound for the
  limiting capped action.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  energy of the perturbed planes of the PSS maps.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  energy identity for Hamiltonian perturbations, and Chapter 12, on the PSS isomorphism and the
  action of capped orbits.
-/

public section

noncomputable section

open Set Real Function MeasureTheory Filter
open scoped Manifold Topology

namespace TauCeti

namespace Floer.PSSPlane

variable {X : Type*}

/-- The **end disc** of a PSS plane `p` at height `R` of a map `u` from the plane: the map
`D_R(r, t) = u(r φ(ε R + i t))` of the unit square, where `φ` is the end lift and `ε` the sign of
the end. It sweeps out the disc `‖w‖ ≤ exp (2πR)` of the plane radially, from the pole at `r = 0`
to the loop `ℓ_R(t) = u(φ(ε R + i t))` along its boundary circle at `r = 1`, and is the disc by
which the plane caps that loop. -/
def endDisc (p : PSSPlane) (u : ℝ × ℝ → X) (R : ℝ) (z : ℝ × ℝ) : X :=
  u (Complex.equivRealProdCLM (z.1 * p.cylindricalEndLift (↑(p.endSign * R) + ↑z.2 * Complex.I)))

theorem endDisc_def (p : PSSPlane) (u : ℝ × ℝ → X) (R : ℝ) (z : ℝ × ℝ) :
    p.endDisc u R z = u (Complex.equivRealProdCLM
      (z.1 * p.cylindricalEndLift (↑(p.endSign * R) + ↑z.2 * Complex.I))) :=
  (rfl)

/-- The end disc starts at the pole of the plane. -/
@[simp]
theorem endDisc_zero (p : PSSPlane) (u : ℝ × ℝ → X) (R t : ℝ) : p.endDisc u R (0, t) = u 0 := by
  simp [endDisc_def, Prod.mk_zero_zero]

/-- The end disc ends at the loop of `u` along the circle `ε s = R` of the end. -/
@[simp]
theorem endDisc_one (p : PSSPlane) (u : ℝ × ℝ → X) (R t : ℝ) :
    p.endDisc u R (1, t) =
      u (Complex.equivRealProdCLM (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))) := by
  simp [endDisc_def]

/-- The end disc is the radial sweep `(r, t) ↦ u(exp (2πR) r exp (2π i ε t))` of the disc of
radius `exp (2πR)`. -/
theorem endDisc_eq_circleMap (p : PSSPlane) (u : ℝ × ℝ → X) (R : ℝ) :
    p.endDisc u R = fun z ↦ u (Complex.equivRealProdCLM
      (circleMap 0 (Real.exp (2 * π * R) * z.1) (p.endSign * (2 * π * z.2)))) := by
  funext z
  rw [endDisc_def, cylindricalEndLift_eq_circleMap]
  simp only [circleMap, zero_add, Complex.ofReal_mul]
  ring_nf

/-- **The end disc caps the end loop.** For a `C²` map `u`, the end disc is a disc bounding the
loop `ℓ_R(t) = u(φ(ε R + i t))`, centred at the image `u 0` of the pole: a `C²` cylinder,
`1`-periodic in `t`, from the constant loop at `u 0` to `ℓ_R`. -/
theorem isLoopCylinder_endDisc {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    (p : PSSPlane) {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u) (R : ℝ) :
    IsLoopCylinder I (p.endDisc u R) (fun _ ↦ u 0)
      (fun t ↦ u (Complex.equivRealProdCLM
        (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) where
  contMDiff := by
    rw [endDisc_eq_circleMap]
    refine hu.comp (ContDiff.contMDiff (Complex.equivRealProdCLM.contDiff.comp ?_))
    simp only [circleMap, ← Complex.ofRealCLM_apply]
    fun_prop
  apply_add_one z := by
    rw [endDisc_def, endDisc_def]
    exact congrArg (fun w ↦ u (Complex.equivRealProdCLM (z.1 * w)))
      (p.periodic_cylindricalEndLift (p.endSign * R) z.2)
  apply_zero t := endDisc_zero p u R t
  apply_one t := endDisc_one p u R t

end Floer.PSSPlane

namespace SmoothTwoForm

open Floer Floer.PSSPlane

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {p : PSSPlane} {H : ℝ → M → ℝ}

/-- **The area of the end disc.** For a continuous two-form `ω` and a `C¹` map `u`, the integral of
`ω` over the end disc `D_R` is `ε` times the symplectic area of `u` over the disc
`‖w‖ ≤ exp (2πR)` of the plane. -/
theorem rectangleIntegral_endDisc (ω : SmoothTwoForm I M) {u : ℝ × ℝ → M}
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (R : ℝ) :
    rectangleIntegral ω.1 (p.endDisc u R) (0, 0) (1, 1) =
      p.endSign * ∫ z in Complex.equivRealProdCLM.symm ⁻¹'
          Metric.closedBall 0 (Real.exp (2 * π * R)),
        SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) := by
  rw [endDisc_eq_circleMap, stdComplexLineReal_eq, stdComplexLineImag_eq]
  exact ω.rectangleIntegral_circleMap hu (Real.exp_pos _).le p.abs_endSign

variable [FiniteDimensional ℝ E]

namespace IsNondegenerate

/-- **The energy identity on discs of a PSS plane, in terms of the capped action.** Let `K` be the
perturbation of a PSS plane given by a period-one `C¹` Hamiltonian `H` on a finite-dimensional
manifold with a nondegenerate two-form `ω`, with components `K_s(z) = K(z)(1)` and
`K_t(z) = K(z)(i)` in the global coordinate `z = s + i t` of `ℂ`, and let `u` be a `C¹` map. For
`R ≥ 2`, the Floer energy of `u` over the disc `‖w‖ ≤ exp (2πR)` is `ε` times the capped action of
the loop `ℓ_R(t) = u(φ(ε R + i t))` along its boundary circle, capped by the end disc `D_R`, minus
the integrated curvature over the plane:

`∫_{D_R} E = ε A_H(ℓ_R, D_R) - ∫_ℂ R_K(u)`.

Here `ε` is the sign of the end of the plane and `φ(z) = exp (2π ε z)` is the end lift. -/
theorem integral_floerEnergyDensity_pssPlanePerturbation_closedBall_eq_endSign_mul_cappedLoopAction
    {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {u : ℝ × ℝ → M}
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) {R : ℝ} (hR : 2 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R)),
        ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      p.endSign * cappedLoopAction ω.1 H (fun t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) (p.endDisc u R) -
        ∫ z, ω.hamiltonianCurvature
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  -- The curvature vanishes outside the disc, which contains the collar `1 ≤ ε s ≤ 2`.
  have hcurv : ∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R)),
      ω.hamiltonianCurvature
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      ∫ z, ω.hamiltonianCurvature
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ ?_
    refine ω.hamiltonianCurvature_pssPlanePerturbation_eq_zero_of_two_lt hH hHs ?_ _
    simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right, not_le] at hz
    have hlog := Real.log_lt_log (Real.exp_pos _) hz
    rw [Real.log_exp] at hlog
    rw [endSign_mul_re_endCoord, lt_div_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  -- The area of `u` over the disc is `ε` times the area of the end disc, and `ε² = 1`.
  have hε (a h r : ℝ) : a + p.endSign * 1 * h - r = p.endSign * (p.endSign * a + h) - r := by
    linear_combination (-a) * p.endSign_mul_endSign
  rw [hω.integral_floerEnergyDensity_pssPlanePerturbation_closedBall hH hHs hu (by linarith), hcurv,
    smoothTransition.one_of_one_le (by linarith : (1 : ℝ) ≤ R - 1), cappedLoopAction_def,
    ω.rectangleIntegral_endDisc hu R]
  exact hε _ _ _

/-- **The energy identity on discs of a PSS plane, against an arbitrary cap.** Let `K` be the
perturbation of a PSS plane given by a period-one `C¹` Hamiltonian `H` on a finite-dimensional
manifold with a nondegenerate two-form `ω`, let `u` be a `C²` map, `R ≥ 2`, and let `D` be any
disc bounding the loop `ℓ_R(t) = u(φ(ε R + i t))`. Then

`∫_{D_R} E = ε (A_H(ℓ_R, D) - ω(D ⋆ D_R⁻¹)) - ∫_ℂ R_K(u)`,

where `D ⋆ D_R⁻¹` is the sphere obtained by gluing `D` to the end disc `D_R` run backwards
(`TauCeti.rectangleTrans`). On the negative plane, `ε = -1`, this is the energy identity
`E = -A_H(ℓ_R, D) + ω(A) - ∫ R_K` of the plane with output cap `D`, in the class `A` of the sphere
formed by `D` and the plane. -/
theorem integral_floerEnergyDensity_pssPlanePerturbation_closedBall_of_isLoopCylinder
    {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {u : ℝ × ℝ → M}
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u) {R : ℝ} (hR : 2 ≤ R) {D : ℝ × ℝ → M} {x : M}
    (hD : IsLoopCylinder I D (fun _ ↦ x) (fun t ↦ u (Complex.equivRealProdCLM
      (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))))) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R)),
        ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      p.endSign * (cappedLoopAction ω.1 H (fun t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) D -
          rectangleIntegral ω.1 (rectangleTrans D (p.endDisc u R ∘ Prod.map (fun s ↦ 1 - s) id))
            (0, 0) (1, 1)) -
        ∫ z, ω.hamiltonianCurvature
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  rw [hω.integral_floerEnergyDensity_pssPlanePerturbation_closedBall_eq_endSign_mul_cappedLoopAction
      hH hHs (hu.of_le one_le_two) hR,
    ← cappedLoopAction_sub_cappedLoopAction (ω.isSmoothForm.of_le (by simp)) H
      (isLoopCylinder_endDisc p hu R) hD, sub_sub_cancel]

omit [FiniteDimensional ℝ E] in
/-- The integrated curvature of the perturbation of a PSS plane over the plane is at most `B` in
absolute value, if `|H| ≤ B`. -/
private theorem abs_integral_hamiltonianCurvature_le (ω : SmoothTwoForm I M) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {B : ℝ} (hB : ∀ t x, |H t x| ≤ B)
    (u : ℝ × ℝ → M) :
    |∫ z, ω.hamiltonianCurvature
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)| ≤ B := by
  have hB₀ : 0 ≤ B := (abs_nonneg _).trans (hB 0 (u 0))
  rw [← ENNReal.ofReal_le_ofReal_iff hB₀, ← Real.enorm_eq_ofReal_abs]
  exact (enorm_integral_le_lintegral_enorm _).trans
    (ω.lintegral_enorm_hamiltonianCurvature_pssPlanePerturbation_le hH hHs hB u)

/-- **The energy and the capped action on discs of a PSS plane.** If `|H| ≤ B`, then for every
`R ≥ 2` the Floer energy of a `C¹` map over the disc `‖w‖ ≤ exp (2πR)` differs from `ε` times the
capped action `A_H(ℓ_R, D_R)` of its boundary loop by at most `B`, uniformly in `R`. -/
theorem abs_integral_floerEnergyDensity_pssPlanePerturbation_closedBall_sub_le
    {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {B : ℝ} (hB : ∀ t x, |H t x| ≤ B)
    {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) {R : ℝ} (hR : 2 ≤ R) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R)),
        ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) -
      p.endSign * cappedLoopAction ω.1 H (fun t ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) (p.endDisc u R)| ≤ B := by
  rw [hω.integral_floerEnergyDensity_pssPlanePerturbation_closedBall_eq_endSign_mul_cappedLoopAction
      hH hHs hu hR, sub_sub_cancel_left, abs_neg]
  exact abs_integral_hamiltonianCurvature_le ω hH hHs hB u

/-- **The capped action bound on the circles of a PSS plane.** Let `K` be the perturbation of a
PSS plane given by a period-one `C¹` Hamiltonian `H` with `|H| ≤ B` on a finite-dimensional
manifold with a nondegenerate two-form `ω`, and let `u` be a `C¹` map solving the Floer equation
`(du - X_K)^{0,1} = 0` on the disc `‖w‖ ≤ exp (2πR)`, `R ≥ 2`, for almost complex structures
`J(z)` tamed by `ω`. Then the capped action of the loop `ℓ_R(t) = u(φ(ε R + i t))` along its
boundary circle, capped by the end disc, satisfies `-B ≤ ε A_H(ℓ_R, D_R)`: on the negative plane
`A_H(ℓ_R, D_R) ≤ B`, and on the positive plane `-B ≤ A_H(ℓ_R, D_R)`. -/
theorem neg_le_endSign_mul_cappedLoopAction_pssPlanePerturbation
    {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate) (hH : Periodic H 1)
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
      (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) (p.endDisc u R) := by
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
for almost complex structures `J(z)` tamed by `ω`. If the capped actions `A_H(ℓ_R, D_R)` of the end
loops `ℓ_R(t) = u(φ(ε R + i t))`, capped by the end discs, converge to `a` as `R → ∞`, then the
energy of `u` is

`E(u) = ε a - ∫_ℂ R_K(u)`. -/
theorem lintegral_floerEnergyDensity_pssPlanePerturbation_eq
    {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {u : ℝ × ℝ → M}
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedMFDeriv (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z).toLinearMap)
    {a : ℝ} (ha : Tendsto (fun R ↦ cappedLoopAction ω.1 H (fun t ↦ u (Complex.equivRealProdCLM
      (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) (p.endDisc u R)) atTop (𝓝 a)) :
    ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) =
      ENNReal.ofReal (p.endSign * a - ∫ z, ω.hamiltonianCurvature
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) := by
  -- Exhaust the plane by the discs `D_(n+2)`.
  set T : ℕ → Set (ℝ × ℝ) := fun n ↦
    Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * (n + 2)))
  have hmono : Monotone T := fun m n hmn ↦ preimage_mono (Metric.closedBall_subset_closedBall
    (Real.exp_le_exp.2 (by gcongr)))
  have hunion : ⋃ n, T n = univ := by
    refine eq_univ_of_forall fun z ↦ mem_iUnion.2 ?_
    obtain ⟨n, hn⟩ := exists_nat_ge ‖Complex.equivRealProdCLM.symm z‖
    refine ⟨n, ?_⟩
    simp only [T, mem_preimage, Metric.mem_closedBall, dist_zero_right]
    have h := Real.add_one_le_exp (2 * π * (n + 2))
    nlinarith [Real.one_le_pi_div_two, n.cast_nonneg (α := ℝ)]
  -- On each disc the energy is the integral of a nonnegative integrable function.
  have hE (n : ℕ) : ∫⁻ z in T n, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) =
      ENNReal.ofReal (∫ z in T n, ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) :=
    (ofReal_integral_eq_lintegral_ofReal
      (hω.integrableOn_floerEnergyDensity_pssPlanePerturbation_closedBall hH hHs hu _)
      (ae_of_all _ fun z ↦ floerEnergyDensity_nonneg hω (hJ z) (hfloer z))).symm
  have hlim : Tendsto (fun n ↦ ∫⁻ z in T n, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z)) atTop
      (𝓝 (∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z))) := by
    rw [← setLIntegral_univ, ← hunion, setLIntegral_iUnion_of_directed _ hmono.directed_le]
    exact tendsto_atTop_iSup fun m n hmn ↦
      lintegral_mono' (Measure.restrict_mono (hmono hmn) le_rfl) le_rfl
  -- The energy over the discs converges to `ε a` minus the integrated curvature.
  have hn : Tendsto (fun n : ℕ ↦ (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hdisc : Tendsto (fun n : ℕ ↦ ∫ z in T n, ω.floerEnergyDensity
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) atTop
      (𝓝 (p.endSign * a - ∫ z, ω.hamiltonianCurvature
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))) := by
    refine (((ha.comp hn).const_mul p.endSign).sub_const _).congr fun n ↦ ?_
    rw [Function.comp_apply,
      hω.integral_floerEnergyDensity_pssPlanePerturbation_closedBall_eq_endSign_mul_cappedLoopAction
        hH hHs hu (by linarith [n.cast_nonneg (α := ℝ)])]
  refine tendsto_nhds_unique hlim ?_
  simp only [hE]
  exact (ENNReal.continuous_ofReal.tendsto _).comp hdisc

/-- **The energy bound for a PSS plane in a manifold.** Under the hypotheses of
`lintegral_floerEnergyDensity_pssPlanePerturbation_eq`, if moreover
`|H| ≤ B`, then the energy of `u` is at most `ε a + B`. -/
theorem lintegral_floerEnergyDensity_pssPlanePerturbation_le
    {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {B : ℝ} (hB : ∀ t x, |H t x| ≤ B)
    {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedMFDeriv (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z).toLinearMap)
    {a : ℝ} (ha : Tendsto (fun R ↦ cappedLoopAction ω.1 H (fun t ↦ u (Complex.equivRealProdCLM
      (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) (p.endDisc u R)) atTop (𝓝 a)) :
    ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≤
      ENNReal.ofReal (p.endSign * a + B) := by
  rw [hω.lintegral_floerEnergyDensity_pssPlanePerturbation_eq hH hHs hu hJ hfloer ha]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith [neg_abs_le (∫ z, ω.hamiltonianCurvature
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)),
    abs_integral_hamiltonianCurvature_le (p := p) ω hH hHs hB u]

/-- **The capped action bound for a PSS plane in a manifold.** Under the hypotheses of
`lintegral_floerEnergyDensity_pssPlanePerturbation_eq`, if moreover
`|H| ≤ B`, then the limiting capped action `a` of the end satisfies `-B ≤ ε a`: on the negative
plane `a ≤ B`, and on the positive plane `-B ≤ a`. This is the limit `R → ∞` of
`neg_le_endSign_mul_cappedLoopAction_pssPlanePerturbation`. -/
theorem neg_le_endSign_mul_of_tendsto_cappedLoopAction_pssPlanePerturbation
    {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {B : ℝ} (hB : ∀ t x, |H t x| ≤ B)
    {u : ℝ × ℝ → M} (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedMFDeriv (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z).toLinearMap)
    {a : ℝ} (ha : Tendsto (fun R ↦ cappedLoopAction ω.1 H (fun t ↦ u (Complex.equivRealProdCLM
      (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) (p.endDisc u R)) atTop (𝓝 a)) :
    -B ≤ p.endSign * a :=
  ge_of_tendsto (ha.const_mul _) <| eventually_atTop.2 ⟨2, fun _ hR ↦
    hω.neg_le_endSign_mul_cappedLoopAction_pssPlanePerturbation hH hHs hB hu hR
      (fun z _ ↦ hJ z) fun z _ ↦ hfloer z⟩

end IsNondegenerate

end SmoothTwoForm

end TauCeti
