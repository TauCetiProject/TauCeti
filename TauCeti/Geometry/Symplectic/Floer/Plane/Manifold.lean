/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold
public import TauCeti.Geometry.Symplectic.Floer.Plane.CappedAction
import TauCeti.Algebra.Ring.Periodic

/-!
# Finite-energy PSS planes in a manifold

Let `K` be the perturbation `TauCeti.Floer.PSSPlane.perturbation` of a PSS plane `p`, built from a
period-one `C¹` Hamiltonian `H` on a finite-dimensional manifold `M` with a nondegenerate two-form
`ω`, such as a closed symplectic manifold, and let `ε = ±1` be the sign of the end of `p`. Let `u`
be a solution of the Floer equation `(du - X_K)^{0,1} = 0`. For `R ∈ ℝ` write
`ℓ_R(t) = u(φ(ε R + i t))` for the loop of `u` along the circle `‖w‖ = exp (2πR)`, where
`φ(z) = exp (2π ε z)` is the end lift. This file proves the two facts about the end of a
finite-energy plane on which its energy identity and its place in the Floer complex rest. On a
symplectic vector space they are `TauCeti.Geometry.Symplectic.Floer.Plane.Orbit`.

**The capped end actions converge.** The disc `D_R = {‖w‖ ≤ exp (2πR)}` caps `ℓ_R` by the
restriction `u ∘ endDisc R` of `u`, and for `R ≥ 2` the energy of `u` over `D_R` is
`ε A_H(ℓ_R, u ∘ endDisc R) - ∫_ℂ R_K(u)`, by the energy identity on discs of
`TauCeti.Geometry.Symplectic.Floer.Plane.CappedAction`. The energy density of a solution is
nonnegative for tamed almost complex structures, and the discs increase with `R`, so
`ε A_H(ℓ_R, u ∘ endDisc R)` increases with `R` on `[2, ∞)`
(`SmoothTwoForm.IsNondegenerate.monotoneOn_endSign_mul_cappedLoopAction_pssPlanePerturbation`).
If the energy of `u` is finite, it bounds these actions above, so they converge to some `a`, and
the energy of `u` is `ε a - ∫_ℂ R_K(u)`
(`SmoothTwoForm.IsNondegenerate.exists_tendsto_cappedLoopAction_pssPlanePerturbation`). This
removes the convergence hypothesis of the energy identity
`SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_pssPlanePerturbation_eq`.

**The end breaks off a periodic orbit.** On the positive plane the end, read through the end lift,
is the half-cylinder `s > a` for the cylindrical datum `H(t) dt`. Since `φ` is holomorphic, the
Floer equation pulls back along it
(`SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_realChart_positive`), and since `φ` is
injective on the half-strip `s > a`, `0 ≤ t < 1`, and preserves orientation, the energy of the
half-cylinder is at most that of `u` on the end
(`SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_realChart_positive_le`). The finite-energy
half-cylinder theorem for a manifold target, of
`TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold`, then gives a one-periodic orbit `x` of
`X_H` with `ℓ_{R_n} → x` along some `R_n → ∞`. The negative plane is the positive plane for the
reversed Hamiltonian `-H(-t)` (`TauCeti.Floer.PSSPlane.perturbation_negative`), and reversing
time turns the orbits of that Hamiltonian into orbits of `H`
(`TauCeti.comp_neg_mem_periodicSolutions`). The result is
`SmoothTwoForm.IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_pssPlanePerturbation`.
As in the half-cylinder theorem, convergence is measured through a `C¹` map `e : M → F` into a
normed space that is injective with injective differential on a compact set containing the end of
`u`; on a closed manifold such a map exists by Mathlib's `exists_embedding_euclidean_of_compact`.

The limit `a` of the capped actions is not identified here with a capped action of the orbit `x`:
that needs a cap of `x` obtained from the caps `u ∘ endDisc R_n` in the limit.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  asymptotics and the energy of the perturbed planes of the PSS maps.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits.
-/

public section

open Set Real Function MeasureTheory Filter Manifold
open TauCeti.Complex (realChart contDiff_realChart)
open scoped Topology

namespace TauCeti.SmoothTwoForm

open Floer Floer.PSSPlane

variable {E G M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {ω : SmoothTwoForm I M} {H : ℝ → M → ℝ}
  {p : PSSPlane} {u : ℝ × ℝ → M}

/-! ### Convergence of the capped end actions -/

namespace IsNondegenerate

variable [FiniteDimensional ℝ E]

/-- The energy density of a `C¹` map for the datum of a PSS plane is integrable over every disc
`‖w‖ ≤ exp (2πR)`. -/
private theorem integrableOn_floerEnergyDensity_pssPlanePerturbation_closedBall
    (hω : ω.IsNondegenerate) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (R : ℝ) :
    IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      (Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R))) :=
  hω.integrableOn_floerEnergyDensity isOpen_univ hu.contMDiffOn
    (contMDiff_uncurry_perturbation hH hHs 1).contMDiffOn
    (contMDiff_uncurry_perturbation hH hHs Complex.I).contMDiffOn
    (Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_closedBall _ _))
    (subset_univ _)
    (ω.integrableOn_hamiltonianCurvature_pssPlanePerturbation_closedBall (p := p) hH hHs
      hu.continuous _)

/-- The energy of a solution of the Floer equation over the disc `‖w‖ ≤ exp (2πR)` increases with
`R`. -/
private theorem monotone_setIntegral_floerEnergyDensity_pssPlanePerturbation_closedBall
    (hω : ω.IsNondegenerate) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedMFDeriv (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z).toLinearMap) :
    Monotone fun R : ℝ ↦
      ∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R)),
        ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z := by
  intro R R' hR
  refine setIntegral_mono_set
    (integrableOn_floerEnergyDensity_pssPlanePerturbation_closedBall (p := p) hω hH hHs hu _)
    (ae_of_all _ fun z ↦ floerEnergyDensity_nonneg hω (hJ z) (hfloer z))
    (Eventually.of_forall fun z hz ↦ ?_)
  exact Metric.closedBall_subset_closedBall
    (Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])) hz

/-- **The capped end actions of a PSS plane are monotone.** Let `K` be the perturbation of a PSS
plane given by a period-one `C¹` Hamiltonian `H` on a finite-dimensional manifold with a
nondegenerate two-form `ω`, and let `u` be a `C¹` map solving the Floer equation
`(du - X_K)^{0,1} = 0` on the whole plane for almost complex structures `J(z)` tamed by `ω`. Then
`ε A_H(ℓ_R, u ∘ endDisc R)` increases with `R` on `[2, ∞)`, where `ℓ_R(t) = u(φ(ε R + i t))` is
the loop along the circle `‖w‖ = exp (2πR)`, capped by the disc of the plane that it bounds: it is
the energy over that disc plus a constant. -/
theorem monotoneOn_endSign_mul_cappedLoopAction_pssPlanePerturbation
    (hω : ω.IsNondegenerate) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedMFDeriv (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z).toLinearMap) :
    MonotoneOn (fun R ↦ p.endSign * cappedLoopAction ω.1 H (fun t ↦ u (Complex.equivRealProdCLM
      (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) (u ∘ p.endDisc R)) (Ici 2) := by
  intro R hR R' hR' hRR'
  have h := monotone_setIntegral_floerEnergyDensity_pssPlanePerturbation_closedBall hω hH hHs hu hJ
    hfloer hRR'
  beta_reduce at h
  rw [hω.integral_floerEnergyDensity_pssPlanePerturbation_closedBall_eq_endSign_mul_cappedLoopAction
      hH hHs hu hR,
    hω.integral_floerEnergyDensity_pssPlanePerturbation_closedBall_eq_endSign_mul_cappedLoopAction
      hH hHs hu hR'] at h
  simpa using h

/-- **The capped end actions of a finite-energy PSS plane converge.** Let `K` be the perturbation
of a PSS plane given by a period-one `C¹` Hamiltonian `H` on a finite-dimensional manifold with a
nondegenerate two-form `ω`, and let `u` be a `C¹` map solving the Floer equation
`(du - X_K)^{0,1} = 0` on the whole plane for almost complex structures `J(z)` tamed by `ω`, with
finite energy. Then the capped actions `A_H(ℓ_R, u ∘ endDisc R)` of the loops
`ℓ_R(t) = u(φ(ε R + i t))`, each capped by the disc of the plane that it bounds, converge to some
`a` as `R → ∞`, and the energy of `u` is

`E(u) = ε a - ∫_ℂ R_K(u)`. -/
theorem exists_tendsto_cappedLoopAction_pssPlanePerturbation
    (hω : ω.IsNondegenerate) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedMFDeriv (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z).toLinearMap)
    (hE : ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∃ a : ℝ, Tendsto (fun R ↦ cappedLoopAction ω.1 H (fun t ↦ u (Complex.equivRealProdCLM
        (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) (u ∘ p.endDisc R)) atTop
          (𝓝 a) ∧
      ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) =
        ENNReal.ofReal (p.endSign * a - ∫ z, ω.hamiltonianCurvature
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) := by
  set C := ∫ z, ω.hamiltonianCurvature
    (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)
  -- The energy over the disc `D_R` increases with `R` and is bounded by the total energy.
  have hmono := monotone_setIntegral_floerEnergyDensity_pssPlanePerturbation_closedBall hω hH hHs
    hu hJ hfloer
  have hbdd : BddAbove (range fun R : ℝ ↦
      ∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R)),
        ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) := by
    refine ⟨(∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z)).toReal,
      ?_⟩
    rintro _ ⟨R, rfl⟩
    refine (integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun z ↦ floerEnergyDensity_nonneg hω (hJ z) (hfloer z))
      (integrableOn_floerEnergyDensity_pssPlanePerturbation_closedBall hω hH hHs hu _).1).trans_le
      ?_
    exact ENNReal.toReal_mono hE (setLIntegral_le_lintegral _ _)
  -- On `[2, ∞)` the capped action is `ε` times the energy over `D_R` plus the curvature term.
  have ha : Tendsto (fun R ↦ cappedLoopAction ω.1 H (fun t ↦ u (Complex.equivRealProdCLM
      (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) (u ∘ p.endDisc R)) atTop
        (𝓝 (p.endSign * ((⨆ R : ℝ, ∫ z in Complex.equivRealProdCLM.symm ⁻¹'
          Metric.closedBall 0 (Real.exp (2 * π * R)), ω.floerEnergyDensity
            (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z) +
          C))) := by
    refine (((tendsto_atTop_ciSup hmono hbdd).add_const C).const_mul p.endSign).congr' <|
      (eventually_ge_atTop 2).mono fun R hR ↦ ?_
    have hid :=
      hω.integral_floerEnergyDensity_pssPlanePerturbation_closedBall_eq_endSign_mul_cappedLoopAction
        (p := p) hH hHs hu hR
    rw [hid, sub_add_cancel, ← mul_assoc, endSign_mul_endSign, one_mul]
  exact ⟨_, ha, hω.lintegral_floerEnergyDensity_pssPlanePerturbation_eq hH hHs hu hJ hfloer ha⟩

end IsNondegenerate

/-! ### The end of the positive plane as a half-cylinder -/

/-- From `s = 2` on, the pullback of the datum of the positive plane along its end lift is the
cylindrical datum `H(t) dt`, so the perturbed derivatives of the two data agree there. -/
private theorem perturbedMFDeriv_comp_realChart_positive (ω : SmoothTwoForm I M)
    (hH : Periodic H 1) (u : ℝ × ℝ → M) {z : ℝ × ℝ} (hz : 2 ≤ z.1) :
    ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z =
      ω.perturbedMFDeriv
        (perturbationPullback (realChart positive.cylindricalEndLift)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          stdComplexLineReal)
        (perturbationPullback (realChart positive.cylindricalEndLift)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          stdComplexLineImag) u z := by
  rw [positive.perturbationPullback_realChart_cylindricalEndLift_stdComplexLineReal H,
    positive.perturbationPullback_realChart_cylindricalEndLift_stdComplexLineImag hH]
  refine ContinuousLinearMap.ext fun a ↦ ?_
  simp only [perturbedMFDeriv_apply, endSign_positive, one_mul,
    smoothTransition.one_of_one_le (by linarith : (1 : ℝ) ≤ z.1 - 1)]

/-- **The Floer equation on the end of the positive plane, for a manifold target.** From `s = 2`
on, if `u` solves the Floer equation for the datum of the positive plane and an almost complex
structure `J` at the image of `(s, t)` under the end lift `φ`, then `u ∘ φ` solves the Floer
equation at `(s, t)` for the cylindrical datum `H(t) dt` and the same structure `J`. -/
theorem isComplexLinearMap_perturbedMFDeriv_comp_realChart_positive (ω : SmoothTwoForm I M)
    (hH : Periodic H 1) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H))
    {z : ℝ × ℝ} (hz : 2 ≤ z.1)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (realChart positive.cylindricalEndLift z))
    {J : AlmostComplexStructure (TangentSpace I (u (realChart positive.cylindricalEndLift z)))}
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u (realChart positive.cylindricalEndLift z)).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2)
        (u ∘ realChart positive.cylindricalEndLift) z).toLinearMap := by
  rw [perturbedMFDeriv_comp_realChart_positive ω hH _ hz]
  exact ω.isComplexLinearMap_perturbedMFDeriv_perturbationPullback
    ((contDiff_realChart positive.contDiff_cylindricalEndLift).differentiable one_ne_zero z) hu
    (mdifferentiableAt_perturbation_target hH hHs _ _ 1)
    (mdifferentiableAt_perturbation_target hH hHs _ _ Complex.I)
    (Floer.isComplexLinearMap_fderiv_realChart (positive.hasDerivAt_cylindricalEndLift _)) hfloer

/-- From `s = 2` on, where `u` is differentiable at the image of `(s, t)` under the end lift `φ`
of the positive plane, the energy density of `u ∘ φ` at `(s, t)` for the cylindrical datum
`H(t) dt` is the Jacobian of `φ` times the energy density of `u` for the datum of the plane. -/
private theorem floerEnergyDensity_comp_realChart_positive (ω : SmoothTwoForm I M)
    (hH : Periodic H 1) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H))
    {z : ℝ × ℝ} (hz : 2 ≤ z.1)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (realChart positive.cylindricalEndLift z)) :
    ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2)
        (u ∘ realChart positive.cylindricalEndLift) z =
      (fderiv ℝ (realChart positive.cylindricalEndLift) z).det *
        ω.floerEnergyDensity
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u
          (realChart positive.cylindricalEndLift z) := by
  rw [floerEnergyDensity_def, perturbedMFDeriv_comp_realChart_positive ω hH _ hz,
    ← floerEnergyDensity_def]
  exact ω.floerEnergyDensity_perturbationPullback
    ((contDiff_realChart positive.contDiff_cylindricalEndLift).differentiable one_ne_zero z) hu
    (mdifferentiableAt_perturbation_target hH hHs _ _ 1)
    (mdifferentiableAt_perturbation_target hH hHs _ _ Complex.I)

/-- **The energy on the end of the positive plane, for a manifold target.** For `a ≥ 2`, if `u` is
differentiable on the part `‖w‖ > exp (2πa)` of the positive plane, then the energy of `u ∘ φ` on
the half-cylinder `s > a`, `0 ≤ t ≤ 1`, for the cylindrical datum `H(t) dt`, is at most the energy
of `u` on that part of the plane: the end lift `φ` is injective on the half-strip `0 ≤ t < 1` and
preserves orientation. -/
theorem setLIntegral_floerEnergyDensity_comp_realChart_positive_le (ω : SmoothTwoForm I M)
    (hH : Periodic H 1) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {a : ℝ}
    (ha : 2 ≤ a) (hu : ∀ z, Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖ →
      MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z) :
    ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ H w.2) (u ∘ realChart positive.cylindricalEndLift) z) ≤
      ∫⁻ z in {z | Real.exp (2 * π * a) < ‖Complex.equivRealProdCLM.symm z‖},
        ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z) := by
  have hS : MeasurableSet (Ioi a ×ˢ Ico (0 : ℝ) 1) :=
    measurableSet_Ioi.prod measurableSet_Ico
  have hae : (Ioi a ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) =ᵐ[volume] Ioi a ×ˢ Ico 0 1 := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Filter.EventuallyEqSet.rfl Ico_ae_eq_Icc.symm
  rw [setLIntegral_congr hae, ← lintegral_ofReal_image_eq_lintegral_ofReal_of_eq_abs_det_mul hS
    (injOn_realChart_positive a)
    (fun z _ ↦ (contDiff_realChart positive.contDiff_cylindricalEndLift).differentiable
      one_ne_zero z) fun z hz ↦ by
      rw [floerEnergyDensity_comp_realChart_positive ω hH hHs (ha.trans hz.1.le)
        (hu _ (exp_lt_norm_realChart_positive hz.1)),
        abs_of_pos (positive.det_fderiv_realChart_cylindricalEndLift_pos z)]]
  refine lintegral_mono_set ?_
  rintro _ ⟨z, hz, rfl⟩
  exact exp_lt_norm_realChart_positive hz.1

namespace IsNondegenerate

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {e : M → F}

/-- **The asymptotic orbit at the end of the positive plane, for a manifold target.** This is the
case `p = positive` of
`SmoothTwoForm.IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_pssPlanePerturbation`,
for an arbitrary Hamiltonian; the negative plane is reduced to it. -/
private theorem exists_mem_periodicSolutions_tendstoUniformly_positive (hω : ω.IsNondegenerate)
    (hH : Periodic H 1) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {K : Set M} (hK : IsCompact K) (he_inj : InjOn e K)
    (hde : ∀ q ∈ K, Injective (mvfderiv I e q)) {r : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (huK : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ K)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ positive.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ K) ∧
      ∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (Complex.equivRealProdCLM
          (positive.cylindricalEndLift (↑(positive.endSign * R n) + ↑t * Complex.I))))) (e ∘ x)
          atTop ∧
        ∀ t, Tendsto (fun n ↦ u (Complex.equivRealProdCLM
          (positive.cylindricalEndLift (↑(positive.endSign * R n) + ↑t * Complex.I)))) atTop
          (𝓝 (x t)) := by
  -- Shrink the end to a part `‖w‖ > exp (2πa)` with `a ≥ 2`, where the datum is cylindrical.
  obtain ⟨a, ha, hsub⟩ := exists_two_le_exp_lt_norm_subset r
  have hmem {z : ℝ × ℝ} (hz : a < z.1) :
      r < ‖Complex.equivRealProdCLM.symm (realChart positive.cylindricalEndLift z)‖ :=
    hsub (exp_lt_norm_realChart_positive hz)
  have hopen : IsOpen {z : ℝ × ℝ | r < ‖Complex.equivRealProdCLM.symm z‖} :=
    isOpen_lt continuous_const (by fun_prop)
  have hmd (z : ℝ × ℝ) (hz : r < ‖Complex.equivRealProdCLM.symm z‖) :
      MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z :=
    (hu.contMDiffAt (hopen.mem_nhds hz)).mdifferentiableAt one_ne_zero
  have hφ : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) 1 (realChart positive.cylindricalEndLift) :=
    (contDiff_realChart positive.contDiff_cylindricalEndLift).contMDiff
  -- The structures `J ∘ φ` along the half-cylinder.
  let J' : ∀ z, AlmostComplexStructure
      (TangentSpace I ((u ∘ realChart positive.cylindricalEndLift) z)) :=
    fun z ↦ J (realChart positive.cylindricalEndLift z)
  have hfloer' (z : ℝ × ℝ) (hz : z ∈ Ioi a ×ˢ Icc (0 : ℝ) 1) :
      mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ realChart positive.cylindricalEndLift) z stdComplexLineReal +
        J' z
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ realChart positive.cylindricalEndLift) z
            stdComplexLineImag - ω.hamiltonianVectorField (H z.2)
              ((u ∘ realChart positive.cylindricalEndLift) z)) = 0 := by
    have h := (ω.isComplexLinearMap_perturbedMFDeriv_iff _ _ _ _ _).1
      (ω.isComplexLinearMap_perturbedMFDeriv_comp_realChart_positive hH hHs (ha.trans hz.1.le)
        (hmd _ (hmem hz.1)) (hfloer _ (hmem hz.1)))
    simpa using h
  have hE' : ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
      (fun w ↦ H w.2) (u ∘ realChart positive.cylindricalEndLift) z) ≠ ⊤ :=
    ((ω.setLIntegral_floerEnergyDensity_comp_realChart_positive_le hH hHs ha
      fun z hz ↦ hmd z (hsub hz)).trans_lt ((lintegral_mono_set hsub).trans_lt hE.lt_top)).ne
  obtain ⟨x, hx, hxK, R, -, hR, hconv, hpt, -⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact hHs hH he hK he_inj hde
      (hu.comp hφ.contMDiffOn fun z hz ↦ hmem hz.1)
      (fun s _ t ↦ by
        simpa only [comp_apply, realChart_positive_mk] using
          positive.periodic_comp_cylindricalEndLift u s t)
      (fun s hs t ↦ huK _ (hmem hs)) J' hc
      (fun z hz ↦ hJc _ (hmem hz.1)) hfloer' hE'
  simp only [comp_apply, realChart_positive_mk] at hconv hpt
  exact ⟨x, hx, hxK, R, hR, hconv, hpt⟩

/-- **The asymptotic orbit at the end of a finite-energy PSS plane in a manifold.** Let `K` be the
perturbation of a PSS plane `p` given by a period-one `C¹` Hamiltonian `H` on a finite-dimensional
manifold `M` with a nondegenerate two-form `ω`. Let `u` be `C¹` on a part `‖w‖ > r` of the end,
with image in a compact set `C`, solving the Floer equation `(du - X_K)^{0,1} = 0` there, with
finite energy there. Let `e : M → F` be a `C¹` map into a finite-dimensional normed space,
injective on `C` and with injective differential at the points of `C`, and suppose that the almost
complex structures are uniformly tame with respect to `e` on the end:
`c ‖d e v‖² ≤ ω(v, J(z) v)` with `c > 0`. Then there are a one-periodic orbit `x` of the
Hamiltonian vector field in `C` and radii `R_n → ∞` such that the loops `ℓ_{R_n}(t) =
u(φ(ε R_n + i t))` converge to `x`, pointwise in `M` and uniformly after applying `e`. Here `φ` is
the end lift `p.cylindricalEndLift` and `ε = p.endSign`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_pssPlanePerturbation (p : PSSPlane)
    (hω : ω.IsNondegenerate) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {C : Set M} (hC : IsCompact C) (he_inj : InjOn e C)
    (hde : ∀ q ∈ C, Injective (mvfderiv I e q)) {r : ℝ}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z | r < ‖Complex.equivRealProdCLM.symm z‖})
    (huC : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → u z ∈ C)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ → ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z, r < ‖Complex.equivRealProdCLM.symm z‖ →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hE : ∫⁻ z in {z | r < ‖Complex.equivRealProdCLM.symm z‖},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤) :
    ∃ x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1, (∀ t, x t ∈ C) ∧
      ∃ R : ℕ → ℝ, Tendsto R atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R n) + ↑t * Complex.I))))) (e ∘ x) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (Complex.equivRealProdCLM
          (p.cylindricalEndLift (↑(p.endSign * R n) + ↑t * Complex.I)))) atTop (𝓝 (x t)) := by
  cases p
  · exact exists_mem_periodicSolutions_tendstoUniformly_positive hω hH hHs he hC he_inj hde hu huC
      J hc hJc hfloer hE
  -- The negative plane is the positive plane for the reversed Hamiltonian `-H(-t)`.
  rw [perturbation_negative] at hfloer hE
  have hHs' : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry fun t y ↦ -H (-t) y) :=
    (hHs.comp ((contDiff_neg.contMDiff (n := 1)).prodMap contMDiff_id)).neg
  obtain ⟨y, hy, hyC, R, hR, hconv, hpt⟩ :=
    exists_mem_periodicSolutions_tendstoUniformly_positive (H := fun t y ↦ -H (-t) y) hω
      (hH.comp_neg.comp Neg.neg) hHs' he hC he_inj hde hu huC J hc hJc hfloer hE
  -- Reversing time turns the orbit `y` of `-H(-t)` into an orbit of `H`.
  have hx : (fun t ↦ y (-t)) ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) 1 := by
    have h := comp_neg_mem_periodicSolutions hy
    convert h using 3 with t
    have hrev : (fun x ↦ -H (-(-t)) x) = -H t := by
      funext
      simp
    funext q
    rw [hrev, hamiltonianVectorField_neg, neg_neg]
  refine ⟨_, hx, fun t ↦ hyC _, R, hR, ?_, fun t ↦ ?_⟩
  · simp only [cylindricalEndLift_negative_endSign_mul]
    exact hconv.comp fun t ↦ -t
  · simp only [cylindricalEndLift_negative_endSign_mul]
    exact hpt (-t)

end IsNondegenerate

end TauCeti.SmoothTwoForm
