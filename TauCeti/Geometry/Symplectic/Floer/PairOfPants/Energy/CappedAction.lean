/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Asymptotic
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Annulus
public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction.Capped

/-!
# The energy of a pair of pants in a manifold in terms of capped actions

Let `K` be the pair-of-pants perturbation `TauCeti.Floer.pairOfPantsPerturbation` built from
period-one `C¹` Hamiltonians `H_q` on the three ends of `S = ℂ ∖ {0, 1}`, and let `u` be a map of
`S` into a finite-dimensional manifold `M` with a nondegenerate two-form `ω`, such as a closed
symplectic manifold. Write `ℓ_{q,R}(t) = u(φ_q(±R + i t))` for the loop of `u` along the circle at
height `R` of the end `q`. Over the truncation `S_R` of `S` at a height `R ≥ 2`, the Floer energy
of `u` is its symplectic area plus the Hamiltonian terms of these loops, with the sign `+` on the
inputs `0`, `1` and `-` on the output `∞`, minus the integrated curvature
(`integral_floerEnergyDensity_pairOfPantsPerturbation_truncation` in the namespace
`TauCeti.SmoothTwoForm.IsNondegenerate`). On a manifold whose symplectic form does not vanish on
spheres, the action of a loop is the capped action `A_H(γ, D) = ∫ D^*ω + ∫₀¹ H(t, γ(t)) dt` of
the loop together with a disc `D` bounding it (`TauCeti.cappedLoopAction`). This file writes the
area term through caps.

**The caps.** Let `D₀` and `D₁` be discs with a common centre bounding the loops of `u` along the
circles at height `0` of the input ends, which touch at `1/2`, and sharing their seam. Following
each of them by `u` along the end annulus between the heights `0` and `R`
(`TauCeti.Floer.endAnnulusChart`) gives discs `D₀^R`, `D₁^R` of the input loops at height `R`.
Gluing `D₀` and `D₁` to `u` over `S₀` gives the disc `TauCeti.Floer.pairOfPantsGluedDisc D₀ D₁ u`
of the output loop at height `0`, and following it by `u` along the output annulus gives a disc
`D_∞^R` of the output loop at height `R`: the cap of the output obtained by gluing the caps of the
inputs to `u` over `S_R`. Its area is `ω(D₀^R) + ω(D₁^R) - ∫_{S_R} u^*ω`
(`TauCeti.Floer.rectangleIntegral_rectangleTrans_pairOfPantsGluedDisc_comp_endAnnulusChart`).

**The energy identity.** Consequently, for `R ≥ 2`,

`∫_{S_R} E = A_{H_0}(ℓ_{0,R}, D₀^R) + A_{H_1}(ℓ_{1,R}, D₁^R) - A_{H_∞}(ℓ_{∞,R}, D_∞^R)
  - ∫_{S_R} R_K(u)`

(`integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_cappedLoopAction` in the
namespace `TauCeti.SmoothTwoForm.IsNondegenerate`). Against any other disc `D` of the output loop
the capped action changes by the area `ω(A)` of the sphere `A` glued from `D` and `D_∞^R` run
backwards, the class `D + u - D₀ - D₁` of the pair of pants relative to these caps, and

`∫_{S_R} E = A_{H_0}(ℓ_{0,R}, D₀^R) + A_{H_1}(ℓ_{1,R}, D₁^R) - A_{H_∞}(ℓ_{∞,R}, D) + ω(A)
  - ∫_{S_R} R_K(u)`

(`integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_of_isLoopCylinder` in the same
namespace). This is the energy identity `E = A₁ + A₂ - A₀ + ω(A) - ∫ R_K` of capped pairs of
pants, on the truncation `S_R` and with the loops of `u` at height `R` in place of its asymptotic
orbits. If `|H_q| ≤ B_q`, the curvature term is at most `B₀ + B₁ + B_∞` in absolute value,
uniformly in `R`
(`abs_integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_sub_cappedLoopAction_le` in
the same namespace). If the energy density of `u` is integrable over `S`, the truncations `S_R`
exhaust `S`, so as `R → ∞` the capped actions `A_{H_0}(ℓ_{0,R}, D₀^R) + A_{H_1}(ℓ_{1,R}, D₁^R) -
A_{H_∞}(ℓ_{∞,R}, D_∞^R)` converge to `∫_S E + ∫_S R_K(u)`
(`tendsto_cappedLoopAction_pairOfPantsPerturbation` in the same namespace).

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the pair-of-pants product and the energy of its solutions.
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on
  capped orbits and the action of glued caps.
-/

public section

open Set Real Function MeasureTheory Manifold Filter TauCeti.ThricePuncturedSphere
open scoped Topology

namespace TauCeti.SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  [IsManifold I (⊤ : ℕ∞) M] [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M}
  {H : Puncture → ℝ → M → ℝ}

namespace IsNondegenerate

/-- **The energy identity on a truncated pair of pants, in terms of capped actions.** Let `K` be
the pair-of-pants perturbation built from period-one `C¹` Hamiltonians `H_q` on a
finite-dimensional manifold with a nondegenerate two-form `ω`, let `u` be a map of the pair of
pants which is `C¹` on `S`, and let `D₀` and `D₁` be `C¹` maps of the plane which end at `s = 1`
at the loops of `u` along the input ends `0` and `1` at height `0` and share their seam. For
`R ≥ 2`, the Floer energy of `u` over the truncation `S_R` is the capped action of the loop of
`u` along the circle at height `R` of each input end, capped by `D₀` or `D₁` followed by `u` along
the end annulus, minus that of the output end, capped by the disc glued from `D₀` and `D₁` along
`u` followed by `u` along the output annulus, minus the integrated curvature over `S_R`. -/
theorem integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_cappedLoopAction
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {D₀ D₁ : ℝ × ℝ → M}
    (hD₀ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 D₀) (hD₁ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 D₁)
    (h₀₁ : ∀ s, D₀ (s, 1) = D₁ (s, 0)) (h₁₀ : ∀ s, D₁ (s, 1) = D₀ (s, 0))
    (h₀ : ∀ t, D₀ (1, t) = u (endChart Puncture.zero (0, t)))
    (h₁ : ∀ t, D₁ (1, t) = u (endChart Puncture.one (0, t))) {R : ℝ} (hR : 2 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      cappedLoopAction ω.val (H Puncture.zero) (fun t ↦ u (endChart Puncture.zero (R, t)))
          (rectangleTrans D₀ (u ∘ endAnnulusChart Puncture.zero 0 R)) +
        cappedLoopAction ω.val (H Puncture.one) (fun t ↦ u (endChart Puncture.one (R, t)))
          (rectangleTrans D₁ (u ∘ endAnnulusChart Puncture.one 0 R)) -
        cappedLoopAction ω.val (H Puncture.inf) (fun t ↦ u (endChart Puncture.inf (-R, t)))
          (rectangleTrans (pairOfPantsGluedDisc D₀ D₁ u)
            (u ∘ endAnnulusChart Puncture.inf 0 R)) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  -- The symplectic area over `S_R` is the area of the input caps minus that of the glued cap.
  have harea : ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R,
      (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) =
      rectangleIntegral ω.val (rectangleTrans D₀ (u ∘ endAnnulusChart Puncture.zero 0 R))
          (0, 0) (1, 1) +
        rectangleIntegral ω.val (rectangleTrans D₁ (u ∘ endAnnulusChart Puncture.one 0 R))
          (0, 0) (1, 1) -
        rectangleIntegral ω.val (rectangleTrans (pairOfPantsGluedDisc D₀ D₁ u)
          (u ∘ endAnnulusChart Puncture.inf 0 R)) (0, 0) (1, 1) := by
    rw [rectangleIntegral_rectangleTrans_pairOfPantsGluedDisc_comp_endAnnulusChart
      (ω.isSmoothForm.of_le (by simp)) hu hD₀ hD₁ h₀₁ h₁₀ h₀ h₁ (by linarith)]
    simp only [SmoothBundleForm.eval₂_apply, stdComplexLineReal, stdComplexLineImag]
    ring
  rw [hω.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation hH hHs
      isOpen_thricePuncturedSphereReal (preimage_truncation_subset_thricePuncturedSphereReal R) hu
      (by linarith), harea, smoothTransition.one_of_one_le (by linarith), one_mul,
    Puncture.sum_univ]
  simp only [cappedLoopAction_def, Puncture.endSign_zero, Puncture.endSign_one,
    Puncture.endSign_inf, endChart_mk, one_mul, neg_one_mul]
  ring

/-- **The energy identity on a truncated pair of pants, against any cap of the output.** Under
the hypotheses of
`integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_cappedLoopAction`, with `u` of
class `C²` on `S` and `D₀`, `D₁` discs centred at a common point, let `D` be any disc bounding the
loop of `u` along the circle at height `R` of the output end, and let `D_∞^R` be the disc glued
from `D₀` and `D₁` along `u` and followed by `u` along the output annulus. Then the Floer energy
of `u` over `S_R` is the capped actions of the input loops at height `R`, capped by `D₀` and `D₁`
followed by `u` along the end annuli, minus the capped action of the output loop capped by `D`,
plus the area of the sphere glued from `D` and `D_∞^R` run backwards, minus the integrated
curvature. That sphere is the class `A = D + u - D₀ - D₁` of the pair of pants relative to these
caps, and the identity is `E = A_{H_0} + A_{H_1} - A_{H_∞} + ω(A) - ∫ R_K` on `S_R`. -/
theorem integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_of_isLoopCylinder
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 2 u thricePuncturedSphereReal) {D₀ D₁ : ℝ × ℝ → M} {x : M}
    (hD₀ : IsLoopCylinder I D₀ (fun _ ↦ x) fun t ↦ u (endChart Puncture.zero (0, t)))
    (hD₁ : IsLoopCylinder I D₁ (fun _ ↦ x) fun t ↦ u (endChart Puncture.one (0, t)))
    (h₀₁ : ∀ s, D₀ (s, 1) = D₁ (s, 0)) (h₁₀ : ∀ s, D₁ (s, 1) = D₀ (s, 0)) {R : ℝ} (hR : 2 ≤ R)
    {D : ℝ × ℝ → M} {y : M}
    (hD : IsLoopCylinder I D (fun _ ↦ y) fun t ↦ u (endChart Puncture.inf (-R, t))) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      cappedLoopAction ω.val (H Puncture.zero) (fun t ↦ u (endChart Puncture.zero (R, t)))
          (rectangleTrans D₀ (u ∘ endAnnulusChart Puncture.zero 0 R)) +
        cappedLoopAction ω.val (H Puncture.one) (fun t ↦ u (endChart Puncture.one (R, t)))
          (rectangleTrans D₁ (u ∘ endAnnulusChart Puncture.one 0 R)) -
        cappedLoopAction ω.val (H Puncture.inf) (fun t ↦ u (endChart Puncture.inf (-R, t))) D +
        rectangleIntegral ω.val (rectangleTrans D
          (rectangleTrans (pairOfPantsGluedDisc D₀ D₁ u) (u ∘ endAnnulusChart Puncture.inf 0 R) ∘
            Prod.map (fun s ↦ 1 - s) id)) (0, 0) (1, 1) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  -- The glued disc followed by the output annulus is a disc of the output loop at height `R`.
  have hann := isLoopCylinder_comp_endAnnulusChart hu Puncture.inf le_rfl (by linarith : 0 ≤ R)
  simp only [mul_zero, Puncture.endSign_inf, neg_one_mul] at hann
  have hglued := (isLoopCylinder_pairOfPantsGluedDisc hu hD₀ hD₁ h₀₁ h₁₀).trans hann
  rw [hω.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_cappedLoopAction hH hHs
      (hu.of_le one_le_two) (hD₀.contMDiff.of_le one_le_two) (hD₁.contMDiff.of_le one_le_two)
      h₀₁ h₁₀ hD₀.apply_one hD₁.apply_one hR,
    ← cappedLoopAction_sub_cappedLoopAction (ω.isSmoothForm.of_le (by simp)) (H Puncture.inf)
      hglued hD]
  ring

/-- **The energy and the capped actions on a truncated pair of pants.** If `|H_q| ≤ B_q`, then
under the hypotheses of
`integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_cappedLoopAction` the Floer
energy of `u` over `S_R` differs from the capped actions of the input loops at height `R` minus
that of the output loop, capped as there, by at most `B₀ + B₁ + B_∞`, uniformly in `R ≥ 2`. -/
theorem abs_integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_sub_cappedLoopAction_le
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {B : Puncture → ℝ}
    (hB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {D₀ D₁ : ℝ × ℝ → M}
    (hD₀ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 D₀) (hD₁ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 D₁)
    (h₀₁ : ∀ s, D₀ (s, 1) = D₁ (s, 0)) (h₁₀ : ∀ s, D₁ (s, 1) = D₀ (s, 0))
    (h₀ : ∀ t, D₀ (1, t) = u (endChart Puncture.zero (0, t)))
    (h₁ : ∀ t, D₁ (1, t) = u (endChart Puncture.one (0, t))) {R : ℝ} (hR : 2 ≤ R) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      (cappedLoopAction ω.val (H Puncture.zero) (fun t ↦ u (endChart Puncture.zero (R, t)))
          (rectangleTrans D₀ (u ∘ endAnnulusChart Puncture.zero 0 R)) +
        cappedLoopAction ω.val (H Puncture.one) (fun t ↦ u (endChart Puncture.one (R, t)))
          (rectangleTrans D₁ (u ∘ endAnnulusChart Puncture.one 0 R)) -
        cappedLoopAction ω.val (H Puncture.inf) (fun t ↦ u (endChart Puncture.inf (-R, t)))
          (rectangleTrans (pairOfPantsGluedDisc D₀ D₁ u)
            (u ∘ endAnnulusChart Puncture.inf 0 R)))| ≤ ∑ q, B q := by
  rw [hω.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_cappedLoopAction hH hHs
    hu hD₀ hD₁ h₀₁ h₁₀ h₀ h₁ hR, sub_sub_cancel_left, abs_neg]
  exact abs_setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_le ω hH hHs hB u _

/-- **The capped actions at height `R` converge.** Under the hypotheses of
`integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_cappedLoopAction`, if the
Floer energy density of `u` is integrable over the pair of pants, then as `R → ∞` the capped
actions of the input loops at height `R` minus that of the output loop, capped as there, converge
to the energy of `u` plus its integrated curvature over the whole pair of pants. No equation is
needed: the truncations `S_R` exhaust `S`. -/
theorem tendsto_cappedLoopAction_pairOfPantsPerturbation (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {D₀ D₁ : ℝ × ℝ → M}
    (hD₀ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 D₀) (hD₁ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 D₁)
    (h₀₁ : ∀ s, D₀ (s, 1) = D₁ (s, 0)) (h₁₀ : ∀ s, D₁ (s, 1) = D₀ (s, 0))
    (h₀ : ∀ t, D₀ (1, t) = u (endChart Puncture.zero (0, t)))
    (h₁ : ∀ t, D₁ (1, t) = u (endChart Puncture.one (0, t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      thricePuncturedSphereReal) :
    Tendsto (fun R : ℝ ↦
        cappedLoopAction ω.val (H Puncture.zero) (fun t ↦ u (endChart Puncture.zero (R, t)))
            (rectangleTrans D₀ (u ∘ endAnnulusChart Puncture.zero 0 R)) +
          cappedLoopAction ω.val (H Puncture.one) (fun t ↦ u (endChart Puncture.one (R, t)))
            (rectangleTrans D₁ (u ∘ endAnnulusChart Puncture.one 0 R)) -
          cappedLoopAction ω.val (H Puncture.inf) (fun t ↦ u (endChart Puncture.inf (-R, t)))
            (rectangleTrans (pairOfPantsGluedDisc D₀ D₁ u)
              (u ∘ endAnnulusChart Puncture.inf 0 R))) atTop
      (𝓝 ((∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z) +
        ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z))) := by
  -- For `R ≥ 2` the capped actions are the energy plus the curvature over `S_R`.
  refine ((tendsto_setIntegral_truncation hE).add (tendsto_setIntegral_truncation
    (ω.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation hH hHs hu.continuousOn))).congr'
    ?_
  filter_upwards [eventually_ge_atTop 2] with R hR
  rw [hω.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_cappedLoopAction hH hHs
    hu hD₀ hD₁ h₀₁ h₁₀ h₀ h₁ hR, sub_add_cancel]

end IsNondegenerate

end TauCeti.SmoothTwoForm
