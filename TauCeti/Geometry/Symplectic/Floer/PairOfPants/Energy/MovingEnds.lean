/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.MovingEnds
import TauCeti.Algebra.Ring.Periodic
import TauCeti.Geometry.Manifold.ContMDiff.Pi

/-!
# The energy identity on spheres with moving input ends

The associativity of the pair-of-pants product is proved with a one-parameter family of spheres
with three moving input ends and one output end. The Floer data on such a sphere are
`TauCeti.Floer.puncturedSpherePerturbation c a H Hout`: the input end `i`, with center `c i` and
nonzero scale `a i`, has end lift `z ↦ c i + a i φ₀(z)`, where `φ₀(z) = exp (-2πz) / 2` is the end
lift of the input end at `0` of the pair of pants, and the datum there is `β(s - 1) H i(t) dt`; the
output end at `∞` has end lift `φ_∞(z) = 2 exp (-2πz)` and datum `β(-s - 1) Hout(t) dt`. This file
proves the energy identity of these data, with constants independent of the configuration, which is
what bounds the energy of the solutions counted along the family.

Assume that the supports `‖w - c i‖ < ‖a i‖ exp (-2π) / 2` of the input end data are pairwise
disjoint and lie in the disc `‖w‖ ≤ 2 exp (2π)` off which the output datum lives. For `R ≥ 1` the
truncation `TauCeti.Floer.puncturedSphereTruncation c a R` is the disc `‖w‖ ≤ 2 exp (2πR)`, bounded
by the circle `s = -R` of the output end, with the discs `‖w - c i‖ < ‖a i‖ exp (-2πR) / 2`, bounded
by the circles `s = R` of the input ends, removed. Let `ω` be a nondegenerate two-form on a
finite-dimensional manifold `M`, such as a closed symplectic manifold, let the Hamiltonians be
period-one and `C¹`, and let `u` be a map which is `C¹` on an open set containing the truncation.
Then the Floer energy of `u` over the truncation is

`∫ E = ∫ u^*ω + β(R - 1) (∑ i, ∫₀¹ H i(t, ℓ_i(t)) dt - ∫₀¹ Hout(t, ℓ_∞(t)) dt) - ∫ R_K(u)`

(`IsNondegenerate.integral_floerEnergyDensity_puncturedSpherePerturbation_truncation` in
`SmoothTwoForm`), where `ℓ_i(t) = u(c i + a i φ₀(R + i t))` and `ℓ_∞(t) = u(φ_∞(-R + i t))` are
the loops of `u` along the boundary circles and `β = smoothTransition`. With the curvature bound
`TauCeti.SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_puncturedSpherePerturbation_le`, the
energy differs from the area plus the Hamiltonian terms by at most `∑ i, B i + Bout` when
`|H i| ≤ B i` and `|Hout| ≤ Bout`, uniformly in the configuration and in `R`
(`IsNondegenerate.abs_integral_floerEnergyDensity_puncturedSpherePerturbation_truncation_sub_le`).
For a solution of the Floer equation with tame almost complex structures the energy is nonnegative,
so the area plus the Hamiltonian terms is at least `-(∑ i, B i + Bout)`
(`IsNondegenerate.neg_sum_add_le_integral_add_of_puncturedSpherePerturbation_truncation`). On a
target which is not symplectically aspherical the area term depends on the homotopy class of `u`;
expressing it through capped actions of the boundary loops is not done here.

The proof cuts the truncation into a closed annulus about each center, on which the datum is, off
its outer boundary circle, that input end's datum alone, and a closed annulus at the outer circle,
on which it is, off its inner boundary circle, the output datum
(`TauCeti.Floer.closedBall_sdiff_ball_subset_puncturedSphereTruncation` and
`TauCeti.Floer.closedBall_zero_sdiff_ball_subset_puncturedSphereTruncation`). These annuli meet only
on their boundary circles, which are null sets. On the remaining
core the datum vanishes nearby
(`TauCeti.Floer.puncturedSpherePerturbation_eventuallyEq_zero_of_mem_puncturedSphereTruncation`),
so the curvature is integrable over the truncation
(`TauCeti.SmoothTwoForm.integrableOn_hamiltonianCurvature_puncturedSpherePerturbation_truncation`)
and the energy minus the area plus the integrated curvature may be computed over the annuli alone
(`TauCeti.SmoothTwoForm.integral_floerEnergyDensity_sub_add_eq_of_eventuallyEq_zero`). The affine
chart `w ↦ c i + a i w` carries the positive plane datum, the pair-of-pants datum whose only
nonzero Hamiltonian is the one at the input `0`, to the input end datum of `i`
(`TauCeti.Floer.perturbationPullback_realChart_inputEndPerturbation`), and the output datum is
the pair-of-pants datum whose only nonzero Hamiltonian is the one at the output. Since the energy
density, the area density and the curvature are two-forms, the identity on each annulus is the
energy identity over the image of an end piece of the pair of pants
(`IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_image_endChart_endPiece` in
`SmoothTwoForm`), whose boundary terms on the angular sides cancel by periodicity and vanish with
the cutoff on the circle `±s = 1`; for the output annulus this is
`IsNondegenerate.integral_floerEnergyDensity_negativePlanePerturbation_closedBall_sdiff_ball` in
`SmoothTwoForm`.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the associativity of the pair-of-pants product and its energy estimates.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Sections 8 and 9, on
  perturbation data over families of punctured surfaces and their energy.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  energy identity for Hamiltonian perturbations.
-/

public section

open Set Real Function MeasureTheory Filter TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open TauCeti.Complex (realChart realChart_apply contDiff_realChart realChart_affine_injective
  det_fderiv_realChart_affine_nonneg image_realChart_affine_closedBall_sdiff_ball
  isCompact_preimage_closedBall_sdiff_ball)
open scoped Topology Manifold

namespace TauCeti

namespace Floer

/-- The affine chart `w ↦ c + a w` maps the image of the end piece `1 ≤ s ≤ R` of the end at `0`
of the pair of pants onto the closed annulus about `c` with radii `‖a‖ exp (-2πR) / 2` and
`‖a‖ exp (-2π) / 2`. -/
private theorem image_realChart_affine_image_endChart_zero_endPiece {c a : ℂ} (ha : a ≠ 0)
    (R : ℝ) :
    realChart (c + a * ·) '' (endChart zero '' endPiece zero R) =
      Complex.equivRealProdCLM.symm ⁻¹'
        (Metric.closedBall c (‖a‖ * Real.exp (-(2 * π)) / 2) \
          Metric.ball c (‖a‖ * Real.exp (-(2 * π * R)) / 2)) := by
  rw [image_endChart_zero_endPiece, image_realChart_affine_closedBall_sdiff_ball ha, mul_zero,
    add_zero, mul_div_assoc, mul_div_assoc]

/-- The affine chart `w ↦ c + a w`, for `a ≠ 0`, maps the image of the end piece `1 ≤ s ≤ R` of
the end at `0` off the center `c`. -/
private theorem realChart_affine_ne_of_mem_image_endChart_zero_endPiece {c a : ℂ} (ha : a ≠ 0)
    {R : ℝ} {w : ℝ × ℝ} (hw : w ∈ endChart zero '' endPiece zero R) :
    Complex.equivRealProdCLM.symm (realChart (c + a * ·) w) ≠ c := by
  obtain ⟨ζ, hζ, rfl⟩ := hw
  have hS := mem_thricePuncturedSphereReal_iff.1 (endChart_mem_thricePuncturedSphereReal
    (q := zero) (z := ζ) (by linarith [(mem_endPiece.1 hζ).1.1]))
  simp only [realChart_apply, ContinuousLinearEquiv.symm_apply_apply]
  exact fun h ↦ hS.1 (by simp [ha] at h)

/-- Germs of a datum at a point give germs of its components there, in real coordinates. -/
private theorem eventuallyEq_apply_of_eventuallyEq {M : Type*} {K K' : ℂ → M → ℂ →L[ℝ] ℝ}
    {z : ℝ × ℝ} (h : K =ᶠ[𝓝 (Complex.equivRealProdCLM.symm z)] K') (v : ℂ) :
    (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x v) =ᶠ[𝓝 z]
      fun z x ↦ K' (Complex.equivRealProdCLM.symm z) x v :=
  (h.comp_tendsto (Complex.equivRealProdCLM.symm.continuous.tendsto z)).fun_comp fun k x ↦ k x v

/-- Off a null set, near every point of the closed support of the input end datum of `i` the datum
is that end's datum, if the closed supports of the input end data meet at most on their boundaries
and lie in the disc `‖w‖ ≤ 2 exp (2π)`. -/
private theorem ae_puncturedSpherePerturbation_eventuallyEq_inputEndPerturbation {ι M : Type*}
    [Fintype ι] {c a : ι → ℂ} {H : ι → ℝ → M → ℝ} {Hout : ℝ → M → ℝ}
    (hsep : Pairwise fun i j =>
      ‖a i‖ * Real.exp (-(2 * π)) / 2 + ‖a j‖ * Real.exp (-(2 * π)) / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ 2 * Real.exp (2 * π)) (i : ι) :
    ∀ᵐ z : ℝ × ℝ, Complex.equivRealProdCLM.symm z ∈
        Metric.closedBall (c i) (‖a i‖ * Real.exp (-(2 * π)) / 2) →
      puncturedSpherePerturbation c a H Hout =ᶠ[𝓝 (Complex.equivRealProdCLM.symm z)]
        inputEndPerturbation (c i) (a i) (H i) := by
  have hN := (Complex.volume_preserving_equiv_real_prod.symm.measure_preimage
    (s := Metric.sphere (c i) (‖a i‖ * Real.exp (-(2 * π)) / 2))
    Metric.isClosed_sphere.measurableSet.nullMeasurableSet).trans
    (Measure.addHaar_sphere volume _ _)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN] with z hz hzi
  exact puncturedSpherePerturbation_eventuallyEq_inputEndPerturbation_of_norm_sub_lt
    (fun j hj ↦ hsep hj.symm) (hout i) (lt_of_le_of_ne (mem_closedBall_iff_norm.1 hzi)
      fun h ↦ hz (mem_sphere_iff_norm.2 h))

/-- Off a null set, near every point outside the open disc `‖w‖ < 2 exp (2π)` the datum is the
output datum, if the closed supports of the input end data lie in the closed disc. -/
private theorem ae_puncturedSpherePerturbation_eventuallyEq_negativePlanePerturbation
    {ι M : Type*} [Fintype ι] {c a : ι → ℂ} {H : ι → ℝ → M → ℝ} {Hout : ℝ → M → ℝ}
    (hout : ∀ i, ‖c i‖ + ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ 2 * Real.exp (2 * π)) :
    ∀ᵐ z : ℝ × ℝ, Complex.equivRealProdCLM.symm z ∉ Metric.ball 0 (2 * Real.exp (2 * π)) →
      puncturedSpherePerturbation c a H Hout =ᶠ[𝓝 (Complex.equivRealProdCLM.symm z)]
        negativePlanePerturbation Hout := by
  have hN := (Complex.volume_preserving_equiv_real_prod.symm.measure_preimage
    (s := Metric.sphere (0 : ℂ) (2 * Real.exp (2 * π)))
    Metric.isClosed_sphere.measurableSet.nullMeasurableSet).trans
    (Measure.addHaar_sphere volume _ _)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN] with z hz hzo
  exact puncturedSpherePerturbation_eventuallyEq_negativePlanePerturbation_of_lt_norm hout
    (lt_of_le_of_ne (not_lt.1 fun h ↦ hzo (mem_ball_zero_iff.2 h))
      fun h ↦ hz (mem_sphere_zero_iff_norm.2 h.symm))

end Floer

namespace SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]

/-! ### The annuli of the ends -/

section Annuli

/-- Data with the same germ at a point have the same curvature there. -/
private theorem hamiltonianCurvature_eq_of_eventuallyEq (ω : SmoothTwoForm I M)
    {K K' : ℂ → M → ℂ →L[ℝ] ℝ} {z : ℝ × ℝ}
    (h : K =ᶠ[𝓝 (Complex.equivRealProdCLM.symm z)] K') (x : M) :
    ω.hamiltonianCurvature (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature (fun z x ↦ K' (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K' (Complex.equivRealProdCLM.symm z) x Complex.I) z x :=
  congrFun (ω.hamiltonianCurvature_congr_of_eventuallyEq (eventuallyEq_apply_of_eventuallyEq h 1)
    (eventuallyEq_apply_of_eventuallyEq h Complex.I)) x

/-- Data with the same germ at a point have the same energy density there. -/
private theorem floerEnergyDensity_eq_of_eventuallyEq (ω : SmoothTwoForm I M)
    {K K' : ℂ → M → ℂ →L[ℝ] ℝ} {z : ℝ × ℝ}
    (h : K =ᶠ[𝓝 (Complex.equivRealProdCLM.symm z)] K') (u : ℝ × ℝ → M) :
    ω.floerEnergyDensity (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      ω.floerEnergyDensity (fun z x ↦ K' (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K' (Complex.equivRealProdCLM.symm z) x Complex.I) u z :=
  ω.floerEnergyDensity_congr_perturbation u (eventuallyEq_apply_of_eventuallyEq h 1).self_of_nhds
    (eventuallyEq_apply_of_eventuallyEq h Complex.I).self_of_nhds

variable {ω : SmoothTwoForm I M}

/-- **The curvature is integrable over an annulus of an input end, for a manifold target.** Let `K`
be the input end datum with center `c` and nonzero scale `a` of a period-one `C¹` Hamiltonian `H`,
and let `u` be continuous on the closed annulus `A` about `c` with radii `‖a‖ exp (-2πR) / 2` and
`‖a‖ exp (-2π) / 2`, the image of the part `1 ≤ s ≤ R` of the end. Then the curvature along `u` is
integrable over `A`: the affine chart `w ↦ c + a w` carries it to the curvature of the positive
plane datum over the part `1 ≤ s ≤ R` of the end at `0` of the pair of pants. -/
private theorem integrableOn_hamiltonianCurvature_inputEndPerturbation_annulus
    (ω : SmoothTwoForm I M) {H : ℝ → M → ℝ} (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {c a : ℂ} (ha : a ≠ 0)
    {u : ℝ × ℝ → M} {R : ℝ}
    (hu : ContinuousOn u (Complex.equivRealProdCLM.symm ⁻¹'
      (Metric.closedBall c (‖a‖ * Real.exp (-(2 * π)) / 2) \
        Metric.ball c (‖a‖ * Real.exp (-(2 * π * R)) / 2)))) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z))
      (Complex.equivRealProdCLM.symm ⁻¹'
        (Metric.closedBall c (‖a‖ * Real.exp (-(2 * π)) / 2) \
          Metric.ball c (‖a‖ * Real.exp (-(2 * π * R)) / 2))) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  -- The affine chart `g` maps the image `A₀` of the end piece at `0` of the pair of pants onto
  -- the annulus about `c`, and maps `A₀` off `c`.
  set g := realChart (c + a * ·)
  set A₀ := endChart zero '' endPiece zero R
  have hgA : g '' A₀ = _ := image_realChart_affine_image_endChart_zero_endPiece ha R
  have hA₀m : MeasurableSet A₀ := measurableSet_image_endChart_endPiece zero R
  have hg : ContDiff ℝ 2 g := contDiff_realChart (by fun_prop)
  have hgc {w : ℝ × ℝ} (hw : w ∈ A₀) :=
    realChart_affine_ne_of_mem_image_endChart_zero_endPiece (c := c) ha hw
  have htgt (w : ℝ × ℝ) (v : ℂ) :=
    mdifferentiableAt_inputEndPerturbation_target hHs c a
      (Complex.equivRealProdCLM.symm (g w)) (u (g w)) v
  have hdom {w : ℝ × ℝ} (hw : w ∈ A₀) (v : ℂ) :=
    differentiableAt_inputEndPerturbation_domain hH hHs ha (hgc hw) (u (g w)) v
  -- In the coordinates of the end, the curvature along `u ∘ g` is integrable.
  have hR₀ := ω.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation_image_endChart
    (hH.piSingle_apply zero) (hHs.uncurry_piSingle_apply zero)
    (hu.comp hg.continuous.continuousOn (mapsTo_preimage g _)) (q := zero) one_pos (b := R)
    fun z h₁ h₂ ↦ by
      rw [mem_preimage, ← hgA]
      exact mem_image_of_mem g (endChart_mem_image_endChart_endPiece h₁ h₂)
  rw [← endPiece_def] at hR₀
  -- Integrability transfers along the chart `g`.
  rw [← hgA, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hA₀m
    (fun w _ ↦ (hg.differentiable (by norm_num) w).hasFDerivAt.hasFDerivWithinAt)
    (realChart_affine_injective ha).injOn]
  refine hR₀.congr_fun (fun w hw ↦ ?_) hA₀m
  rw [abs_of_nonneg (det_fderiv_realChart_affine_nonneg c a w), smul_eq_mul,
    ← ω.hamiltonianCurvature_perturbationPullback hg.contDiffAt (hdom hw 1) (hdom hw Complex.I)
      (htgt _ 1) (htgt _ Complex.I),
    perturbationPullback_realChart_inputEndPerturbation ha,
    perturbationPullback_realChart_inputEndPerturbation ha,
    equivRealProdCLM_symm_stdComplexLineReal, equivRealProdCLM_symm_stdComplexLineImag,
    pairOfPantsPerturbation_single_zero]
  simp only [Function.comp_apply]

variable [FiniteDimensional ℝ E]

/-- **The energy identity on an annulus of an input end, for a manifold target.** Let `K` be the
input end datum with center `c` and nonzero scale `a` of a period-one `C¹` Hamiltonian `H`, and let
`u` be `C¹` on an open set containing the closed annulus `A` about `c` with radii
`‖a‖ exp (-2πR) / 2` and `‖a‖ exp (-2π) / 2`, the image of the part `1 ≤ s ≤ R` of the end. Then
the Floer energy over `A` is the area plus `β(R - 1)` times the integral of `H` along the inner
boundary circle, minus the integrated curvature. -/
private theorem IsNondegenerate.integral_floerEnergyDensity_inputEndPerturbation_annulus
    (hω : ω.IsNondegenerate) {H : ℝ → M → ℝ} (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {c a : ℂ} (ha : a ≠ 0)
    {u : ℝ × ℝ → M} {R : ℝ} (hR : 1 ≤ R) {V : Set (ℝ × ℝ)} (hVo : IsOpen V)
    (hAV : Complex.equivRealProdCLM.symm ⁻¹'
      (Metric.closedBall c (‖a‖ * Real.exp (-(2 * π)) / 2) \
        Metric.ball c (‖a‖ * Real.exp (-(2 * π * R)) / 2)) ⊆ V)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u V) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹'
        (Metric.closedBall c (‖a‖ * Real.exp (-(2 * π)) / 2) \
          Metric.ball c (‖a‖ * Real.exp (-(2 * π * R)) / 2)), ω.floerEnergyDensity
        (fun z x ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹'
          (Metric.closedBall c (‖a‖ * Real.exp (-(2 * π)) / 2) \
            Metric.ball c (‖a‖ * Real.exp (-(2 * π * R)) / 2)),
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        smoothTransition (R - 1) * (∫ t in (0 : ℝ)..1, H t (u (Complex.equivRealProdCLM
          (c + a * zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹'
          (Metric.closedBall c (‖a‖ * Real.exp (-(2 * π)) / 2) \
            Metric.ball c (‖a‖ * Real.exp (-(2 * π * R)) / 2)), ω.hamiltonianCurvature
          (fun z x ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  -- The affine chart `g` maps the image `A₀` of the end piece at `0` of the pair of pants onto
  -- the annulus `A` about `c`, and maps `A₀` off `c`.
  set g := realChart (c + a * ·)
  set A₀ := endChart zero '' endPiece zero R
  have hgA : g '' A₀ = _ := image_realChart_affine_image_endChart_zero_endPiece ha R
  have hA₀m : MeasurableSet A₀ := measurableSet_image_endChart_endPiece zero R
  have hg : ContDiff ℝ 2 g := contDiff_realChart (by fun_prop)
  have hginj : InjOn g A₀ := (realChart_affine_injective ha).injOn
  have hgdiff (w : ℝ × ℝ) : DifferentiableAt ℝ g w := hg.differentiable (by norm_num) w
  have hgc {w : ℝ × ℝ} (hw : w ∈ A₀) :=
    realChart_affine_ne_of_mem_image_endChart_zero_endPiece (c := c) ha hw
  have hud {w : ℝ × ℝ} (hw : w ∈ A₀) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (g w) :=
    (hu.contMDiffAt (hVo.mem_nhds (hAV (hgA.subset (mem_image_of_mem g hw))))).mdifferentiableAt
      one_ne_zero
  have htgt (w : ℝ × ℝ) (v : ℂ) :=
    mdifferentiableAt_inputEndPerturbation_target hHs c a
      (Complex.equivRealProdCLM.symm (g w)) (u (g w)) v
  have hdom {w : ℝ × ℝ} (hw : w ∈ A₀) (v : ℂ) :=
    differentiableAt_inputEndPerturbation_domain hH hHs ha (hgc hw) (u (g w)) v
  -- The reparametrized map is `C¹` on the preimage of `V`.
  have hug : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (u ∘ g) (g ⁻¹' V) :=
    hu.comp (hg.of_le (by norm_num)).contMDiff.contMDiffOn (mapsTo_preimage _ _)
  -- Change variables along `g`, in each of the three integrals, to the pair of pants, where the
  -- pullback of the datum is the positive plane datum, the pair-of-pants datum whose only nonzero
  -- Hamiltonian is `H` at the input `0`.
  rw [← hgA, ω.integral_eval₂_mfderiv_stdComplexLine_image hA₀m hginj (fun w _ ↦ hgdiff w)
      (fun w _ ↦ det_fderiv_realChart_affine_nonneg c a w) (fun w hw ↦ hud hw),
    ω.integral_floerEnergyDensity_image hA₀m hginj (fun w _ ↦ hgdiff w)
      (fun w _ ↦ det_fderiv_realChart_affine_nonneg c a w) (fun w hw ↦ hud hw)
      (fun w _ ↦ htgt w 1) (fun w _ ↦ htgt w _),
    ω.integral_hamiltonianCurvature_image hA₀m hginj (fun w _ ↦ hg.contDiffAt)
      (fun w _ ↦ det_fderiv_realChart_affine_nonneg c a w) (fun w hw ↦ hdom hw 1)
      (fun w hw ↦ hdom hw _) (fun w _ ↦ htgt w 1) (fun w _ ↦ htgt w _),
    perturbationPullback_realChart_inputEndPerturbation ha,
    perturbationPullback_realChart_inputEndPerturbation ha,
    equivRealProdCLM_symm_stdComplexLineReal, equivRealProdCLM_symm_stdComplexLineImag,
    ← pairOfPantsPerturbation_single_zero,
    hω.integral_floerEnergyDensity_pairOfPantsPerturbation_image_endChart_endPiece
      (hH.piSingle_apply zero) (hHs.uncurry_piSingle_apply zero) (hVo.preimage hg.continuous) hug
      hR zero
      fun z h₁ h₂ ↦
        hAV (hgA.subset (mem_image_of_mem g (endChart_mem_image_endChart_endPiece h₁ h₂)))]
  simp only [Pi.single_eq_same, endSign_zero, one_mul, Function.comp_apply, g, A₀,
    realChart_apply, ContinuousLinearEquiv.symm_apply_apply]

end Annuli

/-! ### The truncated sphere with moving input ends -/

section Sphere

variable {ι : Type*} [Fintype ι] {c a : ι → ℂ} {H : ι → ℝ → M → ℝ} {Hout : ℝ → M → ℝ}

/-- **The curvature is integrable over the truncated sphere with moving input ends, for a manifold
target.** Let the input ends have centers `c i`, nonzero scales `a i` and period-one `C¹`
Hamiltonians `H i`, and let the output end have a period-one `C¹` Hamiltonian `Hout`. Assume that
the supports `‖w - c i‖ < ‖a i‖ exp (-2π) / 2` of the input end data are pairwise disjoint and lie
in the disc `‖w‖ ≤ 2 exp (2π)`. Along a map `u` which is continuous on the truncation `T_R`, the
curvature of `TauCeti.Floer.puncturedSpherePerturbation c a H Hout` is integrable over `T_R`: on
the annulus of each end it is, off a null set, the curvature of that end's datum, and elsewhere it
vanishes. -/
theorem integrableOn_hamiltonianCurvature_puncturedSpherePerturbation_truncation
    (ω : SmoothTwoForm I M) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j =>
      ‖a i‖ * Real.exp (-(2 * π)) / 2 + ‖a j‖ * Real.exp (-(2 * π)) / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ 2 * Real.exp (2 * π))
    {u : ℝ × ℝ → M} {R : ℝ}
    (hu : ContinuousOn u (Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R)) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z))
      (Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R) := by
  set K := puncturedSpherePerturbation c a H Hout
  set T := Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R
  -- The annulus `A i` about the center `c i`, on which the datum is that of the input end `i`, and
  -- the annulus `Aout` at the outer circle, on which it is the output datum. They lie in `T`.
  set A : ι → Set (ℝ × ℝ) := fun i ↦ Complex.equivRealProdCLM.symm ⁻¹'
    (Metric.closedBall (c i) (‖a i‖ * Real.exp (-(2 * π)) / 2) \
      Metric.ball (c i) (‖a i‖ * Real.exp (-(2 * π * R)) / 2))
  set Aout := Complex.equivRealProdCLM.symm ⁻¹'
    (Metric.closedBall 0 (2 * Real.exp (2 * π * R)) \ Metric.ball 0 (2 * Real.exp (2 * π)))
  have hAT (i : ι) : A i ⊆ T := preimage_mono
    (closedBall_sdiff_ball_subset_puncturedSphereTruncation (fun j hj ↦ hsep hj.symm) (hout i)
      (.inr (ha i)))
  have hAoutT : Aout ⊆ T :=
    preimage_mono (closedBall_zero_sdiff_ball_subset_puncturedSphereTruncation hout)
  -- On each annulus the curvature is, off a null set, that of a single end's datum, which is
  -- integrable there.
  have hB : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) (Aout ∪ ⋃ i, A i) :=
    ((ω.integrableOn_hamiltonianCurvature_negativePlanePerturbation_closedBall_sdiff_ball hHout
      hHouts (hu.mono hAoutT)).congr_fun_ae ((ae_restrict_iff'
        (isCompact_preimage_closedBall_sdiff_ball _ _ _).isClosed.measurableSet).2
      ((ae_puncturedSpherePerturbation_eventuallyEq_negativePlanePerturbation hout).mono
        fun z hz hzA ↦ (ω.hamiltonianCurvature_eq_of_eventuallyEq (hz hzA.2) (u z)).symm))).union
    (integrableOn_finite_iUnion.2 fun i ↦
      (integrableOn_hamiltonianCurvature_inputEndPerturbation_annulus ω (hH i) (hHs i) (ha i)
        (hu.mono (hAT i))).congr_fun_ae ((ae_restrict_iff'
          (isCompact_preimage_closedBall_sdiff_ball _ _ _).isClosed.measurableSet).2
        ((ae_puncturedSpherePerturbation_eventuallyEq_inputEndPerturbation hsep hout i).mono
          fun z hz hzA ↦ (ω.hamiltonianCurvature_eq_of_eventuallyEq (hz hzA.1) (u z)).symm)))
  -- Off the annuli the datum vanishes nearby, and so does the curvature.
  refine hB.of_forall_sdiff_eq_zero
    (isCompact_preimage_puncturedSphereTruncation c a R).isClosed.measurableSet fun z hz ↦ ?_
  rw [ω.hamiltonianCurvature_eq_of_eventuallyEq
    (puncturedSpherePerturbation_eventuallyEq_zero_of_mem_puncturedSphereTruncation hz.1
      (fun i h ↦ hz.2 (Or.inr (mem_iUnion.2 ⟨i, h⟩))) fun h ↦ hz.2 (Or.inl h))]
  simp

variable [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M}

/-- **The energy identity on the truncated sphere with moving input ends, for a manifold target.**
Let the input ends have centers `c i`, nonzero scales `a i` and period-one `C¹` Hamiltonians `H i`,
and let the output end at `∞` have a period-one `C¹` Hamiltonian `Hout`, on a finite-dimensional
manifold with a nondegenerate two-form. Assume that the supports `‖w - c i‖ < ‖a i‖ exp (-2π) / 2`
of the input end data are pairwise disjoint and lie in the disc `‖w‖ ≤ 2 exp (2π)`. Let `K` be the
perturbation datum `TauCeti.Floer.puncturedSpherePerturbation c a H Hout`, with components
`K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global coordinate `z = s + i t` of `ℂ`, and let `u`
be a map which is `C¹` on an open set `V` containing the truncation
`T_R = puncturedSphereTruncation c a R`. For `R ≥ 1`,
the Floer energy over `T_R` is the symplectic area, plus `β(R - 1)` times the integrals of the input
Hamiltonians along the inner boundary circles `s = R` minus the integral of the output Hamiltonian
along the outer boundary circle `s = -R`, minus the integrated curvature:

`∫_{T_R} E = ∫_{T_R} u^*ω + β(R - 1) (∑ i, ∫₀¹ H i(t, ℓ_i(t)) dt - ∫₀¹ Hout(t, ℓ_∞(t)) dt)
  - ∫_{T_R} R_K(u)`,

where `ℓ_i(t) = u(c i + a i φ₀(R + i t))` and `ℓ_∞(t) = u(φ_∞(-R + i t))` for the end lifts `φ₀` and
`φ_∞` of the ends at `0` and `∞` of the pair of pants, and `β = smoothTransition`, so
`β(R - 1) = 1` for `R ≥ 2`. Nothing is assumed about `u` off `V`. -/
theorem IsNondegenerate.integral_floerEnergyDensity_puncturedSpherePerturbation_truncation
    (hω : ω.IsNondegenerate) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j =>
      ‖a i‖ * Real.exp (-(2 * π)) / 2 + ‖a j‖ * Real.exp (-(2 * π)) / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ 2 * Real.exp (2 * π))
    {u : ℝ × ℝ → M} {R : ℝ} (hR : 1 ≤ R)
    {V : Set (ℝ × ℝ)} (hVo : IsOpen V)
    (hTV : Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R ⊆ V)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u V) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R, ω.floerEnergyDensity
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
          Complex.I) u z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        smoothTransition (R - 1) * ((∑ i, ∫ t in (0 : ℝ)..1, H i t (u (Complex.equivRealProdCLM
            (c i + a i * zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) -
          ∫ t in (0 : ℝ)..1, Hout t (u (Complex.equivRealProdCLM
            (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
          ω.hamiltonianCurvature
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
              Complex.I) z (u z) := by
  classical
  set K := puncturedSpherePerturbation c a H Hout
  set T := Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R
  -- The annulus `A i` about the center `c i`, on which the datum is that of the input end `i`, and
  -- the annulus `Aout` at the outer circle, on which it is the output datum. They lie in `T`.
  set A : ι → Set (ℝ × ℝ) := fun i ↦ Complex.equivRealProdCLM.symm ⁻¹'
    (Metric.closedBall (c i) (‖a i‖ * Real.exp (-(2 * π)) / 2) \
      Metric.ball (c i) (‖a i‖ * Real.exp (-(2 * π * R)) / 2))
  set Aout := Complex.equivRealProdCLM.symm ⁻¹'
    (Metric.closedBall 0 (2 * Real.exp (2 * π * R)) \ Metric.ball 0 (2 * Real.exp (2 * π)))
  have hAT (i : ι) : A i ⊆ T := preimage_mono
    (closedBall_sdiff_ball_subset_puncturedSphereTruncation (fun j hj ↦ hsep hj.symm) (hout i)
      (.inl hR))
  have hAoutT : Aout ⊆ T :=
    preimage_mono (closedBall_zero_sdiff_ball_subset_puncturedSphereTruncation hout)
  have hBT : Aout ∪ ⋃ i, A i ⊆ T := union_subset hAoutT (iUnion_subset hAT)
  -- The closed supports of the input end data meet each other only on their boundary circles, and
  -- meet the closed annulus of the output end only on the circle `s = -1`, so the annuli meet only
  -- on null sets.
  have hnull (w : ℂ) (r : ℝ) :
      volume (Complex.equivRealProdCLM.symm ⁻¹' Metric.sphere w r) = 0 :=
    (Complex.volume_preserving_equiv_real_prod.symm.measure_preimage
      Metric.isClosed_sphere.measurableSet.nullMeasurableSet).trans
      (Measure.addHaar_sphere volume _ _)
  have hAd : Pairwise (AEDisjoint volume on A) := fun i j hij ↦ by
    refine measure_mono_null (fun z ⟨hzi, hzj⟩ ↦ ?_)
      (hnull (c i) (‖a i‖ * Real.exp (-(2 * π)) / 2))
    have hi := mem_closedBall_iff_norm.1 hzi.1
    have hj := mem_closedBall_iff_norm.1 hzj.1
    have := norm_sub_le_norm_sub_add_norm_sub (c i) (Complex.equivRealProdCLM.symm z) (c j)
    rw [norm_sub_rev (c i) (Complex.equivRealProdCLM.symm z)] at this
    exact mem_sphere_iff_norm.2 (by linarith [hsep hij])
  have hAoutd : AEDisjoint volume Aout (⋃ i, A i) := AEDisjoint.iUnion_right_iff.2 fun i ↦ by
    refine measure_mono_null (fun z ⟨hzo, hzi⟩ ↦ ?_) (hnull 0 (2 * Real.exp (2 * π)))
    have ho := not_lt.1 fun h ↦ hzo.2 (mem_ball_zero_iff.2 h)
    have hi := mem_closedBall_iff_norm.1 hzi.1
    exact mem_sphere_zero_iff_norm.2
      (by linarith [norm_le_norm_add_norm_sub' (Complex.equivRealProdCLM.symm z) (c i), hout i])
  have hAm (i : ι) : MeasurableSet (A i) :=
    (isCompact_preimage_closedBall_sdiff_ball _ _ _).isClosed.measurableSet
  have hAoutm : MeasurableSet Aout :=
    (isCompact_preimage_closedBall_sdiff_ball _ _ _).isClosed.measurableSet
  have hTc : IsCompact T := isCompact_preimage_puncturedSphereTruncation c a R
  -- Off a null set, on each annulus the datum is that of a single end, and off the annuli it
  -- vanishes.
  have hKi (i : ι) := ae_puncturedSpherePerturbation_eventuallyEq_inputEndPerturbation (H := H)
    (Hout := Hout) hsep hout i
  have hKout := ae_puncturedSpherePerturbation_eventuallyEq_negativePlanePerturbation (H := H)
    (Hout := Hout) hout
  have hK0 {z : ℝ × ℝ} (hz : z ∈ T \ (Aout ∪ ⋃ i, A i)) :
      K =ᶠ[𝓝 (Complex.equivRealProdCLM.symm z)] 0 :=
    puncturedSpherePerturbation_eventuallyEq_zero_of_mem_puncturedSphereTruncation hz.1
      (fun i h ↦ hz.2 (Or.inr (mem_iUnion.2 ⟨i, h⟩))) fun h ↦ hz.2 (Or.inl h)
  -- Integrability over the truncation. The datum is `C¹` off the centers, so near `T`.
  have harea := ω.integrableOn_eval₂_mfderiv hVo hu hTc hTV stdComplexLineReal stdComplexLineImag
  have hRT := integrableOn_hamiltonianCurvature_puncturedSpherePerturbation_truncation ω hH hHs
    hHout hHouts ha hsep hout (hu.continuousOn.mono hTV)
  set U := V ∩ {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}
  have hUo : IsOpen U := hVo.inter (by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦
      isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const)
  have hTU : T ⊆ U := fun z hz ↦ ⟨hTV hz, fun i ↦ ne_of_mem_puncturedSphereTruncation hz (ha i)⟩
  have hKs (v : ℂ) : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1
      (uncurry fun z x ↦ K (Complex.equivRealProdCLM.symm z) x v) (U ×ˢ univ) :=
    (contMDiffOn_uncurry_puncturedSpherePerturbation_apply (n := 1) hH hHs hHout hHouts ha
      v).mono (prod_mono inter_subset_right subset_rfl)
  have hET := hω.integrableOn_floerEnergyDensity hUo (hu.mono inter_subset_left) (hKs 1)
    (hKs Complex.I) hTc hTU hRT
  -- Off the annuli the datum vanishes, so the energy minus the area plus the integrated curvature
  -- may be computed over the annuli alone, and there split over each annulus.
  have hcore := integral_floerEnergyDensity_sub_add_eq_of_eventuallyEq_zero
    hTc.isClosed.measurableSet hBT
    (fun z hz ↦ (eventuallyEq_apply_of_eventuallyEq (hK0 hz) 1).trans
      (by filter_upwards with z'; funext x; simp))
    (fun z hz ↦ (eventuallyEq_apply_of_eventuallyEq (hK0 hz) Complex.I).trans
      (by filter_upwards with z'; funext x; simp))
    hET harea hRT
  have hsplit (f : ℝ × ℝ → ℝ) (hf : IntegrableOn f T) :
      ∫ z in Aout ∪ ⋃ i, A i, f z = (∫ z in Aout, f z) + ∑ i, ∫ z in A i, f z := by
    rw [setIntegral_union₀ hAoutd (MeasurableSet.iUnion hAm).nullMeasurableSet
        (hf.mono_set hAoutT) (hf.mono_set (iUnion_subset hAT)),
      integral_iUnion_ae (fun i ↦ (hAm i).nullMeasurableSet) hAd (hf.mono_set (iUnion_subset hAT)),
      tsum_fintype]
  -- On the annuli the energy and the curvature are those of the single end data.
  have hEi (i : ι) : ∫ z in A i, ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      (∫ z in A i, (SmoothBundleForm.eval₂ ω (u z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        smoothTransition (R - 1) * (∫ t in (0 : ℝ)..1, H i t (u (Complex.equivRealProdCLM
          (c i + a i * zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) -
        ∫ z in A i, ω.hamiltonianCurvature
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
    rw [setIntegral_congr_ae (hAm i) ((hKi i).mono fun z hz hzA ↦
        ω.floerEnergyDensity_eq_of_eventuallyEq (hz hzA.1) u),
      setIntegral_congr_ae (hAm i) ((hKi i).mono fun z hz hzA ↦
        ω.hamiltonianCurvature_eq_of_eventuallyEq (hz hzA.1) _)]
    exact hω.integral_floerEnergyDensity_inputEndPerturbation_annulus (hH i) (hHs i) (ha i) hR hVo
      ((hAT i).trans hTV) hu
  have hEout : ∫ z in Aout, ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      (∫ z in Aout, (SmoothBundleForm.eval₂ ω (u z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        smoothTransition (R - 1) * (∫ t in (0 : ℝ)..1, Hout t (u (Complex.equivRealProdCLM
          (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) -
        ∫ z in Aout, ω.hamiltonianCurvature
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
    rw [setIntegral_congr_ae hAoutm (hKout.mono fun z hz hzA ↦
        ω.floerEnergyDensity_eq_of_eventuallyEq (hz hzA.2) u),
      setIntegral_congr_ae hAoutm (hKout.mono fun z hz hzA ↦
        ω.hamiltonianCurvature_eq_of_eventuallyEq (hz hzA.2) _)]
    exact hω.integral_floerEnergyDensity_negativePlanePerturbation_closedBall_sdiff_ball hHout
      hHouts hR hVo (hAoutT.trans hTV) hu
  rw [hsplit _ hET, hsplit _ harea, hsplit _ hRT, hEout, Finset.sum_congr rfl fun i _ ↦ hEi i,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hcore
  linear_combination hcore

/-- **The energy bound on the truncated sphere with moving input ends, for a manifold target.**
Under the hypotheses of
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_puncturedSpherePerturbation_truncation`,
if `|H i| ≤ B i` and `|Hout| ≤ Bout`, then the Floer energy over the truncation `T_R` differs from
the symplectic area plus the Hamiltonian terms of its boundary circles by at most
`∑ i, B i + Bout`, uniformly in the configuration of the input ends and in `R ≥ 1`. -/
theorem
    IsNondegenerate.abs_integral_floerEnergyDensity_puncturedSpherePerturbation_truncation_sub_le
    (hω : ω.IsNondegenerate) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j =>
      ‖a i‖ * Real.exp (-(2 * π)) / 2 + ‖a j‖ * Real.exp (-(2 * π)) / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ 2 * Real.exp (2 * π))
    {B : ι → ℝ} {Bout : ℝ}
    (hB : ∀ i t x, |H i t x| ≤ B i) (hBout : ∀ t x, |Hout t x| ≤ Bout) {u : ℝ × ℝ → M} {R : ℝ}
    (hR : 1 ≤ R) {V : Set (ℝ × ℝ)} (hVo : IsOpen V)
    (hTV : Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R ⊆ V)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u V) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
        ω.floerEnergyDensity
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
            Complex.I) u z) -
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        smoothTransition (R - 1) * ((∑ i, ∫ t in (0 : ℝ)..1, H i t (u (Complex.equivRealProdCLM
            (c i + a i * zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) -
          ∫ t in (0 : ℝ)..1, Hout t (u (Complex.equivRealProdCLM
            (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))))| ≤ ∑ i, B i + Bout := by
  have hsub (a b c : ℝ) : a + b - c - a - b = -c := by ring
  rw [hω.integral_floerEnergyDensity_puncturedSpherePerturbation_truncation hH hHs hHout hHouts ha
    hsep hout hR hVo hTV hu, hsub, abs_neg]
  have hB₀ (i : ι) : 0 ≤ B i := (abs_nonneg _).trans (hB i 0 (u 0))
  have hBout₀ : 0 ≤ Bout := (abs_nonneg _).trans (hBout 0 (u 0))
  rw [← ENNReal.ofReal_le_ofReal_iff (add_nonneg (Finset.sum_nonneg fun i _ ↦ hB₀ i) hBout₀),
    ← Real.eNorm_eq_ofReal_abs, ENNReal.ofReal_add (Finset.sum_nonneg fun i _ ↦ hB₀ i) hBout₀,
    ENNReal.ofReal_sum_of_nonneg fun i _ ↦ hB₀ i]
  exact (eNorm_integral_le_lintegral_eNorm _).trans ((setLIntegral_le_lintegral _ _).trans
    (ω.lintegral_enorm_hamiltonianCurvature_puncturedSpherePerturbation_le hH hHs hHout hHouts ha
      hsep hout hB hBout u))

/-- **The topological energy of a solution on a sphere with moving input ends is bounded below,
for a manifold target.** Let `u` solve the Floer equation `(du - X_K)^{0,1} = 0` on the truncation
`T_R` for almost complex structures `J z` on the tangent spaces `T_{u(z)} M` tamed by the two-form,
under the hypotheses of
`IsNondegenerate.abs_integral_floerEnergyDensity_puncturedSpherePerturbation_truncation_sub_le`.
Since its energy is nonnegative, its symplectic area over `T_R` plus the Hamiltonian terms of the
boundary circles is at least `-(∑ i, B i + Bout)`, whatever the configuration of the input ends. -/
theorem IsNondegenerate.neg_sum_add_le_integral_add_of_puncturedSpherePerturbation_truncation
    (hω : ω.IsNondegenerate) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout)) (ha : ∀ i, a i ≠ 0)
    (hsep : Pairwise fun i j =>
      ‖a i‖ * Real.exp (-(2 * π)) / 2 + ‖a j‖ * Real.exp (-(2 * π)) / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ 2 * Real.exp (2 * π))
    {B : ι → ℝ} {Bout : ℝ}
    (hB : ∀ i t x, |H i t x| ≤ B i) (hBout : ∀ t x, |Hout t x| ≤ Bout) {u : ℝ × ℝ → M} {R : ℝ}
    (hR : 1 ≤ R) {V : Set (ℝ × ℝ)} (hVo : IsOpen V)
    (hTV : Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R ⊆ V)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u V)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
      (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ puncturedSpherePerturbation c a H Hout (Complex.equivRealProdCLM.symm z) x
            Complex.I) u z).toLinearMap) :
    -(∑ i, B i + Bout) ≤
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        smoothTransition (R - 1) * ((∑ i, ∫ t in (0 : ℝ)..1, H i t (u (Complex.equivRealProdCLM
            (c i + a i * zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) -
          ∫ t in (0 : ℝ)..1, Hout t (u (Complex.equivRealProdCLM
            (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) := by
  have hE := setIntegral_nonneg (μ := volume)
    (isCompact_preimage_puncturedSphereTruncation c a R).isClosed.measurableSet fun z hz ↦
    floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  have h := (abs_le.1
    (hω.abs_integral_floerEnergyDensity_puncturedSpherePerturbation_truncation_sub_le hH hHs hHout
      hHouts ha hsep hout hB hBout hR hVo hTV hu)).2
  linarith

end Sphere

end SmoothTwoForm

end TauCeti
