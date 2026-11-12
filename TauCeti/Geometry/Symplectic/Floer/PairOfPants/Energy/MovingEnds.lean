/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.MovingEnds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

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

Assume that the discs `‖w - c i‖ < ‖a i‖ / 2` of the input ends are pairwise disjoint and lie in the
disc `‖w‖ ≤ 2 exp (2π)` off which the output datum lives. For `R ≥ 1` the truncation
`TauCeti.Floer.puncturedSphereTruncation c a R` is the disc `‖w‖ ≤ 2 exp (2πR)`, bounded by the
circle `s = -R` of the output end, with the discs `‖w - c i‖ < ‖a i‖ exp (-2πR) / 2`, bounded by the
circles `s = R` of the input ends, removed. Let `ω` be a nondegenerate two-form on a
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

The proof cuts the truncation into a closed annulus about each center, on which the datum is that
input end's datum alone, a closed annulus at the outer circle, on which it is the output datum,
and the remaining core, on which the datum vanishes nearby, so that the energy density there is
the area density and the curvature vanishes. The affine chart `w ↦ c i + a i w` carries the
positive plane datum, the pair-of-pants datum whose only nonzero Hamiltonian is the one at the
input `0`, to the input end datum of `i` (`TauCeti.Floer.inputEndPerturbation_add_mul`), and the
output datum is the pair-of-pants datum whose only nonzero Hamiltonian is the one at the output.
Since the energy density, the area density and the curvature are two-forms, the identity on each
annulus is the energy identity over an end of the pair of pants
(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_image_endChart`), whose boundary terms
on the angular sides cancel by periodicity and vanish with the cutoff on the circle `±s = 1`.

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
open TauCeti.Complex (realChart realChart_apply contDiff_realChart realChart_injective)
open scoped Topology Manifold

namespace TauCeti

namespace Floer

/-! ### The truncation -/

variable {ι : Type*}

/-- The truncation at height `R` of the sphere with input ends of centers `c i` and scales `a i`
and output end at `∞`: the disc `‖w‖ ≤ 2 exp (2πR)`, bounded by the circle `s = -R` of the output
end, with the discs `‖w - c i‖ < ‖a i‖ exp (-2πR) / 2`, bounded by the circles `s = R` of the input
ends, removed. -/
noncomputable def puncturedSphereTruncation (c a : ι → ℂ) (R : ℝ) : Set ℂ :=
  Metric.closedBall 0 (2 * Real.exp (2 * π * R)) \
    ⋃ i, Metric.ball (c i) (‖a i‖ * Real.exp (-(2 * π * R)) / 2)

/-- A point lies in the truncation when it lies in the disc bounded by the outer circle and outside
the discs bounded by the inner circles. -/
@[simp]
theorem mem_puncturedSphereTruncation {c a : ι → ℂ} {R : ℝ} {w : ℂ} :
    w ∈ puncturedSphereTruncation c a R ↔
      ‖w‖ ≤ 2 * Real.exp (2 * π * R) ∧
        ∀ i, ‖a i‖ * Real.exp (-(2 * π * R)) / 2 ≤ ‖w - c i‖ := by
  simp [puncturedSphereTruncation, dist_eq_norm]

/-- The truncation is compact: it is a closed disc with open discs removed. -/
theorem isCompact_puncturedSphereTruncation (c a : ι → ℂ) (R : ℝ) :
    IsCompact (puncturedSphereTruncation c a R) :=
  (isCompact_closedBall _ _).diff (isOpen_iUnion fun _ ↦ Metric.isOpen_ball)

/-- The affine chart `w ↦ c + a w` maps the closed annulus about `0` with radii `r₁` and `r₂` onto
the closed annulus about `c` with radii `‖a‖ r₁` and `‖a‖ r₂`. -/
private theorem image_realChart_affine_annulus {c a : ℂ} (ha : a ≠ 0) (r₁ r₂ : ℝ) :
    realChart (c + a * ·) '' (Complex.equivRealProdCLM.symm ⁻¹'
        (Metric.closedBall 0 r₂ \ Metric.ball 0 r₁)) =
      Complex.equivRealProdCLM.symm ⁻¹'
        (Metric.closedBall c (‖a‖ * r₂) \ Metric.ball c (‖a‖ * r₁)) := by
  have ha' : 0 < ‖a‖ := norm_pos_iff.2 ha
  ext z
  simp only [mem_image, mem_preimage, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
    dist_eq_norm, not_lt, sub_zero, realChart_apply]
  constructor
  · rintro ⟨y, ⟨h₂, h₁⟩, rfl⟩
    rw [ContinuousLinearEquiv.symm_apply_apply, add_sub_cancel_left, norm_mul]
    exact ⟨by gcongr, by gcongr⟩
  · rintro ⟨h₂, h₁⟩
    refine ⟨Complex.equivRealProdCLM ((Complex.equivRealProdCLM.symm z - c) / a), ⟨?_, ?_⟩, ?_⟩
    · rw [ContinuousLinearEquiv.symm_apply_apply, norm_div, div_le_iff₀ ha']
      linarith
    · rw [ContinuousLinearEquiv.symm_apply_apply, norm_div, le_div_iff₀ ha']
      linarith
    · rw [ContinuousLinearEquiv.symm_apply_apply, mul_div_cancel₀ _ ha, add_sub_cancel,
        ContinuousLinearEquiv.apply_symm_apply]

/-- By periodicity, an integral over the angular interval `[-1/2, 1/2]` is an integral over the
period `[0, 1]`. -/
private theorem intervalIntegral_neg_half_half_eq {f : ℝ → ℝ} (hf : Periodic f 1) :
    ∫ t in (-1 / 2 : ℝ)..1 / 2, f t = ∫ t in (0 : ℝ)..1, f t := by
  have h := hf.intervalIntegral_add_eq (-1 / 2) 0
  norm_num at h
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num]
  exact h

end Floer

namespace SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]

/-! ### The annuli of the ends -/

section Annuli

variable [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M}

/-- **The energy identity on an annulus of an input end, for a manifold target.** Let `K` be the
input end datum with center `c` and nonzero scale `a` of a period-one `C¹` Hamiltonian `H`, and let
`u` be `C¹` on an open set containing the closed annulus `A` about `c` with radii
`‖a‖ exp (-2πR) / 2` and `‖a‖ exp (-2π) / 2`, the image of the part `1 ≤ s ≤ R` of the end. Then
the curvature along `u` is integrable over `A`, and the Floer energy over `A` is the area plus
`β(R - 1)` times the integral of `H` along the inner boundary circle, minus the integrated
curvature. -/
private theorem IsNondegenerate.integral_floerEnergyDensity_inputEndPerturbation_annulus
    (hω : ω.IsNondegenerate) {H : ℝ → M → ℝ} (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {c a : ℂ} (ha : a ≠ 0)
    {u : ℝ × ℝ → M} {R : ℝ} (hR : 1 ≤ R) {V : Set (ℝ × ℝ)} (hVo : IsOpen V)
    (hAV : Complex.equivRealProdCLM.symm ⁻¹'
      (Metric.closedBall c (‖a‖ * Real.exp (-(2 * π)) / 2) \
        Metric.ball c (‖a‖ * Real.exp (-(2 * π * R)) / 2)) ⊆ V)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u V) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z))
      (Complex.equivRealProdCLM.symm ⁻¹'
        (Metric.closedBall c (‖a‖ * Real.exp (-(2 * π)) / 2) \
          Metric.ball c (‖a‖ * Real.exp (-(2 * π * R)) / 2))) ∧
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
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  -- The part `1 ≤ s ≤ R` of the end at `0` of the pair of pants is an annulus `A₀`, which the
  -- affine chart `g` maps onto the annulus `A` about `c`.
  have hA₀ : endChart zero '' (Icc 1 R ×ˢ Ico (-1 / 2 : ℝ) (1 / 2)) =
      Complex.equivRealProdCLM.symm ⁻¹'
        (Metric.closedBall 0 (Real.exp (-(2 * π)) / 2) \
          Metric.ball 0 (Real.exp (-(2 * π * R)) / 2)) := by
    rw [image_endChart_Icc_prod_Ico, endCenter_zero, endScale_zero]
    norm_num
    ring_nf
  have hA : Complex.equivRealProdCLM.symm ⁻¹'
      (Metric.closedBall c (‖a‖ * Real.exp (-(2 * π)) / 2) \
        Metric.ball c (‖a‖ * Real.exp (-(2 * π * R)) / 2)) =
      realChart (c + a * ·) '' (endChart zero '' (Icc 1 R ×ˢ Ico (-1 / 2 : ℝ) (1 / 2))) := by
    rw [hA₀, image_realChart_affine_annulus ha, mul_div_assoc, mul_div_assoc]
  set g := realChart (c + a * ·)
  set A₀ := endChart zero '' (Icc 1 R ×ˢ Ico (-1 / 2 : ℝ) (1 / 2))
  set A := Complex.equivRealProdCLM.symm ⁻¹'
    (Metric.closedBall c (‖a‖ * Real.exp (-(2 * π)) / 2) \
      Metric.ball c (‖a‖ * Real.exp (-(2 * π * R)) / 2))
  have hA₀c : IsCompact A₀ := by
    rw [hA₀]
    exact Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
      ((isCompact_closedBall _ _).diff Metric.isOpen_ball)
  have hA₀m : MeasurableSet A₀ := hA₀c.isClosed.measurableSet
  -- The chart `g` is affine and holomorphic, hence injective and orientation preserving.
  have hgd (w : ℝ × ℝ) : HasDerivAt (c + a * ·) a (Complex.equivRealProdCLM.symm w) := by
    simpa using ((hasDerivAt_id _).const_mul a).const_add c
  have hg : ContDiff ℝ 2 g := contDiff_realChart (by fun_prop)
  have hginj : InjOn g A₀ :=
    (realChart_injective fun _ _ h ↦ mul_left_cancel₀ ha (add_left_cancel h)).injOn
  have hgdet (w : ℝ × ℝ) : 0 ≤ (fderiv ℝ g w).det :=
    TauCeti.Complex.det_fderiv_realChart_nonneg (hgd w)
  have hgdiff (w : ℝ × ℝ) : DifferentiableAt ℝ g w := hg.differentiable (by norm_num) w
  -- Points of `A₀` lie in the pair of pants, and `g` maps them into `A`, off the center `c`.
  have hA₀S {w : ℝ × ℝ} (hw : w ∈ A₀) : w ∈ thricePuncturedSphereReal := by
    obtain ⟨ζ, hζ, rfl⟩ := hw
    exact endChart_mem_thricePuncturedSphereReal (by simp; linarith [hζ.1.1])
  have hgA {w : ℝ × ℝ} (hw : w ∈ A₀) : g w ∈ A := by
    rw [hA]
    exact mem_image_of_mem g hw
  have hgc {w : ℝ × ℝ} (hw : w ∈ A₀) : Complex.equivRealProdCLM.symm (g w) ≠ c := by
    simp only [g, realChart_apply, ContinuousLinearEquiv.symm_apply_apply]
    exact fun h ↦ (mem_thricePuncturedSphereReal_iff.1 (hA₀S hw)).1 (by simpa [ha] using h)
  have hud {w : ℝ × ℝ} (hw : w ∈ A₀) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (g w) :=
    (hu.contMDiffAt (hVo.mem_nhds (hAV (hgA hw)))).mdifferentiableAt one_ne_zero
  have htgt {w : ℝ × ℝ} (hw : w ∈ A₀) (v : ℂ) :=
    mdifferentiableAt_inputEndPerturbation_target hH hHs ha (hgc hw) (u (g w)) v
  have hdom {w : ℝ × ℝ} (hw : w ∈ A₀) (v : ℂ) :=
    differentiableAt_inputEndPerturbation_domain hH hHs ha (hgc hw) (u (g w)) v
  -- The pullback of the datum along `g` is the positive plane datum, the pair-of-pants datum
  -- whose only nonzero Hamiltonian is `H` at the input `0`.
  have hpull (v : ℝ × ℝ) : perturbationPullback g
      (fun z x ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ inputEndPerturbation c a H (Complex.equivRealProdCLM.symm z) x Complex.I) v =
      fun w x ↦ pairOfPantsPerturbation (Pi.single zero H) (Complex.equivRealProdCLM.symm w) x
        (Complex.equivRealProdCLM.symm v) := by
    funext w x
    rw [perturbationPullback_realChart _ (hgd w), inputEndPerturbation_add_mul ha,
      pairOfPantsPerturbation_single_zero]
  have hH' (q : Puncture) : Periodic ((Pi.single zero H : Puncture → ℝ → M → ℝ) q) 1 := by
    rcases eq_or_ne q zero with rfl | hq
    · simpa using hH
    · rw [Pi.single_eq_of_ne hq]
      exact fun _ ↦ rfl
  have hHs' (q : Puncture) : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1
      (uncurry ((Pi.single zero H : Puncture → ℝ → M → ℝ) q)) := by
    rcases eq_or_ne q zero with rfl | hq
    · simpa using hHs
    · rw [Pi.single_eq_of_ne hq]
      exact contMDiff_const
  -- The reparametrized map is `C¹` on the preimage of `V`.
  have hgV : IsOpen (g ⁻¹' V) := hVo.preimage hg.continuous
  have hug : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (u ∘ g) (g ⁻¹' V) :=
    hu.comp (hg.of_le (by norm_num)).contMDiff.contMDiffOn (mapsTo_preimage _ _)
  have hA₀V {z : ℝ × ℝ} (hz : z.1 ∈ Icc 1 R) : endChart zero z ∈ g ⁻¹' V := by
    have h := endChart_mem_preimage_closedBall_sdiff_ball zero hz
    rw [← image_endChart_Icc_prod_Ico] at h
    exact hAV (hgA h)
  -- In the coordinates of the end, the curvature and the energy density are integrable.
  have hpiece : Icc 1 R ×ˢ Ico (-1 / 2 : ℝ) (1 / 2) =
      {s : ℝ | 1 ≤ zero.endSign * s ∧ zero.endSign * s ≤ R} ×ˢ Ico (-1 / 2 : ℝ) (1 / 2) := by
    ext ⟨s, t⟩
    simp
  have hR₀ : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation (Pi.single zero H) (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation (Pi.single zero H) (Complex.equivRealProdCLM.symm z) x
        Complex.I) z ((u ∘ g) z)) A₀ := by
    have h := ω.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation_image_endChart hH' hHs'
      hug.continuousOn (q := zero) one_pos (b := R) fun z h₁ h₂ ↦
        hA₀V ⟨by simpa using h₁, by simpa using h₂⟩
    rwa [← hpiece] at h
  have hKp := contMDiffOn_thricePuncturedSphereReal_prod_univ_of_forall_contMDiffAt
    (contMDiffAt_pairOfPantsPerturbation (n := 1) hH' hHs')
  have hE₀ := hω.integrableOn_floerEnergyDensity (hgV.inter isOpen_thricePuncturedSphereReal)
    (hug.mono inter_subset_left) ((hKp 1).mono (prod_mono inter_subset_right subset_rfl))
    ((hKp Complex.I).mono (prod_mono inter_subset_right subset_rfl)) hA₀c
    (fun w hw ↦ ⟨by obtain ⟨ζ, hζ, rfl⟩ := hw; exact hA₀V hζ.1, hA₀S hw⟩) hR₀
  refine ⟨?_, ?_⟩
  · -- Integrability transfers along the chart `g`.
    rw [hA, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hA₀m
      (fun w _ ↦ (hgdiff w).hasFDerivAt.hasFDerivWithinAt) hginj]
    refine hR₀.congr_fun (fun w hw ↦ ?_) hA₀m
    rw [abs_of_nonneg (hgdet w), smul_eq_mul, ← ω.hamiltonianCurvature_perturbationPullback
      hg.contDiffAt (hdom hw 1) (hdom hw Complex.I) (htgt hw 1) (htgt hw Complex.I), hpull, hpull,
      equivRealProdCLM_symm_stdComplexLineReal, equivRealProdCLM_symm_stdComplexLineImag]
    rfl
  · -- Change variables along `g`, in each of the three integrals, to the pair of pants.
    rw [hA, ω.integral_eval₂_mfderiv_stdComplexLine_image hA₀m hginj (fun w _ ↦ hgdiff w)
        (fun w _ ↦ hgdet w) (fun w hw ↦ hud hw),
      ω.integral_floerEnergyDensity_image hA₀m hginj (fun w _ ↦ hgdiff w) (fun w _ ↦ hgdet w)
        (fun w hw ↦ hud hw) (fun w hw ↦ htgt hw 1) (fun w hw ↦ htgt hw _),
      ω.integral_hamiltonianCurvature_image hA₀m hginj (fun w _ ↦ hg.contDiffAt)
        (fun w _ ↦ hgdet w) (fun w hw ↦ hdom hw 1) (fun w hw ↦ hdom hw _)
        (fun w hw ↦ htgt hw 1) (fun w hw ↦ htgt hw _),
      hpull, hpull, equivRealProdCLM_symm_stdComplexLineReal,
      equivRealProdCLM_symm_stdComplexLineImag]
    rw [hω.integral_floerEnergyDensity_image_endChart hH' hHs' hgV hug hR
      (by norm_num) (by simp; linarith) (fun z hz ↦ hA₀V hz) hE₀]
    -- The boundary term on the circle `s = 1` vanishes with the cutoff, and the one on `s = R`
    -- is an integral over a period.
    have hper : Periodic (fun t : ℝ ↦ H t (u (Complex.equivRealProdCLM
        (c + a * zero.cylindricalEndLift (↑R + ↑t * Complex.I))))) 1 := fun t ↦ by
      simp only [zero.periodic_cylindricalEndLift R t, hH t]
    have hloop (t : ℝ) : (u ∘ g) (endChart zero (R, t)) =
        u (Complex.equivRealProdCLM (c + a * zero.cylindricalEndLift (↑R + ↑t * Complex.I))) := by
      simp [g, realChart_apply, endChart_mk]
    simp only [Pi.single_eq_same, endSign_zero, one_mul, sub_self, smoothTransition.zero,
      zero_mul, intervalIntegral.integral_zero, sub_zero, intervalIntegral.integral_const_mul,
      hloop, intervalIntegral_neg_half_half_eq hper]
    rfl

/-- **The energy identity on the annulus of the output end, for a manifold target.** Let `K` be the
negative plane datum of a period-one `C¹` Hamiltonian `H`, and let `u` be `C¹` on an open set
containing the closed annulus `A` about `0` with radii `2 exp (2π)` and `2 exp (2πR)`, the image of
the part `-R ≤ s ≤ -1` of the end at `∞`. Then the curvature along `u` is integrable over `A`, and
the Floer energy over `A` is the area, minus `β(R - 1)` times the integral of `H` along the outer
boundary circle, minus the integrated curvature. -/
private theorem IsNondegenerate.integral_floerEnergyDensity_negativePlanePerturbation_annulus
    (hω : ω.IsNondegenerate) {H : ℝ → M → ℝ} (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {u : ℝ × ℝ → M} {R : ℝ}
    (hR : 1 ≤ R) {V : Set (ℝ × ℝ)} (hVo : IsOpen V)
    (hAV : Complex.equivRealProdCLM.symm ⁻¹'
      (Metric.closedBall 0 (2 * Real.exp (2 * π * R)) \ Metric.ball 0 (2 * Real.exp (2 * π))) ⊆ V)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u V) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z))
      (Complex.equivRealProdCLM.symm ⁻¹'
        (Metric.closedBall 0 (2 * Real.exp (2 * π * R)) \ Metric.ball 0 (2 * Real.exp (2 * π)))) ∧
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹'
        (Metric.closedBall 0 (2 * Real.exp (2 * π * R)) \ Metric.ball 0 (2 * Real.exp (2 * π))),
        ω.floerEnergyDensity
        (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹'
          (Metric.closedBall 0 (2 * Real.exp (2 * π * R)) \ Metric.ball 0 (2 * Real.exp (2 * π))),
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        smoothTransition (R - 1) * (∫ t in (0 : ℝ)..1,
          H t (u (Complex.equivRealProdCLM (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹'
          (Metric.closedBall 0 (2 * Real.exp (2 * π * R)) \ Metric.ball 0 (2 * Real.exp (2 * π))),
          ω.hamiltonianCurvature
          (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ negativePlanePerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  -- The annulus is the part `-R ≤ s ≤ -1` of the end at `∞` of the pair of pants.
  have hA : endChart inf '' (Icc (-R) (-1) ×ˢ Ico (-1 / 2 : ℝ) (1 / 2)) =
      Complex.equivRealProdCLM.symm ⁻¹'
        (Metric.closedBall 0 (2 * Real.exp (2 * π * R)) \
          Metric.ball 0 (2 * Real.exp (2 * π))) := by
    rw [image_endChart_Icc_prod_Ico, endCenter_inf, endScale_inf]
    norm_num
  have hAV' {z : ℝ × ℝ} (hz : z.1 ∈ Icc (-R) (-1)) : endChart inf z ∈ V := by
    have h := endChart_mem_preimage_closedBall_sdiff_ball inf hz
    rw [← image_endChart_Icc_prod_Ico, hA] at h
    exact hAV h
  rw [← hA, ← pairOfPantsPerturbation_single_inf]
  set A := endChart inf '' (Icc (-R) (-1) ×ˢ Ico (-1 / 2 : ℝ) (1 / 2))
  have hAc : IsCompact A := by
    rw [hA]
    exact Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
      ((isCompact_closedBall _ _).diff Metric.isOpen_ball)
  have hH' (q : Puncture) : Periodic ((Pi.single inf H : Puncture → ℝ → M → ℝ) q) 1 := by
    rcases eq_or_ne q inf with rfl | hq
    · simpa using hH
    · rw [Pi.single_eq_of_ne hq]
      exact fun _ ↦ rfl
  have hHs' (q : Puncture) : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1
      (uncurry ((Pi.single inf H : Puncture → ℝ → M → ℝ) q)) := by
    rcases eq_or_ne q inf with rfl | hq
    · simpa using hHs
    · rw [Pi.single_eq_of_ne hq]
      exact contMDiff_const
  have hAS {w : ℝ × ℝ} (hw : w ∈ A) : w ∈ thricePuncturedSphereReal := by
    obtain ⟨ζ, hζ, rfl⟩ := hw
    exact endChart_mem_thricePuncturedSphereReal (by simp; linarith [hζ.1.2])
  -- The curvature and the energy density are integrable over the annulus.
  have hpiece : Icc (-R) (-1) ×ˢ Ico (-1 / 2 : ℝ) (1 / 2) =
      {s : ℝ | 1 ≤ inf.endSign * s ∧ inf.endSign * s ≤ R} ×ˢ Ico (-1 / 2 : ℝ) (1 / 2) := by
    ext ⟨s, t⟩
    simp only [mem_prod, mem_Icc, mem_ofPred_eq, endSign_inf, neg_one_mul]
    constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃⟩ <;> exact ⟨⟨by linarith, by linarith⟩, h₃⟩
  have hRA : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation (Pi.single inf H) (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation (Pi.single inf H) (Complex.equivRealProdCLM.symm z) x
        Complex.I) z (u z)) A := by
    have h := ω.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation_image_endChart hH' hHs'
      hu.continuousOn (q := inf) one_pos (b := R) fun z h₁ h₂ ↦ hAV'
        ⟨by simp at h₂; linarith, by simp at h₁; linarith⟩
    rwa [← hpiece] at h
  have hKp := contMDiffOn_thricePuncturedSphereReal_prod_univ_of_forall_contMDiffAt
    (contMDiffAt_pairOfPantsPerturbation (n := 1) hH' hHs')
  have hEA := hω.integrableOn_floerEnergyDensity (hVo.inter isOpen_thricePuncturedSphereReal)
    (hu.mono inter_subset_left) ((hKp 1).mono (prod_mono inter_subset_right subset_rfl))
    ((hKp Complex.I).mono (prod_mono inter_subset_right subset_rfl)) hAc
    (fun w hw ↦ ⟨by obtain ⟨ζ, hζ, rfl⟩ := hw; exact hAV' hζ.1, hAS hw⟩) hRA
  refine ⟨hRA, ?_⟩
  rw [hω.integral_floerEnergyDensity_image_endChart hH' hHs' hVo hu (by linarith)
    (by simp; linarith) (by norm_num) (fun z hz ↦ hAV' hz) hEA]
  -- The boundary term on the circle `s = -1` vanishes with the cutoff, and the one on `s = -R`
  -- is an integral over a period.
  have hper : Periodic (fun t : ℝ ↦ H t (u (Complex.equivRealProdCLM
      (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I))))) 1 := fun t ↦ by
    simp only [inf.periodic_cylindricalEndLift (-R) t, hH t]
  simp only [Pi.single_eq_same, endSign_inf, neg_mul, one_mul, neg_neg, sub_self,
    smoothTransition.zero, zero_mul, intervalIntegral.integral_zero, zero_sub,
    intervalIntegral.integral_const_mul, endChart_mk, intervalIntegral_neg_half_half_eq hper]
  ring

end Annuli

/-! ### The truncated sphere with moving input ends -/

section Sphere

open Floer

variable {ι : Type*} [Fintype ι] {c a : ι → ℂ} {H : ι → ℝ → M → ℝ} {Hout : ℝ → M → ℝ}

/-- Perturbation data that agree near a point have the same energy density and the same curvature
there. -/
private theorem floerEnergyDensity_eq_and_hamiltonianCurvature_eq_of_eventuallyEq
    (ω : SmoothTwoForm I M) {K K' : ℂ → M → ℂ →L[ℝ] ℝ} (u : ℝ × ℝ → M) {z : ℝ × ℝ}
    (h : ∀ᶠ z' in 𝓝 z, ∀ x, K (Complex.equivRealProdCLM.symm z') x =
      K' (Complex.equivRealProdCLM.symm z') x) :
    ω.floerEnergyDensity (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      ω.floerEnergyDensity (fun z x ↦ K' (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K' (Complex.equivRealProdCLM.symm z) x Complex.I) u z ∧
    ω.hamiltonianCurvature (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      ω.hamiltonianCurvature (fun z x ↦ K' (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K' (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  have h₀ := h.self_of_nhds
  refine ⟨?_, ?_⟩
  · simp only [floerEnergyDensity_def, perturbedMFDeriv_apply_stdComplexLineReal,
      perturbedMFDeriv_apply_stdComplexLineImag, h₀]
  · exact congrFun (ω.hamiltonianCurvature_congr_of_eventuallyEq
      (h.mono fun z' hz' ↦ funext fun x ↦ by simp only [hz' x])
      (h.mono fun z' hz' ↦ funext fun x ↦ by simp only [hz' x])) (u z)

variable [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M}

/-- **The energy identity on the truncated sphere with moving input ends, for a manifold target.**
Let the input ends have centers `c i`, nonzero scales `a i` and period-one `C¹` Hamiltonians `H i`,
and let the output end at `∞` have a period-one `C¹` Hamiltonian `Hout`, on a finite-dimensional
manifold with a nondegenerate two-form. Assume that the discs `‖w - c i‖ < ‖a i‖ / 2` are pairwise
disjoint and lie in the disc `‖w‖ ≤ 2 exp (2π)`. Let `K` be the perturbation datum
`TauCeti.Floer.puncturedSpherePerturbation c a H Hout`, with components `K_s(z) = K(z)(1)` and
`K_t(z) = K(z)(i)` in the global coordinate `z = s + i t` of `ℂ`, and let `u` be a map which is `C¹`
on an open set `V` containing the truncation `T_R = puncturedSphereTruncation c a R`. For `R ≥ 1`,
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
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {u : ℝ × ℝ → M} {R : ℝ} (hR : 1 ≤ R)
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
  have hπ := Real.pi_pos
  have he : Real.exp (-(2 * π)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have heR : Real.exp (-(2 * π * R)) ≤ Real.exp (-(2 * π)) := Real.exp_le_exp.2 (by nlinarith)
  have heR' : Real.exp (2 * π) ≤ Real.exp (2 * π * R) := Real.exp_le_exp.2 (by nlinarith)
  have hapos (i : ι) : 0 < ‖a i‖ := norm_pos_iff.2 (ha i)
  set K := puncturedSpherePerturbation c a H Hout
  set T := Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R
  -- The annulus `A i` about the center `c i`, on which the datum is that of the input end `i`, and
  -- the annulus `Aout` at the outer circle, on which it is the output datum.
  set A : ι → Set (ℝ × ℝ) := fun i ↦ Complex.equivRealProdCLM.symm ⁻¹'
    (Metric.closedBall (c i) (‖a i‖ * Real.exp (-(2 * π)) / 2) \
      Metric.ball (c i) (‖a i‖ * Real.exp (-(2 * π * R)) / 2))
  set Aout := Complex.equivRealProdCLM.symm ⁻¹'
    (Metric.closedBall 0 (2 * Real.exp (2 * π * R)) \ Metric.ball 0 (2 * Real.exp (2 * π)))
  have hmemA {i : ι} {z : ℝ × ℝ} : z ∈ A i ↔
      ‖a i‖ * Real.exp (-(2 * π * R)) / 2 ≤ ‖Complex.equivRealProdCLM.symm z - c i‖ ∧
        ‖Complex.equivRealProdCLM.symm z - c i‖ ≤ ‖a i‖ * Real.exp (-(2 * π)) / 2 := by
    simp only [A, mem_preimage, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
      dist_eq_norm, not_lt]
    exact and_comm
  have hmemAout {z : ℝ × ℝ} : z ∈ Aout ↔ 2 * Real.exp (2 * π) ≤ ‖Complex.equivRealProdCLM.symm z‖ ∧
      ‖Complex.equivRealProdCLM.symm z‖ ≤ 2 * Real.exp (2 * π * R) := by
    simp only [Aout, mem_preimage, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
      dist_zero_right, not_lt]
    exact and_comm
  have hmemT {z : ℝ × ℝ} : z ∈ T ↔ ‖Complex.equivRealProdCLM.symm z‖ ≤ 2 * Real.exp (2 * π * R) ∧
      ∀ i, ‖a i‖ * Real.exp (-(2 * π * R)) / 2 ≤ ‖Complex.equivRealProdCLM.symm z - c i‖ :=
    mem_puncturedSphereTruncation
  -- Distances from the centers.
  have hdist (w : ℂ) (i j : ι) : ‖c i - c j‖ ≤ ‖w - c i‖ + ‖w - c j‖ := by
    have h := norm_sub_le (w - c j) (w - c i)
    rw [show w - c j - (w - c i) = c i - c j by ring] at h
    linarith
  have hai (i : ι) : ‖a i‖ * Real.exp (-(2 * π)) < ‖a i‖ := mul_lt_of_lt_one_right (hapos i) he
  have haiR (i : ι) : ‖a i‖ * Real.exp (-(2 * π * R)) ≤ ‖a i‖ * Real.exp (-(2 * π)) :=
    mul_le_mul_of_nonneg_left heR (norm_nonneg _)
  have hcont (i : ι) : Continuous fun z' : ℝ × ℝ ↦ ‖Complex.equivRealProdCLM.symm z' - c i‖ := by
    fun_prop
  have hcont₀ : Continuous fun z' : ℝ × ℝ ↦ ‖Complex.equivRealProdCLM.symm z'‖ := by
    fun_prop
  have hnorm (w : ℂ) (i : ι) : ‖w‖ ≤ ‖c i‖ + ‖w - c i‖ := by
    simpa using norm_add_le (c i) (w - c i)
  have hnorm' (w : ℂ) (i : ι) : ‖w‖ - ‖c i‖ ≤ ‖w - c i‖ := norm_sub_norm_le w (c i)
  -- The annuli lie in the truncation, and are pairwise disjoint.
  have hAT (i : ι) : A i ⊆ T := fun z hz ↦ by
    obtain ⟨h₁, h₂⟩ := hmemA.1 hz
    refine hmemT.2 ⟨?_, fun j ↦ ?_⟩
    · have := hnorm (Complex.equivRealProdCLM.symm z) i
      linarith [hout i, hai i]
    · rcases eq_or_ne j i with rfl | hji
      · exact h₁
      · have := hsep hji.symm
        have := hdist (Complex.equivRealProdCLM.symm z) i j
        linarith [hai i, hai j, haiR j]
  have hAoutT : Aout ⊆ T := fun z hz ↦ by
    obtain ⟨h₁, h₂⟩ := hmemAout.1 hz
    refine hmemT.2 ⟨h₂, fun i ↦ ?_⟩
    have := hnorm' (Complex.equivRealProdCLM.symm z) i
    linarith [hout i, hai i, haiR i]
  have hAd : Pairwise (Disjoint on A) := fun i j hij ↦ Set.disjoint_left.2 fun z hzi hzj ↦ by
    have h₁ := (hmemA.1 hzi).2
    have h₂ := (hmemA.1 hzj).2
    have := hsep hij
    have := hdist (Complex.equivRealProdCLM.symm z) i j
    linarith [hai i, hai j]
  have hAoutd : Disjoint Aout (⋃ i, A i) := Set.disjoint_left.2 fun z hz hzA ↦ by
    obtain ⟨i, hzi⟩ := mem_iUnion.1 hzA
    have h₁ := (hmemAout.1 hz).1
    have h₂ := (hmemA.1 hzi).2
    have := hnorm (Complex.equivRealProdCLM.symm z) i
    linarith [hout i, hai i]
  have hcl {w : ℂ} {r₁ r₂ : ℝ} :
      MeasurableSet (Complex.equivRealProdCLM.symm ⁻¹'
        (Metric.closedBall w r₂ \ Metric.ball w r₁)) :=
    (Metric.isClosed_closedBall.sdiff Metric.isOpen_ball).measurableSet.preimage
      Complex.equivRealProdCLM.symm.continuous.measurable
  have hAm (i : ι) : MeasurableSet (A i) := hcl
  have hAoutm : MeasurableSet Aout := hcl
  have hTc : IsCompact T := Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
    (isCompact_puncturedSphereTruncation c a R)
  -- On the annuli the datum is that of a single end.
  have hKi (i : ι) {z : ℝ × ℝ} (hz : z ∈ A i) : ∀ᶠ z' in 𝓝 z, ∀ x,
      K (Complex.equivRealProdCLM.symm z') x =
        inputEndPerturbation (c i) (a i) (H i) (Complex.equivRealProdCLM.symm z') x := by
    have hlt : ‖Complex.equivRealProdCLM.symm z - c i‖ < ‖a i‖ / 2 := by
      linarith [(hmemA.1 hz).2, hai i]
    filter_upwards [(isOpen_lt (hcont i) continuous_const).mem_nhds hlt] with z' hz' x
    exact puncturedSpherePerturbation_eq_inputEndPerturbation hsep hout hz' x
  have hKout {z : ℝ × ℝ} (hz : z ∈ Aout) : ∀ᶠ z' in 𝓝 z, ∀ x,
      K (Complex.equivRealProdCLM.symm z') x =
        negativePlanePerturbation Hout (Complex.equivRealProdCLM.symm z') x := by
    have hlt (i : ι) :
        ‖a i‖ * Real.exp (-(2 * π)) / 2 < ‖Complex.equivRealProdCLM.symm z - c i‖ := by
      have := hnorm' (Complex.equivRealProdCLM.symm z) i
      linarith [(hmemAout.1 hz).1, hout i, hai i]
    filter_upwards [eventually_all.2 fun i ↦
      (isOpen_lt continuous_const (hcont i)).mem_nhds (hlt i)] with z' hz' x
    exact puncturedSpherePerturbation_eq_negativePlanePerturbation (fun i ↦ (hz' i).le) x
  -- The annulus identities, with the integrability of the curvature.
  have hAV (i : ι) := (hAT i).trans hTV
  have hIi (i : ι) := hω.integral_floerEnergyDensity_inputEndPerturbation_annulus (hH i) (hHs i)
    (ha i) hR hVo (hAV i) hu
  have hIout := hω.integral_floerEnergyDensity_negativePlanePerturbation_annulus hHout hHouts hR hVo
    (hAoutT.trans hTV) hu
  -- The core: off the annuli the datum vanishes nearby.
  set C := T \ (Aout ∪ ⋃ i, A i)
  have hK0 {z : ℝ × ℝ} (hz : z ∈ C) : ∀ᶠ z' in 𝓝 z, ∀ x,
      K (Complex.equivRealProdCLM.symm z') x = 0 := by
    obtain ⟨hzT, hzA⟩ := hz
    have hzT' := hmemT.1 hzT
    have hlt (i : ι) :
        ‖a i‖ * Real.exp (-(2 * π)) / 2 < ‖Complex.equivRealProdCLM.symm z - c i‖ := by
      by_contra! h
      exact hzA (Or.inr (mem_iUnion.2 ⟨i, hmemA.2 ⟨hzT'.2 i, h⟩⟩))
    have hlt' : ‖Complex.equivRealProdCLM.symm z‖ < 2 * Real.exp (2 * π) := by
      by_contra! h
      exact hzA (Or.inl (hmemAout.2 ⟨h, hzT'.1⟩))
    filter_upwards [eventually_all.2 fun i ↦
      (isOpen_lt continuous_const (hcont i)).mem_nhds (hlt i),
      (isOpen_lt hcont₀ continuous_const).mem_nhds hlt'] with z' hz' hz'' x
    exact (puncturedSpherePerturbation_eq_negativePlanePerturbation (fun i ↦ (hz' i).le) x).trans
      (negativePlanePerturbation_eq_zero_of_norm_le hz''.le x)
  have hcore {z : ℝ × ℝ} (hz : z ∈ C) :=
    floerEnergyDensity_eq_and_hamiltonianCurvature_eq_of_eventuallyEq (K' := fun _ _ ↦ 0) ω u
      (hK0 hz)
  -- Integrability over the truncation.
  have harea := (ω.isSmoothForm.of_le (by simp)).continuousOn_apply_mfderiv hVo hu
    stdComplexLineReal stdComplexLineImag
  simp only [← SmoothBundleForm.eval₂_apply] at harea
  replace harea := (harea.mono hTV).integrableOn_compact (μ := volume) hTc
  have hCm : MeasurableSet C :=
    hTc.isClosed.measurableSet.diff (hAoutm.union (MeasurableSet.iUnion hAm))
  have hRi (i : ι) : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) (A i) :=
    (hIi i).1.congr_fun (fun z hz ↦
      (floerEnergyDensity_eq_and_hamiltonianCurvature_eq_of_eventuallyEq ω u (hKi i hz)).2.symm)
      (hAm i)
  have hRout : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) Aout :=
    hIout.1.congr_fun (fun z hz ↦
      (floerEnergyDensity_eq_and_hamiltonianCurvature_eq_of_eventuallyEq ω u (hKout hz)).2.symm)
      hAoutm
  have hRC : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) C :=
    integrableOn_zero.congr_fun (fun z hz ↦ by
      rw [(hcore hz).2]
      simp) hCm
  have hTsplit : T ⊆ C ∪ (Aout ∪ ⋃ i, A i) := fun z hz ↦ by
    by_cases h : z ∈ Aout ∪ ⋃ i, A i
    · exact Or.inr h
    · exact Or.inl ⟨hz, h⟩
  have hRT : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) T :=
    (hRC.union (hRout.union (integrableOn_finite_iUnion.2 hRi))).mono_set hTsplit
  -- The datum is `C¹` off the centers.
  set U := V ∩ ⋂ i, {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ c i}
  have hUo : IsOpen U := hVo.inter (isOpen_iInter_of_finite fun i ↦
    isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const)
  have hTU : T ⊆ U := fun z hz ↦ ⟨hTV hz, mem_iInter.2 fun i h ↦ by
    have := (hmemT.1 hz).2 i
    rw [h, sub_self, norm_zero] at this
    nlinarith [hapos i, Real.exp_pos (-(2 * π * R))]⟩
  have hKs (v : ℂ) : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1
      (uncurry fun z x ↦ K (Complex.equivRealProdCLM.symm z) x v) (U ×ˢ univ) := by
    rintro ⟨z, x⟩ ⟨hz, -⟩
    have h := contMDiffAt_puncturedSpherePerturbation (n := 1) hH hHs hHout hHouts ha
      (w := Complex.equivRealProdCLM.symm z) (fun i ↦ mem_iInter.1 hz.2 i) x
    have hφ : ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ, (ι → ℂ) × (ι → ℂ)).prod (𝓘(ℝ, ℂ).prod I)) 1
        (fun p : (ℝ × ℝ) × M ↦ ((c, a), (Complex.equivRealProdCLM.symm p.1, p.2))) (z, x) :=
      contMDiffAt_const.prodMk
        ((Complex.equivRealProdCLM.symm.contDiff.contMDiff.contMDiffAt.comp _
          contMDiffAt_fst).prodMk contMDiffAt_snd)
    exact ((h.comp (z, x) hφ).clm_apply contMDiffAt_const).contMDiffWithinAt
  have hET := hω.integrableOn_floerEnergyDensity hUo (hu.mono inter_subset_left) (hKs 1)
    (hKs Complex.I) hTc hTU hRT
  -- Split each integral over the core and the annuli.
  have hsplit (f : ℝ × ℝ → ℝ) (hf : IntegrableOn f T) :
      ∫ z in T, f z = (∫ z in C, f z) + ((∫ z in Aout, f z) + ∑ i, ∫ z in A i, f z) := by
    have hBT : Aout ∪ ⋃ i, A i ⊆ T := union_subset hAoutT (iUnion_subset hAT)
    have hTC : T = C ∪ (Aout ∪ ⋃ i, A i) := (sdiff_union_of_subset hBT).symm
    conv_lhs => rw [hTC]
    rw [setIntegral_union disjoint_sdiff_left (hAoutm.union (MeasurableSet.iUnion hAm))
        (hf.mono_set sdiff_subset) (hf.mono_set hBT),
      setIntegral_union hAoutd (MeasurableSet.iUnion hAm) (hf.mono_set hAoutT)
        (hf.mono_set (iUnion_subset hAT)),
      integral_iUnion_fintype hAm hAd fun i ↦ hf.mono_set (hAT i)]
  -- On the core the energy density is the area density and the curvature vanishes.
  have hCE : ∫ z in C, ω.floerEnergyDensity (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      ∫ z in C, (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) :=
    setIntegral_congr_fun hCm fun z hz ↦ by
      rw [(hcore hz).1]
      simp
  have hCR : ∫ z in C, ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun z hz ↦ by
      rw [(hcore hz).2]
      simp
  -- On the annuli the energy and curvature are those of the single end data.
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
    rw [setIntegral_congr_fun (hAm i) fun z hz ↦
        (floerEnergyDensity_eq_and_hamiltonianCurvature_eq_of_eventuallyEq ω u (hKi i hz)).1,
      setIntegral_congr_fun (hAm i) fun z hz ↦
        (floerEnergyDensity_eq_and_hamiltonianCurvature_eq_of_eventuallyEq ω u (hKi i hz)).2]
    exact (hIi i).2
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
    rw [setIntegral_congr_fun hAoutm fun z hz ↦
        (floerEnergyDensity_eq_and_hamiltonianCurvature_eq_of_eventuallyEq ω u (hKout hz)).1,
      setIntegral_congr_fun hAoutm fun z hz ↦
        (floerEnergyDensity_eq_and_hamiltonianCurvature_eq_of_eventuallyEq ω u (hKout hz)).2]
    exact hIout.2
  rw [hsplit _ hET, hsplit _ harea, hsplit _ hRT, hCE, hCR, hEout,
    Finset.sum_congr rfl fun i _ ↦ hEi i, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

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
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {B : ι → ℝ} {Bout : ℝ}
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
  -- The supports of the input end data are smaller than the discs of the input ends.
  have he : Real.exp (-(2 * π)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [Real.pi_pos])
  have hsep' : Pairwise fun i j =>
      ‖a i‖ * Real.exp (-(2 * π)) / 2 + ‖a j‖ * Real.exp (-(2 * π)) / 2 ≤ ‖c i - c j‖ :=
    fun i j hij ↦ by nlinarith [hsep hij, norm_nonneg (a i), norm_nonneg (a j)]
  have hout' (i : ι) : ‖c i‖ + ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ 2 * Real.exp (2 * π) := by
    nlinarith [hout i, norm_nonneg (a i)]
  rw [← ENNReal.ofReal_le_ofReal_iff (add_nonneg (Finset.sum_nonneg fun i _ ↦ hB₀ i) hBout₀),
    ← Real.enorm_eq_ofReal_abs, ENNReal.ofReal_add (Finset.sum_nonneg fun i _ ↦ hB₀ i) hBout₀,
    ENNReal.ofReal_sum_of_nonneg fun i _ ↦ hB₀ i]
  exact (enorm_integral_le_lintegral_enorm _).trans ((setLIntegral_le_lintegral _ _).trans
    (ω.lintegral_enorm_hamiltonianCurvature_puncturedSpherePerturbation_le hH hHs hHout hHouts ha
      hsep' hout' hB hBout u))

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
    (hsep : Pairwise fun i j => ‖a i‖ / 2 + ‖a j‖ / 2 ≤ ‖c i - c j‖)
    (hout : ∀ i, ‖c i‖ + ‖a i‖ / 2 ≤ 2 * Real.exp (2 * π)) {B : ι → ℝ} {Bout : ℝ}
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
  have hTm : MeasurableSet (Complex.equivRealProdCLM.symm ⁻¹' puncturedSphereTruncation c a R) :=
    (Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
      (isCompact_puncturedSphereTruncation c a R)).isClosed.measurableSet
  have hE := setIntegral_nonneg (μ := volume) hTm fun z hz ↦
    floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  have h := (abs_le.1
    (hω.abs_integral_floerEnergyDensity_puncturedSpherePerturbation_truncation_sub_le hH hHs hHout
      hHouts ha hsep hout hB hBout hR hVo hTV hu)).2
  linarith

end Sphere

end SmoothTwoForm

end TauCeti
