/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Plane.Basic
public import TauCeti.Geometry.Symplectic.Floer.Pullback
public import TauCeti.Geometry.Symplectic.Floer.Manifold
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity

/-!
# The curvature and the energy identity of the perturbation on a PSS plane

The energy identity `TauCeti.SymplecticForm.integral_floerEnergyDensity` on a rectangle expresses
the integrated Floer energy density of a map `u` as its symplectic area, plus a boundary term in
`K(u)`, minus the integrated curvature `∫ R_K(z, u(z))` of the perturbation `K`, where
`R_K = ∂_s K_t - ∂_t K_s - {K_s, K_t}`. This file bounds the curvature term: it computes the
curvature of the perturbation `TauCeti.Floer.PSSPlane.perturbation` of a PSS plane, built from a
period-one Hamiltonian `H` on a manifold `M` with a smooth two-form `ω`, such as a closed
symplectic manifold, and bounds its integral over the whole plane. It then proves the energy
identity on the discs of the plane, for a nondegenerate two-form.

In the end coordinates `(s, t)` of the plane the perturbation is the continuation datum
`β(ε s - 1) H(t) dt` (`TauCeti.Floer.PSSPlane.endComponent_I`), so its curvature there is
`ε β'(ε s - 1) H(t)` (`SmoothTwoForm.hamiltonianCurvature_pssPlaneEndComponent`). It vanishes
outside the collar `1 ≤ ε s ≤ 2`
(`SmoothTwoForm.hamiltonianCurvature_pssPlaneEndComponent_eq_zero`). The integrated curvature
may be computed in any chart (`SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_image`), and the
end lift `z ↦ exp (2π ε z)` maps a band of height one bijectively onto `ℂ ∖ {0}`. Since `β' ≥ 0`
has total integral `1`, if `|H| ≤ B` then

`∫_ℂ |R_K(z, u(z))| dz ≤ B`

for every map `u : ℝ × ℝ → M`, measurable or not
(`SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_pssPlanePerturbation_le`). Here the plane is
identified with `ℝ × ℝ` by `Complex.equivRealProdCLM`, and the curvature is computed in the global
coordinate `z = s + i t`, in which the `ds` and `dt` components of `K` are its values on the
tangent vectors `1` and `i`; in these coordinates the components of `K` are `C¹`
(`TauCeti.Floer.PSSPlane.contMDiff_uncurry_perturbation`). A symplectic vector space is the case
of the constant form `TauCeti.SymplecticForm.constSmooth`, through which the vector-space bound
`TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_pssPlanePerturbation_le` is derived.

The same decomposition of the plane into the pole disc `‖w‖ < exp (2π)`, where `K` vanishes, and
the end integrates the energy identity over the disc `D_R = {‖w‖ ≤ exp (2πR)}`, bounded by the
circle `ε s = R`. On the end the rectangle identity applies in end coordinates; the boundary terms
along the angular sides cancel by periodicity, and the one on the circle `ε s = 1` vanishes with
the cutoff. For a `C¹` map `u` into `M` and `R ≥ 1` this gives

`∫_{D_R} E = ∫_{D_R} u^*ω + ε β(R - 1) ∫₀¹ H(t, u(φ(ε R + i t))) dt - ∫_{D_R} R_K(u)`

(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pssPlanePerturbation_closedBall`),
where `φ` is the end lift and `u^*ω` is the intrinsic area density `ω(∂_s u, ∂_t u)` on
`T_{u(z)} M`. No integrability is assumed: the area density and `d(K(u))` are continuous, and in
end coordinates, times the Jacobian of the end lift, the curvature is the continuous function
`ε β'(ε s - 1) H(t, u)`. Closedness of `ω` is not used. For a solution of the Floer equation
`(du - X_K)^{0,1} = 0` on `D_R` with almost complex structures tamed by `ω` the energy density is
nonnegative, so the area plus the Hamiltonian boundary term bounds the integrated curvature
(`SmoothTwoForm.IsNondegenerate.integral_hamiltonianCurvature_pssPlanePerturbation_closedBall_le`).
For a symplectic vector space the identity is
`SymplecticForm.integral_floerEnergyDensity_pssPlanePerturbation_closedBall`, through the constant
form `SymplecticForm.constSmooth`. The curvature vanishes on the part `ε s > 2` of the end, where
`K` is `H(t) dt` (`SymplecticForm.hamiltonianCurvature_pssPlanePerturbation_eq_zero_of_two_lt`).
For a vector space target the area term is expressed through the action of the boundary loop in
`TauCeti.Geometry.Symplectic.Floer.Plane.Action`.

## Main results

* `TauCeti.SmoothTwoForm.hamiltonianCurvature_pssPlaneEndComponent`: the curvature in end
  coordinates is `ε β'(ε s - 1) H(t)`.
* `TauCeti.SmoothTwoForm.hamiltonianCurvature_pssPlaneEndComponent_eq_zero`: it vanishes outside
  the collar `1 ≤ ε s ≤ 2`.
* `TauCeti.SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_pssPlanePerturbation_le`: the
  integrated curvature of the perturbation along any map is at most a bound for the
  Hamiltonian.
* `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pssPlanePerturbation_closedBall`: the
  energy identity on the discs of the plane, for a manifold target.
* `SmoothTwoForm.IsNondegenerate.integral_hamiltonianCurvature_pssPlanePerturbation_closedBall_le`:
  for a solution of the Floer equation on the disc, the area plus the Hamiltonian boundary term
  bounds the integrated curvature.
* `TauCeti.SymplecticForm.integral_floerEnergyDensity_pssPlanePerturbation_closedBall`: the energy
  identity for a symplectic vector space target.
* `TauCeti.SymplecticForm.hamiltonianCurvature_pssPlanePerturbation_eq_zero_of_two_lt`: the
  curvature vanishes beyond the collar.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the resulting energy bounds.
-/

public section

open Set Real Function MeasureTheory Filter Manifold
open TauCeti.Complex (realChart realChart_apply contDiff_realChart)
open scoped Topology

namespace TauCeti

namespace SmoothTwoForm

open Floer Floer.PSSPlane

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {p : PSSPlane} {H : ℝ → M → ℝ}

/-- **The curvature in end coordinates.** In the end coordinates `(s, t)` of a PSS plane, the
curvature of the perturbation `β(ε s - 1) H(t) dt` is `ε β'(ε s - 1) H(t)`. -/
theorem hamiltonianCurvature_pssPlaneEndComponent (ω : SmoothTwoForm I M) (hH : Periodic H 1)
    (z : ℝ × ℝ) {x : M} (hHx : DifferentiableAt ℝ (fun t ↦ H t x) z.2) :
    ω.hamiltonianCurvature (p.endComponent H 1) (p.endComponent H Complex.I) z x =
      p.endSign * deriv smoothTransition (p.endSign * z.1 - 1) * H z.2 x := by
  have hβ : HasDerivAt (fun s ↦ smoothTransition (p.endSign * s - 1))
      (deriv smoothTransition (p.endSign * z.1 - 1) * p.endSign) z.1 :=
    (((hasDerivAt_id z.1).const_mul p.endSign).sub_const 1).smoothTransition.congr_deriv
      (by simp)
  have h := ω.hamiltonianCurvature_continuation hβ.differentiableAt hHx
  beta_reduce at h
  rw [endComponent_one, endComponent_I hH, h, hβ.deriv]
  ring

/-- **The curvature is supported in the collar.** On the parts `ε s < 1` and `ε s > 2` of the end
of a PSS plane, the curvature of the perturbation in end coordinates vanishes. -/
theorem hamiltonianCurvature_pssPlaneEndComponent_eq_zero (ω : SmoothTwoForm I M)
    (hH : Periodic H 1) {z : ℝ × ℝ} (hz : p.endSign * z.1 < 1 ∨ 2 < p.endSign * z.1) (x : M) :
    ω.hamiltonianCurvature (p.endComponent H 1) (p.endComponent H Complex.I) z x = 0 := by
  -- Near `z`, the cutoff `β(ε s - 1)` is constant, equal to `0` or to `1`.
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ᶠ w in 𝓝 z, smoothTransition (p.endSign * w.1 - 1) = c := by
    have hcont : Continuous fun w : ℝ × ℝ ↦ p.endSign * w.1 :=
      continuous_const.mul continuous_fst
    rcases hz with h | h
    · exact ⟨0, eventually_of_mem (hcont.isOpen_preimage _ isOpen_Iio |>.mem_nhds h) fun w hw ↦
        smoothTransition.zero_of_nonpos (by simp only [mem_preimage, mem_Iio] at hw; linarith)⟩
    · exact ⟨1, eventually_of_mem (hcont.isOpen_preimage _ isOpen_Ioi |>.mem_nhds h) fun w hw ↦
        smoothTransition.one_of_one_le (by simp only [mem_preimage, mem_Ioi] at hw; linarith)⟩
  have ht : p.endComponent H Complex.I =ᶠ[𝓝 z] fun w ↦ (fun t x ↦ c * H t x) w.2 := by
    filter_upwards [hc] with w hw
    rw [endComponent_I hH]
    beta_reduce
    rw [hw]
  rw [endComponent_one, ω.hamiltonianCurvature_congr_of_eventuallyEq (EventuallyEq.refl _ _) ht]
  exact ω.hamiltonianCurvature_cylindrical (fun t x ↦ c * H t x) z x

/-! ### The integrated curvature over the plane -/

/-- The band `ε t ∈ (-1/2, 1/2]` of the cylinder, over one period of the angular coordinate. The
end lift maps it bijectively onto `ℂ ∖ {0}`. -/
private noncomputable def endStrip (p : PSSPlane) : Set (ℝ × ℝ) :=
  univ ×ˢ ((p.endSign * ·) ⁻¹' Ioc (-1 / 2) (1 / 2))

/-- The pullback of the perturbation along the end lift in real coordinates, evaluated on a
tangent vector `v`, is its component `TauCeti.Floer.PSSPlane.endComponent` along `v` in the end
coordinates. -/
private theorem perturbationPullback_realChart_cylindricalEndLift {X : Type*} (p : PSSPlane)
    (H : ℝ → X → ℝ) (v : ℝ × ℝ) :
    perturbationPullback (realChart p.cylindricalEndLift)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) v =
      p.endComponent H (Complex.equivRealProdCLM.symm v) := by
  funext z x
  have hz : Complex.equivRealProdCLM.symm z = ⟨z.1, z.2⟩ := Complex.ext (by simp) (by simp)
  rw [perturbationPullback_realChart _
    (p.hasDerivAt_cylindricalEndLift _).differentiableAt.hasDerivAt, endComponent_def, hz]

/-- The pullback of the perturbation along the end lift in real coordinates has vanishing `ds`
component. -/
private theorem perturbationPullback_realChart_cylindricalEndLift_stdComplexLineReal {X : Type*}
    (p : PSSPlane) (H : ℝ → X → ℝ) :
    perturbationPullback (realChart p.cylindricalEndLift)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        stdComplexLineReal =
      fun _ _ ↦ 0 := by
  rw [perturbationPullback_realChart_cylindricalEndLift, equivRealProdCLM_symm_stdComplexLineReal,
    endComponent_one]

/-- The pullback of the perturbation along the end lift in real coordinates has `dt` component
`β(ε s - 1) H(t)`. -/
private theorem perturbationPullback_realChart_cylindricalEndLift_stdComplexLineImag {X : Type*}
    (p : PSSPlane) {H : ℝ → X → ℝ} (hH : Periodic H 1) :
    perturbationPullback (realChart p.cylindricalEndLift)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        stdComplexLineImag =
      fun z x ↦ smoothTransition (p.endSign * z.1 - 1) * H z.2 x := by
  rw [perturbationPullback_realChart_cylindricalEndLift, equivRealProdCLM_symm_stdComplexLineImag,
    endComponent_I hH]

/-- The end lift is injective on the band `endStrip p`, whose angular coordinate ranges over one
period. -/
private theorem injOn_realChart (p : PSSPlane) :
    InjOn (realChart p.cylindricalEndLift) (endStrip p) := by
  intro a ha b hb hab
  have hπ := Real.pi_pos
  replace ha : -1 / 2 < p.endSign * a.2 ∧ p.endSign * a.2 ≤ 1 / 2 := ha.2
  replace hb : -1 / 2 < p.endSign * b.2 ∧ p.endSign * b.2 ≤ 1 / 2 := hb.2
  have him (z : ℝ × ℝ) :
      (((2 * π * p.endSign : ℝ) : ℂ) * Complex.equivRealProdCLM.symm z).im =
        2 * π * (p.endSign * z.2) := by
    simp only [Complex.im_ofReal_mul, Complex.equivRealProdCLM_symm_apply_im]
    ring
  rw [realChart_apply, realChart_apply] at hab
  have hab' := Complex.equivRealProdCLM.injective hab
  rw [cylindricalEndLift_def, cylindricalEndLift_def] at hab'
  have h := Complex.exp_inj_of_neg_pi_lt_of_le_pi (by rw [him]; nlinarith)
    (by rw [him]; nlinarith) (by rw [him]; nlinarith) (by rw [him]; nlinarith) hab'
  have hc : ((2 * π * p.endSign : ℝ) : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, p.endSign_ne_zero]
  exact Complex.equivRealProdCLM.symm.injective (mul_left_cancel₀ hc h)

/-- Every point of the plane other than the pole is the image of a point of the band. -/
private theorem mem_image_realChart {z : ℝ × ℝ} (hz : Complex.equivRealProdCLM.symm z ≠ 0) :
    z ∈ realChart p.cylindricalEndLift '' endStrip p := by
  have hπ := Real.pi_pos
  refine ⟨Complex.equivRealProdCLM (p.endCoord (Complex.equivRealProdCLM.symm z)),
    ⟨mem_univ _, ?_⟩, ?_⟩
  · have h₁ := Complex.neg_pi_lt_arg (Complex.equivRealProdCLM.symm z)
    have h₂ := Complex.arg_le_pi (Complex.equivRealProdCLM.symm z)
    simp only [mem_preimage, Complex.equivRealProdCLM_apply, mem_Ioc, endSign_mul_im_endCoord]
    rw [lt_div_iff₀ (by positivity), div_le_iff₀ (by positivity)]
    constructor <;> linarith
  · rw [realChart_apply, ContinuousLinearEquiv.symm_apply_apply, p.cylindricalEndLift_endCoord hz,
      ContinuousLinearEquiv.apply_symm_apply]

/-- **The integrated curvature of the perturbation of a PSS plane.** Let `K` be the perturbation
of a PSS plane given by a period-one `C¹` Hamiltonian `H` on a manifold `M` with a two-form `ω`,
with `|H| ≤ B`, and write its components in the global coordinate `z = s + i t` of `ℂ` as
`K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)`. Then for every map `u` into `M`, the integral of
`|R_K(z, u(z))|` over the plane is at most `B`. -/
theorem lintegral_enorm_hamiltonianCurvature_pssPlanePerturbation_le (ω : SmoothTwoForm I M)
    (hH : Periodic H 1) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {B : ℝ}
    (hB : ∀ t x, |H t x| ≤ B) (u : ℝ × ℝ → M) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ENNReal.ofReal B := by
  set φ := realChart p.cylindricalEndLift
  set f : ℝ × ℝ → ENNReal := fun z ↦ ‖ω.hamiltonianCurvature
    (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)‖ₑ
  set N : Set (ℝ × ℝ) := {Complex.equivRealProdCLM 0}
  have hN : volume N = 0 := by
    rw [Measure.volume_eq_prod]
    exact (Set.toFinite N).measure_zero _
  have hT : MeasurableSet ((p.endSign * ·) ⁻¹' Ioc (-1 / 2 : ℝ) (1 / 2)) :=
    measurableSet_Ioc.preimage (measurable_const.mul measurable_id)
  have hmeas : MeasurableSet (endStrip p) := MeasurableSet.univ.prod hT
  have hψ : ∀ s, 0 ≤ deriv smoothTransition s := fun _ ↦ smoothTransition.monotone.deriv_nonneg
  -- Off the pole, every point is the image of a point of the band.
  have hcover : univ ⊆ φ '' endStrip p ∪ N := by
    intro z _
    by_cases h₀ : Complex.equivRealProdCLM.symm z = 0
    · exact Or.inr ((Complex.equivRealProdCLM.apply_symm_apply z).symm.trans (congrArg _ h₀))
    · exact Or.inl (mem_image_realChart h₀)
  calc ∫⁻ z, f z ≤ ∫⁻ z in φ '' endStrip p ∪ N, f z := by
        rw [← setLIntegral_univ]
        exact lintegral_mono_set hcover
    _ ≤ (∫⁻ z in φ '' endStrip p, f z) + ∫⁻ z in N, f z := lintegral_union_le _ _ _
    _ = ∫⁻ z in endStrip p, ‖ω.hamiltonianCurvature (p.endComponent H 1)
          (p.endComponent H Complex.I) z (u (φ z))‖ₑ := by
        -- The curvature is a two-form, and pulled back along the end lift it is the curvature in
        -- end coordinates.
        rw [setLIntegral_measure_zero _ _ hN, add_zero,
          ω.lintegral_enorm_hamiltonianCurvature_image hmeas (injOn_realChart p)
            (fun z _ ↦ (contDiff_realChart (n := 2) p.contDiff_cylindricalEndLift).contDiffAt)
            (fun z _ ↦ differentiableAt_perturbation_domain hH hHs _ _ 1)
            (fun z _ ↦ differentiableAt_perturbation_domain hH hHs _ _ Complex.I)
            (fun z _ ↦ mdifferentiableAt_perturbation_target hH hHs _ _ 1)
            (fun z _ ↦ mdifferentiableAt_perturbation_target hH hHs _ _ Complex.I),
          perturbationPullback_realChart_cylindricalEndLift,
          perturbationPullback_realChart_cylindricalEndLift,
          equivRealProdCLM_symm_stdComplexLineReal, equivRealProdCLM_symm_stdComplexLineImag]
    _ ≤ ∫⁻ z in endStrip p,
          ENNReal.ofReal (deriv smoothTransition (p.endSign * z.1 - 1)) * ENNReal.ofReal B := by
        refine setLIntegral_mono' hmeas fun z _ ↦ ?_
        -- In end coordinates the curvature is `ε β'(ε s - 1) H(t)`.
        have hHt : DifferentiableAt ℝ (fun t ↦ H t (u (φ z))) z.2 :=
          ((hHs.comp (f := fun t : ℝ ↦ (t, u (φ z))) (contMDiff_id.prodMk contMDiff_const)
            ).contDiff.differentiable one_ne_zero) z.2
        rw [ω.hamiltonianCurvature_pssPlaneEndComponent hH z hHt, Real.enorm_eq_ofReal_abs]
        simpa [abs_mul, abs_of_nonneg (hψ _), ← ENNReal.ofReal_mul (hψ _)] using
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hB z.2 (u (φ z))) (hψ _))
    _ = ∫⁻ s, ENNReal.ofReal (deriv smoothTransition (p.endSign * s - 1)) *
          ENNReal.ofReal B := by
        have hm : Measurable fun z : ℝ × ℝ ↦
            ENNReal.ofReal (deriv smoothTransition (p.endSign * z.1 - 1)) * ENNReal.ofReal B :=
          (ENNReal.continuous_ofReal.comp
            (((smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl).comp
              (by fun_prop))).measurable.mul_const _
        have hvol : volume ((p.endSign * ·) ⁻¹' Ioc (-1 / 2 : ℝ) (1 / 2)) = 1 := by
          rw [Real.volume_preimage_mul_left p.endSign_ne_zero, Real.volume_Ioc, abs_inv,
            abs_endSign]
          norm_num
        rw [Measure.volume_eq_prod, endStrip, setLIntegral_prod _ hm.aemeasurable]
        simp only [setLIntegral_const, hvol, mul_one, Measure.restrict_univ]
    _ = ENNReal.ofReal B := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
          smoothTransition.lintegral_ofReal_deriv_mul_sub 1 p.endSign_ne_zero, abs_endSign,
          inv_one, ENNReal.ofReal_one, one_mul]

/-! ### The energy identity on the discs of the plane -/

/-- The end lift preserves orientation in real coordinates: its Jacobian determinant is
positive. -/
private theorem det_fderiv_realChart_pos (p : PSSPlane) (z : ℝ × ℝ) :
    0 < (fderiv ℝ (realChart p.cylindricalEndLift) z).det := by
  -- The derivative is multiplication by the complex number `φ'`, whose real determinant is
  -- `|φ'|²`.
  rw [(TauCeti.Complex.hasFDerivAt_realChart (p.hasDerivAt_cylindricalEndLift _)).fderiv]
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_apply,
    Complex.normSq_pos, p.cylindricalEndLift_ne_zero]

/-- The band `ε t ∈ (-1/2, 1/2]` and the closed interval `[-1/2, 1/2]` differ by a null set. -/
private theorem preimage_endSign_mul_ae_eq (p : PSSPlane) :
    ((p.endSign * ·) ⁻¹' Ioc (-1 / 2 : ℝ) (1 / 2) : Set ℝ) =ᵐ[volume] Icc (-1 / 2 : ℝ) (1 / 2) := by
  cases p
  · simpa using (Ioc_ae_eq_Icc (a := (-1 / 2 : ℝ)) (b := 1 / 2))
  · have h : ((PSSPlane.negative.endSign * ·) ⁻¹' Ioc (-1 / 2 : ℝ) (1 / 2) : Set ℝ) =
        Ico (-1 / 2) (1 / 2) := by
      ext t
      simp only [endSign_negative, mem_preimage, mem_Ioc, mem_Ico]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    rw [h]
    exact Ico_ae_eq_Icc

/-- The part `1 ≤ ε s ≤ R` of the end, over one period `ε t ∈ (-1/2, 1/2]` of the angular
coordinate. -/
private noncomputable def endPiece (p : PSSPlane) (R : ℝ) : Set (ℝ × ℝ) :=
  ((p.endSign * ·) ⁻¹' Icc 1 R) ×ˢ ((p.endSign * ·) ⁻¹' Ioc (-1 / 2) (1 / 2))

/-- The part `1 ≤ ε s ≤ R` of the end is measurable. -/
private theorem measurableSet_endPiece (p : PSSPlane) (R : ℝ) : MeasurableSet (endPiece p R) :=
  (measurableSet_Icc.preimage (measurable_const.mul measurable_id)).prod
    (measurableSet_Ioc.preimage (measurable_const.mul measurable_id))

/-- The part `1 ≤ ε s ≤ R` of the end lies in the compact rectangle where `ε s ∈ [1, R]` and
`ε t ∈ [-1/2, 1/2]`. -/
private theorem endPiece_subset_isCompact (p : PSSPlane) (R : ℝ) :
    ∃ K : Set (ℝ × ℝ), IsCompact K ∧ endPiece p R ⊆ K := by
  have hK (S : Set ℝ) (hS : IsCompact S) : IsCompact ((p.endSign * ·) ⁻¹' S) :=
    (Homeomorph.mulLeft₀ p.endSign p.endSign_ne_zero).isCompact_preimage.2 hS
  exact ⟨_, (hK _ isCompact_Icc).prod (hK _ isCompact_Icc),
    prod_mono subset_rfl (preimage_mono Ioc_subset_Icc_self)⟩

/-- The end lift sends a point with longitudinal coordinate `s` to a point of norm
`exp (2π ε s)`. -/
private theorem norm_symm_realChart (p : PSSPlane) (w : ℝ × ℝ) :
    ‖Complex.equivRealProdCLM.symm (realChart p.cylindricalEndLift w)‖ =
      Real.exp (2 * π * (p.endSign * w.1)) := by
  rw [realChart_apply, ContinuousLinearEquiv.symm_apply_apply, norm_cylindricalEndLift,
    Complex.equivRealProdCLM_symm_apply_re]

/-- The image of the part `1 ≤ ε s ≤ R` of the end lies in the disc `‖w‖ ≤ exp (2πR)`. -/
private theorem image_endPiece_subset_closedBall (p : PSSPlane) (R : ℝ) :
    realChart p.cylindricalEndLift '' endPiece p R ⊆
      Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R)) := by
  rintro _ ⟨w, hw, rfl⟩
  have hw' : p.endSign * w.1 ≤ R := hw.1.2
  simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right, norm_symm_realChart]
  exact Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])

/-- The points of the disc `‖w‖ ≤ exp (2πR)` off the image of the part `1 ≤ ε s ≤ R` of the end
lie in the open pole disc `‖w‖ < exp (2π)`. -/
private theorem norm_lt_of_mem_sdiff_image_endPiece {R : ℝ} {z : ℝ × ℝ}
    (hz : z ∈ Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R)) \
      realChart p.cylindricalEndLift '' endPiece p R) :
    ‖Complex.equivRealProdCLM.symm z‖ < Real.exp (2 * π) := by
  by_contra! h
  have h₀ : Complex.equivRealProdCLM.symm z ≠ 0 := fun h₀ ↦ by
    rw [h₀, norm_zero] at h
    exact (Real.exp_pos _).not_ge h
  obtain ⟨w, hw, rfl⟩ := mem_image_realChart (p := p) h₀
  have hD := hz.1
  simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right, norm_symm_realChart] at hD h
  rw [Real.exp_le_exp] at hD h
  exact hz.2 ⟨w, ⟨⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩, hw.2⟩, rfl⟩

/-- The image of the part `1 ≤ ε s ≤ R` of the end is measurable. -/
private theorem measurableSet_image_endPiece (p : PSSPlane) (R : ℝ) :
    MeasurableSet (realChart p.cylindricalEndLift '' endPiece p R) :=
  measurable_image_of_fderivWithin (measurableSet_endPiece p R)
    (fun w _ ↦ ((contDiff_realChart (n := 1) p.contDiff_cylindricalEndLift).differentiable
      one_ne_zero w).hasFDerivAt.hasFDerivWithinAt)
    ((injOn_realChart p).mono (prod_mono (subset_univ _) subset_rfl))

/-- By periodicity, the integral of `H(t)` along the circle `s = c` of the end may be taken over
`t ∈ [0, 1]` instead of `[-1/2, 1/2]`. -/
private theorem intervalIntegral_realChart {X : Type*} {H : ℝ → X → ℝ} (hH : Periodic H 1)
    (u : ℝ × ℝ → X) (c : ℝ) :
    ∫ t in (-1 / 2 : ℝ)..1 / 2, H t (u (realChart p.cylindricalEndLift (c, t))) =
      ∫ t in (0 : ℝ)..1, H t (u (Complex.equivRealProdCLM
        (p.cylindricalEndLift (↑c + ↑t * Complex.I)))) := by
  have hper : Periodic (fun t : ℝ ↦ H t (u (Complex.equivRealProdCLM
      (p.cylindricalEndLift (↑c + ↑t * Complex.I))))) 1 := fun t ↦ by
    simp only [p.periodic_cylindricalEndLift c t, hH t]
  have h := hper.intervalIntegral_add_eq (-1 / 2) 0
  norm_num at h
  simp only [realChart_apply, Complex.equivRealProdCLM_symm_apply]
  convert h using 1 <;> norm_num

/-- In end coordinates, the curvature of the perturbation along `u`, times the Jacobian of the end
lift, is `ε β'(ε s - 1) H(t)`. -/
private theorem det_mul_hamiltonianCurvature_realChart (ω : SmoothTwoForm I M) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) (w : ℝ × ℝ) (x : M) :
    (fderiv ℝ (realChart p.cylindricalEndLift) w).det * ω.hamiltonianCurvature
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        (realChart p.cylindricalEndLift w) x =
      p.endSign * deriv smoothTransition (p.endSign * w.1 - 1) * H w.2 x := by
  have hHt : DifferentiableAt ℝ (fun t ↦ H t x) w.2 :=
    ((hHs.contMDiffAt.comp (f := fun t : ℝ ↦ (t, x)) w.2
      (contMDiffAt_id.prodMk contMDiffAt_const)).contDiffAt).differentiableAt one_ne_zero
  rw [← ω.hamiltonianCurvature_perturbationPullback
      (contDiff_realChart (n := 2) p.contDiff_cylindricalEndLift).contDiffAt
      (differentiableAt_perturbation_domain hH hHs _ _ 1)
      (differentiableAt_perturbation_domain hH hHs _ _ Complex.I)
      (mdifferentiableAt_perturbation_target hH hHs _ _ 1)
      (mdifferentiableAt_perturbation_target hH hHs _ _ Complex.I),
    perturbationPullback_realChart_cylindricalEndLift,
    perturbationPullback_realChart_cylindricalEndLift,
    equivRealProdCLM_symm_stdComplexLineReal, equivRealProdCLM_symm_stdComplexLineImag,
    ω.hamiltonianCurvature_pssPlaneEndComponent hH w hHt]

/-- Over the image of the part `1 ≤ ε s ≤ R` of the end, the curvature along a continuous map is
integrable: in end coordinates, times the Jacobian, it is the continuous function
`ε β'(ε s - 1) H(t, u)`. -/
private theorem integrableOn_image_endPiece_hamiltonianCurvature (ω : SmoothTwoForm I M)
    (hH : Periodic H 1) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H))
    {u : ℝ × ℝ → M} (hu : Continuous u) (R : ℝ) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
      (realChart p.cylindricalEndLift '' endPiece p R) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have hφ : ContDiff ℝ 1 (realChart p.cylindricalEndLift) :=
    contDiff_realChart p.contDiff_cylindricalEndLift
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    (measurableSet_endPiece p R)
    (fun w _ ↦ (hφ.differentiable one_ne_zero w).hasFDerivAt.hasFDerivWithinAt)
    ((injOn_realChart p).mono (prod_mono (subset_univ _) subset_rfl))]
  obtain ⟨K, hK, hPK⟩ := endPiece_subset_isCompact p R
  have hc : Continuous fun w : ℝ × ℝ ↦ p.endSign * deriv smoothTransition (p.endSign * w.1 - 1) *
      H w.2 (u (realChart p.cylindricalEndLift w)) :=
    (continuous_const.mul (((smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl).comp
      (by fun_prop))).mul (hHs.continuous.comp (continuous_snd.prodMk (hu.comp hφ.continuous)))
  refine ((hc.continuousOn.integrableOn_compact hK).mono_set hPK).congr_fun (fun w _ ↦ ?_)
    (measurableSet_endPiece p R)
  simp only [smul_eq_mul, abs_of_pos (det_fderiv_realChart_pos p w),
    det_mul_hamiltonianCurvature_realChart ω hH hHs]

variable [FiniteDimensional ℝ E]

/-- **The energy identity on a rectangle in end coordinates, for a manifold target.** For the
datum `β(ε s - 1) H(t) dt` of a PSS plane in its end coordinates and a `C¹` map `f`, the energy
over `[a, b] × [-1/2, 1/2]` is the symplectic area, plus the integrals of `β(ε s - 1) H(t)` over
the side `s = b` minus the side `s = a`, minus the integrated curvature. -/
private theorem IsNondegenerate.integral_floerEnergyDensity_endComponent {ω : SmoothTwoForm I M}
    (hω : ω.IsNondegenerate) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H))
    {f : ℝ × ℝ → M} (hf : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 f) {a b : ℝ} (hab : a ≤ b)
    (hE : IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0)
      (fun z x ↦ smoothTransition (p.endSign * z.1 - 1) * H z.2 x) f)
      (Icc ((a, -1 / 2) : ℝ × ℝ) (b, 1 / 2)))
    (hR : IntegrableOn (fun w ↦ ω.hamiltonianCurvature (fun _ _ ↦ 0)
      (fun z x ↦ smoothTransition (p.endSign * z.1 - 1) * H z.2 x) w (f w))
      (Icc ((a, -1 / 2) : ℝ × ℝ) (b, 1 / 2))) :
    ∫ w in Icc ((a, -1 / 2) : ℝ × ℝ) (b, 1 / 2), ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun z x ↦ smoothTransition (p.endSign * z.1 - 1) * H z.2 x) f w =
      (∫ w in Icc ((a, -1 / 2) : ℝ × ℝ) (b, 1 / 2),
          (SmoothBundleForm.eval₂ ω (f w) (mfderiv 𝓘(ℝ, ℝ × ℝ) I f w stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I f w stdComplexLineImag) : ℝ)) +
        ((∫ t in (-1 / 2 : ℝ)..1 / 2, smoothTransition (p.endSign * b - 1) * H t (f (b, t))) -
          ∫ t in (-1 / 2 : ℝ)..1 / 2, smoothTransition (p.endSign * a - 1) * H t (f (a, t))) -
        ∫ w in Icc ((a, -1 / 2) : ℝ × ℝ) (b, 1 / 2), ω.hamiltonianCurvature (fun _ _ ↦ 0)
          (fun z x ↦ smoothTransition (p.endSign * z.1 - 1) * H z.2 x) w (f w) := by
  have hβ : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1
      (fun q : (ℝ × ℝ) × M ↦ smoothTransition (p.endSign * q.1.1 - 1)) :=
    ((smoothTransition.contDiff.comp (f := fun z : ℝ × ℝ ↦ p.endSign * z.1 - 1)
      (by fun_prop)).contMDiff).comp contMDiff_fst
  have hH' : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (fun q : (ℝ × ℝ) × M ↦ H q.1.2 q.2) :=
    hHs.comp ((contDiff_snd.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
  have hK : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1
      (uncurry fun (z : ℝ × ℝ) (x : M) ↦ smoothTransition (p.endSign * z.1 - 1) * H z.2 x) :=
    hβ.smul hH'
  rw [hω.integral_floerEnergyDensity isOpen_univ hf.contMDiffOn contMDiffOn_const
    hK.contMDiffOn
    (Prod.mk_le_mk.2 ⟨hab, by norm_num⟩ : ((a, -1 / 2) : ℝ × ℝ) ≤ (b, 1 / 2)) (subset_univ _)
    hE hR]
  simp only [intervalIntegral.integral_zero]
  ring

/-- **The energy identity over a rectangle of the end, for a manifold target.** Over the image in
the plane of a rectangle `[a, b] × {t | ε t ∈ (-1/2, 1/2]}` of the cylinder, over which the energy
density and the curvature are integrable, the Floer energy is the symplectic area, plus the
integrals of the Hamiltonian term `β(ε s - 1) H(t)` over the circle `s = b` minus the circle
`s = a`, minus the integrated curvature. -/
private theorem IsNondegenerate.integral_floerEnergyDensity_image_realChart
    {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {u : ℝ × ℝ → M}
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) {a b : ℝ} (hab : a ≤ b)
    (hE : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      (realChart p.cylindricalEndLift '' (Icc a b ×ˢ ((p.endSign * ·) ⁻¹' Ioc (-1 / 2) (1 / 2)))))
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
      (realChart p.cylindricalEndLift '' (Icc a b ×ˢ ((p.endSign * ·) ⁻¹' Ioc (-1 / 2) (1 / 2))))) :
    ∫ z in realChart p.cylindricalEndLift ''
        (Icc a b ×ˢ ((p.endSign * ·) ⁻¹' Ioc (-1 / 2) (1 / 2))), ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      (∫ z in realChart p.cylindricalEndLift ''
          (Icc a b ×ˢ ((p.endSign * ·) ⁻¹' Ioc (-1 / 2) (1 / 2))),
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ((∫ t in (-1 / 2 : ℝ)..1 / 2, smoothTransition (p.endSign * b - 1) *
            H t (u (realChart p.cylindricalEndLift (b, t)))) -
          ∫ t in (-1 / 2 : ℝ)..1 / 2, smoothTransition (p.endSign * a - 1) *
            H t (u (realChart p.cylindricalEndLift (a, t)))) -
        ∫ z in realChart p.cylindricalEndLift ''
          (Icc a b ×ˢ ((p.endSign * ·) ⁻¹' Ioc (-1 / 2) (1 / 2))), ω.hamiltonianCurvature
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  set φ := realChart p.cylindricalEndLift
  set s : Set (ℝ × ℝ) := Icc a b ×ˢ ((p.endSign * ·) ⁻¹' Ioc (-1 / 2 : ℝ) (1 / 2))
  have hmeas : MeasurableSet s :=
    measurableSet_Icc.prod (measurableSet_Ioc.preimage (measurable_const.mul measurable_id))
  have hinj : InjOn φ s :=
    (injOn_realChart p).mono (prod_mono (subset_univ _) subset_rfl)
  have hφ : ContDiff ℝ 2 φ := contDiff_realChart p.contDiff_cylindricalEndLift
  have hφd (w : ℝ × ℝ) : DifferentiableAt ℝ φ w := hφ.differentiable (by norm_num) w
  have hdet (w : ℝ × ℝ) : 0 ≤ (fderiv ℝ φ w).det :=
    (det_fderiv_realChart_pos p w).le
  have hud (w : ℝ × ℝ) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (φ w) :=
    (hu (φ w)).mdifferentiableAt one_ne_zero
  have htgt (w : ℝ × ℝ) (v : ℂ) := mdifferentiableAt_perturbation_target (p := p) hH hHs
    (Complex.equivRealProdCLM.symm (φ w)) (u (φ w)) v
  have hds :=
    perturbationPullback_realChart_cylindricalEndLift_stdComplexLineReal p H
  have hdt :=
    perturbationPullback_realChart_cylindricalEndLift_stdComplexLineImag p hH
  -- The band and the closed rectangle differ by a null set.
  have hae : s =ᵐ[volume] Icc ((a, -1 / 2) : ℝ × ℝ) (b, 1 / 2) := by
    rw [Icc_prod_eq, Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq (ae_eq_refl _) (preimage_endSign_mul_ae_eq p)
  -- Integrability over the image transfers to the pulled-back densities on the rectangle.
  have hint {g g' : ℝ × ℝ → ℝ} (hg : IntegrableOn g (φ '' s))
      (hg' : ∀ w, g' w = (fderiv ℝ φ w).det * g (φ w)) :
      IntegrableOn g' (Icc ((a, -1 / 2) : ℝ × ℝ) (b, 1 / 2)) := by
    refine (((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hmeas
      (fun w _ ↦ (hφd w).hasFDerivAt.hasFDerivWithinAt) hinj g).1 hg).congr_fun
      (fun w _ ↦ ?_) hmeas).congr_set_ae hae.symm
    rw [abs_of_nonneg (hdet w), smul_eq_mul, hg']
  have hE' := hint hE fun w ↦ by
    rw [← ω.floerEnergyDensity_perturbationPullback (hφd w) (hud w) (htgt w 1) (htgt w _), hds, hdt]
  have hR' := hint hR fun w ↦ by
    rw [← ω.hamiltonianCurvature_perturbationPullback hφ.contDiffAt
      (differentiableAt_perturbation_domain hH hHs _ _ 1)
      (differentiableAt_perturbation_domain hH hHs _ _ Complex.I) (htgt w 1) (htgt w _), hds,
      hdt]
  -- Change variables to the end coordinates, in each of the three integrals.
  have harea := ω.integral_floerEnergyDensity_image (Ks := fun _ _ ↦ 0) (Kt := fun _ _ ↦ 0)
    hmeas hinj (fun w _ ↦ hφd w) (fun w _ ↦ hdet w) (fun w _ ↦ hud w)
    (fun _ _ ↦ mdifferentiableAt_const) (fun _ _ ↦ mdifferentiableAt_const)
  have h₀ (v : ℝ × ℝ) : perturbationPullback φ (fun (_ : ℝ × ℝ) (_ : M) ↦ (0 : ℝ))
      (fun _ _ ↦ 0) v = fun _ _ ↦ 0 := by
    funext w x
    simp [perturbationPullback_apply]
  simp only [h₀, floerEnergyDensity_zero] at harea
  rw [harea, ω.integral_floerEnergyDensity_image hmeas hinj (fun w _ ↦ hφd w)
      (fun w _ ↦ hdet w) (fun w _ ↦ hud w) (fun w _ ↦ htgt w 1) (fun w _ ↦ htgt w _),
    ω.integral_hamiltonianCurvature_image hmeas hinj (fun w _ ↦ hφ.contDiffAt)
      (fun w _ ↦ hdet w)
      (fun w _ ↦ differentiableAt_perturbation_domain hH hHs _ _ 1)
      (fun w _ ↦ differentiableAt_perturbation_domain hH hHs _ _ Complex.I)
      (fun w _ ↦ htgt w 1) (fun w _ ↦ htgt w _),
    hds, hdt]
  simp only [setIntegral_congr_set hae]
  exact hω.integral_floerEnergyDensity_endComponent hHs (hu.comp (hφ.of_le one_le_two).contMDiff)
    hab hE' hR'

/-- **The energy identity on the annulus of the end, for a manifold target.** Over the image of
the part `1 ≤ ε s ≤ R` of the end, over which the energy density and the curvature are integrable,
the Floer energy is the symplectic area, plus `ε β(R - 1)` times the integral of `H(t)` along the
circle `s = ε R`, minus the integrated curvature. -/
private theorem IsNondegenerate.integral_floerEnergyDensity_image_endPiece
    {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {u : ℝ × ℝ → M}
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) {R : ℝ} (hR : 1 ≤ R)
    (hE : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      (realChart p.cylindricalEndLift '' endPiece p R))
    (hRK : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
      (realChart p.cylindricalEndLift '' endPiece p R)) :
    ∫ z in realChart p.cylindricalEndLift '' endPiece p R, ω.floerEnergyDensity
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      (∫ z in realChart p.cylindricalEndLift '' endPiece p R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        p.endSign * smoothTransition (R - 1) * (∫ t in (-1 / 2 : ℝ)..1 / 2,
          H t (u (realChart p.cylindricalEndLift (p.endSign * R, t)))) -
        ∫ z in realChart p.cylindricalEndLift '' endPiece p R, ω.hamiltonianCurvature
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  cases p
  · have hpiece : endPiece .positive R =
        Icc 1 R ×ˢ ((PSSPlane.positive.endSign * ·) ⁻¹' Ioc (-1 / 2) (1 / 2)) := by
      ext ⟨s, t⟩
      simp [endPiece]
    rw [hpiece] at hE hRK ⊢
    rw [hω.integral_floerEnergyDensity_image_realChart hH hHs hu hR hE hRK]
    simp only [endSign_positive, one_mul, sub_self, smoothTransition.zero, zero_mul,
      intervalIntegral.integral_zero, sub_zero, intervalIntegral.integral_const_mul]
  · have hpiece : endPiece .negative R =
        Icc (-R) (-1) ×ˢ ((PSSPlane.negative.endSign * ·) ⁻¹' Ioc (-1 / 2) (1 / 2)) := by
      ext ⟨s, t⟩
      simp only [endPiece, endSign_negative, mem_prod, mem_preimage, mem_Icc,
        and_congr_left_iff]
      exact fun _ ↦ ⟨fun h ↦ ⟨by linarith, by linarith⟩, fun h ↦ ⟨by linarith, by linarith⟩⟩
    rw [hpiece] at hE hRK ⊢
    rw [hω.integral_floerEnergyDensity_image_realChart hH hHs hu (by linarith) hE hRK]
    simp only [endSign_negative, neg_mul, one_mul, neg_neg, sub_self, smoothTransition.zero,
      zero_mul, intervalIntegral.integral_zero, zero_sub, intervalIntegral.integral_const_mul]

omit [FiniteDimensional ℝ E] in
/-- At points of the open pole disc `‖w‖ < exp (2π)`, where the perturbation vanishes nearby, the
Floer energy density is the symplectic area density and the curvature vanishes. -/
private theorem floerEnergyDensity_eq_and_hamiltonianCurvature_eq_zero_of_norm_lt
    (ω : SmoothTwoForm I M) (u : ℝ × ℝ → M) {z : ℝ × ℝ}
    (hz : ‖Complex.equivRealProdCLM.symm z‖ < Real.exp (2 * π)) :
    ω.floerEnergyDensity (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) ∧
    ω.hamiltonianCurvature (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) = 0 := by
  have hK0 : ∀ᶠ z' in 𝓝 z, ∀ x : M, p.perturbation H (Complex.equivRealProdCLM.symm z') x = 0 :=
    (Complex.equivRealProdCLM.symm.continuous.tendsto z).eventually
      (eventually_perturbation_eq_zero (p := p) (H := H) hz)
  have hK (v : ℂ) : (fun x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x v) = 0 :=
    funext fun x ↦ by simp [hK0.self_of_nhds x]
  refine ⟨?_, ?_⟩
  · simp [floerEnergyDensity_def, hK 1, hK Complex.I, Pi.zero_def, hamiltonianVectorField_const]
  · rw [ω.hamiltonianCurvature_congr_of_eventuallyEq (Ks' := fun _ _ ↦ 0) (Kt' := fun _ _ ↦ 0)
      (hK0.mono fun z' hz' ↦ funext fun y ↦ by simp [hz'])
      (hK0.mono fun z' hz' ↦ funext fun y ↦ by simp [hz']), hamiltonianCurvature_zero]

/-- **The energy identity on discs of a PSS plane, for a manifold target.** Let `K` be the
perturbation of a PSS plane given by a period-one `C¹` Hamiltonian `H` on a finite-dimensional
manifold with a nondegenerate two-form `ω`, with components `K_s(z) = K(z)(1)` and
`K_t(z) = K(z)(i)` in the global coordinate `z = s + i t` of `ℂ`, and let `u` be a `C¹` map. For
`R ≥ 1`, over the disc `D_R = {‖w‖ ≤ exp (2πR)}`, bounded by the circle `ε s = R` of the end, the
Floer energy of `u` is its symplectic area, plus `ε β(R - 1)` times the integral of `H(t)` along the
boundary circle, minus the integrated curvature:

`∫_{D_R} E = ∫_{D_R} u^*ω + ε β(R - 1) ∫₀¹ H(t, u(φ(ε R + i t))) dt - ∫_{D_R} R_K(u)`.

Here `φ` is the end lift `z ↦ exp (2π ε z)`, `ε` is the sign of the end and
`β = smoothTransition`, so `β(R - 1) = 1` for `R ≥ 2`. No integrability hypotheses are needed, and
closedness of `ω` is not used. -/
theorem IsNondegenerate.integral_floerEnergyDensity_pssPlanePerturbation_closedBall
    {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {u : ℝ × ℝ → M}
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) {R : ℝ} (hR : 1 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R)),
        ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R)),
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        p.endSign * smoothTransition (R - 1) * (∫ t in (0 : ℝ)..1,
          H t (u (Complex.equivRealProdCLM
            (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R)),
          ω.hamiltonianCurvature
            (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  -- The disc `D` is the image `A` of the part `1 ≤ ε s ≤ R` of the end, together with points of
  -- the pole disc, where the perturbation vanishes.
  set D := Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall (0 : ℂ) (Real.exp (2 * π * R))
  set A := realChart p.cylindricalEndLift '' endPiece p R
  have hDc : IsCompact D :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_closedBall _ _)
  have hAD : A ⊆ D := image_endPiece_subset_closedBall p R
  have hDAm : MeasurableSet (D \ A) :=
    hDc.isClosed.measurableSet.diff (measurableSet_image_endPiece p R)
  have hpole {z : ℝ × ℝ} (hz : z ∈ D \ A) :=
    floerEnergyDensity_eq_and_hamiltonianCurvature_eq_zero_of_norm_lt (p := p) (H := H) ω u
      (norm_lt_of_mem_sdiff_image_endPiece hz)
  -- The curvature is integrable over the end piece and vanishes on the rest of the disc.
  have hRD : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) D :=
    (integrableOn_image_endPiece_hamiltonianCurvature ω hH hHs hu.continuous
      R).of_forall_sdiff_eq_zero hDc.isClosed.measurableSet fun z hz ↦ (hpole hz).2
  -- The area density is continuous, hence integrable over the compact disc.
  have harea : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) D := by
    have h := (ω.isSmoothForm.of_le (by simp)).continuous_apply_mfderiv hu stdComplexLineReal
      stdComplexLineImag
    simp only [← SmoothBundleForm.eval₂_apply] at h
    exact h.continuousOn.integrableOn_compact hDc
  -- By the pointwise identity `E = u^* ω + d(K(u)) - R_K(u)`, the energy density is integrable.
  have hED : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u) D := by
    have hd (v : ℂ) (e : ℝ × ℝ) : IntegrableOn (fun z ↦ fderiv ℝ
        (fun w ↦ p.perturbation H (Complex.equivRealProdCLM.symm w) (u w) v) z e) D := by
      have hK : ContDiff ℝ 1
          (fun w ↦ p.perturbation H (Complex.equivRealProdCLM.symm w) (u w) v) :=
        contMDiff_iff_contDiff.mp ((contMDiff_uncurry_perturbation hH hHs v).comp
          (contMDiff_id.prodMk hu))
      exact ((hK.continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousOn
        |>.integrableOn_compact hDc
    refine ((harea.add ((hd Complex.I stdComplexLineReal).sub (hd 1 stdComplexLineImag))).sub
      hRD).congr_fun (fun z _ ↦ ?_) hDc.isClosed.measurableSet
    rw [hω.floerEnergyDensity_eq ((hu z).mdifferentiableAt one_ne_zero)
      ((contMDiff_uncurry_perturbation hH hHs 1 _).mdifferentiableAt one_ne_zero)
      ((contMDiff_uncurry_perturbation hH hHs Complex.I _).mdifferentiableAt one_ne_zero)]
    rfl
  have hsplit (f : ℝ × ℝ → ℝ) (hf : IntegrableOn f D) :
      ∫ z in D, f z = (∫ z in A, f z) + ∫ z in D \ A, f z := by
    conv_lhs => rw [← union_sdiff_cancel hAD]
    exact setIntegral_union disjoint_sdiff_right hDAm (hf.mono_set hAD) (hf.mono_set sdiff_subset)
  rw [hsplit _ hED, hsplit _ harea, hsplit _ hRD,
    setIntegral_congr_fun hDAm fun z hz ↦ (hpole hz).1,
    setIntegral_eq_zero_of_forall_eq_zero fun z hz ↦ (hpole hz).2,
    hω.integral_floerEnergyDensity_image_endPiece hH hHs hu hR (hED.mono_set hAD)
      (hRD.mono_set hAD), intervalIntegral_realChart hH]
  ring

/-- **The topological energy of a solution bounds its integrated curvature.** If `u` solves the
Floer equation `(du - X_K)^{0,1} = 0` for the perturbation of a PSS plane on the disc
`D_R = {‖w‖ ≤ exp (2πR)}`, `R ≥ 1`, with almost complex structures `J z` tamed by the two-form,
then the integral of `R_K(u)` over `D_R` is at most the symplectic area of `u` over `D_R` plus
`ε β(R - 1)` times the integral of `H(t)` along the boundary circle. -/
theorem IsNondegenerate.integral_hamiltonianCurvature_pssPlanePerturbation_closedBall_le
    {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {u : ℝ × ℝ → M}
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) {R : ℝ} (hR : 1 ≤ R)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R)),
      (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R)),
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R)),
        ω.hamiltonianCurvature
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) ≤
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R)),
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        p.endSign * smoothTransition (R - 1) * (∫ t in (0 : ℝ)..1,
          H t (u (Complex.equivRealProdCLM
            (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))))) := by
  have h := hω.integral_floerEnergyDensity_pssPlanePerturbation_closedBall (p := p) hH hHs hu hR
  have hE₀ := setIntegral_nonneg (μ := volume)
    ((Metric.isClosed_closedBall.preimage Complex.equivRealProdCLM.symm.continuous).measurableSet)
    fun z hz ↦ floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  linarith

end SmoothTwoForm

namespace SymplecticForm

open Floer Floer.PSSPlane

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {p : PSSPlane} {H : ℝ → V → ℝ}

/-- **The integrated curvature of the perturbation of a PSS plane.** For a period-one `C¹`
Hamiltonian `H` on a symplectic vector space with `|H| ≤ B`, and every map `u` into it, the
integral of `|R_K(z, u(z))|` over the plane is at most `B`. This is the vector-space case of
`TauCeti.SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_pssPlanePerturbation_le`. -/
theorem lintegral_enorm_hamiltonianCurvature_pssPlanePerturbation_le (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {B : ℝ} (hB : ∀ t x, |H t x| ≤ B)
    (u : ℝ × ℝ → V) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ENNReal.ofReal B := by
  simpa using ω.constSmooth.lintegral_enorm_hamiltonianCurvature_pssPlanePerturbation_le hH
    (contMDiff_prod_modelWithCornersSelf_iff.2 hHs.contMDiff) hB u

/-- **The energy identity on discs of a PSS plane.** Let `K` be the perturbation of a PSS plane
given by a period-one `C¹` Hamiltonian `H`, with components `K_s(z) = K(z)(1)` and
`K_t(z) = K(z)(i)` in the global coordinate `z = s + i t` of `ℂ`, and let `u` be a `C¹` map. For
`R ≥ 1`, over the disc `D_R = {‖w‖ ≤ exp (2πR)}`, bounded by the circle `ε s = R` of the end, the
Floer energy of `u` is its symplectic area, plus `ε β(R - 1)` times the integral of `H(t)` along the
boundary circle, minus the integrated curvature:

`∫_{D_R} E = ∫_{D_R} u^*ω + ε β(R - 1) ∫₀¹ H(t, u(φ(ε R + i t))) dt - ∫_{D_R} R_K(u)`.

Here `φ` is the end lift `z ↦ exp (2π ε z)`, `ε` is the sign of the end and
`β = smoothTransition`, so `β(R - 1) = 1` for `R ≥ 2`. This is the vector-space case of
`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pssPlanePerturbation_closedBall`.
-/
theorem integral_floerEnergyDensity_pssPlanePerturbation_closedBall (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u)
    {R : ℝ} (hR : 1 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R)),
        ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R)),
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) +
        p.endSign * smoothTransition (R - 1) * (∫ t in (0 : ℝ)..1,
          H t (u (Complex.equivRealProdCLM
            (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' Metric.closedBall 0 (Real.exp (2 * π * R)),
          ω.hamiltonianCurvature
            (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  simpa only [floerEnergyDensity_constSmooth, hamiltonianCurvature_constSmooth,
    eval₂_constSmooth_mfderiv_stdComplexLine] using
    (isNondegenerate_constSmooth ω).integral_floerEnergyDensity_pssPlanePerturbation_closedBall
      (p := p) hH (contMDiff_prod_modelWithCornersSelf_iff.2 hHs.contMDiff) hu.contMDiff hR

/-- **The curvature vanishes far out on the end.** On the part `ε s > 2` of the end of a PSS
plane, where its perturbation is `H(t) dt`, the curvature of the perturbation vanishes. -/
theorem hamiltonianCurvature_pssPlanePerturbation_eq_zero_of_two_lt (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {z : ℝ × ℝ}
    (hz : 2 < p.endSign * (p.endCoord (Complex.equivRealProdCLM.symm z)).re) (x : V) :
    ω.hamiltonianCurvature (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z x = 0 := by
  have h₀ : Complex.equivRealProdCLM.symm z ≠ 0 := fun h ↦ by
    rw [h, endCoord_zero, Complex.zero_re, mul_zero] at hz
    norm_num at hz
  obtain ⟨w, -, rfl⟩ := SmoothTwoForm.mem_image_realChart (p := p) h₀
  have hH' := contMDiff_prod_modelWithCornersSelf_iff.2 hHs.contMDiff
  have hw : 2 < p.endSign * w.1 := by
    rwa [realChart_apply, ContinuousLinearEquiv.symm_apply_apply, re_endCoord_cylindricalEndLift,
      Complex.equivRealProdCLM_symm_apply_re] at hz
  -- In end coordinates the curvature vanishes, and the end lift is a local diffeomorphism.
  have key := ω.hamiltonianCurvature_perturbationPullback (φ := realChart p.cylindricalEndLift)
    (Ks := fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    (w := w) (x := x) (contDiff_realChart (n := 2) p.contDiff_cylindricalEndLift).contDiffAt
    (PSSPlane.differentiableAt_perturbation_domain hH hH' _ _ 1)
    (PSSPlane.differentiableAt_perturbation_domain hH hH' _ _ Complex.I)
  rw [SmoothTwoForm.perturbationPullback_realChart_cylindricalEndLift,
    SmoothTwoForm.perturbationPullback_realChart_cylindricalEndLift,
    equivRealProdCLM_symm_stdComplexLineReal,
    equivRealProdCLM_symm_stdComplexLineImag,
    ← hamiltonianCurvature_constSmooth ω (p.endComponent H 1) (p.endComponent H Complex.I) w x,
    ω.constSmooth.hamiltonianCurvature_pssPlaneEndComponent_eq_zero hH (Or.inr hw)] at key
  exact (mul_eq_zero.1 key.symm).resolve_left (SmoothTwoForm.det_fderiv_realChart_pos p w).ne'

end SymplecticForm

end TauCeti
