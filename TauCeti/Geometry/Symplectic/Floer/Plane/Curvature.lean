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

/-!
# The curvature of the perturbation on a PSS plane

The energy identity `TauCeti.SymplecticForm.integral_floerEnergyDensity` on a rectangle expresses
the integrated Floer energy density of a map `u` as its symplectic area, plus a boundary term in
`K(u)`, minus the integrated curvature `∫ R_K(z, u(z))` of the perturbation `K`, where
`R_K = ∂_s K_t - ∂_t K_s - {K_s, K_t}`. This file bounds the curvature term: it computes the
curvature of the perturbation `TauCeti.Floer.PSSPlane.perturbation` of a PSS plane, built from a
period-one Hamiltonian `H` on a manifold `M` with a smooth two-form `ω`, such as a closed
symplectic manifold, and bounds its integral over the whole plane.

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
tangent vectors `1` and `i`. A symplectic vector space is the case of the constant form
`TauCeti.SymplecticForm.constSmooth`, through which the vector-space bound
`TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_pssPlanePerturbation_le` is derived.

## Main results

* `TauCeti.SmoothTwoForm.hamiltonianCurvature_pssPlaneEndComponent`: the curvature in end
  coordinates is `ε β'(ε s - 1) H(t)`.
* `TauCeti.SmoothTwoForm.hamiltonianCurvature_pssPlaneEndComponent_eq_zero`: it vanishes outside
  the collar `1 ≤ ε s ≤ 2`.
* `TauCeti.SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_pssPlanePerturbation_le`: the
  integrated curvature of the perturbation along any map is at most a bound for the
  Hamiltonian.

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

omit [IsManifold I ⊤ M] in
/-- The components of the perturbation in real coordinates are differentiable in the domain
point. -/
private theorem differentiableAt_perturbation_domain (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) (z : ℝ × ℝ) (x : M) (v : ℂ) :
    DifferentiableAt ℝ (fun z' ↦ p.perturbation H (Complex.equivRealProdCLM.symm z') x v) z := by
  have hK : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1 (fun w ↦ p.perturbation H w x) :=
    (contMDiff_perturbation (p := p) hH hHs).comp (contMDiff_id.prodMk contMDiff_const)
  exact ((hK.contDiff.differentiable one_ne_zero _).comp z
    Complex.equivRealProdCLM.symm.differentiableAt).clm_apply (differentiableAt_const v)

omit [IsManifold I ⊤ M] in
/-- The components of the perturbation are differentiable in the target point. -/
private theorem mdifferentiableAt_perturbation_target (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) (w : ℂ) (x : M) (v : ℂ) :
    MDifferentiableAt I 𝓘(ℝ) (fun y ↦ p.perturbation H w y v) x :=
  ((((contMDiff_perturbation (p := p) hH hHs).comp
    (contMDiff_const.prodMk contMDiff_id)).contMDiffAt (x := x)).clm_apply
      contMDiffAt_const).mdifferentiableAt one_ne_zero

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

end SymplecticForm

end TauCeti
