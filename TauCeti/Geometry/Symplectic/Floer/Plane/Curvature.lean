/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Plane.Basic
public import TauCeti.Geometry.Symplectic.Floer.Pullback
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.RingTheory.Complex

/-!
# The curvature of the perturbation on a PSS plane

The energy identity `TauCeti.SymplecticForm.integral_floerEnergyDensity` bounds the energy of a
solution of `(du - X_K)^{0,1} = 0` by its topological energy plus the integrated curvature
`∫ |R_K(z, u(z))|` of the perturbation `K`, where
`R_K = ∂_s K_t - ∂_t K_s - {K_s, K_t}`. This file computes the curvature of the perturbation
`TauCeti.Floer.PSSPlane.perturbation` of a PSS plane, built from a period-one Hamiltonian `H` on a
symplectic vector space `V`, and bounds its integral over the whole plane.

In the end coordinates `(s, t)` of the plane the perturbation is the continuation datum
`β(ε s - 1) H(t) dt` (`TauCeti.Floer.PSSPlane.endComponent_I`), so its curvature there is
`ε β'(ε s - 1) H(t)` (`SymplecticForm.hamiltonianCurvature_endComponent`). It vanishes outside the
collar `1 ≤ ε s ≤ 2` (`SymplecticForm.hamiltonianCurvature_endComponent_eq_zero`). The curvature is
a two-form (`SymplecticForm.hamiltonianCurvature_perturbationPullback`), and the end lift
`z ↦ exp (2π ε z)` maps a band of height one bijectively onto `ℂ ∖ {0}`. Since `β' ≥ 0` has total
integral `1`, if `|H| ≤ B` then

`∫_ℂ |R_K(z, u(z))| dz ≤ B`

for every map `u : ℂ → V`, measurable or not
(`SymplecticForm.lintegral_enorm_hamiltonianCurvature_perturbation_le`). Here the curvature is
computed in the global coordinate `z = s + i t` of `ℂ`, in which the `ds` and `dt` components of
`K` are its values on the tangent vectors `1` and `i`.

## Main results

* `TauCeti.SymplecticForm.hamiltonianCurvature_endComponent`: the curvature in end coordinates is
  `ε β'(ε s - 1) H(t)`.
* `TauCeti.SymplecticForm.hamiltonianCurvature_endComponent_eq_zero`: it vanishes outside the
  collar `1 ≤ ε s ≤ 2`.
* `TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_perturbation_le`: the integrated
  curvature of the perturbation along any map is at most a bound for the Hamiltonian.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the resulting energy bounds.
-/

public section

open Set Real Function MeasureTheory Filter Manifold
open scoped Topology

namespace TauCeti

namespace SymplecticForm

open Floer Floer.PSSPlane

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {p : PSSPlane} {H : ℝ → V → ℝ}

/-- **The curvature in end coordinates.** In the end coordinates `(s, t)` of a PSS plane, the
curvature of the perturbation `β(ε s - 1) H(t) dt` is `ε β'(ε s - 1) H(t)`. -/
theorem hamiltonianCurvature_endComponent (ω : SymplecticForm V) (hH : Periodic H 1)
    (z : ℝ × ℝ) {x : V} (hHx : DifferentiableAt ℝ (fun t ↦ H t x) z.2) :
    ω.hamiltonianCurvature (p.endComponent H 1) (p.endComponent H Complex.I) z x =
      p.endSign * deriv smoothTransition (p.endSign * z.1 - 1) * H z.2 x := by
  have hβ : HasDerivAt (fun s ↦ smoothTransition (p.endSign * s - 1))
      (deriv smoothTransition (p.endSign * z.1 - 1) * p.endSign) z.1 :=
    (((hasDerivAt_id z.1).const_mul p.endSign).sub_const 1).smoothTransition.congr_deriv
      (by simp)
  have h := ω.hamiltonianCurvature_continuation hβ.differentiableAt hHx
  beta_reduce at h
  rw [endComponent_one hH, endComponent_I hH, h, hβ.deriv]
  ring

/-- **The curvature is supported in the collar.** On the parts `ε s < 1` and `ε s > 2` of the end
of a PSS plane, the curvature of the perturbation in end coordinates vanishes. -/
theorem hamiltonianCurvature_endComponent_eq_zero (ω : SymplecticForm V) (hH : Periodic H 1)
    {z : ℝ × ℝ} (hz : p.endSign * z.1 < 1 ∨ 2 < p.endSign * z.1) (x : V) :
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
  rw [endComponent_one hH, ω.hamiltonianCurvature_congr_of_eventuallyEq (EventuallyEq.refl _ _) ht]
  exact ω.hamiltonianCurvature_cylindrical (fun t x ↦ c * H t x) z x

/-! ### The integrated curvature over the plane -/

/-- The end lift of a PSS plane, in the real coordinates `ℝ × ℝ ≃ ℂ`. -/
private noncomputable def endChart (p : PSSPlane) (z : ℝ × ℝ) : ℝ × ℝ :=
  Complex.equivRealProdCLM (p.endLift (Complex.equivRealProdCLM.symm z))

/-- The band `ε t ∈ (-1/2, 1/2]` of the cylinder, over one period of the angular coordinate. The
end lift maps it bijectively onto `ℂ ∖ {0}`. -/
private noncomputable def endStrip (p : PSSPlane) : Set (ℝ × ℝ) :=
  univ ×ˢ ((p.endSign * ·) ⁻¹' Ioc (-1 / 2) (1 / 2))

/-- The derivative of the end chart is multiplication by the derivative of the end lift. -/
private theorem hasFDerivAt_endChart (p : PSSPlane) (z : ℝ × ℝ) :
    HasFDerivAt (endChart p)
      ((Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ).comp
        (((ContinuousLinearMap.toSpanSingleton ℂ
          (deriv p.endLift (Complex.equivRealProdCLM.symm z))).restrictScalars ℝ).comp
            (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ))) z := by
  have h := (p.hasDerivAt_endLift
    (Complex.equivRealProdCLM.symm z)).differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  exact Complex.equivRealProdCLM.hasFDerivAt.comp z
    (h.comp z Complex.equivRealProdCLM.symm.hasFDerivAt)

private theorem fderiv_endChart_apply (p : PSSPlane) (z v : ℝ × ℝ) :
    fderiv ℝ (endChart p) z v = Complex.equivRealProdCLM
      (deriv p.endLift (Complex.equivRealProdCLM.symm z) * Complex.equivRealProdCLM.symm v) := by
  rw [(hasFDerivAt_endChart p z).fderiv]
  simp [mul_comm]

private theorem contDiff_endChart (p : PSSPlane) : ContDiff ℝ 2 (endChart p) :=
  Complex.equivRealProdCLM.contDiff.comp
    ((p.contDiff_endLift.restrict_scalars ℝ).comp Complex.equivRealProdCLM.symm.contDiff)

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The pullback of the perturbation along the end chart, evaluated on a tangent vector `v`, is
its component `TauCeti.Floer.PSSPlane.endComponent` along `v` in the end coordinates. -/
private theorem perturbationPullback_endChart (p : PSSPlane) (H : ℝ → V → ℝ) (v : ℝ × ℝ) :
    perturbationPullback (endChart p)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) v =
      p.endComponent H (Complex.equivRealProdCLM.symm v) := by
  -- A real-linear functional `L` on `ℂ` satisfies `L w = Re w · L 1 + Im w · L i`.
  have hL (L : ℂ →L[ℝ] ℝ) (w : ℂ) :
      (Complex.equivRealProdCLM w).1 * L 1 + (Complex.equivRealProdCLM w).2 * L Complex.I =
        L w := by
    have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by simp
    conv_rhs => rw [hw]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    simp
  funext z x
  rw [perturbationPullback_apply, fderiv_endChart_apply, endChart,
    ContinuousLinearEquiv.symm_apply_apply, hL, endComponent_def]
  rfl

omit [FiniteDimensional ℝ V] in
/-- The perturbation is `C¹` jointly in the domain point and the target point. -/
private theorem contDiff_perturbation_prod (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) :
    ContDiff ℝ 1 (fun q : ℂ × V ↦ p.perturbation H q.1 q.2) := by
  have hHs' : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, V)) 𝓘(ℝ, ℝ) 1 (uncurry H) := by
    have h := hHs.contMDiff
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
    exact h
  have h := contMDiff_perturbation (p := p) (n := 1) hH hHs'
  have h' : ContMDiff 𝓘(ℝ, ℂ × V) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun q : ℂ × V ↦ p.perturbation H q.1 q.2) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact h
  exact h'.contDiff

omit [FiniteDimensional ℝ V] in
/-- The components of the perturbation in real coordinates are differentiable in the domain
point. -/
private theorem differentiableAt_perturbation_domain (hH : Periodic H 1)
    (hHs : ContDiff ℝ 1 (uncurry H)) (z : ℝ × ℝ) (x : V) (v : ℂ) :
    DifferentiableAt ℝ (fun z' ↦ p.perturbation H (Complex.equivRealProdCLM.symm z') x v) z := by
  have hK := (contDiff_perturbation_prod (p := p) hH hHs).differentiable one_ne_zero
  exact ((hK _).comp z (Complex.equivRealProdCLM.symm.differentiableAt.prodMk
    (differentiableAt_const x))).clm_apply (differentiableAt_const v)

omit [FiniteDimensional ℝ V] in
/-- The components of the perturbation are differentiable in the target point. -/
private theorem differentiableAt_perturbation_target (hH : Periodic H 1)
    (hHs : ContDiff ℝ 1 (uncurry H)) (w : ℂ) (x : V) (v : ℂ) :
    DifferentiableAt ℝ (fun y ↦ p.perturbation H w y v) x := by
  have hK := (contDiff_perturbation_prod (p := p) hH hHs).differentiable one_ne_zero
  exact ((hK _).comp x ((differentiableAt_const w).prodMk differentiableAt_id)).clm_apply
    (differentiableAt_const v)

/-- The curvature of the perturbation at the image of a cylinder point, multiplied by the
Jacobian of the end chart, is the curvature `ε β'(ε s - 1) H(t)` in end coordinates. -/
private theorem det_mul_hamiltonianCurvature_endChart (ω : SymplecticForm V) (hH : Periodic H 1)
    (hHs : ContDiff ℝ 1 (uncurry H)) (z : ℝ × ℝ) (x : V) :
    (fderiv ℝ (endChart p) z).det * ω.hamiltonianCurvature
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        (endChart p z) x =
      p.endSign * deriv smoothTransition (p.endSign * z.1 - 1) * H z.2 x := by
  have hHt : DifferentiableAt ℝ (fun t ↦ H t x) z.2 :=
    (hHs.comp (contDiff_id.prodMk contDiff_const)).differentiable one_ne_zero z.2
  rw [← ω.hamiltonianCurvature_perturbationPullback (contDiff_endChart p).contDiffAt
    (differentiableAt_perturbation_domain hH hHs _ x 1)
    (differentiableAt_perturbation_domain hH hHs _ x Complex.I)
    (differentiableAt_perturbation_target hH hHs _ x 1)
    (differentiableAt_perturbation_target hH hHs _ x Complex.I),
    perturbationPullback_endChart, perturbationPullback_endChart,
    equivRealProdCLM_symm_stdComplexLineReal, equivRealProdCLM_symm_stdComplexLineImag,
    ω.hamiltonianCurvature_endComponent hH z hHt]

/-- The end chart is injective on the band `endStrip p`, whose angular coordinate ranges over one
period. -/
private theorem injOn_endChart (p : PSSPlane) : InjOn (endChart p) (endStrip p) := by
  intro a ha b hb hab
  have hπ := Real.pi_pos
  replace ha : -1 / 2 < p.endSign * a.2 ∧ p.endSign * a.2 ≤ 1 / 2 := ha.2
  replace hb : -1 / 2 < p.endSign * b.2 ∧ p.endSign * b.2 ≤ 1 / 2 := hb.2
  have him (z : ℝ × ℝ) :
      (((2 * π * p.endSign : ℝ) : ℂ) * Complex.equivRealProdCLM.symm z).im =
        2 * π * (p.endSign * z.2) := by
    simp only [Complex.im_ofReal_mul, Complex.equivRealProdCLM_symm_apply_im]
    ring
  have hab' := Complex.equivRealProdCLM.injective hab
  rw [endLift_def, endLift_def] at hab'
  have h := Complex.exp_inj_of_neg_pi_lt_of_le_pi (by rw [him]; nlinarith)
    (by rw [him]; nlinarith) (by rw [him]; nlinarith) (by rw [him]; nlinarith) hab'
  have hc : ((2 * π * p.endSign : ℝ) : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, p.endSign_ne_zero]
  exact Complex.equivRealProdCLM.symm.injective (mul_left_cancel₀ hc h)

/-- Every point of the plane other than the pole is the image of a point of the band. -/
private theorem mem_image_endChart {z : ℝ × ℝ} (hz : Complex.equivRealProdCLM.symm z ≠ 0) :
    z ∈ endChart p '' endStrip p := by
  have hπ := Real.pi_pos
  refine ⟨Complex.equivRealProdCLM (p.endCoord (Complex.equivRealProdCLM.symm z)),
    ⟨mem_univ _, ?_⟩, ?_⟩
  · have h₁ := Complex.neg_pi_lt_arg (Complex.equivRealProdCLM.symm z)
    have h₂ := Complex.arg_le_pi (Complex.equivRealProdCLM.symm z)
    have hε : p.endSign * (p.endCoord (Complex.equivRealProdCLM.symm z)).im =
        Complex.arg (Complex.equivRealProdCLM.symm z) / (2 * π) := by
      rw [im_endCoord, ← mul_assoc, mul_div_assoc', endSign_mul_endSign, one_div_mul_eq_div]
    simp only [mem_preimage, Complex.equivRealProdCLM_apply, mem_Ioc, hε]
    rw [lt_div_iff₀ (by positivity), div_le_iff₀ (by positivity)]
    constructor <;> linarith
  · rw [endChart, ContinuousLinearEquiv.symm_apply_apply, p.endLift_endCoord hz,
      ContinuousLinearEquiv.apply_symm_apply]

/-- The cutoff of the end has total increase one along the end. -/
private theorem lintegral_deriv_smoothTransition_endSign (p : PSSPlane) :
    ∫⁻ s, ENNReal.ofReal (deriv smoothTransition (p.endSign * s - 1)) = 1 := by
  cases p
  · simp only [endSign_positive, one_mul]
    rw [lintegral_sub_right_eq_self (fun s ↦ ENNReal.ofReal (deriv smoothTransition s)) 1,
      ← ofReal_integral_eq_lintegral_ofReal smoothTransition.integrable_deriv
        (ae_of_all _ fun _ ↦ smoothTransition.monotone.deriv_nonneg),
      smoothTransition.integral_deriv, ENNReal.ofReal_one]
  · convert smoothTransition.lintegral_ofReal_mul_deriv (-1) one_pos using 4 with s
    simp only [endSign_negative, one_mul]
    ring_nf

/-- **The integrated curvature of the perturbation of a PSS plane.** Let `K` be the perturbation
of a PSS plane given by a period-one `C¹` Hamiltonian `H` with `|H| ≤ B`, and write its components
in the global coordinate `z = s + i t` of `ℂ` as `K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)`. Then
for every map `u` into the target, the integral of `|R_K(z, u(z))|` over the plane is at most
`B`. -/
theorem lintegral_enorm_hamiltonianCurvature_perturbation_le (ω : SymplecticForm V)
    (hH : Periodic H 1) (hHs : ContDiff ℝ 1 (uncurry H)) {B : ℝ} (hB : ∀ t x, |H t x| ≤ B)
    (u : ℝ × ℝ → V) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ENNReal.ofReal B := by
  set f : ℝ × ℝ → ENNReal := fun z ↦ ‖ω.hamiltonianCurvature
    (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)‖ₑ
  set N : Set (ℝ × ℝ) := {Complex.equivRealProdCLM 0}
  have hN : volume N = 0 := by
    rw [Measure.volume_eq_prod]
    exact (Set.toFinite N).measure_zero _
  -- Lebesgue measure on `ℝ × ℝ` is the product measure, an additive Haar measure.
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have hT : MeasurableSet ((p.endSign * ·) ⁻¹' Ioc (-1 / 2 : ℝ) (1 / 2)) :=
    measurableSet_Ioc.preimage (measurable_const.mul measurable_id)
  have hmeas : MeasurableSet (endStrip p) := MeasurableSet.univ.prod hT
  have hψ : ∀ s, 0 ≤ deriv smoothTransition s := fun _ ↦ smoothTransition.monotone.deriv_nonneg
  -- Off the pole, every point is the image of a point of the band.
  have hcover : univ ⊆ endChart p '' endStrip p ∪ N := by
    intro z _
    by_cases h₀ : Complex.equivRealProdCLM.symm z = 0
    · exact Or.inr ((Complex.equivRealProdCLM.apply_symm_apply z).symm.trans (congrArg _ h₀))
    · exact Or.inl (mem_image_endChart h₀)
  calc ∫⁻ z, f z ≤ ∫⁻ z in endChart p '' endStrip p ∪ N, f z := by
        rw [← setLIntegral_univ]
        exact lintegral_mono_set hcover
    _ ≤ (∫⁻ z in endChart p '' endStrip p, f z) + ∫⁻ z in N, f z := lintegral_union_le _ _ _
    _ = ∫⁻ z in endStrip p, ENNReal.ofReal |(fderiv ℝ (endChart p) z).det| * f (endChart p z) := by
        rw [setLIntegral_measure_zero _ _ hN, add_zero,
          lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hmeas
            (fun z _ ↦ (hasFDerivAt_endChart p z).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
            (injOn_endChart p)]
    _ ≤ ∫⁻ z in endStrip p,
          ENNReal.ofReal (deriv smoothTransition (p.endSign * z.1 - 1)) * ENNReal.ofReal B := by
        refine setLIntegral_mono' hmeas fun z _ ↦ ?_
        -- The curvature is a two-form, and in end coordinates it is `ε β'(ε s - 1) H(t)`.
        rw [← Real.enorm_eq_ofReal_abs, ← enorm_mul,
          det_mul_hamiltonianCurvature_endChart ω hH hHs z, Real.enorm_eq_ofReal_abs, abs_mul,
          abs_mul, abs_endSign, abs_of_nonneg (hψ _), one_mul, ← ENNReal.ofReal_mul (hψ _)]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hB _ _) (hψ _))
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
          lintegral_deriv_smoothTransition_endSign, one_mul]

end SymplecticForm

end TauCeti
