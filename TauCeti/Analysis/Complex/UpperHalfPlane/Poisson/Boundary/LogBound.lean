/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.Boundary.Function
public import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley
public import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim
import TauCeti.Analysis.Complex.Radial.Jensen
import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.Boundary.Uniqueness

/-!
# The logarithmic bound for bounded holomorphic functions on the half-plane

Let `F` be holomorphic and bounded on the upper half-plane `ℂ₊`, with boundary function
`F* = TauCeti.upperHalfPlaneBoundaryFun F`. Then `log |F*|` is integrable for the Poisson measure
`Π = dx / (1 + x ^ 2)` (`TauCeti.integrable_log_norm_upperHalfPlaneBoundaryFun`), and at every
`z ∈ ℂ₊` with `F z ≠ 0`,
`log |F(z)| ≤ P[log |F*|](z) = ∫ P(z, x) log |F*(x)| dx`
(`TauCeti.log_norm_le_integral_upperHalfPlanePoissonKernel_mul_log_norm`,
`TauCeti.log_norm_le_re_upperHalfPlanePoissonIntegralFun`).

With Lean's convention `log 0 = 0`, the integrability holds for every bounded holomorphic `F`; for
`F ≢ 0` it is the statement `log |F*| ∈ L¹(Π)` (uniqueness,
`TauCeti.eqOn_zero_of_upperHalfPlaneBoundaryFun_eq_zero`, shows that then `F* ≠ 0` almost
everywhere). The bound is stated where `F z ≠ 0`; at a zero of `F` its left side is `-∞`.

The proof transports Jensen's inequality for radial limits,
`TauCeti.log_norm_le_circleAverage_log_norm_of_tendsto_circleMap`, through the Cayley transform.
The inverse Cayley transform carries the radius of the disc ending at `ζ = (x - i)/(x + i)` into
every cone at `x` (`TauCeti.tendsto_I_mul_one_add_div_one_sub_nontangentialFilter`), so the radial
limits of the transported function exist at almost every angle
(`TauCeti.ae_tendsto_circleMap_upperHalfPlaneBoundaryFun`). The substitution
`θ = π + 2 arctan x`, under which `e^{iθ} = (x - i)/(x + i)` and `dθ = 2 dx / (1 + x ^ 2)`, turns
the circle average into the Poisson integral at `i`
(`TauCeti.circleAverage_comp_inverseCayleyCoord`). The affine maps `z ↦ a + b z`, `b > 0`, move
the pole `i` to any `z ∈ ℂ₊`: they preserve nontangential approach
(`TauCeti.tendsto_add_mul_nontangentialFilter`), hence boundary functions
(`TauCeti.upperHalfPlaneBoundaryFun_comp_add_mul_ae_eq`).

## References

* J. B. Garnett, *Bounded Analytic Functions*, revised 1st ed., Springer (2007), Chapter II.
-/

public section

noncomputable section

open Complex MeasureTheory Filter Metric Set Topology
open Real (circleAverage circleAverage_def two_pi_pos)
open scoped Real
open UpperHalfPlane (upperHalfPlaneSet)

namespace TauCeti

/-! ### Affine changes of variable -/

/-- **Affine maps preserve nontangential approach.** For `b > 0`, `z ↦ a + b z` maps nontangential
approach to `x` into nontangential approach, with the same aperture, to `a + b x`. -/
theorem tendsto_add_mul_nontangentialFilter (a : ℝ) {b : ℝ} (hb : 0 < b) (α x : ℝ) :
    Tendsto (fun z : ℂ ↦ (a : ℂ) + b * z) (nontangentialFilter α x)
      (nontangentialFilter α (a + b * x)) := by
  rw [nontangentialFilter_def, nontangentialFilter_def]
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have hc : Continuous fun z : ℂ ↦ (a : ℂ) + b * z := by fun_prop
    have := (hc.tendsto (x : ℂ)).mono_left (nhdsWithin_le_nhds (s := nontangentialCone α ⊤ x))
    simpa using this
  · filter_upwards [self_mem_nhdsWithin] with z hz
    obtain ⟨hz0, hzα, -⟩ := mem_nontangentialCone.1 hz
    have him : ((a : ℂ) + b * z).im = b * z.im := by simp
    have hre : ((a : ℂ) + b * z).re - (a + b * x) = b * (z.re - x) := by simp; ring
    refine mem_nontangentialCone.2 ⟨?_, ?_, ENNReal.ofReal_lt_top⟩
    · rw [him]
      positivity
    · rw [him, hre, abs_mul, abs_of_pos hb]
      nlinarith

variable {F : ℂ → ℂ} {S : ℝ}

/-- **Boundary functions under affine maps.** If `F` is holomorphic and bounded on `ℂ₊` and
`b > 0`, then the boundary function of `w ↦ F(a + b w)` is `x ↦ F*(a + b x)` almost everywhere. -/
theorem upperHalfPlaneBoundaryFun_comp_add_mul_ae_eq (hF : DifferentiableOn ℂ F upperHalfPlaneSet)
    (hS : ∀ z ∈ upperHalfPlaneSet, ‖F z‖ ≤ S) (a : ℝ) {b : ℝ} (hb : 0 < b) :
    upperHalfPlaneBoundaryFun (fun w ↦ F ((a : ℂ) + b * w)) =ᵐ[volume]
      fun x ↦ upperHalfPlaneBoundaryFun F (a + b * x) := by
  set N := {y : ℝ | ¬ ∀ α : ℝ, Tendsto F (nontangentialFilter α y)
    (𝓝 (upperHalfPlaneBoundaryFun F y))}
  have hN : volume N = 0 := ae_tendsto_nontangentialFilter_upperHalfPlaneBoundaryFun hF hS
  have hN' : volume ((fun y ↦ (y - a) / b) '' N) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (by fun_prop) hN
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun x hx ↦ ?_) hN'
  refine ⟨a + b * x, fun hgood ↦ hx ?_, by
    change (a + b * x - a) / b = x
    rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hb.ne']⟩
  have hlim := (hgood 1).comp (tendsto_add_mul_nontangentialFilter a hb 1 x)
  exact upperHalfPlaneBoundaryFun_eq_of_tendsto le_rfl hlim

/-! ### The Cayley transform of the boundary -/

/-- The angle `θ = π + 2 arctan x` of the boundary Cayley point `(x - i)/(x + i) = e^{iθ}`. -/
private def cayleyAngle (x : ℝ) : ℝ := π + 2 * Real.arctan x

private theorem hasDerivAt_cayleyAngle (x : ℝ) :
    HasDerivAt cayleyAngle (2 * (1 + x ^ 2)⁻¹) x := by
  unfold cayleyAngle
  simpa [one_div] using ((Real.hasDerivAt_arctan x).const_mul 2).const_add π

private theorem image_cayleyAngle : cayleyAngle '' univ = Ioo 0 (2 * π) := by
  rw [image_univ]
  ext θ
  constructor
  · rintro ⟨x, rfl⟩
    have h1 := Real.neg_pi_div_two_lt_arctan x
    have h2 := Real.arctan_lt_pi_div_two x
    exact ⟨by simp only [cayleyAngle]; linarith, by simp only [cayleyAngle]; linarith⟩
  · rintro ⟨h0, h2π⟩
    refine ⟨Real.tan ((θ - π) / 2), ?_⟩
    rw [cayleyAngle, Real.arctan_tan (by linarith) (by linarith)]
    ring

private theorem injective_cayleyAngle : Function.Injective cayleyAngle := fun x y h ↦ by
  simp only [cayleyAngle] at h
  exact Real.arctan_injective (by linarith)

private theorem inverseCayleyCoord_circleMap_cayleyAngle (x : ℝ) :
    inverseCayleyCoord (circleMap 0 1 (cayleyAngle x)) = x := by
  rw [circleMap_zero, ofReal_one, one_mul, cayleyAngle, exp_pi_add_two_mul_arctan_mul_I,
    inverseCayleyCoord_cayley, ofReal_re]

/-- **The Cayley change of variables.** For `h : ℝ → ℝ`, the circle average of
`h ∘ inverseCayleyCoord` over the unit circle is the Poisson integral `∫ P(i, x) h(x) dx` at `i`. -/
theorem circleAverage_comp_inverseCayleyCoord (h : ℝ → ℝ) :
    circleAverage (fun w ↦ h (inverseCayleyCoord w)) 0 1 =
      ∫ x, upperHalfPlanePoissonKernel I x * h x := by
  have himg := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ ↦ (hasDerivAt_cayleyAngle x).hasDerivWithinAt) injective_cayleyAngle.injOn
    (fun θ ↦ h (inverseCayleyCoord (circleMap 0 1 θ)))
  rw [image_cayleyAngle, Measure.restrict_univ] at himg
  rw [circleAverage_def, intervalIntegral.integral_of_le two_pi_pos.le,
    integral_Ioc_eq_integral_Ioo, himg, smul_eq_mul, ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  simp only [inverseCayleyCoord_circleMap_cayleyAngle, smul_eq_mul, upperHalfPlanePoissonKernel_I]
  rw [abs_of_pos (by positivity)]
  field_simp

/-- **Integrability under the Cayley change of variables.** If `h ∘ inverseCayleyCoord` is
integrable on the unit circle, then `h` is integrable for the Poisson measure `dx / (1 + x ^ 2)`. -/
theorem integrable_upperHalfPlanePoissonMeasure_of_circleIntegrable {h : ℝ → ℝ}
    (hh : CircleIntegrable (fun w ↦ h (inverseCayleyCoord w)) 0 1) :
    Integrable h upperHalfPlanePoissonMeasure := by
  have hIoo : IntegrableOn (fun θ ↦ h (inverseCayleyCoord (circleMap 0 1 θ))) (Ioo 0 (2 * π)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).1 hh).mono_set
      Ioo_subset_Ioc_self
  rw [← image_cayleyAngle, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ ↦ (hasDerivAt_cayleyAngle x).hasDerivWithinAt) injective_cayleyAngle.injOn,
    integrableOn_univ] at hIoo
  rw [integrable_upperHalfPlanePoissonMeasure_iff_integrable_smul]
  refine (hIoo.const_mul (1 / 2)).congr (.of_forall fun x ↦ ?_)
  simp only [inverseCayleyCoord_circleMap_cayleyAngle, smul_eq_mul]
  rw [abs_of_pos (by positivity)]
  ring

/-- **Radial limits of the Cayley transport.** If `F` is holomorphic and bounded on `ℂ₊`, then
for almost every angle `θ`, `F(i (1 + w)/(1 - w))` tends to `F*(x)` as `w = r e^{iθ}` runs along
the radius, `r → 1⁻`, where `x` is the inverse Cayley coordinate of `e^{iθ}`. -/
theorem ae_tendsto_circleMap_upperHalfPlaneBoundaryFun
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) (hS : ∀ z ∈ upperHalfPlaneSet, ‖F z‖ ≤ S) :
    ∀ᵐ θ : ℝ, Tendsto (fun r ↦ F (I * (1 + circleMap 0 r θ) / (1 - circleMap 0 r θ))) (𝓝[<] 1)
      (𝓝 (upperHalfPlaneBoundaryFun F (inverseCayleyCoord (circleMap 0 1 θ)))) := by
  set N := {y : ℝ | ¬ ∀ α : ℝ, Tendsto F (nontangentialFilter α y)
    (𝓝 (upperHalfPlaneBoundaryFun F y))}
  have hN : volume N = 0 := ae_tendsto_nontangentialFilter_upperHalfPlaneBoundaryFun hF hS
  -- the exceptional angles
  set B : Set ℝ := range (fun n : ℤ ↦ n * (2 * π)) ∪
    ⋃ n : ℤ, (fun x ↦ cayleyAngle x + n * (2 * π)) '' N
  have hB : volume B = 0 := by
    refine measure_union_null ((countable_range _).measure_zero volume)
      (measure_iUnion_null fun n ↦ ?_)
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ hN
    exact fun x _ ↦ ((hasDerivAt_cayleyAngle x).add_const _).differentiableAt.differentiableWithinAt
  refine measure_mono_null (fun θ hθ ↦ ?_) hB
  by_contra hθB
  obtain ⟨hθ1, hθN⟩ := not_or.1 hθB
  set w := circleMap 0 1 θ with hw
  have hw1 : w ≠ 1 := by
    rintro h
    rw [hw, circleMap_zero, ofReal_one, one_mul, exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    refine hθ1 ⟨n, ?_⟩
    have := congrArg Complex.im hn
    simp at this
    linarith
  have hwn : ‖w‖ = 1 := by simp [hw]
  set x := inverseCayleyCoord w
  have hζ : ((x : ℂ) - I) / ((x : ℂ) + I) = w := cayley_inverseCayleyCoord hwn hw1
  have hxN : x ∉ N := by
    intro hxN
    have hexp : exp ((cayleyAngle x : ℝ) * I) = exp ((θ : ℝ) * I) := by
      rw [cayleyAngle, exp_pi_add_two_mul_arctan_mul_I, hζ, hw, circleMap_zero, ofReal_one,
        one_mul]
    obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 hexp
    refine hθN (mem_iUnion.2 ⟨-n, x, hxN, ?_⟩)
    have := congrArg Complex.im hn
    simp at this
    push_cast
    linarith
  refine hθ ?_
  simp only [not_not, N, mem_ofPred_eq] at hxN
  have hr : (fun r : ℝ ↦ F (I * (1 + circleMap 0 r θ) / (1 - circleMap 0 r θ))) =
      fun r : ℝ ↦ F (I * (1 + r * (((x : ℂ) - I) / ((x : ℂ) + I))) /
        (1 - r * (((x : ℂ) - I) / ((x : ℂ) + I)))) := by
    funext r
    rw [hζ, hw, circleMap_zero, circleMap_zero, ofReal_one, one_mul]
  change Tendsto (fun r : ℝ ↦ F (I * (1 + circleMap 0 r θ) / (1 - circleMap 0 r θ))) (𝓝[<] 1)
    (𝓝 (upperHalfPlaneBoundaryFun F x))
  rw [hr]
  exact (hxN 1).comp (tendsto_I_mul_one_add_div_one_sub_nontangentialFilter x one_pos)

/-! ### The logarithmic bound -/

/-- The transport of `F` to the unit disc, its bound, and Jensen's data: the circle average of
`log |F*|` along the inverse Cayley coordinate is integrable and bounds `log |F(i)|` when
`F(i) ≠ 0`. -/
private theorem jensen_cayley (hF : DifferentiableOn ℂ F upperHalfPlaneSet)
    (hS : ∀ z ∈ upperHalfPlaneSet, ‖F z‖ ≤ S) :
    CircleIntegrable (fun w ↦ Real.log ‖upperHalfPlaneBoundaryFun F (inverseCayleyCoord w)‖) 0 1 ∧
      (F I ≠ 0 → Real.log ‖F I‖ ≤
        circleAverage (fun w ↦ Real.log ‖upperHalfPlaneBoundaryFun F (inverseCayleyCoord w)‖)
          0 1) := by
  set g : ℂ → ℂ := fun w ↦ F (I * (1 + w) / (1 - w))
  have hmaps := bijOn_I_mul_one_add_div_one_sub_ball.mapsTo
  have hg : DifferentiableOn ℂ g (ball 0 1) := by
    refine hF.comp (fun w hw ↦ ?_) hmaps
    have hw1 : w ≠ 1 := by
      rintro rfl
      simp at hw
    exact (hasDerivAt_I_mul_one_add_div_one_sub hw1).differentiableAt.differentiableWithinAt
  have hgS : ∀ w ∈ ball (0 : ℂ) 1, ‖g w‖ ≤ S := fun w hw ↦ hS _ (hmaps hw)
  have hlim := ae_tendsto_circleMap_upperHalfPlaneBoundaryFun hF hS
  refine ⟨circleIntegrable_log_norm_of_tendsto_circleMap (G := fun w ↦
    upperHalfPlaneBoundaryFun F (inverseCayleyCoord w)) one_pos hg hgS hlim, fun hFI ↦ ?_⟩
  have hg0 : g 0 = F I := by simp [g]
  rw [← hg0] at hFI ⊢
  exact log_norm_le_circleAverage_log_norm_of_tendsto_circleMap (G := fun w ↦
    upperHalfPlaneBoundaryFun F (inverseCayleyCoord w)) one_pos hg hgS hFI hlim

/-- **`log |F*| ∈ L¹(Π)`.** If `F` is holomorphic and bounded on `ℂ₊`, then `log |F*|` is
integrable for the Poisson measure `dx / (1 + x ^ 2)`. (With `log 0 = 0` this needs no hypothesis
`F ≢ 0`.) -/
theorem integrable_log_norm_upperHalfPlaneBoundaryFun
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) (hS : ∀ z ∈ upperHalfPlaneSet, ‖F z‖ ≤ S) :
    Integrable (fun x ↦ Real.log ‖upperHalfPlaneBoundaryFun F x‖) upperHalfPlanePoissonMeasure :=
  integrable_upperHalfPlanePoissonMeasure_of_circleIntegrable (jensen_cayley hF hS).1

/-- The logarithmic bound at the pole `i`. -/
private theorem log_norm_le_integral_I (hF : DifferentiableOn ℂ F upperHalfPlaneSet)
    (hS : ∀ z ∈ upperHalfPlaneSet, ‖F z‖ ≤ S) (hFI : F I ≠ 0) :
    Real.log ‖F I‖ ≤
      ∫ x, upperHalfPlanePoissonKernel I x * Real.log ‖upperHalfPlaneBoundaryFun F x‖ := by
  rw [← circleAverage_comp_inverseCayleyCoord]
  exact (jensen_cayley hF hS).2 hFI

/-- **The logarithmic bound.** If `F` is holomorphic and bounded on `ℂ₊` and `F z ≠ 0` at
`z ∈ ℂ₊`, then `log |F(z)| ≤ ∫ P(z, x) log |F*(x)| dx`. -/
theorem log_norm_le_integral_upperHalfPlanePoissonKernel_mul_log_norm
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) (hS : ∀ z ∈ upperHalfPlaneSet, ‖F z‖ ≤ S)
    {z : ℂ} (hz : z ∈ upperHalfPlaneSet) (hFz : F z ≠ 0) :
    Real.log ‖F z‖ ≤
      ∫ x, upperHalfPlanePoissonKernel z x * Real.log ‖upperHalfPlaneBoundaryFun F x‖ := by
  have hb : 0 < z.im := hz
  set a := z.re
  set b := z.im with hbz
  set H : ℂ → ℂ := fun w ↦ F ((a : ℂ) + b * w)
  have hA : MapsTo (fun w : ℂ ↦ (a : ℂ) + b * w) upperHalfPlaneSet upperHalfPlaneSet :=
    fun w (hw : 0 < w.im) ↦ show 0 < ((a : ℂ) + b * w).im by simpa using mul_pos hb hw
  have hH : DifferentiableOn ℂ H upperHalfPlaneSet :=
    hF.comp (by fun_prop) hA
  have hHS : ∀ w ∈ upperHalfPlaneSet, ‖H w‖ ≤ S := fun w hw ↦ hS _ (hA hw)
  have hzab : (a : ℂ) + b * I = z := by simp [a, b, Complex.re_add_im]
  have hHI : H I = F z := by simp only [H, hzab]
  rw [← hHI] at hFz ⊢
  refine (log_norm_le_integral_I hH hHS hFz).trans_eq ?_
  have hae := upperHalfPlaneBoundaryFun_comp_add_mul_ae_eq hF hS a hb
  rw [integral_congr_ae (hae.mono fun x hx ↦ by simp only [H] at hx ⊢; rw [hx])]
  -- the substitution `y = a + b x`
  set K : ℝ → ℝ := fun y ↦
    upperHalfPlanePoissonKernel z y * Real.log ‖upperHalfPlaneBoundaryFun F y‖
  have hK : ∀ x : ℝ, upperHalfPlanePoissonKernel I x *
      Real.log ‖upperHalfPlaneBoundaryFun F (a + b * x)‖ = b * K (a + b * x) := fun x ↦ by
    simp only [K, ← mul_assoc]
    congr 1
    rw [upperHalfPlanePoissonKernel_I, upperHalfPlanePoissonKernel_eq, normSq_apply]
    simp only [sub_re, ofReal_re, sub_im, ofReal_im, zero_sub]
    rw [show a + b * x - z.re = b * x by simp [a], ← hbz]
    field_simp
    ring
  simp_rw [hK]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun x ↦ K (a + x)) b,
    integral_add_left_eq_self K a, smul_eq_mul, abs_inv, abs_of_pos hb, ← mul_assoc,
    mul_inv_cancel₀ hb.ne', one_mul]

/-- **The logarithmic bound, as a Poisson integral.** If `F` is holomorphic and bounded on `ℂ₊`
and `F z ≠ 0` at `z ∈ ℂ₊`, then `log |F(z)| ≤ Re P[log |F*|](z)`. -/
theorem log_norm_le_re_upperHalfPlanePoissonIntegralFun
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) (hS : ∀ z ∈ upperHalfPlaneSet, ‖F z‖ ≤ S)
    {z : ℂ} (hz : z ∈ upperHalfPlaneSet) (hFz : F z ≠ 0) :
    Real.log ‖F z‖ ≤ (upperHalfPlanePoissonIntegralFun
      (fun x ↦ (Real.log ‖upperHalfPlaneBoundaryFun F x‖ : ℂ)) z).re := by
  have hi : Integrable (fun x ↦ (Real.log ‖upperHalfPlaneBoundaryFun F x‖ : ℂ))
      upperHalfPlanePoissonMeasure :=
    (integrable_log_norm_upperHalfPlaneBoundaryFun hF hS).ofReal
  rw [re_upperHalfPlanePoissonIntegralFun hi]
  simpa using log_norm_le_integral_upperHalfPlanePoissonKernel_mul_log_norm hF hS hz hFz

end TauCeti
