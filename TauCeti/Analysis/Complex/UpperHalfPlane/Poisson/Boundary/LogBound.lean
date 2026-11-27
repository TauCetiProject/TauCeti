/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.Boundary.Function
public import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley
public import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim
import TauCeti.Analysis.Complex.Radial.Jensen
import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.Boundary.Uniqueness
import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.Covariance

/-!
# The logarithmic bound for bounded holomorphic functions on the half-plane

Let `F` be holomorphic and bounded on the upper half-plane `ℂ₊`, with boundary function
`F* = TauCeti.upperHalfPlaneBoundaryFun F`. Then `log |F*|` is integrable for the Poisson measure
`Π = dx / (1 + x ^ 2)`
(`TauCeti.integrable_upperHalfPlanePoissonMeasure_log_norm_upperHalfPlaneBoundaryFun`), and at
every `z ∈ ℂ₊` with `F z ≠ 0`,
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
`θ = π + 2 arctan x` (`TauCeti.cayleyAngle`), under which `e^{iθ} = (x - i)/(x + i)` and
`dθ = 2 dx / (1 + x ^ 2)`, turns the circle average into the Poisson integral at `i`
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

variable {F : ℂ → ℂ} {S : ℝ}

/-! ### The Cayley transform of the boundary -/

section ChangeOfVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The Cayley change of variables.** For `h : ℝ → E`, the circle average of
`h ∘ inverseCayleyCoord` over the unit circle is the Poisson integral `∫ P(i, x) h(x) dx` at `i`. -/
theorem circleAverage_comp_inverseCayleyCoord (h : ℝ → E) :
    circleAverage (fun w ↦ h (inverseCayleyCoord w)) 0 1 =
      ∫ x, upperHalfPlanePoissonKernel I x • h x := by
  have himg := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ ↦ (hasDerivAt_cayleyAngle x).hasDerivWithinAt) cayleyAngle_injective.injOn
    (fun θ ↦ h (inverseCayleyCoord (circleMap 0 1 θ)))
  rw [image_univ, range_cayleyAngle, Measure.restrict_univ] at himg
  rw [circleAverage_def, intervalIntegral.integral_of_le two_pi_pos.le,
    integral_Ioc_eq_integral_Ioo, himg, ← integral_smul]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  simp only [circleMap_zero, ofReal_one, one_mul, inverseCayleyCoord_exp_cayleyAngle_mul_I,
    smul_smul, upperHalfPlanePoissonKernel_I]
  rw [abs_of_pos (by positivity)]
  congr 1
  field_simp

/-- **Integrability under the Cayley change of variables.** If `h ∘ inverseCayleyCoord` is
integrable on the unit circle, then `h` is integrable for the Poisson measure `dx / (1 + x ^ 2)`. -/
theorem integrable_upperHalfPlanePoissonMeasure_of_circleIntegrable {h : ℝ → E}
    (hh : CircleIntegrable (fun w ↦ h (inverseCayleyCoord w)) 0 1) :
    Integrable h upperHalfPlanePoissonMeasure := by
  have hIoo : IntegrableOn (fun θ ↦ h (inverseCayleyCoord (circleMap 0 1 θ))) (Ioo 0 (2 * π)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).1 hh).mono_set
      Ioo_subset_Ioc_self
  rw [← range_cayleyAngle, ← image_univ, integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ (fun x _ ↦ (hasDerivAt_cayleyAngle x).hasDerivWithinAt)
    cayleyAngle_injective.injOn, integrableOn_univ] at hIoo
  rw [integrable_upperHalfPlanePoissonMeasure_iff_integrable_smul]
  refine (hIoo.smul (1 / 2 : ℝ)).congr (.of_forall fun x ↦ ?_)
  simp only [Pi.smul_apply, circleMap_zero, ofReal_one, one_mul,
    inverseCayleyCoord_exp_cayleyAngle_mul_I, smul_smul]
  rw [abs_of_pos (by positivity)]
  congr 1
  ring

end ChangeOfVariables

/-- **Radial limits of the Cayley transport.** If `F` is holomorphic and bounded on `ℂ₊`, then
for almost every angle `θ`, `F(i (1 + w)/(1 - w))` tends to `F*(x)` as `w = r e^{iθ}` runs along
the radius, `r → 1⁻`, where `x` is the inverse Cayley coordinate of `e^{iθ}`. -/
theorem ae_tendsto_circleMap_upperHalfPlaneBoundaryFun
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) (hS : ∀ z ∈ upperHalfPlaneSet, ‖F z‖ ≤ S) :
    ∀ᵐ θ : ℝ, Tendsto (fun r ↦ F (I * (1 + circleMap 0 r θ) / (1 - circleMap 0 r θ))) (𝓝[<] 1)
      (𝓝 (upperHalfPlaneBoundaryFun F (inverseCayleyCoord (circleMap 0 1 θ)))) := by
  -- the boundary points without nontangential limits form a null set `N`
  set N := {y : ℝ | ¬ ∀ α : ℝ, Tendsto F (nontangentialFilter α y)
    (𝓝 (upperHalfPlaneBoundaryFun F y))}
  have hN : volume N = 0 := ae_tendsto_nontangentialFilter_upperHalfPlaneBoundaryFun hF hS
  -- the exceptional angles: those with `e^{iθ} = 1`, and the Cayley angles of `N` modulo `2π`
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
  -- off `B`, `e^{iθ} ≠ 1` is the Cayley point of `x = inverseCayleyCoord e^{iθ}` ...
  have hw1 : circleMap 0 1 θ ≠ 1 := fun h ↦ by
    obtain ⟨n, hn⟩ := (Circle.exp_eq_exp (x := θ) (y := 0)).1 <| Circle.ext <| by
      rw [Circle.coe_exp, Circle.coe_exp, ofReal_zero, zero_mul, exp_zero, ← h, circleMap_zero,
        ofReal_one, one_mul]
    exact hθ1 ⟨n, by rw [hn, zero_add]⟩
  have hζ := cayley_inverseCayleyCoord (by simp) hw1
  set x := inverseCayleyCoord (circleMap 0 1 θ)
  -- ... and `x` has nontangential limits, as `θ` is a Cayley angle of `x` modulo `2π`
  have hxN : x ∉ N := fun hxN ↦ by
    obtain ⟨n, hn⟩ := (Circle.exp_eq_exp (x := θ) (y := cayleyAngle x)).1 <| by
      rw [exp_cayleyAngle]
      ext1
      rw [Circle.coe_exp, coe_boundaryCayley, hζ, circleMap_zero, ofReal_one, one_mul]
    exact hθN (mem_iUnion.2 ⟨n, x, hxN, hn.symm⟩)
  -- the radius ending at `e^{iθ}` is carried into every cone at `x`
  refine hθ ?_
  have hr : ∀ r : ℝ, circleMap 0 r θ = r * (((x : ℂ) - I) / ((x : ℂ) + I)) := fun r ↦ by
    rw [hζ, circleMap_zero, circleMap_zero, ofReal_one, one_mul]
  exact ((not_not.1 hxN 1).comp (tendsto_I_mul_one_add_div_one_sub_nontangentialFilter x
    one_pos)).congr fun r ↦ by rw [Function.comp_apply, hr]

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
  have hgS : ∀ w ∈ ball (0 : ℂ) 1, ‖F (I * (1 + w) / (1 - w))‖ ≤ S :=
    fun w hw ↦ hS _ (bijOn_I_mul_one_add_div_one_sub_ball.mapsTo hw)
  have hlim := ae_tendsto_circleMap_upperHalfPlaneBoundaryFun hF hS
  refine ⟨circleIntegrable_log_norm_of_tendsto_circleMap one_pos hF.comp_I_mul_one_add_div_one_sub
    hgS hlim, fun hFI ↦ ?_⟩
  simpa only [add_zero, sub_zero, mul_one, div_one] using
    log_norm_le_circleAverage_log_norm_of_tendsto_circleMap one_pos
      hF.comp_I_mul_one_add_div_one_sub hgS (by simpa only [add_zero, sub_zero, mul_one, div_one])
      hlim

/-- **`log |F*| ∈ L¹(Π)`.** If `F` is holomorphic and bounded on `ℂ₊`, then `log |F*|` is
integrable for the Poisson measure `dx / (1 + x ^ 2)`. (With `log 0 = 0` this needs no hypothesis
`F ≢ 0`.) -/
theorem integrable_upperHalfPlanePoissonMeasure_log_norm_upperHalfPlaneBoundaryFun
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) (hS : ∀ z ∈ upperHalfPlaneSet, ‖F z‖ ≤ S) :
    Integrable (fun x ↦ Real.log ‖upperHalfPlaneBoundaryFun F x‖) upperHalfPlanePoissonMeasure :=
  integrable_upperHalfPlanePoissonMeasure_of_circleIntegrable (jensen_cayley hF hS).1

/-- The logarithmic bound at the pole `i`. -/
private theorem log_norm_le_integral_I (hF : DifferentiableOn ℂ F upperHalfPlaneSet)
    (hS : ∀ z ∈ upperHalfPlaneSet, ‖F z‖ ≤ S) (hFI : F I ≠ 0) :
    Real.log ‖F I‖ ≤
      ∫ x, upperHalfPlanePoissonKernel I x * Real.log ‖upperHalfPlaneBoundaryFun F x‖ :=
  ((jensen_cayley hF hS).2 hFI).trans_eq
    (circleAverage_comp_inverseCayleyCoord fun x ↦ Real.log ‖upperHalfPlaneBoundaryFun F x‖)

/-- **The logarithmic bound.** If `F` is holomorphic and bounded on `ℂ₊` and `F z ≠ 0` at
`z ∈ ℂ₊`, then `log |F(z)| ≤ ∫ P(z, x) log |F*(x)| dx`. -/
theorem log_norm_le_integral_upperHalfPlanePoissonKernel_mul_log_norm
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) (hS : ∀ z ∈ upperHalfPlaneSet, ‖F z‖ ≤ S)
    {z : ℂ} (hz : z ∈ upperHalfPlaneSet) (hFz : F z ≠ 0) :
    Real.log ‖F z‖ ≤
      ∫ x, upperHalfPlanePoissonKernel z x * Real.log ‖upperHalfPlaneBoundaryFun F x‖ := by
  have hb : 0 < z.im := hz
  set a := z.re
  set b := z.im
  set H : ℂ → ℂ := fun w ↦ F ((a : ℂ) + b * w)
  have hA : MapsTo (fun w : ℂ ↦ (a : ℂ) + b * w) upperHalfPlaneSet upperHalfPlaneSet :=
    fun w hw ↦ by simpa [upperHalfPlaneSet] using mul_pos hb hw
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
    -- `P(z, a + b x) = P(a + b i, a + b x) = b⁻¹ P(i, x)` by the affine covariance of the kernel
    simp only [K]
    rw [← hzab, upperHalfPlanePoissonKernel_add_mul a hb.ne', mul_assoc,
      mul_inv_cancel_left₀ hb.ne']
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
    (integrable_upperHalfPlanePoissonMeasure_log_norm_upperHalfPlaneBoundaryFun hF hS).ofReal
  rw [re_upperHalfPlanePoissonIntegralFun hi]
  simpa using log_norm_le_integral_upperHalfPlanePoissonKernel_mul_log_norm hF hS hz hFz

end TauCeti
