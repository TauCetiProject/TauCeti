/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Canonical.Basic
import Mathlib.Analysis.Complex.Liouville
import TauCeti.Analysis.Complex.RiemannSurface.Differential.IdentityTheorem
import TauCeti.Analysis.Complex.RiemannSurface.RationalFunction

/-!
# A canonical divisor on the Riemann sphere

The differential `dz` of the affine coordinate on `OnePoint ℂ` has no zeros or poles at
finite points and has a double pole at infinity. In the coordinate `w = 1/z` it is
`-w⁻² dw`, an instance of the transformation law `ω = -g(1/w) / w² dw` for a `1`-form
`ω = g(z) dz` (`TauCeti.RiemannSurface.OneForm.coeff_invChart_eq_neg_inv_sq_mul`). Thus its
divisor is `-2[∞]`, an explicit canonical divisor of degree `-2`.
This is the sphere contribution in the canonical-divisor form of Riemann–Hurwitz.

The sphere has no nonzero holomorphic `1`-form
(`TauCeti.RiemannSurface.holomorphicOneForms_onePoint_eq_bot`). If `η = f dz` is holomorphic, then
`f` is entire, and in the coordinate `w = 1/z` the form is `-f(1/w) w⁻² dw` with holomorphic
coefficient `g`, so `f(z) = -g(1/z) z⁻²` tends to zero at infinity and vanishes by Liouville's
theorem. So `h⁰(K) = 0` on the sphere, the genus-zero case of `h⁰(K) = g`.

The affine coordinate itself is assigned the value zero at infinity. Its manifold
differential there is likewise a junk value; meromorphy, order and divisor only depend
on punctured neighbourhoods, so the double pole is retained.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, GTM 81, §§9 and 17
  (meromorphic differentials and the canonical divisor of the sphere, and the absence of
  holomorphic differentials on it).
-/

public noncomputable section

open Filter Function OnePoint Set Topology
open scoped Manifold

namespace TauCeti.RiemannSurface

open AlgebraicGeometry WeilDivisor

/-- The meromorphic differential `dz` on the sphere, obtained by differentiating the
affine coordinate. Its value at infinity is irrelevant to its meromorphic germ. -/
def sphereCoordinateDifferential : OneForm (OnePoint ℂ) :=
  mvfderiv 𝓘(ℂ) (affineChart : OnePoint ℂ → ℂ)

/-- In the affine chart the coefficient of `dz` is the constant one. -/
@[simp]
theorem coeff_sphereCoordinateDifferential_affineChart :
    sphereCoordinateDifferential.coeff affineChart = fun _ => 1 := by
  funext z
  have he := affineChart_mem_maximalAtlas (𝕜 := ℂ) (n := 1)
  rw [sphereCoordinateDifferential, OneForm.coeff_mvfderiv he (by simp)
    (mdifferentiableAt_of_mem_maximalAtlas he (by simp))]
  simp [comp_def]

/-- **The transformation law between the two charts of the sphere.** If `ω = g(z) dz` in the
affine chart, then `ω = -g(1/w) / w² dw` in the inverted chart, at every `w ≠ 0`. -/
theorem OneForm.coeff_invChart_eq_neg_inv_sq_mul (ω : OneForm (OnePoint ℂ)) {w : ℂ}
    (hw : w ≠ 0) : ω.coeff invChart w = -(w ^ 2)⁻¹ * ω.coeff affineChart w⁻¹ := by
  have hw' : w⁻¹ ≠ 0 := inv_ne_zero hw
  have h := ω.coeff_eq_coeff_mul_deriv affineChart_mem_maximalAtlas invChart_mem_maximalAtlas
    (y := ((w⁻¹ : ℂ) : OnePoint ℂ)) (by simp)
    (by simpa using fun h ↦ hw' (coe_injective h))
  rw [invChart_coe, inv_inv, affineChart_coe, affineChart_comp_invChart_symm, deriv_inv] at h
  rw [h, mul_comm]

/-- The coefficient of an everywhere meromorphic `1`-form in the inverted chart is meromorphic. -/
theorem OneForm.meromorphicAt_coeff_invChart {ω : OneForm (OnePoint ℂ)}
    (hω : ∀ x, ω.MeromorphicAt x) (w : ℂ) : _root_.MeromorphicAt (ω.coeff invChart) w := by
  rcases eq_or_ne w 0 with rfl | hw
  · simpa only [meromorphicAt_def, chartAt_infty, invChart_infty] using hω ∞
  · have hsrc : ((w⁻¹ : ℂ) : OnePoint ℂ) ∈ invChart.source := by
      simpa using fun h ↦ inv_ne_zero hw (coe_injective h)
    simpa only [invChart_coe, inv_inv] using
      (meromorphicAt_iff_of_mem_maximalAtlas invChart_mem_maximalAtlas hsrc).1 (hω _)

/-- Off the support of the divisor, the coefficient in the affine chart has no pole. -/
theorem OneForm.meromorphicOrderAt_coeff_affineChart_nonneg {ω : OneForm (OnePoint ℂ)}
    (hω : ∀ x, ω.MeromorphicAt x) {z : ℂ} (hz : (z : OnePoint ℂ) ∉ ω.divisor.support) :
    0 ≤ _root_.meromorphicOrderAt (ω.coeff affineChart) z := by
  simpa only [order_def, chartAt_coe, affineChart_coe] using order_nonneg_of_notMem_support hω hz

/-- Off the support of the divisor, the coefficient in the inverted chart has no pole at a nonzero
point. -/
theorem OneForm.meromorphicOrderAt_coeff_invChart_nonneg {ω : OneForm (OnePoint ℂ)}
    (hω : ∀ x, ω.MeromorphicAt x) {w : ℂ} (hw : w ≠ 0)
    (hwS : ((w⁻¹ : ℂ) : OnePoint ℂ) ∉ ω.divisor.support) :
    0 ≤ _root_.meromorphicOrderAt (ω.coeff invChart) w := by
  have hsrc : ((w⁻¹ : ℂ) : OnePoint ℂ) ∈ invChart.source := by
    simpa using fun h ↦ inv_ne_zero hw (coe_injective h)
  have := order_nonneg_of_notMem_support hω hwS
  rwa [order_eq_of_mem_maximalAtlas invChart_mem_maximalAtlas hsrc, invChart_coe, inv_inv] at this

/-- The differential `dz` is holomorphic at every finite point of the sphere. -/
theorem holomorphicAt_sphereCoordinateDifferential_coe (z : ℂ) :
    sphereCoordinateDifferential.HolomorphicAt (z : OnePoint ℂ) := by
  rw [OneForm.holomorphicAt_def, chartAt_coe,
    coeff_sphereCoordinateDifferential_affineChart]
  exact analyticAt_const

/-- The differential `dz` has order zero at every finite point. -/
@[simp]
theorem order_sphereCoordinateDifferential_coe (z : ℂ) :
    sphereCoordinateDifferential.order (z : OnePoint ℂ) = 0 := by
  rw [OneForm.order_def, chartAt_coe, coeff_sphereCoordinateDifferential_affineChart]
  rw [_root_.meromorphicOrderAt_const]
  norm_num

/-- In the inverted coordinate, `dz = -w⁻² dw`, so `dz` has a double pole at infinity. -/
@[simp]
theorem order_sphereCoordinateDifferential_infty :
    sphereCoordinateDifferential.order ∞ = (-2 : ℤ) := by
  exact OneForm.order_mvfderiv (by norm_num : (-1 : ℤ) ≠ 0)
    meromorphicOrderAt_affineChart_infty

/-- The differential `dz` is meromorphic everywhere on the sphere. -/
theorem meromorphicAt_sphereCoordinateDifferential (x : OnePoint ℂ) :
    sphereCoordinateDifferential.MeromorphicAt x := by
  apply OneForm.meromorphicAt_mvfderiv
  have hcoord : MeromorphicFunction.coordinate.finitePart = (affineChart : OnePoint ℂ → ℂ) := by
    funext y
    rw [MeromorphicFunction.finitePart_def, MeromorphicFunction.coordinate_apply]
  simpa only [hcoord] using MeromorphicFunction.coordinate.meromorphicAt_finitePart x

/-- The differential `dz` has finite order at every point. -/
theorem order_sphereCoordinateDifferential_ne_top (x : OnePoint ℂ) :
    sphereCoordinateDifferential.order x ≠ ⊤ := by
  induction x using OnePoint.rec <;> simp

/-- The divisor of `dz` on the sphere is `-2[∞]`. -/
@[simp]
theorem divisor_sphereCoordinateDifferential :
    sphereCoordinateDifferential.divisor = (-2 : ℤ) • ofPoint (∞ : OnePoint ℂ) := by
  classical
  apply WeilDivisor.ext
  intro x
  rw [OneForm.coeff_divisor meromorphicAt_sphereCoordinateDifferential]
  induction x using OnePoint.rec with
  | infty => simp only [order_sphereCoordinateDifferential_infty, WithTop.untop₀_coe,
      coeff_zsmul, coeff_ofPoint_self, mul_one]
  | coe z => simp only [order_sphereCoordinateDifferential_coe, WithTop.untop₀_zero,
      coeff_zsmul, coeff_ofPoint_of_ne (coe_ne_infty z), mul_zero]

/-- The sphere has the explicit canonical divisor `-2[∞]`. -/
theorem isCanonicalDivisor_neg_two_infty :
    IsCanonicalDivisor ((-2 : ℤ) • ofPoint (∞ : OnePoint ℂ)) := by
  rw [← divisor_sphereCoordinateDifferential]
  exact isCanonicalDivisor_divisor meromorphicAt_sphereCoordinateDifferential
    order_sphereCoordinateDifferential_ne_top

/-- The explicit canonical divisor of the sphere has degree `-2`. -/
theorem degree_divisor_sphereCoordinateDifferential :
    WeilDivisor.degree sphereCoordinateDifferential.divisor = -2 := by
  simp [divisor_sphereCoordinateDifferential, degree_ofPoint]

/-- **The sphere has no nonzero holomorphic `1`-form.** A holomorphic `η = f dz` has entire
coefficient `f` with `f(z) = -g(1/z) z⁻²` for the holomorphic coefficient `g` at infinity, so `f`
tends to zero at infinity and vanishes by Liouville's theorem. -/
theorem holomorphicOneForms_onePoint_eq_bot : holomorphicOneForms (OnePoint ℂ) = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun η hη ↦ ?_
  have hη' := mem_holomorphicOneForms.1 hη
  set f := η.coeff affineChart
  set g := η.coeff invChart
  have hf : Differentiable ℂ f := fun z ↦ by
    have h := hη' z
    rw [OneForm.holomorphicAt_def, chartAt_coe, affineChart_coe] at h
    exact h.differentiableAt
  have hg : ContinuousAt g 0 := by
    have h := hη' ∞
    rw [OneForm.holomorphicAt_def, chartAt_infty, invChart_infty] at h
    exact h.continuousAt
  -- Away from `0`, `f z = -g(1/z) z⁻²`, which tends to `-g(0) · 0 = 0` at infinity.
  have hfg : ∀ᶠ z in cocompact ℂ, -(g z⁻¹ * z⁻¹ ^ 2) = f z := by
    filter_upwards [(isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact] with z hz
    have hz : z ≠ 0 := hz
    simp only [g, f, OneForm.coeff_invChart_eq_neg_inv_sq_mul η (inv_ne_zero hz), inv_inv]
    field_simp
  have hinv : Tendsto (fun z : ℂ ↦ z⁻¹) (cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded
  have hlim : Tendsto f (cocompact ℂ) (𝓝 0) := by
    have h := ((hg.tendsto.comp hinv).mul (hinv.pow 2)).neg
    rw [zero_pow two_ne_zero, mul_zero, neg_zero] at h
    exact h.congr' hfg
  have hf0 : f = 0 := hf.eq_const_of_tendsto_cocompact hlim
  have hord : η.order ((0 : ℂ) : OnePoint ℂ) = ⊤ := by
    rw [OneForm.order_def, chartAt_coe, affineChart_coe]
    exact meromorphicOrderAt_eq_top_iff.2 (Eventually.of_forall fun z ↦ congrFun hf0 z)
  exact (OneForm.order_eq_top_iff_eq_zero hη' _).1 hord

/-- **`h⁰(K) = 0` on the sphere**: the space of holomorphic `1`-forms on `OnePoint ℂ` has
dimension zero, the genus-zero case of `h⁰(K) = g`. -/
theorem finrank_holomorphicOneForms_onePoint :
    Module.finrank ℂ (holomorphicOneForms (OnePoint ℂ)) = 0 := by
  rw [holomorphicOneForms_onePoint_eq_bot, finrank_bot]

end TauCeti.RiemannSurface
