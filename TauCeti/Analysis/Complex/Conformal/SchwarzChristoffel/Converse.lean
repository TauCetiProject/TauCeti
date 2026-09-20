/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.PreSchwarzian
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Primitive

/-!
# Integrating the Schwarz--Christoffel differential equation

The pre-Schwarzian differential equation

`F'' / F' = ∑ i, e i / (z - a i)`

determines a locally conformal holomorphic map of the upper half-plane up to an affine
postcomposition. Indeed, the right-hand side is the pre-Schwarzian derivative of the normalized
Schwarz--Christoffel primitive. Equality of the two logarithmic derivatives first identifies their
first derivatives up to a nonzero constant, and connectedness then identifies the functions up to
an additive constant.

This is the integration step in the converse Schwarz--Christoffel theorem. Once reflection and
partial fractions identify the pre-Schwarzian of a polygon map with the displayed sum, the result
here recovers the map itself as an affine image of the normalized primitive.

## Main result

* `TauCeti.exists_eqOn_const_mul_schwarzChristoffelPrimitive_add_iff` -- a locally conformal
  holomorphic map solves the Schwarz--Christoffel pre-Schwarzian equation exactly when it is
  `A * primitive + B` for a nonzero `A`.
* `TauCeti.eqOn_const_mul_schwarzChristoffelPrimitive_add_of_logDeriv_deriv_eqOn` -- the same
  integration result with `A` and `B` read off from the value and derivative at the normalization
  point.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Set UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- **Integration of the Schwarz--Christoffel differential equation.** A holomorphic function
`f` with holomorphic, nonvanishing derivative on the upper half-plane has pre-Schwarzian
`∑ i, e i / (z - a i)` exactly when it is `A * F + B` for a nonzero constant `A`, where `F` is
the normalized Schwarz--Christoffel primitive for the prevertices `a` and exponents `e`.

No separate regularity assumption is needed for `deriv f`: complex differentiability on an open
set already implies complex differentiability of the derivative there. -/
theorem exists_eqOn_const_mul_schwarzChristoffelPrimitive_add_iff (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hfn : ∀ z ∈ upperHalfPlaneSet, deriv f z ≠ 0) :
    (∃ A : ℂ, A ≠ 0 ∧ ∃ B : ℂ,
      EqOn f (fun z => A * schwarzChristoffelPrimitive a e z₀ z + B) upperHalfPlaneSet) ↔
      EqOn (logDeriv (deriv f))
        (fun z => ∑ i, (e i : ℂ) / (z - (a i : ℂ))) upperHalfPlaneSet := by
  let F := schwarzChristoffelPrimitive a e z₀
  have hF : DifferentiableOn ℂ F upperHalfPlaneSet :=
    differentiableOn_schwarzChristoffelPrimitive a e z₀
  have hnF : ∀ z ∈ upperHalfPlaneSet, deriv F z ≠ 0 := by
    intro z hz
    rw [deriv_schwarzChristoffelPrimitive a e z₀ hz]
    exact schwarzChristoffelIntegrand_ne_zero a e hz
  rw [exists_eqOn_const_mul_add_iff_logDeriv_deriv_eqOn isOpen_upperHalfPlaneSet
    (convex_halfSpace_im_gt 0).isPreconnected hf hF hfn hnF]
  constructor
  · intro h z hz
    exact (h hz).trans (logDeriv_deriv_schwarzChristoffelPrimitive a e z₀ hz)
  · intro h z hz
    exact (h hz).trans (logDeriv_deriv_schwarzChristoffelPrimitive a e z₀ hz).symm

/-- **Normalized integration of the Schwarz--Christoffel differential equation.** If the
pre-Schwarzian of `f` is the Schwarz--Christoffel partial-fraction sum, then throughout the upper
half-plane

`f z = (f'(z₀) / integrand(z₀)) * primitive(z) + f(z₀)`.

Thus the value and derivative at the primitive's base point determine the two constants.
The denominator is nonzero because the Schwarz--Christoffel integrand has no zeros in the upper
half-plane. -/
theorem eqOn_const_mul_schwarzChristoffelPrimitive_add_of_logDeriv_deriv_eqOn
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hfn : ∀ z ∈ upperHalfPlaneSet, deriv f z ≠ 0)
    (hpre : EqOn (logDeriv (deriv f))
      (fun z => ∑ i, (e i : ℂ) / (z - (a i : ℂ))) upperHalfPlaneSet) :
    EqOn f (fun z =>
      deriv f z₀ / schwarzChristoffelIntegrand a e z₀ *
        schwarzChristoffelPrimitive a e z₀ z + f z₀) upperHalfPlaneSet := by
  obtain ⟨A, _, B, hEq⟩ :=
    (exists_eqOn_const_mul_schwarzChristoffelPrimitive_add_iff a e z₀ hf hfn).mpr hpre
  have hB : B = f z₀ := by
    simpa using (hEq z₀.im_pos).symm
  have hderiv := hEq.deriv isOpen_upperHalfPlaneSet z₀.im_pos
  have hAeq : A = deriv f z₀ / schwarzChristoffelIntegrand a e z₀ := by
    rw [deriv_add_const, deriv_const_mul_field,
      deriv_schwarzChristoffelPrimitive a e z₀ z₀.im_pos] at hderiv
    exact (eq_div_iff (schwarzChristoffelIntegrand_ne_zero a e z₀.im_pos)).mpr hderiv.symm
  intro z hz
  rw [hEq hz, hAeq, hB]

end TauCeti
