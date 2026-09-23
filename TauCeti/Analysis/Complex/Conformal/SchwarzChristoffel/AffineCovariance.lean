/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Primitive
public import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Affine covariance of the Schwarz--Christoffel map

A positive affine change `x ↦ c * x + d` of the real prevertices extends to an automorphism of
the upper half-plane.  This file computes its effect on the Schwarz--Christoffel integrand and on
the normalized primitive.  If `S = ∑ i, e i`, then the integrand acquires the factor `c ^ S`,
while the primitive acquires `c ^ (S + 1)` because the change of variable contributes one further
factor of `c`.

This covariance removes the translation and positive-scaling redundancy from the prevertex
parameters.  The corresponding normalization of two ordered real points is developed separately
in `TauCeti.Algebra.Order.Field.Basic`.

## Main results

* `TauCeti.schwarzChristoffelIntegrand_affine_prevertices` -- covariance of the integrand.
* `TauCeti.schwarzChristoffelPrimitive_affine_prevertices` -- covariance of the normalized
  primitive.
* `TauCeti.schwarzChristoffelPrimitive_affine_prevertices_of_exponent_sum_eq_neg_two` -- under
  the closing condition, the affine change scales the primitive by the inverse scale factor.

## References

* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Finset Set UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The Schwarz--Christoffel integrand is covariant under a positive affine change of all its
prevertices.  The exponent of the scale factor is the total turning exponent. -/
theorem schwarzChristoffelIntegrand_affine_prevertices (a e : ι → ℝ) {c : ℝ} (hc : 0 < c)
    (d : ℝ) (z : ℂ) :
    schwarzChristoffelIntegrand (fun i ↦ c * a i + d) e ((c : ℂ) * z + (d : ℂ)) =
      (c : ℂ) ^ ((∑ i, e i : ℝ) : ℂ) * schwarzChristoffelIntegrand a e z := by
  rw [schwarzChristoffelIntegrand_def, schwarzChristoffelIntegrand_def]
  have h_affine (i : ι) : (c : ℂ) * z + (d : ℂ) - ((c * a i + d : ℝ) : ℂ) =
      (c : ℂ) * (z - (a i : ℂ)) := by
    push_cast
    ring
  simp_rw [h_affine, TauCeti.ofReal_mul_cpow hc.le, Finset.prod_mul_distrib]
  congr 1
  exact (ofReal_cpow_sum hc e Finset.univ).symm

/-- The normalized Schwarz--Christoffel primitive is covariant under a simultaneous positive
affine change of its prevertices, base point, and argument.  Its scale exponent is one more than
the total turning exponent. -/
theorem schwarzChristoffelPrimitive_affine_prevertices (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {c : ℝ} (hc : 0 < c) (d : ℝ) {z : ℂ}
    (hz : z ∈ upperHalfPlaneSet) :
    schwarzChristoffelPrimitive (fun i ↦ c * a i + d) e
        (d +ᵥ ((⟨c, hc⟩ : {x : ℝ // 0 < x}) • z₀))
        ((c : ℂ) * z + (d : ℂ)) =
      (c : ℂ) ^ (((∑ i, e i) + 1 : ℝ) : ℂ) *
        schwarzChristoffelPrimitive a e z₀ z := by
  let a' : ι → ℝ := fun i ↦ c * a i + d
  let z₀' : UpperHalfPlane := d +ᵥ ((⟨c, hc⟩ : {x : ℝ // 0 < x}) • z₀)
  let C : ℂ := (c : ℂ) ^ (((∑ i, e i) + 1 : ℝ) : ℂ)
  have hc₀ : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hcoe : (z₀' : ℂ) = (c : ℂ) * (z₀ : ℂ) + (d : ℂ) := by
    simp [z₀', UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_pos_real_smul,
      Complex.real_smul, add_comm]
  have hC : C = (c : ℂ) ^ ((∑ i, e i : ℝ) : ℂ) * (c : ℂ) := by
    dsimp only [C]
    have h_exp : (((∑ i, e i) + 1 : ℝ) : ℂ) = ((∑ i, e i : ℝ) : ℂ) + 1 := by
      push_cast
      ring
    rw [h_exp, Complex.cpow_add _ _ hc₀, Complex.cpow_one]
  have hleft : ∀ w ∈ upperHalfPlaneSet,
      HasDerivAt
        (schwarzChristoffelPrimitive a' e z₀' ∘
          fun ζ : ℂ ↦ (c : ℂ) * ζ + (d : ℂ))
        (C * schwarzChristoffelIntegrand a e w) w := by
    intro w hw
    have hinner : HasDerivAt (fun ζ : ℂ ↦ (c : ℂ) * ζ + (d : ℂ)) (c : ℂ) w := by
      simpa using ((hasDerivAt_id w).const_mul (c : ℂ)).add_const (d : ℂ)
    have hcomp :=
      (hasDerivAt_schwarzChristoffelPrimitive a' e z₀'
        (by simpa [upperHalfPlaneSet, mul_im] using mul_pos hc hw)).comp w hinner
    have hderiv :
        schwarzChristoffelIntegrand a' e
            ((c : ℂ) * w + (d : ℂ)) * (c : ℂ) =
          C * schwarzChristoffelIntegrand a e w := by
      simp only [a']
      rw [schwarzChristoffelIntegrand_affine_prevertices a e hc d w, hC]
      ring
    exact hcomp.congr_deriv hderiv
  have hC₀ : C ≠ 0 := by
    rw [hC]
    exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hc₀)) hc₀
  have hg : ∀ w ∈ upperHalfPlaneSet,
      HasDerivAt
        (fun ζ : ℂ ↦ C⁻¹ * schwarzChristoffelPrimitive a' e z₀'
          ((c : ℂ) * ζ + (d : ℂ)))
        (schwarzChristoffelIntegrand a e w) w := by
    intro w hw
    refine ((hleft w hw).const_mul C⁻¹).congr_deriv ?_
    rw [← mul_assoc, inv_mul_cancel₀ hC₀, one_mul]
  have hg₀ : C⁻¹ * schwarzChristoffelPrimitive a' e z₀'
      ((c : ℂ) * (z₀ : ℂ) + (d : ℂ)) = 0 := by
    rw [← hcoe, schwarzChristoffelPrimitive_apply_base, mul_zero]
  have heq := eqOn_schwarzChristoffelPrimitive a e z₀ hg hg₀ hz
  have hscaled : schwarzChristoffelPrimitive a' e z₀'
      ((c : ℂ) * z + (d : ℂ)) = C * schwarzChristoffelPrimitive a e z₀ z := by
    calc
      _ = C * (C⁻¹ * schwarzChristoffelPrimitive a' e z₀'
          ((c : ℂ) * z + (d : ℂ))) := (mul_inv_cancel_left₀ hC₀ _).symm
      _ = C * schwarzChristoffelPrimitive a e z₀ z := congr_arg (C * ·) heq
  simpa only [a', z₀', C] using hscaled

/-- Under the polygonal closing condition `∑ i, e i = -2`, a positive affine change
`x ↦ c * x + d` of the prevertices, base point, and argument multiplies the normalized
Schwarz--Christoffel primitive by `c⁻¹`. -/
theorem schwarzChristoffelPrimitive_affine_prevertices_of_exponent_sum_eq_neg_two (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {c : ℝ} (hc : 0 < c) (d : ℝ) (hsum : ∑ i, e i = -2)
    {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    schwarzChristoffelPrimitive (fun i ↦ c * a i + d) e
        (d +ᵥ ((⟨c, hc⟩ : {x : ℝ // 0 < x}) • z₀))
        ((c : ℂ) * z + (d : ℂ)) =
      (c : ℂ)⁻¹ * schwarzChristoffelPrimitive a e z₀ z := by
  rw [schwarzChristoffelPrimitive_affine_prevertices a e z₀ hc d hz, hsum]
  norm_num [Complex.cpow_neg]

end TauCeti

end
