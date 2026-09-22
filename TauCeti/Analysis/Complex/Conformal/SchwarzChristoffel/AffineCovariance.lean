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
parameters.  In particular, two distinct prevertices may be normalized to any two prescribed real
points in the same order; below they are normalized canonically to `0` and `1`.

## Main results

* `TauCeti.schwarzChristoffelIntegrand_affine_prevertices` -- covariance of the integrand.
* `TauCeti.schwarzChristoffelPrimitive_affine_prevertices` -- covariance of the normalized
  primitive.
* `TauCeti.exists_affine_prevertices_eq_zero_one` -- a positive affine change normalizes two
  ordered prevertices to `0` and `1`.

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
    (d : ℝ) {z : ℂ} (hz : ∀ i, z - (a i : ℂ) ≠ 0) :
    schwarzChristoffelIntegrand (fun i ↦ c * a i + d) e ((c : ℂ) * z + (d : ℂ)) =
      (c : ℂ) ^ ((∑ i, e i : ℝ) : ℂ) * schwarzChristoffelIntegrand a e z := by
  rw [schwarzChristoffelIntegrand_def, schwarzChristoffelIntegrand_def]
  have h_affine (i : ι) : (c : ℂ) * z + (d : ℂ) - ((c * a i + d : ℝ) : ℂ) =
      (c : ℂ) * (z - (a i : ℂ)) := by
    push_cast
    ring
  simp_rw [h_affine, Complex.ofReal_mul_cpow hc (hz _), Finset.prod_mul_distrib]
  congr 1
  calc
    ∏ i, (c : ℂ) ^ (e i : ℂ) = ∏ i, ((c ^ e i : ℝ) : ℂ) := by
      apply Finset.prod_congr rfl
      intro i _
      exact (Complex.ofReal_cpow hc.le (e i)).symm
    _ = ((∏ i, c ^ e i : ℝ) : ℂ) := by push_cast; rfl
    _ = ((c ^ ∑ i, e i : ℝ) : ℂ) :=
      congr_arg ((↑) : ℝ → ℂ) (Real.rpow_sum_of_pos hc e Finset.univ).symm
    _ = (c : ℂ) ^ ((∑ i, e i : ℝ) : ℂ) := Complex.ofReal_cpow hc.le _

/-- The normalized Schwarz--Christoffel primitive is covariant under a positive affine change of
all prevertices and of its argument.  Its scale exponent is one more than the total turning
exponent. -/
theorem schwarzChristoffelPrimitive_affine_prevertices (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {c : ℝ} (hc : 0 < c) (d : ℝ) {z : ℂ}
    (hz : z ∈ upperHalfPlaneSet) :
    schwarzChristoffelPrimitive (fun i ↦ c * a i + d) e
        (d +ᵥ ((⟨c, hc⟩ : {x : ℝ // 0 < x}) • z₀))
        ((c : ℂ) * z + (d : ℂ)) =
      (c : ℂ) ^ (((∑ i, e i) + 1 : ℝ) : ℂ) *
        schwarzChristoffelPrimitive a e z₀ z := by
  let C : ℂ := (c : ℂ) ^ (((∑ i, e i) + 1 : ℝ) : ℂ)
  have hc₀ : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hC : C = (c : ℂ) ^ ((∑ i, e i : ℝ) : ℂ) * (c : ℂ) := by
    dsimp only [C]
    have h_exp : (((∑ i, e i) + 1 : ℝ) : ℂ) = ((∑ i, e i : ℝ) : ℂ) + 1 := by
      push_cast
      ring
    rw [h_exp, Complex.cpow_add _ _ hc₀, Complex.cpow_one]
  have hleft : ∀ w ∈ upperHalfPlaneSet,
      HasDerivAt
        (schwarzChristoffelPrimitive (fun i ↦ c * a i + d) e
            (d +ᵥ ((⟨c, hc⟩ : {x : ℝ // 0 < x}) • z₀)) ∘
          fun ζ : ℂ ↦ (c : ℂ) * ζ + (d : ℂ))
        (C * schwarzChristoffelIntegrand a e w) w := by
    intro w hw
    have hinner : HasDerivAt (fun ζ : ℂ ↦ (c : ℂ) * ζ + (d : ℂ)) (c : ℂ) w := by
      simpa using ((hasDerivAt_id w).const_mul (c : ℂ)).add_const (d : ℂ)
    have hcomp :=
      (hasDerivAt_schwarzChristoffelPrimitive (fun i ↦ c * a i + d) e
        (d +ᵥ ((⟨c, hc⟩ : {x : ℝ // 0 < x}) • z₀))
        (by simpa [upperHalfPlaneSet, mul_im] using mul_pos hc hw)).comp w hinner
    have hderiv :
        schwarzChristoffelIntegrand (fun i ↦ c * a i + d) e
            ((c : ℂ) * w + (d : ℂ)) * (c : ℂ) =
          C * schwarzChristoffelIntegrand a e w := by
      have hne (i : ι) : w - (a i : ℂ) ≠ 0 :=
        fun h ↦ hw.ne' (by simpa using congr_arg Complex.im h)
      rw [schwarzChristoffelIntegrand_affine_prevertices a e hc d hne, hC]
      ring
    exact hcomp.congr_deriv hderiv
  have hright : ∀ w ∈ upperHalfPlaneSet,
      HasDerivAt (fun ζ : ℂ ↦ C * schwarzChristoffelPrimitive a e z₀ ζ)
        (C * schwarzChristoffelIntegrand a e w) w :=
    fun w hw ↦ (hasDerivAt_schwarzChristoffelPrimitive a e z₀ hw).const_mul C
  have heq : EqOn
      (schwarzChristoffelPrimitive (fun i ↦ c * a i + d) e
          (d +ᵥ ((⟨c, hc⟩ : {x : ℝ // 0 < x}) • z₀)) ∘
        fun w : ℂ ↦ (c : ℂ) * w + (d : ℂ))
      (fun w : ℂ ↦ C * schwarzChristoffelPrimitive a e z₀ w) upperHalfPlaneSet := by
    apply isOpen_upperHalfPlaneSet.eqOn_of_deriv_eq
      (convex_halfSpace_im_gt 0).isPreconnected
      (fun w hw ↦ (hleft w hw).differentiableAt.differentiableWithinAt)
      (fun w hw ↦ (hright w hw).differentiableAt.differentiableWithinAt)
      (fun w hw ↦ (hleft w hw).deriv.trans (hright w hw).deriv.symm)
      z₀.coe_im_pos
    rw [Function.comp_apply, schwarzChristoffelPrimitive_apply_base, mul_zero]
    exact (congr_arg
      (schwarzChristoffelPrimitive (fun i ↦ c * a i + d) e
        (d +ᵥ ((⟨c, hc⟩ : {x : ℝ // 0 < x}) • z₀)))
      (by simp [UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_pos_real_smul,
        Complex.real_smul, add_comm])).trans
        (schwarzChristoffelPrimitive_apply_base _ _ _)
  exact heq hz

/-- Under the polygonal closing condition `∑ i, e i = -2`, positively scaling the prevertices by
`c` scales the normalized Schwarz--Christoffel primitive by `c⁻¹`. -/
theorem schwarzChristoffelPrimitive_affine_prevertices_of_sum_eq_neg_two (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {c : ℝ} (hc : 0 < c) (d : ℝ) (hsum : ∑ i, e i = -2)
    {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    schwarzChristoffelPrimitive (fun i ↦ c * a i + d) e
        (d +ᵥ ((⟨c, hc⟩ : {x : ℝ // 0 < x}) • z₀))
        ((c : ℂ) * z + (d : ℂ)) =
      (c : ℂ)⁻¹ * schwarzChristoffelPrimitive a e z₀ z := by
  rw [schwarzChristoffelPrimitive_affine_prevertices a e z₀ hc d hz, hsum]
  norm_num [Complex.cpow_neg]

omit [Fintype ι] in
/-- Two ordered prevertices can be normalized to `0` and `1` by a positive affine change.  Thus a
prevertex parameter space containing two distinguished ordered entries may be studied with those
two entries fixed. -/
theorem exists_affine_prevertices_eq_zero_one (a : ι → ℝ) {i j : ι} (hij : a i < a j) :
    ∃ c > 0, ∃ d, c * a i + d = 0 ∧ c * a j + d = 1 := by
  let c := (a j - a i)⁻¹
  refine ⟨c, inv_pos.mpr (sub_pos.mpr hij), -c * a i, by ring, ?_⟩
  calc
    c * a j + -c * a i = c * (a j - a i) := by ring
    _ = 1 := inv_mul_cancel₀ (sub_ne_zero.mpr hij.ne')

end TauCeti

end
