/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import TauCeti.Geometry.Symplectic.Complex.Line

/-!
# Radial maps of the complex line and the standard area form

A *radial map* of a real inner product space `E` is a map `x ↦ g(‖x‖²) • x` for a real function
`g`. Where `g` is differentiable at `s = ‖z‖²`, its derivative at `z` is
`v ↦ g(s) v + 2 g'(s) ⟪z, v⟫ z` (`TauCeti.hasFDerivAt_smul_self_of_hasDerivAt_sq_norm`).

On the complex line this derivative scales the standard area form
`ω(v, w) = v.re * w.im - v.im * w.re` (`TauCeti.stdComplexSymplecticForm`) by the constant factor

`g(s) (g(s) + 2 s g'(s))`

(`TauCeti.stdComplexSymplecticForm_fderiv_smul_self`), which is therefore the Jacobian determinant
of the radial map at `z`. In polar form, with `b(t) = g(t²)`, this is the familiar
`b(t) (b(t) + t b'(t))`. The linear-algebra step is that `v ↦ a v + b ⟪z, v⟫ z` scales the area
form by `a (a + b ‖z‖²)` (`TauCeti.stdComplexSymplecticForm_smul_add_inner_smul`).

Radial maps are how symplectic embeddings and cutoffs of discs into the Riemann sphere are written
in a disc coordinate: the factor above is the area density that such a map pulls back.

## Main results

* `TauCeti.hasFDerivAt_smul_self_of_hasDerivAt_sq_norm`: the derivative of a radial map.
* `TauCeti.stdComplexSymplecticForm_smul_add_inner_smul`: the area scaling of
  `v ↦ a v + b ⟪z, v⟫ z`.
* `TauCeti.stdComplexSymplecticForm_fderiv_smul_self`: a radial map of `ℂ` scales the standard
  area form by `g(s) (g(s) + 2 s g'(s))`.
-/

public section

open RealInnerProductSpace

namespace TauCeti

/-- **The derivative of a radial map.** If `g` is differentiable at `‖z‖²`, the map
`x ↦ g(‖x‖²) • x` has derivative `v ↦ g(‖z‖²) v + 2 g'(‖z‖²) ⟪z, v⟫ z` at `z`. -/
theorem hasFDerivAt_smul_self_of_hasDerivAt_sq_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {g : ℝ → ℝ} {g' : ℝ} {z : E} (hg : HasDerivAt g g' (‖z‖ ^ 2)) :
    HasFDerivAt (fun x : E ↦ g (‖x‖ ^ 2) • x)
      (g (‖z‖ ^ 2) • ContinuousLinearMap.id ℝ E + (2 * g') • (innerSL ℝ z).smulRight z) z := by
  have hn : HasFDerivAt (fun x : E ↦ g (‖x‖ ^ 2)) (g' • (2 • innerSL ℝ z)) z :=
    hg.comp_hasFDerivAt z (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  refine (hn.smul (hasFDerivAt_id z)).congr_fderiv ?_
  ext v
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, id_eq, smul_smul]
  ring_nf

/-- **Area scaling of `v ↦ a v + b ⟪z, v⟫ z`.** On the complex line, the real-linear map
`v ↦ a v + b ⟪z, v⟫ z` scales the standard area form by `a (a + b ‖z‖²)`. -/
theorem stdComplexSymplecticForm_smul_add_inner_smul (a b : ℝ) (z v w : ℂ) :
    stdComplexSymplecticForm (a • v + (b * ⟪z, v⟫) • z) (a • w + (b * ⟪z, w⟫) • z) =
      a * (a + b * ‖z‖ ^ 2) * stdComplexSymplecticForm v w := by
  simp only [stdComplexSymplecticForm_apply, Complex.inner, Complex.add_re, Complex.add_im,
    Complex.smul_re, Complex.smul_im, smul_eq_mul, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

/-- **A radial map of `ℂ` scales the standard area form by `g(s) (g(s) + 2 s g'(s))`.** If `g` is
differentiable at `s = ‖z‖²` with derivative `g'`, the derivative at `z` of the map
`x ↦ g(‖x‖²) • x` multiplies the standard area form of `ℂ` by `g(s) (g(s) + 2 s g')`. -/
theorem stdComplexSymplecticForm_fderiv_smul_self {g : ℝ → ℝ} {g' : ℝ} {z : ℂ}
    (hg : HasDerivAt g g' (‖z‖ ^ 2)) (v w : ℂ) :
    stdComplexSymplecticForm (fderiv ℝ (fun x : ℂ ↦ g (‖x‖ ^ 2) • x) z v)
        (fderiv ℝ (fun x : ℂ ↦ g (‖x‖ ^ 2) • x) z w) =
      g (‖z‖ ^ 2) * (g (‖z‖ ^ 2) + 2 * ‖z‖ ^ 2 * g') * stdComplexSymplecticForm v w := by
  rw [(hasFDerivAt_smul_self_of_hasDerivAt_sq_norm hg).fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul]
  refine (stdComplexSymplecticForm_smul_add_inner_smul _ _ z v w).trans ?_
  ring

end TauCeti
