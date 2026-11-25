/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.ModelSpace
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville
public import TauCeti.Geometry.Symplectic.StandardCompatible

/-!
# The canonical symplectic form of the cotangent bundle of a normed space

Let `E` be a finite-dimensional real normed space. Its cotangent bundle is globally the product
`E × (E →L[ℝ] ℝ)`, through the diffeomorphism `(q, p) ↦ (q, p)`
(`TauCeti.CotangentBundle.modelSpaceDiffeomorph`). This file shows that in these global coordinates
the canonical symplectic form `ω = -dλ` of `T*E` is the constant linear form

`ω((δq, δp), (δq', δp')) = δp'(δq) - δp(δq')`,

that is `Σ dqᵢ ∧ dpᵢ` (`TauCeti.strongDualCotangentSymplecticForm`):
`TauCeti.CotangentBundle.mpullback_modelSpaceDiffeomorph_constSmooth`. So `T*E` is
symplectomorphic to the symplectic vector space `E × E*`, with no change of sign.

For the line, the further identification `p ↦ p 1` of a covector with its value on the unit vector
gives the diffeomorphism `T*ℝ ≃ ℝ × ℝ`, `(q, p) ↦ (q, p 1)`
(`TauCeti.CotangentBundle.lineDiffeomorph`), and it carries `ω` to the standard area form
`dq ∧ dp` of the plane, `(a, b), (a', b') ↦ a b' - b a'`
(`TauCeti.CotangentBundle.mpullback_lineDiffeomorph_constSmooth`). This is the global form of the
coordinate plane `(t, e)` of a time and its conjugate momentum in the extended phase space of
time-dependent mechanics.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 2.
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti.CotangentBundle

/-- **The cotangent bundle of a normed space is a symplectic vector space.** The global
coordinates `T*E ≃ E × (E →L[ℝ] ℝ)` pull the constant linear form
`((δq, δp), (δq', δp')) ↦ δp'(δq) - δp(δq')` back to the canonical symplectic form `ω = -dλ`. -/
@[simp]
theorem mpullback_modelSpaceDiffeomorph_constSmooth (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    SmoothForm.mpullback (modelSpaceDiffeomorph E) (modelSpaceDiffeomorph E).contMDiff
        (strongDualCotangentSymplecticForm (V := E)).constSmooth =
      symplecticForm 𝓘(ℝ, E) E := by
  refine SmoothBundleForm.ext_eval₂ fun z v w ↦ ?_
  rw [SmoothForm.eval₂_mpullback, mfderiv_modelSpaceDiffeomorph,
    SymplecticForm.fromTangentSpace_constSmooth_apply, eval₂_symplecticForm,
    NormedSpace.fromTangentSpace_apply, NormedSpace.fromTangentSpace_apply]
  -- Both sides evaluate the linear form on the coordinate vectors `v` and `w`.
  exact congrArg₂ (fun a b ↦ strongDualCotangentSymplecticForm a b)
    (ContinuousLinearMap.id_apply v) (ContinuousLinearMap.id_apply w)

/-- On the line, the linear cotangent form is the standard area form in the coordinates
`(q, p 1)`: a covector `p` is multiplication by `p 1`. -/
private theorem stdSymplecticForm_apply_one (v w : ℝ × (ℝ →L[ℝ] ℝ)) :
    stdSymplecticForm (V := ℝ) (v.1, v.2 1) (w.1, w.2 1) =
      strongDualCotangentSymplecticForm (V := ℝ) v w := by
  have hv : w.2 v.1 = v.1 * w.2 1 := by rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  have hw : v.2 w.1 = w.1 * v.2 1 := by rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  simp only [stdSymplecticForm_apply, strongDualCotangentSymplecticForm_apply, RCLike.inner_apply,
    conj_trivial, hv, hw]
  ring

/-- **The cotangent bundle of the line is the symplectic plane.** The global coordinates
`T*ℝ ≃ ℝ × ℝ`, `(q, p) ↦ (q, p 1)`, pull the standard area form `dq ∧ dp` of the plane back to
the canonical symplectic form `ω = -dλ`. -/
@[simp]
theorem mpullback_lineDiffeomorph_constSmooth :
    SmoothForm.mpullback (lineDiffeomorph ℝ) (lineDiffeomorph ℝ).contMDiff
        (stdSymplecticForm (V := ℝ)).constSmooth =
      symplecticForm 𝓘(ℝ) ℝ := by
  refine SmoothBundleForm.ext_eval₂ fun z v w ↦ ?_
  rw [SmoothForm.eval₂_mpullback, mfderiv_lineDiffeomorph_apply ℝ z v,
    mfderiv_lineDiffeomorph_apply ℝ z w]
  -- Tangent vectors of `T*ℝ` and of the plane are their own coordinate vectors.
  exact ((SymplecticForm.constSmooth_apply _ _ _ _).trans (stdSymplecticForm_apply_one v w)).trans
    (eval₂_symplecticForm z v w).symm

end TauCeti.CotangentBundle
