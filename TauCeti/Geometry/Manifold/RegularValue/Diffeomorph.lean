/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Geometry.Manifold.RegularValue

/-!
# Regular points and regular values under diffeomorphisms

Postcomposing an arbitrary map `f` between manifolds with a `C^n` diffeomorphism (`n ≠ 0`)
preserves regular points and regular values without any differentiability assumption on `f`.
(Precomposition is in `TauCeti.Geometry.Manifold.RegularValue`.)

## Main results

* `Diffeomorph.isRegularPoint`, `Diffeomorph.isRegularValue`: every point and value of a `C^n`
  diffeomorphism (`n ≠ 0`) is regular.
* `Diffeomorph.isRegularPoint_diffeomorph_comp_iff`: invariance of regular points under
  postcomposition with a diffeomorphism.
* `Diffeomorph.isRegularValue_diffeomorph_comp_apply_iff`,
  `Diffeomorph.isRegularValue_diffeomorph_comp_iff`: invariance of regular values under
  postcomposition with a diffeomorphism.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 4 (regular points and values).
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5.
-/

public section

open Function Set
open scoped ContDiff Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 G H''}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  {n : ℕ∞ω}

namespace Diffeomorph

/-- Every point is a regular point of a `C^n` diffeomorphism (`n ≠ 0`). -/
theorem isRegularPoint (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (x : M) :
    TauCeti.IsRegularPoint I J h x :=
  TauCeti.isRegularPoint_iff.2 (h.isInvertible_mfderiv hn).surjective

/-- Every value is a regular value of a `C^n` diffeomorphism (`n ≠ 0`). -/
theorem isRegularValue (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (y : N) :
    TauCeti.IsRegularValue I J h y :=
  TauCeti.isRegularValue_iff.2 fun x _ ↦ h.isRegularPoint hn x

/-- Postcomposing with a `C^n` diffeomorphism (`n ≠ 0`) preserves regular points, with no
differentiability assumption on `f`. -/
@[simp]
theorem isRegularPoint_diffeomorph_comp_iff (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (f : P → M) (x : P) :
    TauCeti.IsRegularPoint K J (h ∘ f) x ↔ TauCeti.IsRegularPoint K I f x := by
  rw [TauCeti.isRegularPoint_iff, TauCeti.isRegularPoint_iff, h.mfderiv_diffeomorph_comp hn,
    ← h.mfderivToContinuousLinearEquiv_coe hn, ContinuousLinearMap.coe_comp,
    ContinuousLinearEquiv.coe_coe]
  exact EquivLike.comp_surjective _ (h.mfderivToContinuousLinearEquiv hn (f x))

/-- Under postcomposition with a `C^n` diffeomorphism `h` (`n ≠ 0`), `h y` is a regular value of
`h ∘ f` if and only if `y` is a regular value of `f`. -/
@[simp]
theorem isRegularValue_diffeomorph_comp_apply_iff (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0)
    (f : P → M) (y : M) :
    TauCeti.IsRegularValue K J (h ∘ f) (h y) ↔ TauCeti.IsRegularValue K I f y := by
  simp only [TauCeti.isRegularValue_iff, Function.comp_apply, EquivLike.apply_eq_iff_eq h,
    h.isRegularPoint_diffeomorph_comp_iff hn]

/-- A point `z` of the target is a regular value of `h ∘ f`, for a `C^n` diffeomorphism `h`
(`n ≠ 0`), if and only if `h.symm z` is a regular value of `f`. -/
theorem isRegularValue_diffeomorph_comp_iff (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (f : P → M) (z : N) :
    TauCeti.IsRegularValue K J (h ∘ f) z ↔ TauCeti.IsRegularValue K I f (h.symm z) := by
  conv_lhs => rw [← h.apply_symm_apply z]
  exact h.isRegularValue_diffeomorph_comp_apply_iff hn f (h.symm z)

end Diffeomorph
