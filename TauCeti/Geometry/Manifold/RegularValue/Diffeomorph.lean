/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Geometry.Manifold.RegularValue

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.ModelWithCorners.LinearEquiv

/-!
# Regular points and regular values under local diffeomorphisms and diffeomorphisms

Precomposing or postcomposing a map `f` between manifolds with a `C^n` diffeomorphism (`n ≠ 0`)
preserves regular points and regular values without any differentiability assumption on `f`, as
does precomposing with a `C^n` local diffeomorphism (surjective, for regular values) or changing
source model coordinates along a continuous linear equivalence.

## Main results

* `Diffeomorph.isRegularPoint`, `Diffeomorph.isRegularValue`: every point and value of a `C^n`
  diffeomorphism (`n ≠ 0`) is regular.
* `IsLocalDiffeomorphAt.isRegularPoint_comp_iff`, `IsLocalDiffeomorph.isRegularValue_comp_iff`,
  `Diffeomorph.isRegularPoint_comp_iff`, `Diffeomorph.isRegularValue_comp_iff`: invariance of
  regular points and regular values under precomposition with a `C^n` local diffeomorphism or
  diffeomorphism (`n ≠ 0`).
* `TauCeti.isRegularPoint_transContinuousLinearEquiv_left_iff`,
  `TauCeti.isRegularValue_transContinuousLinearEquiv_left_iff`: continuous linear changes of
  source model coordinates preserve regular points and regular values.
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

section Precomposition

open TauCeti

/-- Precomposing a map with a `C^n` local diffeomorphism at `x` (`n ≠ 0`) preserves regularity at
`x`. No manifold smoothness or finite-dimensionality assumption is needed. -/
theorem IsLocalDiffeomorphAt.isRegularPoint_comp_iff {φ : P → M} {f : M → N} {x : P}
    (hφ : IsLocalDiffeomorphAt K I n φ x) (hn : n ≠ 0) :
    IsRegularPoint K J (f ∘ φ) x ↔ IsRegularPoint I J f (φ x) := by
  by_cases hf : MDifferentiableAt I J f (φ x)
  · rw [isRegularPoint_iff, isRegularPoint_iff, _root_.mfderiv_comp x hf (hφ.mdifferentiableAt hn)]
    exact (hφ.isInvertible_mfderiv hn).surjective.of_comp_iff (mfderiv I J f (φ x))
  · have hcomp : ¬MDifferentiableAt K J (f ∘ φ) x :=
      (hφ.mdifferentiableAt_comp_iff hn).not.mpr hf
    simp [isRegularPoint_iff, mfderiv_zero_of_not_mdifferentiableAt hf,
      mfderiv_zero_of_not_mdifferentiableAt hcomp, Function.Surjective]

/-- Precomposing a map with a surjective `C^n` local diffeomorphism (`n ≠ 0`) preserves regular
values. -/
theorem IsLocalDiffeomorph.isRegularValue_comp_iff {φ : P → M} {f : M → N} {y : N}
    (hφ : IsLocalDiffeomorph K I n φ) (hsurj : Surjective φ) (hn : n ≠ 0) :
    IsRegularValue K J (f ∘ φ) y ↔ IsRegularValue I J f y := by
  rw [isRegularValue_iff, isRegularValue_iff]
  refine ⟨fun h z hz ↦ ?_, fun h x hx ↦ ((hφ x).isRegularPoint_comp_iff hn).2 (h (φ x) hx)⟩
  obtain ⟨x, rfl⟩ := hsurj z
  exact ((hφ x).isRegularPoint_comp_iff hn).1 (h x hz)

end Precomposition

namespace Diffeomorph

open TauCeti

/-- Every point is a regular point of a `C^n` diffeomorphism (`n ≠ 0`). -/
theorem isRegularPoint (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (x : M) :
    TauCeti.IsRegularPoint I J h x :=
  TauCeti.isRegularPoint_iff.2 (h.isInvertible_mfderiv hn).surjective

/-- Every value is a regular value of a `C^n` diffeomorphism (`n ≠ 0`). -/
theorem isRegularValue (h : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (y : N) :
    TauCeti.IsRegularValue I J h y :=
  TauCeti.isRegularValue_iff.2 fun x _ ↦ h.isRegularPoint hn x

/-- Precomposing a map with a `C^n` diffeomorphism (`n ≠ 0`) preserves regular points. No manifold
smoothness or finite-dimensionality assumption is needed. -/
theorem isRegularPoint_comp_iff (Φ : P ≃ₘ^n⟮K, I⟯ M) (hn : n ≠ 0)
    {f : M → N} {x : P} :
    IsRegularPoint K J (f ∘ Φ) x ↔ IsRegularPoint I J f (Φ x) :=
  (Φ.isLocalDiffeomorph x).isRegularPoint_comp_iff hn

/-- Precomposing a map with a `C^n` diffeomorphism (`n ≠ 0`) preserves regular values. -/
theorem isRegularValue_comp_iff (Φ : P ≃ₘ^n⟮K, I⟯ M) (hn : n ≠ 0)
    {f : M → N} {y : N} :
    IsRegularValue K J (f ∘ Φ) y ↔ IsRegularValue I J f y :=
  Φ.isLocalDiffeomorph.isRegularValue_comp_iff Φ.surjective hn

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

namespace TauCeti

/-- A continuous linear change of source model coordinates preserves regular points, including on
manifolds with boundary or corners. -/
@[simp]
theorem isRegularPoint_transContinuousLinearEquiv_left_iff (e : E ≃L[𝕜] F) {f : M → N} {x : M} :
    IsRegularPoint (I.transContinuousLinearEquiv e) J f x ↔ IsRegularPoint I J f x := by
  simpa only [e.coe_toTransContinuousLinearEquiv_symm I M, comp_id, id_eq] using
    (e.toTransContinuousLinearEquiv (n := 1) I M).symm.isRegularPoint_comp_iff
      one_ne_zero (J := J) (f := f) (x := x)

/-- A continuous linear change of source model coordinates preserves regular values, including on
manifolds with boundary or corners. -/
@[simp]
theorem isRegularValue_transContinuousLinearEquiv_left_iff (e : E ≃L[𝕜] F) {f : M → N} {y : N} :
    IsRegularValue (I.transContinuousLinearEquiv e) J f y ↔ IsRegularValue I J f y := by
  simpa only [e.coe_toTransContinuousLinearEquiv_symm I M, comp_id] using
    (e.toTransContinuousLinearEquiv (n := 1) I M).symm.isRegularValue_comp_iff
      one_ne_zero (J := J) (f := f) (y := y)

end TauCeti
