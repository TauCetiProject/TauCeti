/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Algebraically closed fields

Supplements to Mathlib's `IsAlgClosed` API.

## Main results

* `IsAlgClosed.iff_algebraMap_surjective`: a field is algebraically closed if and only if the
  algebra map into an algebraically closed algebraic extension is surjective.
-/

public section

/-- A field `K` is algebraically closed if and only if the algebra map into an algebraically
closed algebraic extension `E` of `K` is surjective. -/
theorem IsAlgClosed.iff_algebraMap_surjective (K E : Type*) [Field K] [Field E] [Algebra K E]
    [IsAlgClosed E] [Algebra.IsAlgebraic K E] :
    IsAlgClosed K ↔ Function.Surjective (algebraMap K E) := by
  refine ⟨fun _ ↦ IsAlgClosed.algebraMap_bijective_of_isIntegral.2, fun h ↦ ?_⟩
  -- `IsAlgClosed.of_ringEquiv` requires both fields in the same universe, so we lift roots
  -- directly.
  refine IsAlgClosed.of_exists_root K fun p _ hp ↦ ?_
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero E p
    (Polynomial.degree_pos_of_irreducible hp).ne'
  obtain ⟨y, rfl⟩ := h x
  exact ⟨y, (algebraMap K E).injective (by simpa [Polynomial.aeval_algebraMap_apply] using hx)⟩

end
