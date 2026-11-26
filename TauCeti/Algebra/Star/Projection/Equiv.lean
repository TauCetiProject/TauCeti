/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.StarProjection

/-!
# Star algebra equivalences on star projections

A star algebra equivalence restricts to an equivalence of the subtypes of star projections.
Its restriction preserves and reflects zero products over nonunital nonassociative semirings.
-/

public section

namespace StarAlgEquiv

section

variable {R A B : Type*} [Add A] [Mul A] [Star A] [SMul R A]
  [Add B] [Mul B] [Star B] [SMul R B]

/-- Forgetting the algebraic structure of a star algebra equivalence leaves its action unchanged. -/
theorem toEquiv_apply (φ : A ≃⋆ₐ[R] B) (a : A) : φ.toEquiv a = φ a := (rfl)

/-- Restrict a star algebra equivalence to the star projections of its domain and codomain. -/
def starProjectionCongr (φ : A ≃⋆ₐ[R] B) :
    {p : A // IsStarProjection p} ≃ {q : B // IsStarProjection q} :=
  φ.toEquiv.subtypeEquiv fun p ↦ by
    rw [toEquiv_apply]
    exact ⟨fun hp ↦ hp.map φ, fun hp ↦ by
      simpa only [symm_apply_apply] using hp.map φ.symm⟩

/-- The restriction acts by the original equivalence on the underlying elements. -/
@[simp]
theorem starProjectionCongr_apply (φ : A ≃⋆ₐ[R] B) (p : {p : A // IsStarProjection p}) :
    (φ.starProjectionCongr p).val = φ p.val := by
  simp only [starProjectionCongr, Equiv.subtypeEquiv_apply, toEquiv_apply]

/-- The inverse restriction acts by the inverse star algebra equivalence. -/
@[simp]
theorem starProjectionCongr_symm_apply (φ : A ≃⋆ₐ[R] B) (q : {q : B // IsStarProjection q}) :
    (φ.starProjectionCongr.symm q).val = φ.symm q.val := by
  apply φ.eq_symm_apply.mpr
  rw [← starProjectionCongr_apply, Equiv.apply_symm_apply]

end

/-- A star algebra equivalence of nonunital nonassociative semirings preserves and reflects zero
products of projections. -/
theorem starProjectionCongr_mul_eq_zero_iff {R A B : Type*}
    [NonUnitalNonAssocSemiring A] [Star A] [SMul R A]
    [NonUnitalNonAssocSemiring B] [Star B] [SMul R B]
    (φ : A ≃⋆ₐ[R] B) (p q : {x : A // IsStarProjection x}) :
    (φ.starProjectionCongr p).val * (φ.starProjectionCongr q).val = 0 ↔ p.val * q.val = 0 := by
  simp only [starProjectionCongr_apply, ← map_mul, map_eq_zero_iff φ φ.injective]

end StarAlgEquiv
