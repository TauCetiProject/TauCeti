/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Star.Prod
import Mathlib.Algebra.Star.StarRingHom
import Mathlib.Algebra.Star.Orthogonal
import TauCeti.Algebra.Group.Idempotent
import TauCeti.LinearAlgebra.Matrix.StarProjection

/-!
# Finite examples of projection orthogonality symmetries

Transposition on finite complex matrices and coordinate exchange on `ℂ × ℂ` preserve
star projections and their orthogonality. In `ℂ × ℂ` the only projections are zero, one,
and the two coordinate projections, which the swap interchanges.

These examples illustrate the hypothesis of Hamhalter, *Dye’s theorem and Gleason’s theorem
for AW*-algebras* (2015), Theorem 4.3.
-/

open scoped Matrix

example {n : Type*} [Fintype n] :
    ∃ e : Equiv.Perm {p : Matrix n n ℂ // IsStarProjection p},
      (∀ p, (e p).val = p.valᵀ) ∧
        ∀ p q, p.val * q.val = 0 ↔ (e p).val * (e q).val = 0 := by
  let e := (Matrix.transposeAddEquiv n n ℂ).toEquiv.subtypeEquiv
    (p := IsStarProjection) (q := IsStarProjection)
    fun p ↦ (Matrix.isStarProjection_transpose_iff (p := p)).symm
  refine ⟨e, fun _ ↦ rfl, ?_⟩
  intro p q
  rw [← p.property.isSelfAdjoint.isStarOrtho_iff_mul_eq_zero q.property.isSelfAdjoint,
    ← (e p).property.isSelfAdjoint.isStarOrtho_iff_mul_eq_zero (e q).property.isSelfAdjoint]
  exact Matrix.isStarOrtho_transpose_iff.symm

namespace TauCeti.DyeExamples

/-- The idempotents of `ℂ × ℂ` are zero, one, and the two coordinate projections. -/
public theorem complexProd_isIdempotentElem_iff {x : ℂ × ℂ} :
    IsIdempotentElem x ↔ x = 0 ∨ x = (1, 0) ∨ x = (0, 1) ∨ x = 1 := by
  simp only [Prod.isIdempotentElem_iff, IsIdempotentElem.iff_eq_zero_or_one, Prod.ext_iff,
    Prod.fst_zero, Prod.snd_zero, Prod.fst_one, Prod.snd_one]
  tauto

example {x : ℂ × ℂ} :
    IsStarProjection x ↔ x = 0 ∨ x = (1, 0) ∨ x = (0, 1) ∨ x = 1 := by
  refine ⟨fun h ↦ complexProd_isIdempotentElem_iff.mp h.isIdempotentElem, ?_⟩
  rintro (rfl | rfl | rfl | rfl) <;> simp [isStarProjection_iff', Prod.ext_iff]

end TauCeti.DyeExamples

example : ∃ φ : ℂ × ℂ ≃⋆+* ℂ × ℂ, ∀ x, φ x = x.swap :=
  ⟨{ RingEquiv.prodComm with map_star' := fun _ ↦ rfl }, fun _ ↦ rfl⟩

example (p q : ℂ × ℂ) : IsStarOrtho p.swap q.swap ↔ IsStarOrtho p q := by
  simp only [IsStarOrtho.prod_iff, Prod.fst_swap, Prod.snd_swap, and_comm]
