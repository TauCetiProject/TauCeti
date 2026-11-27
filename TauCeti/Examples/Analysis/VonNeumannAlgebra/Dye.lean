/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Basic.Complex.Basic
import TauCeti.Algebra.Star.Prod
import TauCeti.Algebra.Star.Projection.Equiv
import TauCeti.LinearAlgebra.Matrix.StarProjection.Transpose

/-!
# Finite examples of projection orthogonality symmetries

Transposition on finite complex matrices and coordinate exchange on `ℂ × ℂ` preserve
star projections and their orthogonality. In `ℂ × ℂ` the only projections are zero, one,
and the two coordinate projections. The swap interchanges the coordinate projections and
extends to a complex-linear star algebra automorphism.

These are concrete projection orthoisomorphisms in the sense of Hamhalter,
*Dye’s theorem and Gleason’s theorem for AW*-algebras* (2015), §4.
-/

open scoped Matrix

example {n : Type*} [Fintype n] :
    ∃ e : Equiv.Perm {p : Matrix n n ℂ // IsStarProjection p},
      (∀ p, (e p).val = p.valᵀ) ∧
        ∀ p q, p.val * q.val = 0 ↔ (e p).val * (e q).val = 0 := by
  refine ⟨Matrix.transposeStarProjection n ℂ, Matrix.transposeStarProjection_apply, ?_⟩
  intro p q
  rw [Matrix.transposeStarProjection_apply, Matrix.transposeStarProjection_apply]
  exact (Matrix.transpose_mul_eq_zero_iff_of_isSelfAdjoint _ _
    p.property.isSelfAdjoint q.property.isSelfAdjoint).symm

example (x : ℂ × ℂ) :
    IsStarProjection x ↔ x = 0 ∨ x = (1, 0) ∨ x = (0, 1) ∨ x = 1 :=
  x.isStarProjection_iff_eq_zero_or_one

example :
    ∃ (e : Equiv.Perm {p : ℂ × ℂ // IsStarProjection p})
      (φ : ℂ × ℂ ≃⋆ₐ[ℂ] ℂ × ℂ),
      (∀ x, φ x = (RingEquiv.prodComm : ℂ × ℂ ≃+* ℂ × ℂ) x) ∧
        (∀ p, (e p).val = φ p.val) ∧
          ∀ p q, p.val * q.val = 0 ↔ (e p).val * (e q).val = 0 := by
  let φ : ℂ × ℂ ≃⋆ₐ[ℂ] ℂ × ℂ := StarAlgEquiv.prodComm ℂ
  refine ⟨φ.starProjectionCongr, φ,
    fun x ↦ by simp only [φ, StarAlgEquiv.prodComm_apply, RingEquiv.coe_prodComm],
    φ.starProjectionCongr_apply, fun p q ↦ (φ.starProjectionCongr_mul_eq_zero_iff p q).symm⟩
