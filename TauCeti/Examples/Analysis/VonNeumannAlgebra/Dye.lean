/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import TauCeti.Algebra.Star.Prod
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
open TauCeti

example {n : Type*} [Fintype n] :
    ∃ e : Equiv.Perm {p : Matrix n n ℂ // IsStarProjection p},
      (∀ p, (e p).val = p.valᵀ) ∧
        ∀ p q, p.val * q.val = 0 ↔ (e p).val * (e q).val = 0 := by
  let e := matrixTransposeStarProjection n ℂ
  refine ⟨e, matrixTransposeStarProjection_apply, ?_⟩
  intro p q
  rw [← p.property.isSelfAdjoint.isStarOrtho_iff_mul_eq_zero q.property.isSelfAdjoint,
    ← (e p).property.isSelfAdjoint.isStarOrtho_iff_mul_eq_zero (e q).property.isSelfAdjoint]
  simp only [e, matrixTransposeStarProjection_apply, Matrix.isStarOrtho_transpose_iff]

/-- The star projections of `ℂ × ℂ` are zero, one, and the two coordinate projections. -/
public theorem Prod.isStarProjection_complex_prod_iff (x : ℂ × ℂ) :
    IsStarProjection x ↔ x = 0 ∨ x = (1, 0) ∨ x = (0, 1) ∨ x = 1 := by
  rw [Prod.isStarProjection_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    have h₁' := IsIdempotentElem.iff_eq_zero_or_one.mp h₁.isIdempotentElem
    have h₂' := IsIdempotentElem.iff_eq_zero_or_one.mp h₂.isIdempotentElem
    simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, Prod.fst_one, Prod.snd_one]
    tauto
  · rintro (rfl | rfl | rfl | rfl) <;> simp

example :
    ∃ (e : Equiv.Perm {p : ℂ × ℂ // IsStarProjection p})
      (φ : ℂ × ℂ ≃⋆ₐ[ℂ] ℂ × ℂ),
      (∀ x, φ x = (RingEquiv.prodComm : ℂ × ℂ ≃+* ℂ × ℂ) x) ∧
        (∀ p, (e p).val = φ p.val) ∧
          ∀ p q, p.val * q.val = 0 ↔ (e p).val * (e q).val = 0 := by
  let φ : ℂ × ℂ ≃⋆ₐ[ℂ] ℂ × ℂ := starAlgProdComm ℂ
  refine ⟨φ.starProjectionCongr, φ,
    fun x ↦ by simp only [φ, starAlgProdComm_apply, RingEquiv.coe_prodComm],
    φ.starProjectionCongr_apply, ?_⟩
  intro p q
  symm
  simp only [StarAlgEquiv.starProjectionCongr_apply, ← map_mul, map_eq_zero_iff φ φ.injective]
