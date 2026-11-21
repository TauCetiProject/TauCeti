/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Star.Prod
import Mathlib.Algebra.Star.Orthogonal
import TauCeti.Algebra.Group.Idempotent
import TauCeti.LinearAlgebra.Matrix.StarProjection

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
  let e := (Matrix.transposeAddEquiv n n ℂ).toEquiv.subtypeEquiv
    (p := IsStarProjection) (q := IsStarProjection)
    fun p ↦ (Matrix.isStarProjection_transpose_iff (p := p)).symm
  refine ⟨e, fun _ ↦ rfl, ?_⟩
  intro p q
  rw [← p.property.isSelfAdjoint.isStarOrtho_iff_mul_eq_zero q.property.isSelfAdjoint,
    ← (e p).property.isSelfAdjoint.isStarOrtho_iff_mul_eq_zero (e q).property.isSelfAdjoint]
  exact Matrix.isStarOrtho_transpose_iff.symm

example {x : ℂ × ℂ} :
    IsStarProjection x ↔ x = 0 ∨ x = (1, 0) ∨ x = (0, 1) ∨ x = 1 := by
  constructor
  · intro h
    have hIdem := h.isIdempotentElem
    simp only [Prod.isIdempotentElem_iff, IsIdempotentElem.iff_eq_zero_or_one] at hIdem
    simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, Prod.fst_one, Prod.snd_one]
    tauto
  · rintro (rfl | rfl | rfl | rfl) <;> simp [isStarProjection_iff', Prod.ext_iff]

example :
    ∃ (e : Equiv.Perm {p : ℂ × ℂ // IsStarProjection p})
      (φ : ℂ × ℂ ≃⋆ₐ[ℂ] ℂ × ℂ),
      (∀ x, φ x = x.swap) ∧ (∀ p, (e p).val = φ p.val) ∧
        ∀ p q, p.val * q.val = 0 ↔ (e p).val * (e q).val = 0 := by
  let φ : ℂ × ℂ ≃⋆ₐ[ℂ] ℂ × ℂ :=
    { RingEquiv.prodComm with map_star' := fun _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  let e := φ.toEquiv.subtypeEquiv (p := IsStarProjection) (q := IsStarProjection) fun p ↦
    ⟨fun hp ↦ hp.map φ, fun hp ↦ by
      have hφ : IsStarProjection (φ p) := hp
      simpa only [StarAlgEquiv.symm_apply_apply] using hφ.map φ.symm⟩
  have hExt (p : {p : ℂ × ℂ // IsStarProjection p}) : (e p).val = φ p.val := rfl
  refine ⟨e, φ, fun _ ↦ rfl, hExt, fun p q ↦ ?_⟩
  simp only [hExt, ← map_mul, map_eq_zero_iff φ φ.injective]
