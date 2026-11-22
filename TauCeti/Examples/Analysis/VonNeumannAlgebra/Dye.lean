/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Basic.Complex.Basic
public import TauCeti.Algebra.Star.Prod
import TauCeti.Algebra.Group.Idempotent
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
  exact ⟨Matrix.transposeStarProjection n ℂ, Matrix.transposeStarProjection_apply,
    fun p q ↦ (Matrix.transposeStarProjection_mul_eq_zero_iff p q).symm⟩

public section

namespace TauCeti

/-- The star projections of `ℂ × ℂ` are zero, one, and the two coordinate projections. -/
theorem isStarProjection_complex_prod_iff (x : ℂ × ℂ) :
    IsStarProjection x ↔ x = 0 ∨ x = (1, 0) ∨ x = (0, 1) ∨ x = 1 := by
  constructor
  · intro h
    have hIdem := h.isIdempotentElem
    simp only [Prod.isIdempotentElem_iff, IsIdempotentElem.iff_eq_zero_or_one] at hIdem
    simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, Prod.fst_one, Prod.snd_one]
    tauto
  · rintro (rfl | rfl | rfl | rfl) <;> simp [isStarProjection_iff', Prod.ext_iff]

/-- The coordinate swap permutes the star projections of `ℂ × ℂ`. -/
def complexProdSwapStarProjection : Equiv.Perm {p : ℂ × ℂ // IsStarProjection p} :=
  let φ : ℂ × ℂ ≃⋆ₐ[ℂ] ℂ × ℂ := StarAlgEquiv.prodComm ℂ
  φ.toEquiv.subtypeEquiv (p := IsStarProjection) (q := IsStarProjection) fun p ↦ by
    have hcoe : (⇑φ.toEquiv : ℂ × ℂ → ℂ × ℂ) = ⇑φ := rfl
    rw [hcoe]
    exact ⟨fun hp ↦ hp.map φ, fun hp ↦ by
      simpa only [StarAlgEquiv.symm_apply_apply] using hp.map φ.symm⟩

@[simp]
theorem complexProdSwapStarProjection_apply (p : {p : ℂ × ℂ // IsStarProjection p}) :
    (complexProdSwapStarProjection p).val =
      (StarAlgEquiv.prodComm ℂ : ℂ × ℂ ≃⋆ₐ[ℂ] ℂ × ℂ) p.val := by
  have hcoe (φ : ℂ × ℂ ≃⋆ₐ[ℂ] ℂ × ℂ) : (⇑φ.toEquiv : ℂ × ℂ → ℂ × ℂ) = ⇑φ := rfl
  simp only [complexProdSwapStarProjection, Equiv.subtypeEquiv_apply, hcoe]

/-- The coordinate swap preserves zero products of star projections in both directions. -/
theorem complexProdSwapStarProjection_mul_eq_zero_iff
    (p q : {p : ℂ × ℂ // IsStarProjection p}) :
    (complexProdSwapStarProjection p).val * (complexProdSwapStarProjection q).val = 0 ↔
      p.val * q.val = 0 := by
  simp only [complexProdSwapStarProjection_apply, ← map_mul,
    map_eq_zero_iff (StarAlgEquiv.prodComm ℂ) (StarAlgEquiv.prodComm ℂ).injective]

example :
    ∃ (e : Equiv.Perm {p : ℂ × ℂ // IsStarProjection p})
      (φ : ℂ × ℂ ≃⋆ₐ[ℂ] ℂ × ℂ),
      (∀ x, φ x = (RingEquiv.prodComm : ℂ × ℂ ≃+* ℂ × ℂ) x) ∧
        (∀ p, (e p).val = φ p.val) ∧
          ∀ p q, p.val * q.val = 0 ↔ (e p).val * (e q).val = 0 := by
  exact ⟨complexProdSwapStarProjection, StarAlgEquiv.prodComm ℂ,
    fun x ↦ by simp only [StarAlgEquiv.prodComm_apply, RingEquiv.coe_prodComm],
    complexProdSwapStarProjection_apply,
    fun p q ↦ (complexProdSwapStarProjection_mul_eq_zero_iff p q).symm⟩

end TauCeti
