/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Transporting embeddings of a number field to an algebraic closure

Let `F` be a field of characteristic zero receiving all `[K : ℚ]` embeddings of a number field
`K`. Composing with `F → AlgebraicClosure F` then matches the embeddings `K →+* F` with the
`ℚ`-algebra maps `K →ₐ[ℚ] AlgebraicClosure F`, the indexing used by Mathlib's embeddings
matrices. For an algebraic extension of `ℚ`, composing with an embedding of the algebraic
closure of `ℚ` into `ℂ` likewise identifies the embeddings into that closure with the complex
embeddings.

## Main declarations

* `TauCeti.NumberField.ringHomEquivAlgHomAlgebraicClosure`: the equivalence
  `(K →+* F) ≃ (K →ₐ[ℚ] AlgebraicClosure F)`.
* `RingHom.complexEmbeddingsEquiv`: the equivalence `(K →+* AlgebraicClosure ℚ) ≃ (K →+* ℂ)`.
-/

public section

open Module

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {F : Type*} [Field F] [CharZero F]

/-- When `F` receives all `[K : ℚ]` embeddings of `K`, composing with `F → AlgebraicClosure F`
matches the embeddings `K →+* F` with the `ℚ`-algebra maps `K →ₐ[ℚ] AlgebraicClosure F`. -/
noncomputable def ringHomEquivAlgHomAlgebraicClosure
    (hF : Fintype.card (K →+* F) = finrank ℚ K) :
    (K →+* F) ≃ (K →ₐ[ℚ] AlgebraicClosure F) :=
  Equiv.ofBijective (fun σ ↦ RingHom.equivRatAlgHom K _ ((algebraMap F _).comp σ)) <|
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun σ τ h ↦ RingHom.ext fun x ↦ (algebraMap F (AlgebraicClosure F)).injective <| by
        simpa [RingHom.equivRatAlgHom_apply] using DFunLike.congr_fun h x,
        by rw [hF, AlgHom.card]⟩

/-- `ringHomEquivAlgHomAlgebraicClosure hF σ` is `σ` followed by `F → AlgebraicClosure F`. -/
@[simp]
theorem ringHomEquivAlgHomAlgebraicClosure_apply
    (hF : Fintype.card (K →+* F) = finrank ℚ K) (σ : K →+* F) (x : K) :
    ringHomEquivAlgHomAlgebraicClosure hF σ x = algebraMap F (AlgebraicClosure F) (σ x) :=
  (rfl)

end TauCeti.NumberField

namespace RingHom

variable {K : Type*} [Field K] [CharZero K] [Algebra.IsAlgebraic ℚ K]

/-- Composing with an embedding of the algebraic closure of `ℚ` into `ℂ` gives all complex
embeddings of an algebraic extension of `ℚ`, each exactly once. -/
noncomputable def complexEmbeddingsEquiv (ι : AlgebraicClosure ℚ →+* ℂ) :
    (K →+* AlgebraicClosure ℚ) ≃ (K →+* ℂ) := by
  let := ι.toAlgebra
  let : IsScalarTower ℚ (AlgebraicClosure ℚ) ℂ := .of_algebraMap_eq fun _ ↦ by simp
  exact (RingHom.equivRatAlgHom K _).trans <|
    (Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits ℂ (AlgebraicClosure ℚ)
      (fun _ : K ↦ IsAlgClosed.splits _)).trans (RingHom.equivRatAlgHom K ℂ).symm

/-- The equivalence on complex embeddings acts by postcomposition. -/
@[simp]
theorem complexEmbeddingsEquiv_apply (ι : AlgebraicClosure ℚ →+* ℂ)
    (σ : K →+* AlgebraicClosure ℚ) :
    ι.complexEmbeddingsEquiv σ = ι.comp σ :=
  (rfl)

end RingHom
