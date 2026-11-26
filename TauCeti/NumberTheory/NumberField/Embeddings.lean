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
matrices.

## Main declarations

* `TauCeti.NumberField.ringHomEquivAlgHomAlgebraicClosure`: the equivalence
  `(K →+* F) ≃ (K →ₐ[ℚ] AlgebraicClosure F)`.
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
