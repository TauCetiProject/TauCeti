/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Idempotents.FunctorExtension

/-!
# Contravariant functors on the Karoubi envelope

Restriction along `(toKaroubi C).op` gives an equivalence for contravariant functors into an
idempotent-complete category `E`. By `Functor.leftOpRightOpEquiv`, this is the covariant
universal property `Idempotents.karoubiUniversal` applied to `Eᵒᵖ`.
-/

public section

namespace CategoryTheory.Idempotents

open CategoryTheory.Functor Opposite

variable (C : Type*) [Category* C] (E : Type*) [Category* E] [IsIdempotentComplete E]

/-- Restriction from the Karoubi envelope is an equivalence on contravariant functors
to an idempotent-complete category. -/
instance isEquivalence_whiskeringLeft_toKaroubi_op :
    ((whiskeringLeft Cᵒᵖ (Karoubi C)ᵒᵖ E).obj (toKaroubi C).op).IsEquivalence := by
  let restrictOp := (whiskeringLeft Cᵒᵖ (Karoubi C)ᵒᵖ E).obj (toKaroubi C).op
  let restrict := (whiskeringLeft C (Karoubi C) Eᵒᵖ).obj (toKaroubi C)
  -- Turn contravariant functors to `E` into covariant functors to `Eᵒᵖ`.
  have h : restrictOp.op ⋙ (leftOpRightOpEquiv C E).functor =
      (leftOpRightOpEquiv (Karoubi C) E).functor ⋙ restrict := rfl
  have : restrict.IsEquivalence := inferInstanceAs
    ((whiskeringLeft C (Karoubi C) Eᵒᵖ).obj (toKaroubi C)).IsEquivalence
  have : (restrictOp.op ⋙ (leftOpRightOpEquiv C E).functor).IsEquivalence := by
    rw [h]
    infer_instance
  let := isEquivalence_of_comp_right restrictOp.op (leftOpRightOpEquiv C E).functor
  exact restrictOp.op.asEquivalence.unop.isEquivalence_functor

end CategoryTheory.Idempotents
