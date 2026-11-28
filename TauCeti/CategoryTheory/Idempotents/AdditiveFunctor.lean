/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Idempotents.FunctorExtension
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import TauCeti.CategoryTheory.Preadditive.AdditiveFunctor.Restriction

/-!
# Additive functors on the Karoubi envelope

If `E` is idempotent complete, restriction along `toKaroubi C` induces an equivalence on
additive functors with values in `E`. The same holds for contravariant additive functors.
In particular, modules on a preadditive category and on its Karoubi envelope are equivalent by
restriction, in any value universe. The equivalence is
`((toKaroubi C).op.additiveWhiskeringLeft AddCommGrpCat).asEquivalence`.

This is the additive and contravariant form of Mathlib's `Idempotents.karoubiUniversal`.
See B. Mitchell, *Rings with several objects*, §1, pp. 11–12.
-/

public section

namespace CategoryTheory.Idempotents

open CategoryTheory.Functor Opposite

variable (C : Type*) [Category* C] (E : Type*) [Category* E] [IsIdempotentComplete E]

private theorem isEquivalence_whiskeringLeft_toKaroubi_op :
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

variable [Preadditive C] [Preadditive E]

/-- Restriction from the Karoubi envelope is an equivalence on additive functors to an
idempotent-complete preadditive category. -/
instance : ((toKaroubi C).additiveWhiskeringLeft E).IsEquivalence :=
  (toKaroubi C).isEquivalence_additiveWhiskeringLeft_of_retract
    (fun X ↦ ⟨X.X, ⟨X.retract⟩⟩)

/-- Restriction from the Karoubi envelope is an equivalence on contravariant additive functors
to an idempotent-complete preadditive category. -/
instance : ((toKaroubi C).op.additiveWhiskeringLeft E).IsEquivalence := by
  let := isEquivalence_whiskeringLeft_toKaroubi_op C E
  exact (toKaroubi C).op.isEquivalence_additiveWhiskeringLeft_of_retract
    (fun X ↦ ⟨op X.unop.X, ⟨X.unop.retract.op⟩⟩)

end CategoryTheory.Idempotents
