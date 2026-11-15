/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.RingHomProperties
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Base-change properties of induced quotient maps

For a ring homomorphism `f : A →+* B`, the induced map `A/I → B/IB` is a base change
of `f`. Hence it inherits every ring-homomorphism property stable under base change.
This applies, in particular, to faithful flatness and finite presentation.
-/

public section

open scoped TensorProduct

namespace RingHom.IsStableUnderBaseChange

universe u

/-- A property stable under base change passes from `f : A →+* B` to `A/I → B/IB`. -/
theorem quotientMap
    {P : ∀ {A B : Type u} [CommRing A] [CommRing B], (A →+* B) → Prop}
    (hP : RingHom.IsStableUnderBaseChange P)
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (hf : P f) :
    P (Ideal.quotientMap (I.map f) f Ideal.le_comap_map) := by
  algebraize [f]
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I
  let : Algebra B ((A ⧸ I) ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  have : Algebra.IsPushout A B (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
    (Algebra.IsPushout.of_equiv e.symm (by
      ext b
      exact e.symm_apply_eq.2
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk B I b).symm)).symm
  -- The quotient algebra structure on `B ⧸ I.map f` is induced by this very quotient map.
  exact hP A B (A ⧸ I) (B ⧸ I.map (algebraMap A B)) hf

end RingHom.IsStableUnderBaseChange
