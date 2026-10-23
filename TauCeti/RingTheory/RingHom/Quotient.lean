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
of `f`. Hence it inherits every ring-homomorphism property stable under base change and
isomorphism. This applies, in particular, to faithful flatness and finite presentation.
-/

public section

open scoped TensorProduct

namespace RingHom.IsStableUnderBaseChange

universe u

/-- A property stable under base change and isomorphism passes from `f : A →+* B` to
`A/I → B/IB`. -/
theorem quotientMap
    {P : ∀ {A B : Type u} [CommRing A] [CommRing B], (A →+* B) → Prop}
    (hP : RingHom.IsStableUnderBaseChange P) (hiso : RingHom.RespectsIso P)
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (hf : P f) :
    P (Ideal.quotientMap (I.map f) f Ideal.le_comap_map) := by
  let := f.toAlgebra
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I
  have h := hiso.left (algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] B)) e.symm.toRingEquiv
    (hP.tensorProduct (A ⧸ I) hf)
  have he : Ideal.quotientMap (I.map f) f Ideal.le_comap_map =
      e.symm.toRingEquiv.toRingHom.comp (algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] B)) := by
    ext a
    -- The quotient algebra structure is induced by this very quotient map.
    exact (e.symm.commutes (Ideal.Quotient.mk I a)).symm
  exact he ▸ h

end RingHom.IsStableUnderBaseChange
