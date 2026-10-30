/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Endomorphism rings under fully faithful additive functors

A fully faithful functor `F` gives Mathlib's monoid isomorphism
`CategoryTheory.Functor.FullyFaithful.mulEquivEnd : End X ≃* End (F.obj X)`. When `F` is additive
between preadditive categories, it is a ring isomorphism
(`CategoryTheory.Functor.FullyFaithful.ringEquivEnd`). This transports ring-theoretic properties of
endomorphism rings, such as being local or Artinian, along the inclusion of a full subcategory or
along an equivalence.
-/

public section

namespace CategoryTheory.Functor.FullyFaithful

variable {C : Type*} {D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  {F : C ⥤ D} [F.Additive] (hF : F.FullyFaithful)

/-- A fully faithful additive functor `F` induces a ring isomorphism `End X ≃+* End (F.obj X)`, the
additive version of `CategoryTheory.Functor.FullyFaithful.mulEquivEnd`. -/
noncomputable def ringEquivEnd (X : C) : End X ≃+* End (F.obj X) :=
  { hF.mulEquivEnd X with map_add' := fun _ _ ↦ End.ext F.map_add }

@[simp]
theorem ringEquivEnd_apply_asHom (X : C) (f : End X) :
    (hF.ringEquivEnd X f).asHom = F.map f.asHom :=
  (rfl)

@[simp]
theorem ringEquivEnd_symm_apply_asHom (X : C) (g : End (F.obj X)) :
    ((hF.ringEquivEnd X).symm g).asHom = hF.preimage g.asHom :=
  (rfl)

end CategoryTheory.Functor.FullyFaithful
