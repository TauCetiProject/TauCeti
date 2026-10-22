/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.SingleObj

/-!
# Prelax functors out of locally discrete bicategories

In a locally discrete bicategory every `2`-morphism `η : f ⟶ g` forces `f = g`, so a prelax
functor (in particular a pseudofunctor) sends `η` to an `eqToHom`. This lets the coherence
data of a pseudofunctor out of `LocallyDiscrete B₀`, such as `F.map₂ (α_ f g h).hom`, be
computed componentwise.

We also define `Pseudofunctor.restrictFiber`, the restriction of a pseudofunctor out of
`LocallyDiscrete (Γ × SingleObj H)` to the fiber `{p} × SingleObj H`.
-/

@[expose] public section

namespace CategoryTheory.PrelaxFunctor

open Bicategory

/-- A prelax functor out of a locally discrete bicategory sends every `2`-morphism to an
`eqToHom`. -/
lemma map₂_eq_eqToHom {B C : Type*} [Bicategory B] [IsLocallyDiscrete B] [Bicategory C]
    (F : PrelaxFunctor B C) {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    F.map₂ η = eqToHom (by rw [obj_ext_of_isDiscrete η]) := by
  obtain rfl := obj_ext_of_isDiscrete η
  rw [Subsingleton.elim η (𝟙 f)]
  simp

end CategoryTheory.PrelaxFunctor

namespace CategoryTheory.Pseudofunctor

open Bicategory

variable {Γ : Type*} [Category Γ] {H : Type*} [Monoid H]

/-- The restriction of a pseudofunctor `F` out of `LocallyDiscrete (Γ × SingleObj H)` to the
fiber `{p} × SingleObj H`, that is, its composite with `Prod.sectR p (SingleObj H)`. Its value
at the unique object is `F.obj ⟨(p, ⋆)⟩` and its value at `a : H` is `F.map (𝟙 p, a)`. -/
abbrev restrictFiber {B : Type*} [Bicategory B] (F : LocallyDiscrete (Γ × SingleObj H) ⥤ᵖ B)
    (p : Γ) : LocallyDiscrete (SingleObj H) ⥤ᵖ B :=
  (Prod.sectR p (SingleObj H)).toPseudofunctor.comp F

end CategoryTheory.Pseudofunctor
