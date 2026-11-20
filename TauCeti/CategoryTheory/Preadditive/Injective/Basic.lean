/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Injective objects are coseparating

In a category with enough injective objects, the injective objects form a coseparating family
(`TauCeti.isCoseparating_isInjective`): two morphisms `f g : X ⟶ Y` agreeing after every morphism
of `Y` into an injective object agree after the monomorphism `Injective.ι Y`, hence are equal.

In a balanced category, such as an abelian one, a coseparating family is codetecting
(`CategoryTheory.ObjectProperty.IsCoseparating.isCodetecting`). So a morphism `f : X ⟶ Y` is an
isomorphism as soon as precomposition with `f` is a bijection `(Y ⟶ I) → (X ⟶ I)` for every
injective `I`. For modules, where an injective module can serve as the coefficients of
cohomology, this turns a statement about cohomology with all injective coefficients into one about
homology, through the universal coefficient theorem for injective coefficients.
-/

public section

open CategoryTheory

namespace TauCeti

variable {C : Type*} [Category* C]

/-- **Injective objects are coseparating** in a category with enough injectives: morphisms into
injective objects tell morphisms apart. -/
theorem isCoseparating_isInjective [EnoughInjectives C] : (isInjective C).IsCoseparating :=
  fun _ Y _ _ h ↦ (cancel_mono (Injective.ι Y)).1 (h _ (Injective.injective_under Y) _)

end TauCeti
