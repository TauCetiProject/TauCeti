/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# The closed monoidal category of presheaves of modules

Let `R₀` be a presheaf of commutative rings on a small category. This file makes presheaves of
`R₀`-modules into a closed monoidal category. Tensoring presheaves of modules preserves small
colimits, and the free modules on representables form a small separating family, so the special
adjoint functor theorem gives a right adjoint to tensoring by each presheaf of modules.

## Main declarations

* `TauCeti.PresheafOfModules.monoidalClosed` gives the closed structure on presheaves of modules
  over a presheaf of commutative rings.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

universe u

noncomputable section

namespace PresheafOfModules

variable {C : Type u} [SmallCategory C] (R₀ : Cᵒᵖ ⥤ CommRingCat.{u})

/-- The closed monoidal structure on presheaves of modules over a presheaf of commutative rings.
Its internal Hom is the right adjoint supplied by the special adjoint functor theorem. -/
instance monoidalClosed : MonoidalClosed (PresheafOfModules.{u} (R₀ ⋙ forget₂ _ RingCat)) where
  closed M :=
    letI := isLeftAdjoint_of_preservesColimits_of_isSeparating.{u}
      (_root_.PresheafOfModules.freeYoneda.isSeparating (R₀ ⋙ forget₂ _ RingCat)) (tensorLeft M)
    { rightAdj := (tensorLeft M).rightAdjoint
      adj := Adjunction.ofIsLeftAdjoint (tensorLeft M) }

end PresheafOfModules

end

end TauCeti
