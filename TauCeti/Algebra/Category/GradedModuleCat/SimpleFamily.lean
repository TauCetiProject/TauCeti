/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Basic
public import TauCeti.CategoryTheory.Simple

/-!
# Exhaustive families of graded simple modules

A family is exhaustive up to internal shifts when every simple finite graded module is
isomorphic to a shift of a member. This property is used both to classify simple modules and
to construct their classes in the graded Grothendieck group.
-/

public section

namespace TauCeti

open CategoryTheory

universe uk uA uI

/-! ### Exhaustive families of graded simples -/

section Exhaustive

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} {I : Type uI}

/-- A family of finite graded modules is an **exhaustive family of graded simples up to shift** if
every finite graded module which is a simple object of the graded module category is isomorphic to
an internal shift `(S i){d}` of a member of the family. -/
def IsExhaustiveGradedSimpleFamily (S : I → (gradedFiniteModules 𝒜).FullSubcategory) : Prop :=
  ∀ M : (gradedFiniteModules 𝒜).FullSubcategory, Simple M.obj →
    ∃ i d, Nonempty (M.obj ≅ (S i).obj.shiftObj d)

/-- Characterization of `IsExhaustiveGradedSimpleFamily`, for importing modules, to which the body
of the definition is not exposed. -/
theorem isExhaustiveGradedSimpleFamily_iff (S : I → (gradedFiniteModules 𝒜).FullSubcategory) :
    IsExhaustiveGradedSimpleFamily S ↔
      ∀ M : (gradedFiniteModules 𝒜).FullSubcategory, Simple M.obj →
        ∃ i d, Nonempty (M.obj ≅ (S i).obj.shiftObj d) :=
  Iff.rfl

end Exhaustive

end TauCeti
