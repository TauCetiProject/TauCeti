/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Translation on complexes of representations

An element of a monoid acts degreewise on the underlying module complex of a complex of
representations. The differentials are intertwining maps, so these actions are chain maps.
For a noncommutative monoid they need not be morphisms of representations.
-/

public section

open CategoryTheory

namespace HomologicalComplex

universe u v w t

variable {k : Type u} [Ring k] {G : Type v} [Monoid G] {ι : Type t}
  {c : ComplexShape ι} (C : HomologicalComplex (Rep.{w} k G) c)

/-- The degreewise action of a monoid element on the underlying complex of modules. -/
def repTranslation (g : G) :
    ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex c).obj C ⟶
      ((forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex c).obj C where
  f n := ModuleCat.ofHom ((C.X n).ρ g)
  comm' i j _ := ModuleCat.hom_ext ((C.d i j).hom.isIntertwining' g)

/-- The component of translation is the action on that degree's representation. -/
@[simp]
theorem repTranslation_f (g : G) (n : ι) :
    (C.repTranslation g).f n = ModuleCat.ofHom ((C.X n).ρ g) := (rfl)

end HomologicalComplex
