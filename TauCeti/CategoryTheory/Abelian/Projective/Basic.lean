/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Basic
public import TauCeti.CategoryTheory.ObjectProperty.Presented

/-!
# Projective objects in abelian categories

In an abelian category with enough projectives, every object is a cokernel of a morphism between
projective objects (`CategoryTheory.ObjectProperty.presented_isProjective_eq_top`).
-/

public section

universe v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C]

/-- In an abelian category with enough projectives, every object is a cokernel of a morphism
between projective objects. -/
theorem presented_isProjective_eq_top [Abelian C] [EnoughProjectives C] :
    (isProjective C).presented = ⊤ :=
  presented_eq_top fun X ↦
    ⟨Projective.over X, Projective.π X, Projective.projective_over X, Projective.π_epi X⟩

end CategoryTheory.ObjectProperty
