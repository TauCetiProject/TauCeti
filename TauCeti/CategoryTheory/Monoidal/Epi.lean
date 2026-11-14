/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Epimorphisms under tensor products

Whiskerings and tensor products of epimorphisms are epimorphisms whenever the relevant tensoring
functors preserve epimorphisms. The instances `TauCeti.epi_whiskerLeft`,
`TauCeti.epi_whiskerRight` and `TauCeti.epi_tensorHom` make this available to instance search,
including in braided closed monoidal categories, where tensoring is a left adjoint.
-/

public section

namespace TauCeti

open CategoryTheory MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Left whiskering an epimorphism is an epimorphism when tensoring on the left preserves
epimorphisms. -/
instance epi_whiskerLeft (X : C) {A B : C} (f : A ⟶ B) [Epi f]
    [(tensorLeft X).PreservesEpimorphisms] : Epi (X ◁ f) :=
  (tensorLeft X).map_epi f

/-- Right whiskering an epimorphism is an epimorphism when tensoring on the right preserves
epimorphisms. -/
instance epi_whiskerRight {A B : C} (f : A ⟶ B) [Epi f] (X : C)
    [(tensorRight X).PreservesEpimorphisms] : Epi (f ▷ X) :=
  (tensorRight X).map_epi f

/-- The tensor product of two epimorphisms is an epimorphism when the relevant tensoring
functors preserve epimorphisms. -/
instance epi_tensorHom {A B A' B' : C} (f : A ⟶ B) (g : A' ⟶ B') [Epi f] [Epi g]
    [(tensorRight A').PreservesEpimorphisms] [(tensorLeft B).PreservesEpimorphisms] :
    Epi (f ⊗ₘ g) := by
  rw [tensorHom_def]
  infer_instance

end TauCeti
