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

Tensor products of epimorphisms are epimorphisms whenever the relevant tensoring functors
preserve epimorphisms. The instance `TauCeti.epi_tensorHom` makes this available to instance
search, including in braided closed monoidal categories, where tensoring is a left adjoint.
-/

public section

namespace TauCeti

open CategoryTheory MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The tensor product of two epimorphisms is an epimorphism when the relevant tensoring
functors preserve epimorphisms. -/
instance epi_tensorHom {A B A' B' : C} (f : A ⟶ B) (g : A' ⟶ B') [Epi f] [Epi g]
    [(tensorRight A').PreservesEpimorphisms] [(tensorLeft B).PreservesEpimorphisms] :
    Epi (f ⊗ₘ g) := by
  rw [tensorHom_def]
  exact epi_comp' ((tensorRight A').map_epi f) ((tensorLeft B).map_epi g)

end TauCeti
