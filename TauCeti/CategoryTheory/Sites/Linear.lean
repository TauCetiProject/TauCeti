/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Linear sheafification

Sheafification with coefficients in an `R`-linear category preserves scalar multiplication of
morphisms. The result applies whenever the inclusion of sheaves has a left adjoint.
-/

public section

open CategoryTheory

namespace TauCeti

variable {R C A : Type*} [Semiring R] [Category* C] [Category* A] [Preadditive A]
  [Linear R A] (J : GrothendieckTopology C) [HasWeakSheafify J A]

/-- Sheafification with linear coefficients preserves scalar multiplication of morphisms. -/
instance presheafToSheafLinear : (presheafToSheaf J A).Linear R where
  map_smul {X Y} f r := by
    let adj := sheafificationAdjunction J A
    apply (adj.homEquiv X ((presheafToSheaf J A).obj Y)).injective
    simp only [Adjunction.homEquiv_unit, Functor.map_smul, adj.unit_naturality,
      Linear.comp_smul, Linear.smul_comp]

end TauCeti
