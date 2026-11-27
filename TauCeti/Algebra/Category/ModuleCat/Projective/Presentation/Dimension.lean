/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Projective.Presentation.Basic
public import TauCeti.Algebra.Module.MinimalProjectivePresentation.Basic
public import TauCeti.Algebra.Category.ModuleCat.Projective.Dimension

/-!
# Projective dimension and finite projective presentations

A minimal presentation of a module of projective dimension at most one is a resolution of
length one.
-/

public section

namespace TauCeti.FiniteProjectivePresentation

open CategoryTheory

universe u v

variable {A : Type u} [Ring A] {M : ModuleCat.{v} A} (P : FiniteProjectivePresentation M)

/-- If the presented module has projective dimension at most one, the relation map of a
minimal projective presentation is injective. -/
theorem p_injective_of_hasProjectiveDimensionLE_one [Small.{v} A]
    (hP : IsMinimalProjectivePresentation P.p P.π) (hM : HasProjectiveDimensionLE M 1) :
    Function.Injective P.p := by
  have hker := (LinearMap.hasProjectiveDimensionLE_succ_iff_ker P.surjective 0).mp hM
  have : Projective (ModuleCat.of A (LinearMap.ker P.π)) :=
    projective_iff_hasProjectiveDimensionLT_one.mpr hker
  exact hP.p₁_injective_iff_projective_ker.mpr
    (ModuleCat.of A (LinearMap.ker P.π)).projective_of_module_projective

end TauCeti.FiniteProjectivePresentation
