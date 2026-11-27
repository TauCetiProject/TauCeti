/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Projective.FinitePresentation
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Algebra.Module.MinimalProjectivePresentation.Basic
public import TauCeti.Algebra.Category.ModuleCat.Projective.Dimension

/-!
# Short complexes of finite projective presentations

A finite projective presentation gives a short complex in the module category. The complex is
short exact when the map from the relation module is injective.
-/

public section

namespace TauCeti.FiniteProjectivePresentation

open CategoryTheory

universe u v

variable {A : Type u} [Ring A] {M : ModuleCat.{v} A} (P : FiniteProjectivePresentation M)

/-- The generator and relation maps of a finite projective presentation as a short complex. -/
abbrev shortComplex : ShortComplex (ModuleCat A) :=
  ModuleCat.shortComplexOfCompEqZero P.p P.π P.exact.linearMap_comp_eq_zero

/-- A finite projective presentation with an injective relation map is short exact. -/
theorem shortExact_shortComplex (hp : Function.Injective P.p) : P.shortComplex.ShortExact :=
  ModuleCat.shortComplex_shortExact _ P.exact hp P.surjective

/-- If the presented module has projective dimension at most one, the relation map of a
minimal projective presentation is injective. -/
theorem injective_p_of_hasProjectiveDimensionLE_one [Small.{v} A]
    (hP : IsMinimalProjectivePresentation P.p P.π) (hM : HasProjectiveDimensionLE M 1) :
    Function.Injective P.p := by
  have hker := (LinearMap.hasProjectiveDimensionLE_succ_iff_ker P.surjective 0).mp hM
  have : Projective (ModuleCat.of A (LinearMap.ker P.π)) :=
    projective_iff_hasProjectiveDimensionLT_one.mpr hker
  have : Module.Projective A (LinearMap.ker P.π) :=
    (ModuleCat.of A (LinearMap.ker P.π)).projective_of_module_projective
  exact (LinearMap.ker P.π).injective_subtype.comp
    hP.isProjectiveCover_codRestrict.bijective_of_projective.injective

end TauCeti.FiniteProjectivePresentation
