/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Projective.FinitePresentation
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

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

end TauCeti.FiniteProjectivePresentation
