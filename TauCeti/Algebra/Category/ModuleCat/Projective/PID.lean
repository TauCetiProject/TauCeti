/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import TauCeti.LinearAlgebra.FreeModule.PID

/-!
# Subobjects of projective modules over a principal ideal domain

Over a principal ideal ring without zero divisors, every submodule of a projective module is
projective (`Submodule.projective_of_isPrincipalIdealRing`). This file records the categorical
form: in `ModuleCat`, the source of a monomorphism into a projective object is projective. This is
the hereditary property of principal ideal domains which makes cycles and boundaries of a complex
of projective modules projective.
-/

public section

open CategoryTheory

universe v u

namespace ModuleCat

variable {k : Type u} [CommRing k] [NoZeroDivisors k] [IsPrincipalIdealRing k] [Small.{v} k]

/-- Over a principal ideal ring without zero divisors, the source of a monomorphism into a
projective module is projective. -/
theorem projective_of_mono {A P : ModuleCat.{v} k} (f : A ⟶ P) [Mono f] [Projective P] :
    Projective A := by
  have : Module.Projective k (LinearMap.range f.hom) :=
    (LinearMap.range f.hom).projective_of_isPrincipalIdealRing
  have : Module.Projective k A :=
    .of_equiv' (LinearEquiv.ofInjective f.hom ((mono_iff_injective f).mp ‹_›)).symm
  exact A.projective_of_categoryTheory_projective

end ModuleCat
