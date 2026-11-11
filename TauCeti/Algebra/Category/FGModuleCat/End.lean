/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import TauCeti.CategoryTheory.Functor.RingEquivEnd

/-!
# Endomorphism rings in `FGModuleCat`

An object of `FGModuleCat A` has a local endomorphism ring when its underlying module does
(`FGModuleCat.isLocalRing_end_of_isLocalRing_moduleEnd`). In particular a local ring, as a finitely
generated module over itself, has a local endomorphism ring without any finiteness assumption, that
ring being the opposite of the ring.
-/

public section

namespace FGModuleCat

open CategoryTheory

universe v

variable {A : Type v} [Ring A]

/-- An object of `FGModuleCat A` has a local endomorphism ring as soon as its underlying module
does. -/
theorem isLocalRing_end_of_isLocalRing_moduleEnd {X : FGModuleCat A}
    (h : IsLocalRing (Module.End A X.obj)) : IsLocalRing (End X) := by
  have : IsLocalRing (End ((ObjectProperty.ι _).obj X)) :=
    (ModuleCat.endRingEquiv X.obj).symm.isLocalRing
  exact ((ObjectProperty.fullyFaithfulι _).ringEquivEnd X).symm.isLocalRing

/-- A local ring, as a finitely generated module over itself, has a local endomorphism ring: that
ring is the opposite of the ring. -/
instance [IsLocalRing A] : IsLocalRing (End (FGModuleCat.of A A)) :=
  -- `(FGModuleCat.of A A).obj` is `ModuleCat.of A A`, whose carrier is `A` by definition.
  isLocalRing_end_of_isLocalRing_moduleEnd (RingEquiv.moduleEndSelf A).isLocalRing

end FGModuleCat
