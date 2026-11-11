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

A local ring, as a finitely generated module over itself, has a local endomorphism ring without
any finiteness assumption, that ring being the opposite of the ring.
-/

public section

namespace FGModuleCat

open CategoryTheory

universe v

variable {A : Type v} [Ring A]

/-- A local ring, as a finitely generated module over itself, has a local endomorphism ring: that
ring is the opposite of the ring. -/
instance [IsLocalRing A] : IsLocalRing (End (FGModuleCat.of A A)) := by
  have : IsLocalRing (Module.End A A) := (RingEquiv.moduleEndSelf A).isLocalRing
  have : IsLocalRing (Module.End A (FGModuleCat.of A A).obj) := ‹IsLocalRing (Module.End A A)›
  have : IsLocalRing (End ((ObjectProperty.ι _).obj (FGModuleCat.of A A))) :=
    (ModuleCat.endRingEquiv (FGModuleCat.of A A).obj).symm.isLocalRing
  exact ((ObjectProperty.fullyFaithfulι _).ringEquivEnd (FGModuleCat.of A A)).symm.isLocalRing

end FGModuleCat
