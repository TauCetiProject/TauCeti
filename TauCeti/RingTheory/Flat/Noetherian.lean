/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Descent of Noetherianity along faithfully flat algebras

A ring is Noetherian as soon as some faithfully flat algebra over it is Noetherian: extension of
scalars embeds the ideals of the base into the submodules of the base change, which is the
algebra itself.

## Main results

* `IsNoetherianRing.of_faithfullyFlat`: Noetherianity descends along a faithfully flat algebra.
-/

public section

/-- A ring is Noetherian if some faithfully flat algebra over it is Noetherian. -/
theorem IsNoetherianRing.of_faithfullyFlat {A : Type*} (B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [Module.FaithfullyFlat A B] [IsNoetherianRing B] : IsNoetherianRing A :=
  Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat (A := B) inferInstance
