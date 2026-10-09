/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Epi
public import Mathlib.Data.ZMod.Basic

/-!
# `ℤ → ZMod n` is an epimorphism of commutative rings

Every element of `ZMod n` is the image of an integer, so `ℤ → ZMod n` is surjective and hence an
epimorphism of commutative rings (`Algebra.isEpi_of_surjective_algebraMap`). This file records the
instance `Algebra.IsEpi ℤ (ZMod n)`, so that results stated for an epimorphic `ℤ`-algebra apply to
`ZMod n` by typeclass inference.
-/

public section

namespace TauCeti

namespace ZMod

/-- `ℤ → ZMod n` is an epimorphism of commutative rings, being surjective. -/
instance isEpi_int (n : ℕ) : Algebra.IsEpi ℤ (_root_.ZMod n) :=
  Algebra.isEpi_of_surjective_algebraMap ℤ (_root_.ZMod n) _root_.ZMod.intCast_surjective

end ZMod

end TauCeti
