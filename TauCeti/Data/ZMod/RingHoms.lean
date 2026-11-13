/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Data.ZMod.Basic

/-!
# Surjectivity of integer reduction

The canonical map from `ℤ` to `ZMod n` is surjective, including at modulus zero.
The instance makes semilinear submodule images along integer reduction available.
-/

public section

namespace ZMod

/-- Integer reduction is surjective for every modulus. -/
instance (n : ℕ) : RingHomSurjective (Int.castRingHom (ZMod n)) :=
  ⟨intCast_surjective⟩

end ZMod
