/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharP.Defs

import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Tactic.Ring

/-!
# Translating an Artin–Schreier generator

In characteristic `p`, a root `y` of `X ^ p - X - u` translated by an element `w` of the base
field is a root of `X ^ p - X - (u - (w ^ p - w))`. Thus `u` and `u - (w ^ p - w)` define the
same Artin–Schreier extension.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.7.8.
-/

public section

namespace TauCeti

/-- Translating an Artin–Schreier generator `y` by `w ∈ F` translates the right-hand side of
`y ^ p - y = u` by `w ^ p - w`. -/
theorem sub_algebraMap_pow_sub_self_eq {F F' : Type*} [CommRing F] [CommRing F']
    [Algebra F F'] (p : ℕ) [ExpChar F' p] (y : F') (w : F) :
    (y - algebraMap F F' w) ^ p - (y - algebraMap F F' w) =
      (y ^ p - y) - algebraMap F F' (w ^ p - w) := by
  rw [sub_pow_expChar, map_sub, map_pow]
  ring

end TauCeti
