/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Notation.Pi.Basic

/-!
# Values of `Pi.mulSingle` at distinct coordinates

A family `Pi.mulSingle i a` with `a ≠ 1` takes different values at `i` and at any other
coordinate `j`, so it separates `i` from every other coordinate.

## Main declarations

* `TauCeti.Pi.mulSingle_apply_ne_of_ne_one`: for `a ≠ 1` and `i ≠ j`,
  `Pi.mulSingle i a i ≠ Pi.mulSingle i a j`; the additive version is
  `TauCeti.Pi.single_apply_ne_of_ne_zero`.
-/

public section

namespace TauCeti.Pi

variable {ι M : Type*} [DecidableEq ι] [One M]

/-- If `a ≠ 1`, the family `Pi.mulSingle i a` takes different values at `i` and at any other
coordinate `j`. -/
@[to_additive /-- If `a ≠ 0`, the family `Pi.single i a` takes different values at `i` and at any
other coordinate `j`. -/]
theorem mulSingle_apply_ne_of_ne_one {a : M} (ha : a ≠ 1) {i j : ι} (hij : i ≠ j) :
    (Pi.mulSingle i a : ι → M) i ≠ (Pi.mulSingle i a : ι → M) j := by
  rwa [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij.symm]

end TauCeti.Pi
