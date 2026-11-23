/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Ring.Subring.Defs

/-!
# Algebra structure map on subrings

For a commutative ring `R` and a subring-class `E` of `R`, Mathlib installs the subsemiring
algebra structure `Algebra.ofSubsemiring E`. This file normalizes its structure map
`algebraMap E R` to the canonical ring inclusion `SubringClass.subtype E`.

## Main results

* `Algebra.algebraMap_ofSubsemiring_eq_subtype`: `(algebraMap E R : E →+* R) =
  SubringClass.subtype E`.
-/

public section

namespace Algebra

/-- For a subring-class `E` of a commutative ring `R`, the algebra structure map `algebraMap E R`
equals the canonical inclusion `SubringClass.subtype E`. -/
@[simp]
theorem algebraMap_ofSubsemiring_eq_subtype {R S : Type*} [CommRing R] [SetLike S R]
    [SubringClass S R] (E : S) :
    (algebraMap E R : E →+* R) = SubringClass.subtype E :=
  rfl

end Algebra
