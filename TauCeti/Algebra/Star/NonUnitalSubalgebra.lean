/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.NonUnitalSubalgebra

/-!
# Direct `SMul` instance on `NonUnitalStarSubalgebra`

Mathlib defines `NonUnitalStarSubalgebra.instModule` at default priority while leaving the direct
`SMul R S` instance to `SetLike.smul` at priority `50`. Consequently, synthesizing `SMul R S`
directly (as `StarAlgEquiv` does) traverses the module and action hierarchy instead of resolving on
`NonUnitalStarSubalgebra` immediately, which can time out on operator algebras over submodules. We
register `NonUnitalStarSubalgebra.instSMul := SetLike.smul S` at default priority, definitionally
equal to `S.instModule.toSMul`.
-/

public section

namespace NonUnitalStarSubalgebra

/-- Direct `R`-scalar action on the carrier of a `NonUnitalStarSubalgebra R A`, definitionally equal
to `S.instModule.toSMul`. -/
instance instSMul {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    [Star A] (S : NonUnitalStarSubalgebra R A) : SMul R S :=
  SetLike.smul S

end NonUnitalStarSubalgebra
