/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Opposite

/-!
# Inverse pairs for the double-opposite ring equivalence

The canonical equivalence `RingEquiv.opOp A` identifies a semiring with its double opposite.
The inverse-pair instances here allow semilinear maps along this equivalence to invert and compose.
-/

public section

namespace TauCeti

/-- The canonical double-opposite ring equivalence and its inverse form an inverse pair. -/
instance opOpRingHomInvPair (A : Type*) [Semiring A] :
    RingHomInvPair (RingHomClass.toRingHom (RingEquiv.opOp A))
      (RingHomClass.toRingHom (RingEquiv.opOp A).symm) :=
  RingHomInvPair.of_ringEquiv (RingEquiv.opOp A)

/-- The inverse double-opposite ring equivalence and the forward equivalence form
an inverse pair. -/
instance opOpRingHomInvPairSymm (A : Type*) [Semiring A] :
    RingHomInvPair (RingHomClass.toRingHom (RingEquiv.opOp A).symm)
      (RingHomClass.toRingHom (RingEquiv.opOp A)) :=
  RingHomInvPair.of_ringEquiv_symm (RingEquiv.opOp A)

end TauCeti
