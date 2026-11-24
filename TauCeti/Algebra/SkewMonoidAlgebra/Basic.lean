/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.SkewMonoidAlgebra.Basic

/-!
# Basic lemmas on the skew monoid algebra

This file records `SkewMonoidAlgebra.liftNCRingHom_single`, the value of the ring homomorphism
`SkewMonoidAlgebra.liftNCRingHom f g h : SkewMonoidAlgebra k G →+* R` on `single a b`. It is the
skew counterpart of Mathlib's `MonoidAlgebra.liftNCRingHom_single`.
-/

public section

namespace SkewMonoidAlgebra

variable {k G R : Type*} [Semiring k] [Monoid G] [MulSemiringAction G k] [Semiring R]

/-- `SkewMonoidAlgebra.liftNCRingHom f g h` sends `single a b` to `f b * g a`. -/
@[simp]
theorem liftNCRingHom_single (f : k →+* R) (g : G →* R)
    (h_comm : ∀ {x y}, f (y • x) * g y = g y * f x) (a : G) (b : k) :
    liftNCRingHom f g h_comm (single a b) = f b * g a :=
  liftNC_single _ _ _ _

end SkewMonoidAlgebra
