/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Pi

/-!
# The inclusion of a factor of a product of semirings

For a family of non-unital semirings `R i`, the function `Pi.single i : R i → Π j, R j`,
supported at `i`, is additive and multiplicative. This file packages it as a non-unital ring
homomorphism `NonUnitalRingHom.single R i`, the non-unital companion of Mathlib's
`MulHom.single` and `AddMonoidHom.single`. It is a right inverse of the evaluation
`Pi.evalNonUnitalRingHom R i`, whose coercion `Pi.coe_evalNonUnitalRingHom` puts in simp normal
form, and it is not unital as soon as another factor is nonzero. Applied entrywise, it shows that
a matrix over `R i` placed in the factor `i` keeps properties such as idempotence. It
describes the objects of a finite product of rings that are supported in a single factor, for
instance idempotent matrices.
-/

public section

/-- The evaluation `Pi.evalNonUnitalRingHom R i` is the function `f ↦ f i`. -/
@[simp]
theorem Pi.coe_evalNonUnitalRingHom {ι : Type*} (R : ι → Type*)
    [∀ i, NonUnitalNonAssocSemiring (R i)] (i : ι) :
    ⇑(Pi.evalNonUnitalRingHom R i) = fun f ↦ f i :=
  (rfl)

namespace NonUnitalRingHom

variable {ι : Type*} [DecidableEq ι] (R : ι → Type*) [∀ i, NonUnitalNonAssocSemiring (R i)]

/-- **The inclusion of a factor** `R i →ₙ+* Π j, R j`, as the elements supported at `i`: this is
`Pi.single i` as a non-unital ring homomorphism. -/
def single (i : ι) : R i →ₙ+* ∀ j, R j :=
  { MulHom.single i, AddMonoidHom.single R i with }

/-- `NonUnitalRingHom.single R i` is `Pi.single i`. -/
@[simp]
theorem coe_single (i : ι) : ⇑(single R i) = Pi.single i :=
  (rfl)

end NonUnitalRingHom
