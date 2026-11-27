/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.SingleObj
public import TauCeti.CategoryTheory.SingleObj

/-!
# Linear structure on the one-object category of an algebra

A ring `A` is a preadditive category `SingleObj A` with one object. When `A` is an algebra over a
commutative semiring `R`, the scalar action of `R` on `A` makes `SingleObj A` an `R`-linear
category. At `R = ℤ` this linear structure is definitionally Mathlib's `preadditiveIntLinear`
with `Ring.toIntAlgebra`, or with `Algebra.id ℤ` when `A = ℤ`. The isomorphism
`SingleObj Aᵐᵒᵖ ≌ (SingleObj A)ᵒᵖ` is additive.

## Main results

* `CategoryTheory.SingleObj.linear : Linear R (SingleObj A)`, an instance.
* The instance `(SingleObj.mulOppositeEquiv A).functor.Additive`.
-/

public section

namespace CategoryTheory.SingleObj

variable (R A : Type*) [CommSemiring R] [Ring A] [Algebra R A]

/-- **`SingleObj A` is `R`-linear** for an `R`-algebra `A`, with the scalar action on `A`. At
`R = ℤ` it is definitionally `preadditiveIntLinear` with `Ring.toIntAlgebra`, or with
`Algebra.id ℤ` when `A = ℤ`. -/
instance linear : Linear R (SingleObj A) where
  homModule _ _ := inferInstanceAs (Module R A)
  smul_comp _ _ _ r f g := Algebra.mul_smul_comm (A := A) r g f
  comp_smul _ _ _ f r g := Algebra.smul_mul_assoc (A := A) r g f

/-- At `R = ℤ`, with the canonical algebra `Ring.toIntAlgebra`, `linear ℤ A` is Mathlib's
`preadditiveIntLinear` up to reducible and instance unfolding, so the two instances do not form a
non-definitional diamond. -/
example : Linear.preadditiveIntLinear (C := SingleObj A) = linear ℤ A := by
  with_reducible_and_instances rfl

/-- The same holds for `A = ℤ` with the algebra `Algebra.id ℤ`. -/
example : Linear.preadditiveIntLinear (C := SingleObj ℤ) = @linear ℤ ℤ _ _ (Algebra.id ℤ) := by
  with_reducible_and_instances rfl

/-- The isomorphism
`SingleObj Aᵐᵒᵖ ≌ (SingleObj A)ᵒᵖ` is additive. -/
instance : (mulOppositeEquiv A).functor.Additive where
  map_add {_ _ f g} := by
    simp only [mulOppositeEquiv_functor_map]
    rfl

end CategoryTheory.SingleObj
