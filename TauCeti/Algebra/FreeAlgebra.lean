/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FreeAlgebra

/-!
# Left induction on words in the free algebra

Every element of `FreeAlgebra R X` is a linear combination of words, and every word is built from
`1` by multiplying on the left by generators. Hence a property of elements that holds at `1` and
is preserved by scalar multiplication, addition and left multiplication by a generator holds
everywhere (`FreeAlgebra.induction_ι_mul`). Compared with Mathlib's `FreeAlgebra.induction`, the
multiplication step only has to handle a generator on the left. This is the form needed for
statements about an operator defined by its action on a generator times an arbitrary element, such
as a bilinear form `B` determined by `B (ι x * y) z = B y (D z)` for some operator `D`.

This file also records that the constant term `FreeAlgebra.algebraMapInv` vanishes on generators.
-/

public section

namespace FreeAlgebra

variable {R X : Type*} [CommSemiring R]

/-- An induction principle for the free algebra by left multiplication with generators: a property
holding at `1` and preserved by scalar multiplication, addition and left multiplication by any
`ι R x` holds for every element. -/
@[elab_as_elim]
theorem induction_ι_mul {motive : FreeAlgebra R X → Prop} (one : motive 1)
    (smul : ∀ (r : R) a, motive a → motive (r • a))
    (add : ∀ a b, motive a → motive b → motive (a + b))
    (ι_mul : ∀ x a, motive a → motive (ι R x * a)) (a : FreeAlgebra R X) : motive a := by
  -- Every element `a` maps elements satisfying the property, by left multiplication, to elements
  -- satisfying it; apply this to `1`.
  suffices h : ∀ b, motive b → motive (a * b) by simpa using h 1 one
  induction a using FreeAlgebra.induction with
  | grade0 r => exact fun b hb => by simpa [Algebra.smul_def] using smul r b hb
  | grade1 x => exact ι_mul x
  | mul a a' ha ha' => exact fun b hb => by simpa [mul_assoc] using ha _ (ha' b hb)
  | add a a' ha ha' => exact fun b hb => by simpa [add_mul] using add _ _ (ha b hb) (ha' b hb)

/-- The constant term of a generator is zero. -/
@[simp]
theorem algebraMapInv_ι (x : X) : algebraMapInv (ι R x) = 0 :=
  lift_ι_apply _ _

end FreeAlgebra
