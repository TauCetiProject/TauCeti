/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Range

/-!
# The embedding of the value group with zero on nonzero elements

For a monoid-with-zero homomorphism `f : A →*₀ B` into a group with zero, the embedding
`MonoidWithZeroHom.ValueGroup₀.embedding : ValueGroup₀ f →*₀ B` sends an element `x` of the
value group `valueGroup f`, viewed in `ValueGroup₀ f`, to its underlying element of `B`.
Together with `MonoidWithZeroHom.valueGroup.mk_eq_div`, `simp` evaluates the embedding on
`valueGroup.mk f r s hr hs` as `f s / f r`.

## Main results

* `MonoidWithZeroHom.ValueGroup₀.embedding_coe`: the embedding sends `x : valueGroup f`, viewed
  in `ValueGroup₀ f`, to `((x : Bˣ) : B)`.
-/

public section

namespace MonoidWithZeroHom.ValueGroup₀

variable {A B : Type*} [MonoidWithZero A] [GroupWithZero B] {f : A →*₀ B}

/-- The embedding of the value group with zero into the codomain sends an element `x` of the
value group, viewed in `ValueGroup₀ f`, to its underlying element `((x : Bˣ) : B)`. -/
@[simp]
theorem embedding_coe (x : valueGroup f) : embedding (x : ValueGroup₀ f) = ((x : Bˣ) : B) := by
  simp [embedding_apply]

end MonoidWithZeroHom.ValueGroup₀
