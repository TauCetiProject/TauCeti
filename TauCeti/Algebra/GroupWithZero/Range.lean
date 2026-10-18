/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Range

/-!
# The embedding of a value-group quotient

For a monoid-with-zero homomorphism `f : A →*₀ B` into a commutative group with zero,
`MonoidWithZeroHom.valueGroup.mk f r s hr hs` is the element `(f r)⁻¹ * f s` of the value group
of `f`. This file records its image under the embedding `ValueGroup₀ f →*₀ B`.

## Main results

* `MonoidWithZeroHom.ValueGroup₀.embedding_valueGroup_mk`: the embedding sends
  `valueGroup.mk f r s hr hs` to `(f r)⁻¹ * f s`.
-/

public section

namespace MonoidWithZeroHom.ValueGroup₀

variable {A B : Type*} [MonoidWithZero A] [CommGroupWithZero B] {f : A →*₀ B}

/-- The embedding of the value group into the codomain sends `valueGroup.mk f r s hr hs` to
`(f r)⁻¹ * f s`. -/
@[simp]
theorem embedding_valueGroup_mk (r s : A) (hr : f r ≠ 0) (hs : f s ≠ 0) :
    embedding (valueGroup.mk f r s hr hs : ValueGroup₀ f) = (f r)⁻¹ * f s := by
  rw [embedding_apply, WithZero.map'_coe, WithZero.recZeroCoe_coe]
  simp [valueGroup.mk]

end MonoidWithZeroHom.ValueGroup₀
