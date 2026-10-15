/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic

/-!
# Scalar towers one step below an intermediate field

Mathlib's `IntermediateField.isScalarTower_mid` supplies `IsScalarTower K E L` for an intermediate
field `E` of `L / K`.  The same statement holds one step further down: a commutative semiring `k`
whose actions on `K` and on `L` form a scalar tower `k → K → L` also acts compatibly through `E`.

## Main results

* `IntermediateField.instIsScalarTower`: `IsScalarTower k E L` for an intermediate field
  `E` of `L / K` and a commutative semiring `k` acting compatibly on `K` and `L`.
* `IntermediateField.le_of_isScalarTower`: an intermediate field `E` lies in an intermediate
  field `E'` as soon as some algebra structure of `E'` over `E` is compatible with `L`.
-/

public section

namespace IntermediateField

/-- Mathlib's `IntermediateField.isScalarTower_mid` supplies `IsScalarTower K E L` for an
intermediate field `E` of `L / K`; this is the same statement for a commutative semiring `k` that
acts on `K` compatibly with its algebra structure on `L`, which is what an object of `L` defined
over `k` needs in order to be restricted to `E`. -/
instance instIsScalarTower {k K L : Type*} [CommSemiring k] [Field K] [Field L]
    [SMul k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    (E : IntermediateField K L) : IsScalarTower k E L :=
  Subalgebra.isScalarTower_mid E.toSubalgebra

/-- If `E'` is an algebra over `E` compatibly with their inclusions in `L`, then `E ≤ E'`: every
`x ∈ E` is the image in `L` of `algebraMap E E' x ∈ E'`. -/
theorem le_of_isScalarTower {K L : Type*} [Field K] [Field L] [Algebra K L]
    {E E' : IntermediateField K L} [Algebra E E'] [IsScalarTower E E' L] : E ≤ E' := fun x hx ↦ by
  have h : ((algebraMap E E' ⟨x, hx⟩ : E') : L) = x := by
    rw [← algebraMap_apply, ← IsScalarTower.algebraMap_apply, algebraMap_apply]
  exact h ▸ (algebraMap E E' ⟨x, hx⟩).2

end IntermediateField
