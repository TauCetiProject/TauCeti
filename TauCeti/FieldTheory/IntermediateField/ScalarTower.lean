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
field `E` of `L / K`.  The same statement holds one step further down: a semiring `k`
whose actions on `K` and on `L` form a scalar tower `k → K → L` also acts compatibly through `E`.
Conversely, restricting the scalars of an intermediate field of `L / K` to `k` does not change the
field, as a `k`-algebra.

## Main results

* `IntermediateField.instIsScalarTower`: `IsScalarTower k E L` for an intermediate field
  `E` of `L / K` and a semiring `k` acting compatibly on `K` and `L`.
* `IntermediateField.le_of_isScalarTower`: an intermediate field `E` lies in an intermediate
  field `E'` as soon as some algebra structure of `E'` over `E` is compatible with `L`.
* `IntermediateField.restrictScalarsAlgEquiv`: an intermediate field `E` of `L / L'` and its
  restriction of scalars `E.restrictScalars K` are the same field over `K`.
-/

public section

namespace IntermediateField

/-- Mathlib's `IntermediateField.isScalarTower_mid` supplies `IsScalarTower K E L` for an
intermediate field `E` of `L / K`; this is the same statement for a semiring `k` that acts on `K`
compatibly with its module structure on `L`, which is what an object of `L` defined over `k` needs
in order to be restricted to `E`. -/
instance instIsScalarTower {k K L : Type*} [Semiring k] [Field K] [Field L]
    [SMul k K] [Module k L] [Algebra K L] [IsScalarTower k K L]
    (E : IntermediateField K L) : IsScalarTower k E L :=
  IsScalarTower.to₁₃₄ k K E L

/-- If `E'` is an algebra over `E` compatibly with their inclusions in `L`, then `E ≤ E'`: every
`x ∈ E` is the image in `L` of `algebraMap E E' x ∈ E'`. -/
theorem le_of_isScalarTower {K L : Type*} [Field K] [Field L] [Algebra K L]
    {E E' : IntermediateField K L} [Algebra E E'] [IsScalarTower E E' L] : E ≤ E' := fun x hx ↦ by
  have h := (algebraMap E E' ⟨x, hx⟩).2
  rwa [← algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h

section RestrictScalars

variable (K : Type*) {L' L : Type*} [Field K] [Field L'] [Field L] [Algebra K L'] [Algebra K L]
  [Algebra L' L] [IsScalarTower K L' L] (E : IntermediateField L' L)

/-- An intermediate field `E` of `L / L'` and its restriction of scalars `E.restrictScalars K`
have the same carrier; this is the resulting `K`-algebra equivalence between them, where `E` is a
`K`-algebra through `L'`. It lets a statement about `E` over `K` be read on the intermediate field
`E.restrictScalars K` of `L / K`, and conversely. -/
def restrictScalarsAlgEquiv : E.restrictScalars K ≃ₐ[K] E where
  toFun x := ⟨x, x.2⟩
  invFun x := ⟨x, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem coe_restrictScalarsAlgEquiv_apply (x : E.restrictScalars K) :
    (restrictScalarsAlgEquiv K E x : L) = x :=
  (rfl)

@[simp]
theorem coe_restrictScalarsAlgEquiv_symm_apply (x : E) :
    ((restrictScalarsAlgEquiv K E).symm x : L) = x :=
  (rfl)

end RestrictScalars

end IntermediateField
