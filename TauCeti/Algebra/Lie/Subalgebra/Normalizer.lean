/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Normalizer

/-!
# A Lie subalgebra as an ideal of a subalgebra that normalizes it

A Lie subalgebra `T` of `L` is a Lie ideal of every Lie subalgebra `T'` of its normalizer, namely
of `T'` cut down to the elements of `T`. This file names that ideal, and records when a sum of `T`
and a normalizing subalgebra normalizes `T`.

## Main definitions

* `LieSubalgebra.idealOfLeNormalizer`: `T` as a Lie ideal of a subalgebra `T' ≤ T.normalizer`, the
  named form of `LieSubalgebra.exists_nested_lieIdeal_ofLe_normalizer`.

## Main results

* `LieSubalgebra.toLieSubalgebra_idealOfLeNormalizer`: when `T ≤ T'`, this ideal is `T` read as a
  subalgebra of `T'`.
* `LieSubalgebra.le_normalizer_of_le_sup`: a subalgebra contained in the sum of `T` and a
  subalgebra `H` normalizing `T` normalizes `T`.
-/

public section

namespace LieSubalgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

variable {T T' H : LieSubalgebra R L}

/-- A Lie subalgebra `T`, cut down to a Lie subalgebra `T'` that normalizes it, is a Lie ideal of
`T'`: the named form of `LieSubalgebra.exists_nested_lieIdeal_ofLe_normalizer`. -/
def idealOfLeNormalizer (hT' : T' ≤ T.normalizer) : LieIdeal R T' where
  __ := T.toSubmodule.comap T'.toSubmodule.subtype
  lie_mem {x m} hm := by
    -- membership in the comap is membership of the underlying element of `L` in `T`
    change ⁅(x : L), (m : L)⁆ ∈ T
    exact ideal_in_normalizer (hT' x.2) hm

@[simp]
theorem mem_idealOfLeNormalizer (hT' : T' ≤ T.normalizer) {x : T'} :
    x ∈ T.idealOfLeNormalizer hT' ↔ (x : L) ∈ T :=
  Iff.rfl

/-- When `T ≤ T'`, the ideal `T.idealOfLeNormalizer hT'` is `T` viewed as a Lie subalgebra of
`T'`. -/
@[simp]
theorem toLieSubalgebra_idealOfLeNormalizer (hT' : T' ≤ T.normalizer) (hle : T ≤ T') :
    (T.idealOfLeNormalizer hT').toLieSubalgebra = ofLe hle := by
  ext x
  simp

/-- If a Lie subalgebra `T'` lies in the sum of `T` and a Lie subalgebra `H` normalizing `T`, then
`T'` normalizes `T`. -/
theorem le_normalizer_of_le_sup (hsup : T'.toSubmodule ≤ T.toSubmodule ⊔ H.toSubmodule)
    (hH : H ≤ T.normalizer) : T' ≤ T.normalizer :=
  hsup.trans (sup_le T.le_normalizer hH)

end LieSubalgebra
