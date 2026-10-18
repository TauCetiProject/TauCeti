/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.GaloisClosure

/-!
# The normal closure of a finite intermediate field

In a Galois extension `K/k`, the normal closure of a finite intermediate field `L` is finite and
Galois over `k`. This file records it as an element of `FiniteGaloisIntermediateField k K`
(`FiniteGaloisIntermediateField.normalClosure`), the smallest one containing `L`
(`FiniteGaloisIntermediateField.normalClosure_le_iff`). In particular every finite intermediate
field lies in a finite Galois one, which is how statements about the finite Galois subextensions of
an infinite Galois extension reach its other finite subextensions.

## Main definitions

* `FiniteGaloisIntermediateField.normalClosure k L`: the normal closure of `L`, as a finite Galois
  intermediate field.

## Main results

* `FiniteGaloisIntermediateField.le_normalClosure`: `L` lies in its normal closure.
* `FiniteGaloisIntermediateField.normalClosure_le_iff`: the normal closure of `L` is the smallest
  finite Galois intermediate field containing `L`.
* `IntermediateField.fixingSubgroup_normalClosure`: in a Galois extension, the subgroup fixing
  the normal closure of `L` is the normal core of the subgroup fixing `L`.
* `IntermediateField.normalClosure_fixedField`: in a finite Galois extension, the normal closure
  of the fixed field of `H` is the fixed field of the normal core of `H`.
-/

public section

namespace FiniteGaloisIntermediateField

variable (k : Type*) {K : Type*} [Field k] [Field K] [Algebra k K] [IsGalois k K]
  (L : IntermediateField k K) [FiniteDimensional k L]

/-- **The normal closure of a finite intermediate field** `L` of a Galois extension `K/k`, as a
finite Galois intermediate field. It is the smallest finite Galois intermediate field containing
`L` (`normalClosure_le_iff`). -/
noncomputable def normalClosure : FiniteGaloisIntermediateField k K where
  toIntermediateField := IntermediateField.normalClosure k L K
  finiteDimensional := normalClosure.is_finiteDimensional k L K
  isGalois := IsGalois.normalClosure k L K

/-- The underlying intermediate field of `normalClosure k L` is the normal closure of `L`. -/
@[simp]
theorem normalClosure_toIntermediateField :
    (normalClosure k L).toIntermediateField = IntermediateField.normalClosure k L K :=
  (rfl)

/-- A finite intermediate field lies in its normal closure. -/
theorem le_normalClosure : L ≤ (normalClosure k L).toIntermediateField :=
  IntermediateField.le_normalClosure L

variable {k L} in
/-- **The universal property of the normal closure**: it lies in a finite Galois intermediate
field `M` exactly when `L` does. -/
theorem normalClosure_le_iff {M : FiniteGaloisIntermediateField k K} :
    normalClosure k L ≤ M ↔ L ≤ M.toIntermediateField :=
  IntermediateField.normalClosure_le_iff_of_normal

end FiniteGaloisIntermediateField

namespace IntermediateField

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsGalois k K]

/-- **The subgroup fixing a normal closure is a normal core.** In a Galois extension `K/k`, the
subgroup fixing the normal closure of an intermediate field `L` is the largest normal subgroup
fixing `L`, that is, the normal core of the subgroup fixing `L`. -/
theorem fixingSubgroup_normalClosure (L : IntermediateField k K) :
    (normalClosure k L K).fixingSubgroup = L.fixingSubgroup.normalCore := by
  refine le_antisymm (Subgroup.normal_le_normalCore.2 (fixingSubgroup_le (le_normalClosure L)))
    ?_
  -- The fixed field of the normal core is normal over `k` and contains `L`.
  rw [← le_fixedField_iff_le_fixingSubgroup, normalClosure_le_iff_of_normal,
    le_fixedField_iff_le_fixingSubgroup]
  exact Subgroup.normalCore_le _

/-- **The normal closure of a fixed field.** In a finite Galois extension `K/k`, the normal
closure of the fixed field of a subgroup `H` of `Gal(K/k)` is the fixed field of the normal core
of `H`. -/
theorem normalClosure_fixedField [FiniteDimensional k K] (H : Subgroup Gal(K/k)) :
    normalClosure k (fixedField H) K = fixedField H.normalCore := by
  rw [← IsGalois.fixedField_fixingSubgroup (normalClosure k (fixedField H) K),
    fixingSubgroup_normalClosure, fixingSubgroup_fixedField]

end IntermediateField
