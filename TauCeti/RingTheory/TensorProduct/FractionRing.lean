/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.LinearDisjoint

/-!
# The fraction field of a tensor product of fields

If `F ⊗[k] K` is a domain, its fraction field is a compositum of the two factors,
with linearly disjoint images. Unlike the existential construction
`IntermediateField.LinearDisjoint.exists_field_of_isDomain`, these statements retain
an arbitrary specified fraction field and its scalar maps. This is useful when the
same fraction field must also be compared with localizations or geometric base change.

The right-factor algebra is Mathlib's `Algebra.TensorProduct.rightAlgebra`, installed
locally together with `right_isScalarTower`; all maps to the fraction field are the
usual scalar-tower maps. The linear-disjointness argument follows Jz Pan's
`Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective` in Mathlib,
using `Subalgebra.LinearDisjoint.include_range` and transport along the fraction map.

## References

* S. Lang, *Algebra*, the construction of linearly disjoint composita by tensor products.
-/

public section

open scoped TensorProduct

namespace TauCeti

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

section Generation

variable {k F K Q : Type*} [CommRing k] [Field F] [CommRing K] [Field Q]
  [Algebra k F] [Algebra k K] [Algebra (F ⊗[k] K) Q]
  [Algebra F Q] [Algebra K Q]
  [IsScalarTower F (F ⊗[k] K) Q] [IsScalarTower K (F ⊗[k] K) Q]
  [IsFractionRing (F ⊗[k] K) Q]

include k in
/-- The two factors generate the fraction field of their tensor product as a field.
No algebraicity assumption on either factor is needed. -/
theorem adjoin_range_right_eq_top_of_isFractionRing_tensorProduct :
    IntermediateField.adjoin F (Set.range (algebraMap K Q)) = ⊤ := by
  let E := IntermediateField.adjoin F (Set.range (algebraMap K Q))
  have hmem : (⊤ : Subring (F ⊗[k] K)) ≤
      E.toSubring.comap (algebraMap (F ⊗[k] K) Q) := by
    rw [← Algebra.TensorProduct.closure_range_union_range_eq_top k F K]
    apply Subring.closure_le.mpr
    rintro _ (⟨f, rfl⟩ | ⟨c, rfl⟩)
    -- Unpack comap membership and identify each tensor inclusion with its algebra map;
    -- the scalar-tower rewrite needs this form of the goal in both branches.
    · change algebraMap (F ⊗[k] K) Q (algebraMap F (F ⊗[k] K) f) ∈ E
      rw [← IsScalarTower.algebraMap_apply]
      exact E.algebraMap_mem f
    · change algebraMap (F ⊗[k] K) Q (algebraMap K (F ⊗[k] K) c) ∈ E
      rw [← IsScalarTower.algebraMap_apply]
      exact IntermediateField.subset_adjoin F _ ⟨c, rfl⟩
  apply IntermediateField.toSubfield_injective
  apply top_unique
  rw [← IsFractionRing.closure_range_algebraMap (F ⊗[k] K) Q]
  apply Subfield.closure_le.mpr
  rintro _ ⟨z, rfl⟩
  exact hmem (Subring.mem_top z)

end Generation

variable {k F K Q : Type*} [Field k] [Field F] [Field K] [Field Q]
  [Algebra k F] [Algebra k K] [Algebra (F ⊗[k] K) Q]
  [Algebra k Q] [Algebra F Q] [Algebra K Q]
  [IsScalarTower k (F ⊗[k] K) Q] [IsScalarTower F (F ⊗[k] K) Q]
  [IsScalarTower K (F ⊗[k] K) Q] [IsScalarTower k F Q] [IsScalarTower k K Q]
  [IsFractionRing (F ⊗[k] K) Q]

/-- The images of the two factors in a fraction field of their tensor product are
linearly disjoint. This is the concrete fraction-field form of Mathlib's
`Subalgebra.LinearDisjoint.exists_field_of_isDomain_of_injective`. -/
theorem linearDisjoint_of_isFractionRing_tensorProduct :
    (IsScalarTower.toAlgHom k K Q).fieldRange.LinearDisjoint F := by
  let i := IsScalarTower.toAlgHom k (F ⊗[k] K) Q
  have hi : Function.Injective i := IsFractionRing.injective (F ⊗[k] K) Q
  have H := (Subalgebra.LinearDisjoint.include_range k F K).map i hi
  rw [IntermediateField.linearDisjoint_iff, AlgHom.fieldRange_toSubalgebra]
  have hleft : i.comp Algebra.TensorProduct.includeLeft = IsScalarTower.toAlgHom k F Q := by
    ext f
    exact (IsScalarTower.algebraMap_apply F (F ⊗[k] K) Q f).symm
  have hright : i.comp Algebra.TensorProduct.includeRight = IsScalarTower.toAlgHom k K Q := by
    ext c
    exact (IsScalarTower.algebraMap_apply K (F ⊗[k] K) Q c).symm
  simpa only [← AlgHom.range_comp, hleft, hright] using H.symm

end TauCeti
