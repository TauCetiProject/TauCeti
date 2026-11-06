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
  have hleft : (algebraMap (F ⊗[k] K) Q) ∘
      (Algebra.TensorProduct.includeLeft : F →ₐ[k] F ⊗[k] K) = algebraMap F Q := by
    exact congrArg DFunLike.coe (IsScalarTower.algebraMap_eq F (F ⊗[k] K) Q).symm
  have hright : (algebraMap (F ⊗[k] K) Q) ∘
      (Algebra.TensorProduct.includeRight : K →ₐ[k] F ⊗[k] K) = algebraMap K Q := by
    exact congrArg DFunLike.coe (IsScalarTower.algebraMap_eq K (F ⊗[k] K) Q).symm
  have hs : (algebraMap (F ⊗[k] K) Q).range =
      Subring.closure (Set.range (algebraMap F Q) ∪ Set.range (algebraMap K Q)) := by
    rw [RingHom.range_eq_map,
      ← Algebra.TensorProduct.closure_range_union_range_eq_top k F K,
      RingHom.map_closure, Set.image_union, ← Set.range_comp, ← Set.range_comp,
      hleft, hright]
  have h := IsFractionRing.ringHom_fieldRange_eq_of_comp_eq_of_range_eq
    (f := RingHom.id Q) (g := algebraMap (F ⊗[k] K) Q) rfl hs
  apply IntermediateField.toSubfield_injective
  rw [IntermediateField.adjoin_toSubfield, ← h]
  exact RingHom.fieldRange_eq_top_iff.mpr Function.surjective_id

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
    apply AlgHom.toRingHom_injective
    exact (IsScalarTower.algebraMap_eq F (F ⊗[k] K) Q).symm
  have hright : i.comp Algebra.TensorProduct.includeRight = IsScalarTower.toAlgHom k K Q := by
    apply AlgHom.toRingHom_injective
    exact (IsScalarTower.algebraMap_eq K (F ⊗[k] K) Q).symm
  simpa only [← AlgHom.range_comp, hleft, hright] using H.symm

end TauCeti
