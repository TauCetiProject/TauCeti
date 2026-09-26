/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic

/-!
# The Galois group of a normal subextension as a quotient

Let `E/F` be a normal extension and `M` an intermediate field normal over `F`. Restriction of
automorphisms is a surjection `Gal(E/F) → Gal(M/F)` whose kernel is the fixing subgroup of `M`, so
it descends to an isomorphism of groups

```
Gal(E/F) ⧸ M.fixingSubgroup ≃ Gal(M/F).
```

This file proves that the isomorphism is one of **topological** groups, for the quotient topology
on the left and the Krull topology on the right: `TauCeti.quotientFixingSubgroupEquiv` is an
isomorphism of topological groups for any normal `E/F` and any intermediate field `M` normal over
`F`, with no separability assumed anywhere. So the quotient of `Gal(E/F)` cut out by a normal
subextension and the Galois group of that subextension are interchangeable, topology included:
a quotient of `Gal(E/F)` is compact, profinite, or finite exactly when `Gal(M/F)` is. Its reading
at an algebraic closure, comparing a quotient of `Field.absoluteGaloisGroup K` with `Gal(M/K)`, is
in `TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Quotient`.

Normality of `M/F` alone makes `M.fixingSubgroup` a normal subgroup of `Gal(E/F)`, since it is the
kernel of restriction; Mathlib's `IsGalois.fixingSubgroup_normal_of_isGalois` asks in addition that
`E/F` and `M/F` be separable, which an algebraic closure in positive characteristic need not be.
The same separability is what keeps `InfiniteGalois.normalAutEquivQuotient`, which identifies the
quotient of `Gal(E/F)` by a closed normal subgroup with the Galois group of its fixed field, from
covering an algebraic closure; that identification is also one of abstract groups only.

## Main results

* `IntermediateField.fixingSubgroup_normal`: the fixing subgroup of a normal intermediate field is
  a normal subgroup.
* `TauCeti.quotientFixingSubgroupEquiv`: the isomorphism of topological groups
  `Gal(E/F) ⧸ M.fixingSubgroup ≃ₜ* Gal(M/F)`, for `E/F` and `M/F` normal.
-/

public section

noncomputable section

namespace TauCeti

variable (F E : Type*) [Field F] [Field E] [Algebra F E] (M : IntermediateField F E) [Normal F M]

/-- **The fixing subgroup of a normal intermediate field is normal**, being the kernel of
restriction. Neither separability nor normality of the ambient extension `E/F` is used. -/
instance _root_.IntermediateField.fixingSubgroup_normal : M.fixingSubgroup.Normal :=
  M.restrictNormalHom_ker (K := F) (L := E) ▸ (AlgEquiv.restrictNormalHom M).normal_ker

variable [Normal F E]

-- The multiplicative equivalence is named so that the structure field of
-- `quotientFixingSubgroupEquiv` and the continuity proof below refer to one and the same term
-- rather than to two separately built copies identified by definitional unfolding.
/-- Restriction to a normal intermediate field, descended to the quotient by its fixing subgroup:
the underlying multiplicative equivalence of `quotientFixingSubgroupEquiv`. -/
private def quotientFixingSubgroupMulEquiv :
    Gal(E/F) ⧸ M.fixingSubgroup ≃* Gal(↥M/F) :=
  QuotientGroup.liftEquiv _ (AlgEquiv.restrictNormalHom_surjective E)
    M.restrictNormalHom_ker.symm

private theorem continuous_quotientFixingSubgroupMulEquiv :
    Continuous (quotientFixingSubgroupMulEquiv F E M) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2
    (InfiniteGalois.restrictNormalHom_continuous M)

/-- **The Galois group of a normal subextension is a quotient of the Galois group**, as a
topological group: for `E/F` and `M/F` normal, restriction induces an isomorphism
`Gal(E/F) ⧸ M.fixingSubgroup ≃ₜ* Gal(M/F)`. -/
def quotientFixingSubgroupEquiv : Gal(E/F) ⧸ M.fixingSubgroup ≃ₜ* Gal(↥M/F) where
  __ := quotientFixingSubgroupMulEquiv F E M
  __ := Continuous.homeoOfEquivCompactToT2 (f := (quotientFixingSubgroupMulEquiv F E M).toEquiv)
    (continuous_quotientFixingSubgroupMulEquiv F E M)

variable {F E M}

/-- The isomorphism `quotientFixingSubgroupEquiv` sends the class of `σ` to its restriction, which
is what identifies it with the map Mathlib's API is about; its value at a point of `M` is then
`AlgEquiv.restrictNormalHom_apply`, namely `σ` evaluated there. -/
@[simp]
theorem quotientFixingSubgroupEquiv_mk (σ : Gal(E/F)) :
    quotientFixingSubgroupEquiv F E M (σ : Gal(E/F) ⧸ M.fixingSubgroup) =
      AlgEquiv.restrictNormalHom M σ :=
  (rfl)

/-- The inverse of the isomorphism sends the restriction of `σ` back to the class of `σ`; with
`AlgEquiv.restrictNormalHom_surjective` this computes it on every element. -/
@[simp]
theorem quotientFixingSubgroupEquiv_symm_restrictNormalHom (σ : Gal(E/F)) :
    (quotientFixingSubgroupEquiv F E M).symm (AlgEquiv.restrictNormalHom M σ) =
      (σ : Gal(E/F) ⧸ M.fixingSubgroup) := by
  rw [← quotientFixingSubgroupEquiv_mk σ, ContinuousMulEquiv.symm_apply_apply]

end TauCeti
