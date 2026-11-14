/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
public import TauCeti.FieldTheory.Galois.Restriction
public import TauCeti.FieldTheory.KrullTopology
public import TauCeti.Topology.Algebra.Group.Quotient.Basic

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
kernel of restriction (`IntermediateField.fixingSubgroup_normal`, in
`TauCeti.FieldTheory.Galois.Restriction`); Mathlib's `IsGalois.fixingSubgroup_normal_of_isGalois`
asks in addition that `E/F` and `M/F` be separable, which an algebraic closure in positive
characteristic need not be.
The same separability is what keeps `InfiniteGalois.normalAutEquivQuotient`, which identifies the
quotient of `Gal(E/F)` by a closed normal subgroup with the Galois group of its fixed field, from
covering an algebraic closure; that identification is also one of abstract groups only.

## Main results

* `TauCeti.quotientFixingSubgroupEquiv`: the isomorphism of topological groups
  `Gal(E/F) ⧸ M.fixingSubgroup ≃ₜ* Gal(M/F)`, for `E/F` and `M/F` normal.
* `AlgHom.continuous_restrictNormalHom`, `AlgEquiv.continuous_restrictNormalHom`: Krull continuity
  of Galois restriction along an `F`-embedding `f : M →ₐ[F] K` or scalar tower `F → M → K` of a
  normal extension `M/F`, without normality of `K/F`.
* `AlgHom.isOpen_ker_restrictNormalHom`: openness of `f.restrictNormalHom.ker` when `M/F` is finite
  and normal.
* `AlgHom.quotientKerRestrictNormalHomEquiv`: the isomorphism of topological groups
  `Gal(E/F) ⧸ f.restrictNormalHom.ker ≃ₜ* Gal(M/F)` along `f : M →ₐ[F] E`.
-/

public section

noncomputable section

namespace TauCeti

variable (F E : Type*) [Field F] [Field E] [Algebra F E] (M : IntermediateField F E) [Normal F M]
  [Normal F E]

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

section RestrictAlong

/-- **Restriction along an embedding of a normal extension is continuous** for the Krull
topologies: it factors as restriction to `f.fieldRange` followed by conjugation along
`f.equivFieldRange.symm`. Neither normality of `K/F` nor finiteness of `M/F` is needed. -/
theorem _root_.AlgHom.continuous_restrictNormalHom {F K M : Type*} [Field F] [Field K] [Field M]
    [Algebra F K] [Algebra F M] (f : M →ₐ[F] K) [Normal F M] :
    Continuous f.restrictNormalHom := by
  refine (f.equivFieldRange.symm.continuous_autCongr.comp
    (InfiniteGalois.restrictNormalHom_continuous f.fieldRange)).congr fun σ ↦ ?_
  symm
  refine f.restrictNormalHom_eq_iff.2 fun x ↦ ?_
  simp only [Function.comp_apply, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
    AlgEquiv.symm_symm]
  symm
  rw [← AlgHom.equivFieldRange_apply_coe, AlgEquiv.apply_symm_apply,
    AlgEquiv.restrictNormalHom_apply, ← AlgHom.equivFieldRange_apply_coe]

/-- **Restriction to a normal intermediate field in a scalar tower is continuous** for the Krull
topologies, with no normality assumption on the top field `K/F`. -/
theorem _root_.AlgEquiv.continuous_restrictNormalHom {F : Type*} (M : Type*) {K : Type*} [Field F]
    [Field M] [Field K] [Algebra F M] [Algebra F K] [Algebra M K] [IsScalarTower F M K]
    [Normal F M] :
    Continuous (AlgEquiv.restrictNormalHom (F := F) (K₁ := K) M) := by
  rw [← AlgHom.restrictNormalHom_toAlgHom]
  exact (IsScalarTower.toAlgHom F M K).continuous_restrictNormalHom

/-- **The kernel of restriction to a finite normal extension is open** in the Krull topology. -/
theorem _root_.AlgHom.isOpen_ker_restrictNormalHom {F K M : Type*} [Field F] [Field K] [Field M]
    [Algebra F K] [Algebra F M] (f : M →ₐ[F] K) [FiniteDimensional F M] [Normal F M] :
    IsOpen (f.restrictNormalHom.ker : Set Gal(K/F)) := by
  have : FiniteDimensional F f.fieldRange := f.equivFieldRange.toLinearEquiv.finiteDimensional
  rw [f.ker_restrictNormalHom]
  exact f.fieldRange.fixingSubgroup_isOpen

/-- **The Galois group of an embedded normal extension is the topological quotient by the
restriction kernel**: for `E/F` and `M/F` normal and `f : M →ₐ[F] E`, restriction along `f`
descends to an isomorphism of topological groups `Gal(E/F) ⧸ f.restrictNormalHom.ker ≃ₜ* Gal(M/F)`.
-/
def _root_.AlgHom.quotientKerRestrictNormalHomEquiv {F E M : Type*} [Field F] [Field E] [Field M]
    [Algebra F E] [Algebra F M] (f : M →ₐ[F] E) [Normal F M] [Normal F E] :
    Gal(E/F) ⧸ f.restrictNormalHom.ker ≃ₜ* Gal(M/F) :=
  (Subgroup.quotientContinuousMulEquivOfEq f.ker_restrictNormalHom).trans <|
    (quotientFixingSubgroupEquiv F E f.fieldRange).trans f.equivFieldRange.symm.autContinuousCongr

/-- `quotientKerRestrictNormalHomEquiv` sends the class of `σ` to `f.restrictNormalHom σ`. -/
@[simp]
theorem _root_.AlgHom.quotientKerRestrictNormalHomEquiv_mk {F E M : Type*} [Field F] [Field E]
    [Field M] [Algebra F E] [Algebra F M] (f : M →ₐ[F] E) [Normal F M] [Normal F E]
    (σ : Gal(E/F)) :
    f.quotientKerRestrictNormalHomEquiv (σ : Gal(E/F) ⧸ f.restrictNormalHom.ker) =
      f.restrictNormalHom σ := by
  rw [AlgHom.quotientKerRestrictNormalHomEquiv, ContinuousMulEquiv.trans_apply,
    ContinuousMulEquiv.trans_apply, Subgroup.quotientContinuousMulEquivOfEq_mk,
    quotientFixingSubgroupEquiv_mk, AlgEquiv.autContinuousCongr_apply]
  symm
  refine f.restrictNormalHom_eq_iff.2 fun x ↦ ?_
  simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.symm_symm]
  symm
  rw [← AlgHom.equivFieldRange_apply_coe, AlgEquiv.apply_symm_apply,
    AlgEquiv.restrictNormalHom_apply, ← AlgHom.equivFieldRange_apply_coe]

/-- The inverse of `quotientKerRestrictNormalHomEquiv` sends `f.restrictNormalHom σ` back to the
class of `σ`. -/
@[simp]
theorem _root_.AlgHom.quotientKerRestrictNormalHomEquiv_symm_restrictNormalHom {F E M : Type*}
    [Field F] [Field E] [Field M] [Algebra F E] [Algebra F M] (f : M →ₐ[F] E) [Normal F M]
    [Normal F E] (σ : Gal(E/F)) :
    f.quotientKerRestrictNormalHomEquiv.symm (f.restrictNormalHom σ) =
      (σ : Gal(E/F) ⧸ f.restrictNormalHom.ker) := by
  rw [← f.quotientKerRestrictNormalHomEquiv_mk σ, ContinuousMulEquiv.symm_apply_apply]

end RestrictAlong

end TauCeti
