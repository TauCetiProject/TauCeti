/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Invariant
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Transitivity

/-!
# The local invariant of an open subgroup of the absolute Galois group

Let `K` be a nonarchimedean local field with separable closure `Kˢ` and absolute Galois group
`G_K`. An open subgroup `U ≤ G_K` is the absolute Galois group of its fixed field `E`, a finite
extension of `K`, so `H²(U, (Kˢ)ˣ)` is the Brauer group `Br E`, and the local invariant of `E`
gives an invariant on it. This file constructs that invariant directly on `H²(U, (Kˢ)ˣ)`, inside
the single Galois module `(Kˢ)ˣ` over `G_K`, which is the form in which the class-formation axioms
for the units of `Kˢ` are stated.

Corestriction `H²(U, (Kˢ)ˣ) → H²(G_K, (Kˢ)ˣ) = Br K` is bijective
(`explicitCor2_unitsCoeff_bijective`): read through `G_E ≃ U`, it is corestriction of Brauer
classes along `E/K`, which preserves the local invariant
(`TauCeti.ClassFieldTheory.brCor_bijective`). The **invariant of `U`** is therefore defined as

`inv_U = inv_K ∘ cor_U^{G_K} : H²(U, (Kˢ)ˣ) ≃+ ℚ/ℤ`

(`subgroupInvMap`). It satisfies the compatibilities that the invariant maps of a class formation
are required to have:

* on a class transported from `Br L` along a `K`-embedding `σ : L → Kˢ`, it is the local
  invariant of `L` (`subgroupInvMap_explicitMap2`);
* restriction to an open subgroup `V ≤ U` multiplies the invariant by the index `[U : V]`
  (`subgroupInvMap_explicitMap2_subgroupInclusion`, and `subgroupInvMap_explicitRes2` for
  `U = G_K`);
* corestriction from `V` to `U` preserves the invariant (`subgroupInvMap_explicitCor2Le`).

## Main definitions

* `TauCeti.ClassFieldTheory.subgroupInvMap K U hU`: the local invariant
  `H²(U, (Kˢ)ˣ) ≃+ ℚ/ℤ` of an open subgroup `U` of `G_K`.

## Main results

* `TauCeti.ClassFieldTheory.explicitCor2_unitsCoeff_bijective`: corestriction from an open
  subgroup of `G_K` is bijective on `H²` of `(Kˢ)ˣ`.
* `TauCeti.ClassFieldTheory.subgroupInvMap_explicitMap2`: the invariant of the subgroup cut out by
  a finite extension `L/K` is the local invariant of `L`.
* `TauCeti.ClassFieldTheory.subgroupInvMap_explicitMap2_subgroupInclusion`: restriction multiplies
  the invariant by the relative index.
* `TauCeti.ClassFieldTheory.subgroupInvMap_explicitCor2Le`: corestriction preserves the invariant.

## Implementation notes

The subgroup `U` is a plain `Subgroup` with a proof of openness, and its finite index is an instance
argument, as for `TauCeti.ContCohomology.explicitCor2`. For an `OpenSubgroup` the instance is
`OpenSubgroup.finiteIndex_toSubgroup`, and for the subgroup `Gal(Kˢ/σ(L))` fixing the image of a
`K`-embedding it is `TauCeti.finiteIndex_fixingSubgroup_fieldRange`, so both kinds of subgroup are
accepted without transport.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §1.
* J.-P. Serre, *Local Fields*, Chapter XI, §1 and Chapter XIII, §3.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open ContCohomology

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **Corestriction from an open subgroup of `G_K` is bijective on `H²` of `(Kˢ)ˣ`.** The subgroup
is the absolute Galois group of its fixed field `E`, a finite extension of `K`, and through this
identification corestriction is corestriction of Brauer classes along `E/K`
(`TauCeti.ClassFieldTheory.brCor_bijective`). -/
theorem explicitCor2_unitsCoeff_bijective (U : Subgroup (AbsoluteGaloisGroup K)) [U.FiniteIndex]
    (hU : IsOpen (U : Set (AbsoluteGaloisGroup K))) :
    Function.Bijective (explicitCor2 (AbsoluteGaloisGroup K) (UnitsCoeff K) U hU) := by
  -- `U` is the subgroup fixing its fixed field `E`, which is finite over `K`.
  obtain ⟨E, _, rfl⟩ : ∃ E : IntermediateField K (SeparableClosure K),
      FiniteDimensional K E ∧ E.val.fieldRange.fixingSubgroup = U := by
    obtain ⟨E, hE⟩ : ∃ E : IntermediateField K (SeparableClosure K), E.fixingSubgroup = U :=
      ⟨_, InfiniteGalois.fixingSubgroup_fixedField ⟨U, Subgroup.isClosed_of_isOpen U hU⟩⟩
    refine ⟨E, ?_, by rw [IntermediateField.fieldRange_val, hE]⟩
    rw [← InfiniteGalois.isOpen_iff_finite, hE]
    exact hU
  -- The canonical structure of nonarchimedean local field on `E`.
  let _ := finiteExtensionValuativeRel K E
  let _ := finiteExtensionNormedFieldTopology K E
  have := finiteExtension_isNonarchimedeanLocalField K E
  have := finiteExtension_valuativeExtension K E
  -- Read through the transport `T` from `G_E` to `Gal(Kˢ/E)`, corestriction is `brCor`, and `T`
  -- is surjective, with a right inverse given by the transport the other way.
  let T := explicitMap2 (AbsoluteGaloisGroup E) (UnitsCoeff E) ↥E.val.fieldRange.fixingSubgroup
    (UnitsCoeff K) ((absoluteGaloisGroupEquivFixingSubgroup K E E.val).symm :
      ↥E.val.fieldRange.fixingSubgroup →ₜ* AbsoluteGaloisGroup E)
    (unitsCoeffMapSymm K E E.val) continuous_of_discreteTopology (unitsCoeffMapSymm_smul K E E.val)
  have hT : Function.RightInverse (explicitMap2 ↥E.val.fieldRange.fixingSubgroup (UnitsCoeff K)
      (AbsoluteGaloisGroup E) (UnitsCoeff E) (absoluteGaloisGroupEquivFixingSubgroup K E E.val :
        AbsoluteGaloisGroup E →ₜ* ↥E.val.fieldRange.fixingSubgroup)
      (unitsCoeffMap K E E.val) continuous_of_discreteTopology (unitsCoeffMap_smul K E E.val)) T :=
    explicitMap2_unitsCoeffMapSymm_explicitMap2_unitsCoeffMap K E E.val
  have hcomp : explicitCor2 (AbsoluteGaloisGroup K) (UnitsCoeff K) _ hU ∘ T =
      (unitsRepH2Equiv K).symm ∘ brCor K E E.val ∘ unitsRepH2Equiv E := by
    funext y
    simp only [Function.comp_apply, brCor_apply, AddEquiv.symm_apply_apply]
    -- The two corestrictions differ only in their proofs that the subgroup is open and of finite
    -- index.
    rfl
  have hbij :
      Function.Bijective (explicitCor2 (AbsoluteGaloisGroup K) (UnitsCoeff K) _ hU ∘ T) := by
    rw [hcomp]
    exact (unitsRepH2Equiv K).symm.bijective.comp
      ((brCor_bijective K E E.val).comp (unitsRepH2Equiv E).bijective)
  refine ⟨fun a b hab => ?_, hbij.2.of_comp⟩
  rw [← hT a, ← hT b] at hab ⊢
  exact congrArg T (hbij.1 hab)

/-- **The local invariant of an open subgroup** `U` of `G_K`: the invariant
`H²(U, (Kˢ)ˣ) ≃+ ℚ/ℤ` obtained by corestriction to `Br K = H²(G_K, (Kˢ)ˣ)`, which is bijective
(`explicitCor2_unitsCoeff_bijective`), followed by the local invariant `invMap K`. On a class
transported from the Brauer group of a finite extension `L/K` it is the local invariant of `L`
(`subgroupInvMap_explicitMap2`). -/
def subgroupInvMap (U : Subgroup (AbsoluteGaloisGroup K)) [U.FiniteIndex]
    (hU : IsOpen (U : Set (AbsoluteGaloisGroup K))) :
    H2 U (UnitsCoeff K) ≃+ AddCircle (1 : ℚ) :=
  ((AddEquiv.ofBijective _ (explicitCor2_unitsCoeff_bijective K U hU)).trans
    (unitsRepH2Equiv K)).trans (invMap K)

/-- The invariant of an open subgroup is the local invariant of the corestriction to `G_K`. -/
theorem subgroupInvMap_apply (U : Subgroup (AbsoluteGaloisGroup K)) [U.FiniteIndex]
    (hU : IsOpen (U : Set (AbsoluteGaloisGroup K))) (x : H2 U (UnitsCoeff K)) :
    subgroupInvMap K U hU x =
      invMap K (unitsRepH2Equiv K (explicitCor2 (AbsoluteGaloisGroup K) (UnitsCoeff K) U hU x)) :=
  (rfl)

/-- **The normalization of the invariant of an open subgroup**: for a finite extension `L/K`
embedded in `Kˢ` by `σ`, a Brauer class of `L`, transported to `H²` of the subgroup
`Gal(Kˢ/σ(L))` of `G_K` along `G_L ≃ Gal(Kˢ/σ(L))` and the identification of separable closures,
has the local invariant of `L` as invariant. -/
@[simp]
theorem subgroupInvMap_explicitMap2 (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
    (σ : L →ₐ[K] SeparableClosure K) (y : Br L) :
    subgroupInvMap K σ.fieldRange.fixingSubgroup (isOpen_fixingSubgroup_fieldRange K L σ)
        (explicitMap2 (AbsoluteGaloisGroup L) (UnitsCoeff L) ↥σ.fieldRange.fixingSubgroup
          (UnitsCoeff K)
          ((absoluteGaloisGroupEquivFixingSubgroup K L σ).symm :
            ↥σ.fieldRange.fixingSubgroup →ₜ* AbsoluteGaloisGroup L)
          (unitsCoeffMapSymm K L σ) continuous_of_discreteTopology
          (unitsCoeffMapSymm_smul K L σ) ((unitsRepH2Equiv L).symm y)) =
      invMap L y := by
  rw [subgroupInvMap_apply, ← brCor_apply, invMap_brCor]

/-- **Restriction from `G_K` multiplies the invariant by the index**:
`inv_U (res x) = [G_K : U] • inv_K x`, since `cor ∘ res` is multiplication by the index. -/
@[simp]
theorem subgroupInvMap_explicitRes2 (U : Subgroup (AbsoluteGaloisGroup K)) [U.FiniteIndex]
    (hU : IsOpen (U : Set (AbsoluteGaloisGroup K)))
    (x : H2 (AbsoluteGaloisGroup K) (UnitsCoeff K)) :
    subgroupInvMap K U hU (explicitRes2 (AbsoluteGaloisGroup K) (UnitsCoeff K) U x) =
      U.index • invMap K (unitsRepH2Equiv K x) := by
  rw [subgroupInvMap_apply, explicitCor2_comp_res2, map_nsmul, map_nsmul]

section Relative

variable (U V : Subgroup (AbsoluteGaloisGroup K)) [U.FiniteIndex] [V.FiniteIndex]
  (hU : IsOpen (U : Set (AbsoluteGaloisGroup K))) (hV : IsOpen (V : Set (AbsoluteGaloisGroup K)))
  (hVU : V ≤ U)

/-- **Corestriction preserves the invariant**: for open subgroups `V ≤ U` of `G_K`,
`inv_U (cor_V^U y) = inv_V y`, by transitivity of corestriction. -/
theorem subgroupInvMap_explicitCor2Le (y : H2 V (UnitsCoeff K)) :
    subgroupInvMap K U hU (explicitCor2Le (AbsoluteGaloisGroup K) (UnitsCoeff K) U V hVU
      (Subgroup.subgroupOf_isOpen U V hV) y) = subgroupInvMap K V hV y := by
  rw [subgroupInvMap_apply, subgroupInvMap_apply,
    explicitCor2_trans (AbsoluteGaloisGroup K) (UnitsCoeff K) U V hVU hU hV,
    AddMonoidHom.comp_apply]

/-- **Restriction multiplies the invariant by the relative index**: for open subgroups `V ≤ U` of
`G_K`, `inv_V (res_U^V x) = [U : V] • inv_U x`. -/
theorem subgroupInvMap_explicitMap2_subgroupInclusion (x : H2 U (UnitsCoeff K)) :
    subgroupInvMap K V hV (explicitMap2 U (UnitsCoeff K) V (UnitsCoeff K)
      (ContinuousMonoidHom.subgroupInclusion hVU) (AddMonoidHom.id _) continuous_id
      (fun _ _ => rfl) x) = V.relIndex U • subgroupInvMap K U hU x := by
  rw [← subgroupInvMap_explicitCor2Le K U V hU hV hVU,
    explicitCor2Le_explicitMap2_subgroupInclusion, map_nsmul]

end Relative

end TauCeti.ClassFieldTheory
