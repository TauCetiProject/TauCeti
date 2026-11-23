/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Completion.LocalDegree
public import TauCeti.FieldTheory.FunctionField.Place.Completion.ResidueExtension
import Mathlib.FieldTheory.SeparableClosure

/-!
# Integral closure, separability, and local invariants of completed places

Let `P'` be a place of `F' / k'` lying over a place `P` of `F / k` in an integral field extension
`F' / F`. Without any residue-field finiteness hypothesis, the local integral closure `𝒪'_P` of
`𝒪_P` in `F'` embeds injectively into the completed valuation ring `𝒪̂_{P'}` via
`TauCeti.Place.completionIntegersIntegralClosureHom`, and when `F' / F` is separable every
completed element of `F'` remains separable over `F̂_P`
(`TauCeti.Place.isSeparable_completionEmbedding`).

Under the locally installed algebra structures `TauCeti.Place.completionExtensionAlgebra` and
`TauCeti.Place.completionIntegersExtensionAlgebra`, when the residue extension at `P'` is finite,
`𝒪̂_{P'}` is finite over `𝒪̂_P` (`TauCeti.Place.moduleFinite_completionIntegers`), hence integral
over `𝒪̂_P`; since valuation rings are integrally closed in their fraction fields, `𝒪̂_{P'}` is the
integral closure of `𝒪̂_P` in `F̂_{P'}` (`TauCeti.Place.isIntegralClosure_completionIntegers`). If
`F' / F` is also separable, those completed elements of `F'` span `F̂_{P'}` over `F̂_P`, so the
completed extension `F̂_{P'} / F̂_P` is separable as well (`TauCeti.Place.isSeparable_completion`),
regardless of whether the residue extension is separable.

When `F` and `F'` share a constant field `k` and the residue extension is finite, the completed
places `P'.completionPlace` and `P.completionPlace` form an extension of places with
`P'.completionPlace.restrict k P.Completion = P.completionPlace` and matching relative degree. This
makes `𝒪̂_P ⊆ 𝒪̂_{P'}` an instance of the general local-extension and different-ideal machinery for
discrete valuation rings.

The integral-closure identification parallels the affine-model theorem in
`TauCeti/RingTheory/DedekindDomain/AdicValuation/IntegralClosure.lean`, and the separability
transfer provides the intrinsic-place counterpart of
`TauCeti/NumberTheory/NumberField/LocalGlobal/Separable.lean`.

## Main definitions

* `TauCeti.Place.completionIntegersIntegralClosureHom`: the canonical ring homomorphism
  `𝒪'_P →+* 𝒪̂_{P'}` from the local integral closure at `P` to the completed valuation ring at `P'`.

## Main results

* `TauCeti.Place.completionIntegersIntegralClosureHom_injective`: the canonical homomorphism
  `𝒪'_P →+* 𝒪̂_{P'}` is injective.
* `TauCeti.Place.isIntegralClosure_completionIntegers`: when the residue extension is finite,
  `𝒪̂_{P'}` is the integral closure of `𝒪̂_P` in `F̂_{P'}`.
* `TauCeti.Place.isSeparable_completionEmbedding` and `TauCeti.Place.isSeparable_completion`:
  when `F' / F` is separable, completed elements of `F'` are separable over `F̂_P`, and when the
  residue extension is finite `F̂_{P'} / F̂_P` is separable (even if the residue extension is
  inseparable).
* `TauCeti.Place.completionPlace_restrict` and `TauCeti.Place.relativeDegree_completionPlace`:
  over a common constant field and with finite residue extension, completion commutes with place
  restriction and preserves the full relative degree.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Sections I.7 and III.1.
* J.-P. Serre, *Local Fields*, Chapter II, Section 3.
-/

public section

open Polynomial IsLocalRing

namespace TauCeti.Place

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

section General

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra.IsIntegral F F'] (P : Place k F) (P' : Place k' F')
  (hP : P'.restrict k F = P)

/-- Every element of `F'` remains separable over `F̂_P` inside `F̂_{P'}`. -/
theorem isSeparable_completionEmbedding [Algebra.IsSeparable F F'] (y : F') :
    letI := P.completionExtensionAlgebra P' hP
    IsSeparable P.Completion (P'.completionEmbedding y) := by
  let _ := P.completionExtensionAlgebra P' hP
  have hsep : ((minpoly F y).map P.completionEmbedding.toRingHom).Separable :=
    Polynomial.Separable.map (Algebra.IsSeparable.isSeparable F y)
  refine hsep.of_dvd (minpoly.dvd P.Completion (P'.completionEmbedding y) ?_)
  have hcomp :
      (algebraMap P.Completion P'.Completion).comp P.completionEmbedding.toRingHom =
        (P'.completionEmbedding : F' →+* P'.Completion).comp (algebraMap F F') := by
    ext x
    simp [algebraMap_completionExtensionAlgebra]
  rw [aeval_def, eval₂_map, hcomp, ← AlgHom.coe_toRingHom (f := P'.completionEmbedding),
    ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]

/-- The canonical ring homomorphism from the local integral closure `𝒪'_P` to the completed
valuation ring `𝒪̂_{P'}` at a place `P'` lying over `P`. -/
noncomputable def completionIntegersIntegralClosureHom :
    integralClosure P.integers F' →+* P'.completionPlace.integers :=
  P'.completionIntegersEmbedding.toRingHom.comp
    ((algebraMap (integralClosure P.integers F') F').codRestrict P'.integers fun b ↦ by
      subst hP
      exact algebraMap_mem_integers_of_mem_integralClosure k F P' b)

/-- Coercing `completionIntegersIntegralClosureHom` to `F̂_{P'}` is `P'.completionEmbedding`. -/
@[simp]
theorem coe_completionIntegersIntegralClosureHom (b : integralClosure P.integers F') :
    (P.completionIntegersIntegralClosureHom P' hP b : P'.Completion) =
      P'.completionEmbedding (b : F') := by
  simp [completionIntegersIntegralClosureHom]

/-- On `𝒪_P`, `completionIntegersIntegralClosureHom` agrees with `completionIntegersExtension`. -/
@[simp]
theorem completionIntegersIntegralClosureHom_algebraMap (r : P.integers) :
    P.completionIntegersIntegralClosureHom P' hP
        (algebraMap P.integers (integralClosure P.integers F') r) =
      P.completionIntegersExtension P' hP (P.completionIntegersEmbedding r) := by
  apply Subtype.ext
  simp [coe_completionIntegersIntegralClosureHom, IsScalarTower.algebraMap_apply P.integers F F']

/-- The canonical homomorphism `𝒪'_P →+* 𝒪̂_{P'}` is injective. -/
theorem completionIntegersIntegralClosureHom_injective :
    Function.Injective (P.completionIntegersIntegralClosureHom P' hP) := fun _ _ h ↦
  Subtype.ext <| P'.completionEmbedding.toRingHom.injective <| by
    simpa only [coe_completionIntegersIntegralClosureHom, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe] using congrArg Subtype.val h

section FiniteResidue

variable [FiniteDimensional (P'.restrict k F).ResidueField P'.ResidueField]

end FiniteResidue

end General

section SameConstants

variable {k F F' : Type*} [Field k] [Field F] [Field F']
  [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']
  [Algebra.IsIntegral F F'] (P : Place k F) (P' : Place k F')
  (hP : P'.restrict k F = P)
  [FiniteDimensional (P'.restrict k F).ResidueField P'.ResidueField]

/-- Over a common constant field `k`, the completed place `P'.completionPlace` restricts to
`P.completionPlace` along the completed field extension. -/
theorem completionPlace_restrict :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.isScalarTower_completionExtensionAlgebra P' hP
    haveI : FiniteDimensional P.Completion P'.Completion := finiteDimensional_completion P P' hP
    P'.completionPlace.restrict k P.Completion = P.completionPlace := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.isScalarTower_completionExtensionAlgebra P' hP
  have : FiniteDimensional P.Completion P'.Completion := finiteDimensional_completion P P' hP
  rw [restrict_eq_iff_exists_ord_eq]
  refine ⟨ramificationIdx F P', ramificationIdx_pos F P', fun x ↦ ?_⟩
  rw [algebraMap_completionExtensionAlgebra, P.ord_completionExtension P' hP x]

/-- Over a common constant field `k`, completion preserves the full relative degree `f(P' ∣ P)`,
including any inseparable residue factor. -/
theorem relativeDegree_completionPlace :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.isScalarTower_completionExtensionAlgebra P' hP
    haveI : FiniteDimensional P.Completion P'.Completion := finiteDimensional_completion P P' hP
    relativeDegree k P.Completion P'.completionPlace = relativeDegree k F P' := by
  subst hP
  let P := P'.restrict k F
  let _ := P.completionExtensionAlgebra P' rfl
  let _ := P.isScalarTower_completionExtensionAlgebra P' rfl
  let _ := P.completionIntegersExtensionAlgebra P' rfl
  have : FiniteDimensional P.Completion P'.Completion := finiteDimensional_completion P P' rfl
  let Q := P'.completionPlace.restrict k P.Completion
  have hsub : Q.integers.toSubring = P.completionPlace.integers.toSubring :=
    congrArg (fun R : Place k P.Completion ↦ R.integers.toSubring)
      (completionPlace_restrict P P' rfl)
  rw [relativeDegree_def, ← P'.finrank_residueField_completion (k := k) (F := F)]
  refine Algebra.finrank_eq_of_equiv_equiv (ResidueField.mapEquiv (RingEquiv.subringCongr hsub))
    (.refl _) ?_
  ext x
  obtain ⟨a, rfl⟩ := residue_surjective x
  simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, Function.comp_apply,
    RingEquiv.refl_apply, ResidueField.mapEquiv_apply, ResidueField.map_residue,
    ResidueField.algebraMap_residue]
  congr 1
  apply Subtype.ext
  rw [coe_algebraMap_integers, coe_algebraMap_completionIntegersExtensionAlgebra,
    algebraMap_completionExtensionAlgebra, RingEquiv.coe_subringCongr_apply]

end SameConstants

end TauCeti.Place
