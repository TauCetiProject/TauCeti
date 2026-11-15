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
`F' / F`. Under the locally installed algebra structures `TauCeti.Place.completionExtensionAlgebra`
and `TauCeti.Place.completionIntegersExtensionAlgebra`, the completed valuation ring `𝒪̂_{P'}` is a
torsion-free `𝒪̂_P`-subalgebra of `F̂_{P'}`, and completion preserves the ramification index
`e(P' ∣ P)` without any residue-field hypothesis.

When the residue extension at `P'` is finite, `𝒪̂_{P'}` is finite over `𝒪̂_P`
(`TauCeti.Place.moduleFinite_completionIntegers`), hence integral over `𝒪̂_P`; since valuation
rings are integrally closed in their fraction fields, `𝒪̂_{P'}` is the integral closure of `𝒪̂_P`
in `F̂_{P'}` (`TauCeti.Place.isIntegralClosure_completionIntegers`). If `F' / F` is also separable,
every completed element of `F'` remains separable over `F̂_P`, and because those elements span
`F̂_{P'}` over `F̂_P`, the completed extension `F̂_{P'} / F̂_P` is separable as well
(`TauCeti.Place.isSeparable_completion`), regardless of whether the residue extension is separable.

When `F` and `F'` share a constant field `k`, the completed places `P'.completionPlace` and
`P.completionPlace` form an extension of places with `P'.completionPlace.restrict k P.Completion =
P.completionPlace` and matching relative degree. This makes `𝒪̂_P ⊆ 𝒪̂_{P'}` an instance of the
general local-extension and different-ideal machinery for discrete valuation rings.

The integral-closure identification parallels the affine-model theorem in
`TauCeti/RingTheory/DedekindDomain/AdicValuation/IntegralClosure.lean`, and the separability
transfer provides the intrinsic-place counterpart of
`TauCeti/NumberTheory/NumberField/LocalGlobal/Separable.lean`.

## Main results

* `TauCeti.Place.completionIntegersExtension_injective`,
  `TauCeti.Place.isScalarTower_completionIntegers`, and
  `TauCeti.Place.isTorsionFree_completionIntegers`: structural compatibility of the completed
  valuation-ring extension `𝒪̂_P → 𝒪̂_{P'} → F̂_{P'}`.
* `TauCeti.Place.ramificationIdx_completionPlace`: completion preserves the ramification index.
* `TauCeti.Place.isIntegralClosure_completionIntegers`: when the residue extension is finite,
  `𝒪̂_{P'}` is the integral closure of `𝒪̂_P` in `F̂_{P'}`.
* `TauCeti.Place.isSeparable_completionEmbedding` and `TauCeti.Place.isSeparable_completion`:
  when `F' / F` is separable, completed elements of `F'` are separable over `F̂_P`, and when the
  residue extension is finite `F̂_{P'} / F̂_P` is separable (even if the residue extension is
  inseparable).
* `TauCeti.Place.completionPlace_restrict` and `TauCeti.Place.relativeDegree_completionPlace`:
  over a common constant field, completion commutes with place restriction and preserves the
  full relative degree.

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

/-- The canonical map `𝒪̂_P →+* 𝒪̂_{P'}` of completed valuation rings is injective. -/
theorem completionIntegersExtension_injective :
    Function.Injective (P.completionIntegersExtension P' hP) := fun _ _ h ↦
  Subtype.ext <| (P.completionExtension P' hP).injective <| by
    simpa only [coe_completionIntegersExtension] using congrArg Subtype.val h

/-- The action of `𝒪̂_P` on `F̂_{P'}` factors through `𝒪̂_{P'}`. -/
theorem isScalarTower_completionIntegers :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    IsScalarTower P.completionPlace.integers P'.completionPlace.integers P'.Completion := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  rw [IsScalarTower.algebraMap_apply P.completionPlace.integers P.Completion P'.Completion,
    algebraMap_completionExtensionAlgebra, ValuationSubring.algebraMap_apply,
    ValuationSubring.algebraMap_apply, coe_algebraMap_completionIntegersExtensionAlgebra]

/-- The completed valuation ring `𝒪̂_{P'}` is torsion-free over `𝒪̂_P`. -/
theorem isTorsionFree_completionIntegers :
    letI := P.completionIntegersExtensionAlgebra P' hP
    Module.IsTorsionFree P.completionPlace.integers P'.completionPlace.integers := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := P.isScalarTower_completionIntegers P' hP
  exact (FaithfulSMul.algebraMap_injective
    P'.completionPlace.integers P'.Completion).moduleIsTorsionFree _ fun c x ↦
      map_smul (IsScalarTower.toAlgHom
        P.completionPlace.integers P'.completionPlace.integers P'.Completion) c x

/-- Completion preserves the ramification index, with no finiteness assumption on the residue
extension. -/
theorem ramificationIdx_completionPlace :
    letI := P.completionExtensionAlgebra P' hP
    ramificationIdx P.Completion P'.completionPlace = ramificationIdx F P' := by
  let _ := P.completionExtensionAlgebra P' hP
  rw [ramificationIdx_def,
    Valuation.ordIndex_eq_mul_of_forall_ord_eq _ P.completionPlace.valuation (fun x ↦ by
      rw [Valuation.ord_comap, ord_valuation, ord_valuation, algebraMap_completionExtensionAlgebra,
        P.ord_completionExtension P' hP x]),
    Valuation.ordIndex_eq_one_of_surjective _ P.completionPlace.valuation_surjective, mul_one]

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
        P'.completionEmbedding.toRingHom.comp (algebraMap F F') := by
    ext x
    simp [algebraMap_completionExtensionAlgebra]
  rw [aeval_def, eval₂_map, hcomp]
  simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_def] using
    (hom_eval₂ (minpoly F y) (algebraMap F F') P'.completionEmbedding.toRingHom y).symm.trans
      (by simp [← aeval_def])

section FiniteResidue

variable [FiniteDimensional (P'.restrict k F).ResidueField P'.ResidueField]

/-- **The completed valuation ring upstairs is the integral closure of the completed valuation
ring downstairs** when the residue extension is finite. Finiteness of the residue extension is
sharp here: without it `F̂_{P'}` need not even be algebraic over `F̂_P`. -/
theorem isIntegralClosure_completionIntegers :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    IsIntegralClosure P'.completionPlace.integers P.completionPlace.integers P'.Completion := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  have := P.isScalarTower_completionIntegers P' hP
  have := moduleFinite_completionIntegers P P' hP
  refine ⟨FaithfulSMul.algebraMap_injective P'.completionPlace.integers P'.Completion, fun {x} ↦
    ⟨fun hx ↦ ⟨⟨x, P'.completionPlace.mem_integers_of_isIntegral (fun r ↦ ?_) hx⟩, rfl⟩, ?_⟩⟩
  · rw [IsScalarTower.algebraMap_apply P.completionPlace.integers P.Completion P'.Completion,
      algebraMap_completionExtensionAlgebra]
    exact P.completionExtension_mem_integers P' hP r.2
  · rintro ⟨y, rfl⟩
    exact (Algebra.IsIntegral.isIntegral (R := P.completionPlace.integers) y).algebraMap

/-- **Completion preserves separability of the field extension**, with no separability hypothesis
on the residue extension: `F̂_{P'}` is spanned over `F̂_P` by elements from `F'`, each of which is
annihilated by the image of its separable minimal polynomial over `F`. -/
theorem isSeparable_completion [Algebra.IsSeparable F F'] :
    letI := P.completionExtensionAlgebra P' hP
    Algebra.IsSeparable P.Completion P'.Completion := by
  let _ := P.completionExtensionAlgebra P' hP
  let bκ := Module.finBasis (P'.restrict k F).ResidueField P'.ResidueField
  choose u hu using fun i ↦ residue_surjective (bκ i)
  obtain ⟨t, -, ht⟩ := P'.exists_ne_zero_ord_eq 1
  have ht0 : t ∈ P'.integers := P'.mem_integers_iff_ord_nonneg.mpr (by omega)
  have hsp : Submodule.span (P'.restrict k F).ResidueField
      (Set.range fun i ↦ residue P'.integers (u i)) = ⊤ := by
    simp [hu]
  have htop : (⊤ : Submodule P.Completion P'.Completion) ≤
      (separableClosure P.Completion P'.Completion).toSubmodule := by
    rw [← span_completion_eq_top P P' hP u hsp (t := ⟨t, ht0⟩) ht, Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact mem_separableClosure_iff.mpr (isSeparable_completionEmbedding P P' hP _)
  exact ⟨fun z ↦ mem_separableClosure_iff.mp (htop Submodule.mem_top)⟩

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
