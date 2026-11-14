/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Completion.LocalDegree
public import TauCeti.FieldTheory.FunctionField.Place.Completion.ResidueExtension

/-!
# Integrality and separability of completed extensions of function fields

Let `P'` be a place of `F' / k'` lying over the place `P` of `F / k`, where `F' / F` is an
integral extension and the residue extension `F'_{P'} / F_P` is finite (for instance when `F' / F`
is finite). Under the completed algebra structures `TauCeti.Place.completionExtensionAlgebra` and
`TauCeti.Place.completionIntegersExtensionAlgebra`:

* the completed valuation ring `𝒪̂_{P'}` is the integral closure of `𝒪̂_P` in `F̂'_{P'}`
  (`TauCeti.Place.isIntegralClosure_completionIntegers`);
* the image of `F'` generates `F̂'_{P'}` as an intermediate field over `F̂_P`
  (`TauCeti.Place.adjoin_range_completionEmbedding_eq_top`);
* if `F' / F` is separable, then the completed field extension `F̂'_{P'} / F̂_P` is separable
  (`TauCeti.Place.isSeparable_completion`), with no assumption on the characteristic or on the
  separability or finiteness of the residue fields;
* completion preserves the ramification index (`TauCeti.Place.ramificationIdx_completionPlace`),
  and, when the constant fields agree, the restriction of the completed place and the relative
  residue degree (`TauCeti.Place.restrict_completionPlace`,
  `TauCeti.Place.relativeDegree_completionPlace`).

Separability of `F̂'_{P'} / F̂_P` is proved directly from the expansion basis of
`TauCeti/FieldTheory/FunctionField/Place/Completion/LocalDegree.lean`: every element in the image
of `F'` is annihilated by the image of its minimal polynomial over `F`, hence is separable over
`F̂_P`, and the expansion basis lies in the image of `F'` and spans `F̂'_{P'}` over `F̂_P`. The
minimal-polynomial step adapts the argument of
`IsDedekindDomain.HeightOneSpectrum.isSeparable_adicCompletionExtension` in
`TauCeti/NumberTheory/NumberField/LocalGlobal/Separable.lean`, replacing dense Krasner-style or
characteristic-zero arguments with the explicit local expansion basis so that arbitrary positive
characteristic and inseparable residue extensions are covered.

## References

* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter II, §§2–3.
-/

public section

open IsLocalRing Polynomial

namespace TauCeti.Place

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

section General

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra.IsIntegral F F'] (P : Place k F) (P' : Place k' F')
  (hP : P'.restrict k F = P)

/-- The action of `𝒪̂_P` on `F̂'_{P'}` via `F̂_P` factors through `𝒪̂_{P'}`. -/
theorem isScalarTower_completionIntegersExtension :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    IsScalarTower P.completionPlace.integers P'.completionPlace.integers P'.Completion := by
  let := P.completionExtensionAlgebra P' hP
  let := P.completionIntegersExtensionAlgebra P' hP
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  rw [IsScalarTower.algebraMap_apply P.completionPlace.integers P.Completion P'.Completion,
    P.algebraMap_completionExtensionAlgebra P' hP]
  exact (P.coe_algebraMap_completionIntegersExtensionAlgebra P' hP x).symm

/-- The completed valuation ring above is torsion-free over the completed valuation ring below. -/
theorem isTorsionFree_completionIntegersExtension :
    letI := P.completionIntegersExtensionAlgebra P' hP
    Module.IsTorsionFree P.completionPlace.integers P'.completionPlace.integers := by
  let := P.completionIntegersExtensionAlgebra P' hP
  refine Module.IsTorsionFree.of_smul_eq_zero fun r m h ↦ ?_
  have h' : P.completionExtension P' hP r * (m : P'.Completion) = 0 := by
    simpa only [Algebra.smul_def, MulMemClass.coe_mul, ZeroMemClass.coe_zero,
      P.coe_algebraMap_completionIntegersExtensionAlgebra P' hP] using
      congrArg (fun z : P'.completionPlace.integers ↦ (z : P'.Completion)) h
  exact (mul_eq_zero.mp h').imp
    (fun hr ↦ Subtype.ext ((map_eq_zero _).mp hr))
    (fun hm ↦ Subtype.ext hm)

/-- Completion preserves the ramification index of `P'` over `P`. -/
@[simp]
theorem ramificationIdx_completionPlace :
    letI := P.completionExtensionAlgebra P' hP
    ramificationIdx P.Completion P'.completionPlace = ramificationIdx F P' := by
  let := P.completionExtensionAlgebra P' hP
  rw [ramificationIdx_def,
    Valuation.ordIndex_eq_mul_of_forall_ord_eq _ P.completionPlace.valuation
      (e := ramificationIdx F P') fun x ↦ by
        simpa only [Valuation.ord_comap, ← ord_valuation,
          P.algebraMap_completionExtensionAlgebra P' hP] using P.ord_completionExtension P' hP x,
    Valuation.ordIndex_eq_one_of_surjective _ P.completionPlace.valuation_surjective, mul_one]

/-- Every element of `F'` becomes separable over `F̂_P` inside `F̂'_{P'}` when `F' / F` is
separable: its minimal polynomial over `F` maps to a separable polynomial over `F̂_P` vanishing at
its image in `F̂'_{P'}`. -/
theorem isSeparable_completionEmbedding [Algebra.IsSeparable F F'] (x : F') :
    letI := P.completionExtensionAlgebra P' hP
    IsSeparable P.Completion (P'.completionEmbedding x) := by
  let := P.completionExtensionAlgebra P' hP
  have hsep : ((minpoly F x).map P.completionEmbedding.toRingHom).Separable :=
    Polynomial.Separable.map (Algebra.IsSeparable.isSeparable F x)
  have haeval : aeval (P'.completionEmbedding x)
      ((minpoly F x).map P.completionEmbedding.toRingHom) = 0 := by
    rw [aeval_def, eval₂_map, P.algebraMap_completionExtensionAlgebra P' hP]
    have hcomp : (P.completionExtension P' hP).comp P.completionEmbedding.toRingHom =
        P'.completionEmbedding.toRingHom.comp (algebraMap F F') :=
      RingHom.ext (P.completionExtension_completionEmbedding P' hP)
    have h0 := congrArg P'.completionEmbedding.toRingHom (minpoly.aeval F x)
    rw [map_zero, aeval_def,
      hom_eval₂ (minpoly F x) (algebraMap F F') P'.completionEmbedding.toRingHom x, ← hcomp] at h0
    exact h0
  exact hsep.of_dvd (minpoly.dvd P.Completion (P'.completionEmbedding x) haeval)

end General

section FiniteResidue

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra.IsIntegral F F'] (P : Place k F) (P' : Place k' F')
  (hP : P'.restrict k F = P)
  [FiniteDimensional (P'.restrict k F).ResidueField P'.ResidueField]

/-- When the residue extension is finite, the completed field extension is integral. -/
theorem isIntegral_completion :
    letI := P.completionExtensionAlgebra P' hP
    Algebra.IsIntegral P.Completion P'.Completion := by
  let := P.completionExtensionAlgebra P' hP
  have := P.finiteDimensional_completion P' hP
  exact Algebra.IsIntegral.of_finite P.Completion P'.Completion

/-- **The completed valuation ring `𝒪̂_{P'}` is the integral closure of `𝒪̂_P` in `F̂'_{P'}`.** -/
theorem isIntegralClosure_completionIntegers :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    IsIntegralClosure P'.completionPlace.integers P.completionPlace.integers P'.Completion := by
  let := P.completionExtensionAlgebra P' hP
  let := P.completionIntegersExtensionAlgebra P' hP
  have := P.isScalarTower_completionIntegersExtension P' hP
  have := P.moduleFinite_completionIntegers P' hP
  have : Algebra.IsIntegral P.completionPlace.integers P'.completionPlace.integers :=
    Algebra.IsIntegral.of_finite P.completionPlace.integers P'.completionPlace.integers
  refine ⟨Subtype.val_injective, fun {x} ↦ ⟨fun hx ↦ ?_, ?_⟩⟩
  · refine ⟨⟨x, P'.completionPlace.mem_integers_of_isIntegral (fun a ↦ ?_) hx⟩, rfl⟩
    rw [IsScalarTower.algebraMap_apply P.completionPlace.integers P'.completionPlace.integers
      P'.Completion]
    exact (algebraMap P.completionPlace.integers P'.completionPlace.integers a).2
  · rintro ⟨y, rfl⟩
    exact IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral y)

/-- The image of `F'` generates `F̂'_{P'}` over `F̂_P` when the residue extension is finite,
because `F'` already contains a residue basis and a uniformizer at `P'`. -/
theorem adjoin_range_completionEmbedding_eq_top :
    letI := P.completionExtensionAlgebra P' hP
    IntermediateField.adjoin P.Completion (Set.range P'.completionEmbedding) = ⊤ := by
  let := P.completionExtensionAlgebra P' hP
  let bκ := Module.finBasisOfFinrankEq (P'.restrict k F).ResidueField P'.ResidueField
    (relativeDegree_def k F P').symm
  choose u hu using fun i ↦ residue_surjective (bκ i)
  obtain ⟨t, -, ht⟩ := P'.exists_ne_zero_ord_eq 1
  let t' : P'.integers := ⟨t, by rw [mem_integers_iff_ord_nonneg, ht]; norm_num⟩
  have hsp : Submodule.span (P'.restrict k F).ResidueField
      (Set.range fun i ↦ residue P'.integers (u i)) = ⊤ := by
    simp [hu]
  have htop := P.span_completion_eq_top P' hP u hsp (t := t') ht
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Submodule.span P.Completion (Set.range P'.completionEmbedding) := by
    have hsub : Set.range (fun p : Fin (relativeDegree k F P') × Fin (ramificationIdx F P') ↦
        P'.completionEmbedding ((u p.1 : F') * (t' : F') ^ (p.2 : ℕ))) ⊆
        Set.range P'.completionEmbedding := by
      rintro _ ⟨p, rfl⟩
      exact ⟨(u p.1 : F') * (t' : F') ^ (p.2 : ℕ), rfl⟩
    exact Submodule.span_mono hsub (htop ▸ Submodule.mem_top)
  exact Submodule.span_le
    (p := (IntermediateField.adjoin P.Completion
      (Set.range P'.completionEmbedding)).toSubalgebra.toSubmodule)
    |>.mpr (fun y hy ↦ IntermediateField.subset_adjoin P.Completion _ hy) hx

/-- **Completion preserves separability of field extensions**: if `F' / F` is separable and the
residue extension at `P'` is finite, then `F̂'_{P'} / F̂_P` is separable. No assumption is made on
the characteristic or on the separability of the residue extension. -/
theorem isSeparable_completion [Algebra.IsSeparable F F'] :
    letI := P.completionExtensionAlgebra P' hP
    Algebra.IsSeparable P.Completion P'.Completion := by
  let := P.completionExtensionAlgebra P' hP
  have hadj : Algebra.IsSeparable P.Completion
      (IntermediateField.adjoin P.Completion (Set.range P'.completionEmbedding)) := by
    rw [IntermediateField.isSeparable_adjoin_iff_isSeparable]
    rintro _ ⟨x, rfl⟩
    exact P.isSeparable_completionEmbedding P' hP x
  have htop := P.adjoin_range_completionEmbedding_eq_top P' hP
  exact AlgEquiv.Algebra.isSeparable
    ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv)

end FiniteResidue

section Constants

variable {k F F' : Type*} [Field k] [Field F] [Field F']
  [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']
  [Algebra.IsIntegral F F'] (P : Place k F) (P' : Place k F')
  (hP : P'.restrict k F = P)
  [FiniteDimensional (P'.restrict k F).ResidueField P'.ResidueField]

/-- When the constant fields agree, the canonical place of `F̂'_{P'}` restricts to the canonical
place of `F̂_P`. -/
@[simp]
theorem restrict_completionPlace :
    letI := P.completionExtensionAlgebra P' hP
    haveI := P.isScalarTower_completionExtensionAlgebra P' hP
    haveI := P.isIntegral_completion P' hP
    P'.completionPlace.restrict k P.Completion = P.completionPlace := by
  let := P.completionExtensionAlgebra P' hP
  have := P.isScalarTower_completionExtensionAlgebra P' hP
  have := P.isIntegral_completion P' hP
  refine (restrict_eq_iff_exists_ord_eq k P.Completion P'.completionPlace P.completionPlace).mpr
    ⟨ramificationIdx F P', ramificationIdx_pos F P', fun x ↦ ?_⟩
  rw [P.algebraMap_completionExtensionAlgebra P' hP, P.ord_completionExtension P' hP]

/-- Completion preserves the relative residue degree of `P'` over `P` when viewed as an extension
of completed places over `k`. -/
@[simp]
theorem relativeDegree_completionPlace :
    letI := P.completionExtensionAlgebra P' hP
    haveI := P.isScalarTower_completionExtensionAlgebra P' hP
    haveI := P.isIntegral_completion P' hP
    relativeDegree k P.Completion P'.completionPlace = relativeDegree k F P' := by
  subst hP
  let := (P'.restrict k F).completionExtensionAlgebra P' rfl
  let := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  have := (P'.restrict k F).isScalarTower_completionExtensionAlgebra P' rfl
  have := (P'.restrict k F).isIntegral_completion P' rfl
  have hres := (P'.restrict k F).restrict_completionPlace P' rfl
  let eInt : (P'.completionPlace.restrict k (P'.restrict k F).Completion).integers ≃+*
      (P'.restrict k F).completionPlace.integers :=
    { toFun x := ⟨x.1, hres ▸ x.2⟩
      invFun x := ⟨x.1, hres.symm ▸ x.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_mul' _ _ := rfl
      map_add' _ _ := rfl }
  have : IsLocalHom eInt.toRingHom := ⟨fun x hx ↦ (isUnit_map_iff eInt x).mp hx⟩
  rw [relativeDegree_def, ← P'.finrank_residueField_completion (k := k) (F := F)]
  refine Algebra.finrank_eq_of_equiv_equiv (ResidueField.mapEquiv eInt) (RingEquiv.refl _) ?_
  ext x
  obtain ⟨x, rfl⟩ := residue_surjective x
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    ResidueField.algebraMap_residue]
  -- Unfold `(ResidueField.mapEquiv eInt).toRingHom` and `(RingEquiv.refl _).toRingHom` to the
  -- underlying `RingEquiv` applications so `ResidueField.mapEquiv_apply` applies.
  change algebraMap (P'.restrict k F).completionPlace.ResidueField P'.completionPlace.ResidueField
      (ResidueField.mapEquiv eInt (residue _ x)) =
    residue P'.completionPlace.integers (algebraMap _ P'.completionPlace.integers x)
  rw [ResidueField.mapEquiv_apply, ResidueField.map_residue, ResidueField.algebraMap_residue]
  refine congrArg (residue P'.completionPlace.integers) (Subtype.ext ?_)
  rw [coe_algebraMap_completionIntegersExtensionAlgebra, coe_algebraMap_integers,
    (P'.restrict k F).algebraMap_completionExtensionAlgebra P' rfl]
  rfl

end Constants

end TauCeti.Place
