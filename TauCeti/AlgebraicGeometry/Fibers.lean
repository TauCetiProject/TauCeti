/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.FunctionField
public import TauCeti.AlgebraicGeometry.PullbackSpecMap
public import TauCeti.RingTheory.DiscreteValuationRing.FractionRing

/-!
# Generic and special fibres

For a scheme over a ring `R`, this file defines its scalar-extension fibre along a ring map
`R → K`. For a local ring, it also defines the special fibre obtained by base change to the
residue field. The projection identities and pullback witnesses expose the defining squares.

When `R` is a discrete valuation ring and `K` is a fraction ring, the generic fibre is an open
subscheme of the total space. The special fibre over any local ring is a closed subscheme.

For a domain, the generic fibre is canonically isomorphic to Mathlib's scheme-theoretic fibre at
the generic point. Iterated scalar extension is also canonically isomorphic to direct scalar
extension, compatibly with both pullback projections.
-/

public section

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry IsLocalRing

namespace TauCeti

universe u

/-- The scalar extension of a scheme over `R` to a ring `K`, regarded as a scheme over `K`.
When `K` is a fraction field of `R`, this is the generic fibre. -/
noncomputable abbrev genericFiber (R K : Type u) [CommRing R] [CommRing K] [Algebra R K]
    {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) :
    Over (Spec (.of K)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj (Over.mk toBase)

/-- The canonical morphism from the scalar-extended fibre to the original total space. -/
noncomputable abbrev genericFiberι (R K : Type u) [CommRing R] [CommRing K] [Algebra R K]
    {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) :
    (genericFiber R K toBase).left ⟶ X :=
  pullback.fst toBase (Spec.map (CommRingCat.ofHom (algebraMap R K)))

/-- The special fibre of a scheme over a local ring, as a scheme over the residue field. -/
noncomputable abbrev specialFiber (R : Type u) [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) : Over (Spec (.of (ResidueField R))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R))))).obj
    (Over.mk toBase)

/-- The canonical morphism from the special fibre to the total space. -/
noncomputable abbrev specialFiberι (R : Type u) [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) : (specialFiber R toBase).left ⟶ X :=
  pullback.fst toBase (Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R))))

/-- The structure morphism of the generic fibre is the second projection of its defining
pullback square. -/
@[simp]
lemma genericFiber_hom (R K : Type u) [CommRing R] [CommRing K] [Algebra R K]
    {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) :
    (genericFiber R K toBase).hom =
      pullback.snd toBase (Spec.map (CommRingCat.ofHom (algebraMap R K))) := rfl

/-- The structure morphism of the special fibre is the second projection of its defining
pullback square. -/
@[simp]
lemma specialFiber_hom (R : Type u) [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) :
    (specialFiber R toBase).hom =
      pullback.snd toBase
        (Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R)))) := rfl

/-- The generic-fibre projections satisfy their defining commutativity identity. -/
@[reassoc (attr := simp)]
lemma genericFiberι_toBase (R K : Type u) [CommRing R] [CommRing K] [Algebra R K]
    {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) :
    genericFiberι R K toBase ≫ toBase =
      (genericFiber R K toBase).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K)) :=
  pullback.condition

/-- The special-fibre projections satisfy their defining commutativity identity. -/
@[reassoc (attr := simp)]
lemma specialFiberι_toBase (R : Type u) [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) :
    specialFiberι R toBase ≫ toBase =
      (specialFiber R toBase).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R))) :=
  pullback.condition

/-- The square defining the generic fibre is a pullback. -/
lemma isPullback_genericFiber (R K : Type u) [CommRing R] [CommRing K] [Algebra R K]
    {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) :
    IsPullback (genericFiberι R K toBase) (genericFiber R K toBase).hom toBase
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  rw [genericFiber_hom]
  exact IsPullback.of_hasPullback _ _

/-- The square defining the special fibre is a pullback. -/
lemma isPullback_specialFiber (R : Type u) [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) :
    IsPullback (specialFiberι R toBase) (specialFiber R toBase).hom toBase
      (Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R)))) := by
  rw [specialFiber_hom]
  exact IsPullback.of_hasPullback _ _

/-- The morphism from the spectrum of a DVR's fraction ring is an open immersion. -/
lemma isOpenImmersion_Spec_map_fractionRing (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing K] [Algebra R K] [IsFractionRing R K] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let : IsLocalization.Away ϖ K :=
    isLocalizationAway_fractionRing hϖ
  exact IsOpenImmersion.of_isLocalization ϖ

/-- The morphism from the spectrum of a local ring's residue field is a closed immersion. -/
lemma isClosedImmersion_Spec_map_residue (R : Type u) [CommRing R] [IsLocalRing R] :
    IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R)))) := by
  apply IsClosedImmersion.spec_of_surjective
  intro y
  obtain ⟨x, rfl⟩ := residue_surjective (R := R) y
  exact ⟨x, by simp [ResidueField.algebraMap_eq]⟩

/-- The generic fibre of a scheme over a discrete valuation ring is an open subscheme of the
total space. -/
lemma isOpenImmersion_genericFiberι (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) :
    IsOpenImmersion (genericFiberι R K toBase) := by
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    isOpenImmersion_Spec_map_fractionRing R K
  exact inferInstance

/-- The special fibre of a scheme over a local ring is a closed subscheme of the total space. -/
lemma isClosedImmersion_specialFiberι (R : Type u) [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) :
    IsClosedImmersion (specialFiberι R toBase) := by
  let : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R)))) :=
    isClosedImmersion_Spec_map_residue R
  exact inferInstance

section GenericPoint

variable (R : CommRingCat.{u}) (K : Type u) [IsDomain R]
variable [CommRing K] [Algebra R K] [IsFractionRing R K]

/-- A chosen fraction ring of a domain is isomorphic to the residue field at its generic prime.

The generic prime of `Spec R` is represented here by the zero ideal. Mathlib's
`genericPoint_eq_bot_of_affine` identifies this point with `genericPoint (Spec R)`. -/
private noncomputable def fractionRingEquivResidueFieldGenericPrime :
    K ≃+* (Spec R).residueField (⟨⊥, inferInstance⟩ : Spec R) :=
  (IsFractionRing.ringEquivOfRingEquiv (K := K)
      (L := (⊥ : Ideal R).ResidueField) (.refl R)).trans
    (Scheme.Spec.residueFieldIso R
      (⟨⊥, inferInstance⟩ : Spec R)).commRingCatIsoToRingEquiv.symm

/-- The fraction-ring equivalence at the generic prime respects the maps from the domain. -/
@[simp]
private lemma fractionRingEquivResidueFieldGenericPrime_algebraMap (r : R) :
    fractionRingEquivResidueFieldGenericPrime R K (algebraMap R K r) =
      (Scheme.Spec.residueFieldIso R (⟨⊥, inferInstance⟩ : Spec R)).inv
        (algebraMap R (⊥ : Ideal R).ResidueField r) := by
  -- `Iso.commRingCatIsoToRingEquiv` has no `symm`-application lemma, so it is unfolded here,
  -- as in `Mathlib/Algebra/Category/Ring/Constructions.lean`.
  simp [fractionRingEquivResidueFieldGenericPrime, Iso.commRingCatIsoToRingEquiv]

/-- The spectrum of a chosen fraction ring is isomorphic to the spectrum of the residue field at
the generic prime. -/
private noncomputable def specFractionRingIsoResidueFieldGenericPrime :
    Spec (.of K) ≅
      Spec (.of ((Spec R).residueField (⟨⊥, inferInstance⟩ : Spec R))) :=
  Scheme.Spec.mapIso
    (fractionRingEquivResidueFieldGenericPrime R K).toCommRingCatIso.symm.op

/-- The spectrum isomorphism from the fraction ring to the generic residue field commutes with
the two canonical maps to `Spec R`. -/
@[reassoc (attr := simp)]
private lemma specFractionRingIsoResidueFieldGenericPrime_hom_fromSpecResidueField :
    (specFractionRingIsoResidueFieldGenericPrime R K).hom ≫
        (Spec R).fromSpecResidueField (⟨⊥, inferInstance⟩ : Spec R) =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  erw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
  dsimp [specFractionRingIsoResidueFieldGenericPrime]
  rw [← Spec.map_comp_assoc]
  have h : CommRingCat.ofHom (algebraMap R (⊥ : Ideal R).ResidueField) ≫
        (Scheme.Spec.residueFieldIso R (⟨⊥, inferInstance⟩ : Spec R)).inv ≫
        (fractionRingEquivResidueFieldGenericPrime R K).toCommRingCatIso.inv =
      CommRingCat.ofHom (algebraMap R K) := by
    ext r
    simp only [RingEquiv.toCommRingCatIso_inv, CommRingCat.hom_comp,
      ConcreteCategory.hom_ofHom, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
    rw [← fractionRingEquivResidueFieldGenericPrime_algebraMap R K r,
      RingEquiv.symm_apply_apply]
  exact (Scheme.Spec.map_comp _ _).symm.trans (congrArg Spec.map h)

/-- The spectrum of a chosen fraction ring is isomorphic to the spectrum of the residue field at
the generic point. -/
noncomputable def specFractionRingIsoResidueFieldGenericPoint :
    Spec (.of K) ≅ Spec (.of ((Spec R).residueField (genericPoint (Spec R)))) :=
  specFractionRingIsoResidueFieldGenericPrime R K ≪≫
    Scheme.Spec.mapIso ((Spec R).residueFieldCongr
      (show genericPoint (Spec R) = (⟨⊥, inferInstance⟩ : Spec R) from
        genericPoint_eq_bot_of_affine R)).op

/-- The spectrum isomorphism from the fraction ring to the residue field at the generic point
commutes with the two canonical maps to `Spec R`. -/
@[reassoc (attr := simp)]
lemma specFractionRingIsoResidueFieldGenericPoint_hom_fromSpecResidueField :
    (specFractionRingIsoResidueFieldGenericPoint R K).hom ≫
        (Spec R).fromSpecResidueField (genericPoint (Spec R)) =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  rw [specFractionRingIsoResidueFieldGenericPoint, Iso.trans_hom, Category.assoc]
  exact (congrArg ((specFractionRingIsoResidueFieldGenericPrime R K).hom ≫ ·)
      (Scheme.residueFieldCongr_fromSpecResidueField
        (genericPoint_eq_bot_of_affine R))).trans
    (specFractionRingIsoResidueFieldGenericPrime_hom_fromSpecResidueField R K)

variable {R K} {X : Scheme.{u}} (toBase : X ⟶ Spec R)

/-- After identifying the fraction ring with the residue field at the generic point, the square
defining `genericFiber` is the square defining Mathlib's `Scheme.Hom.fiber`. -/
lemma isPullback_genericFiber_genericPoint :
    IsPullback (genericFiberι R K toBase)
      ((genericFiber R K toBase).hom ≫
        (specFractionRingIsoResidueFieldGenericPoint R K).hom)
      toBase ((Spec R).fromSpecResidueField (genericPoint (Spec R))) := by
  refine (isPullback_genericFiber R K toBase).of_iso (Iso.refl _) (Iso.refl _)
    (specFractionRingIsoResidueFieldGenericPoint R K) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · rfl
  · simp
  · simp

/-- The scalar-extension generic fibre is isomorphic to Mathlib's scheme-theoretic fibre at the
generic point. -/
noncomputable def genericFiberIsoFiberGenericPoint :
    (genericFiber R K toBase).left ≅ toBase.fiber (genericPoint (Spec R)) :=
  (isPullback_genericFiber_genericPoint toBase).isoIsPullback X
    (Spec (.of ((Spec R).residueField (genericPoint (Spec R)))))
    (IsPullback.of_hasPullback toBase
      ((Spec R).fromSpecResidueField (genericPoint (Spec R))))

/-- The generic-point fibre comparison commutes with the projections to the total space. -/
@[reassoc (attr := simp)]
lemma genericFiberIsoFiberGenericPoint_hom_fiberι :
    (genericFiberIsoFiberGenericPoint toBase).hom ≫
        toBase.fiberι (genericPoint (Spec R)) =
      genericFiberι R K toBase :=
  (isPullback_genericFiber_genericPoint toBase).isoIsPullback_hom_fst _ _
    (IsPullback.of_hasPullback toBase
      ((Spec R).fromSpecResidueField (genericPoint (Spec R))))

/-- The generic-point fibre comparison commutes with the projections to the residue-field
spectrum. -/
@[reassoc (attr := simp)]
lemma genericFiberIsoFiberGenericPoint_hom_fiberToSpecResidueField :
    (genericFiberIsoFiberGenericPoint toBase).hom ≫
        toBase.fiberToSpecResidueField (genericPoint (Spec R)) =
      (genericFiber R K toBase).hom ≫
        (specFractionRingIsoResidueFieldGenericPoint R K).hom :=
  (isPullback_genericFiber_genericPoint toBase).isoIsPullback_hom_snd _ _
    (IsPullback.of_hasPullback toBase
      ((Spec R).fromSpecResidueField (genericPoint (Spec R))))

/-- The inverse generic-point fibre comparison commutes with the projections to the total
space. -/
@[reassoc (attr := simp)]
lemma genericFiberIsoFiberGenericPoint_inv_genericFiberι :
    (genericFiberIsoFiberGenericPoint toBase).inv ≫ genericFiberι R K toBase =
      toBase.fiberι (genericPoint (Spec R)) :=
  (isPullback_genericFiber_genericPoint toBase).isoIsPullback_inv_fst _ _
    (IsPullback.of_hasPullback toBase
      ((Spec R).fromSpecResidueField (genericPoint (Spec R))))

/-- The inverse generic-point fibre comparison commutes with the projections to the
residue-field spectrum. -/
@[reassoc (attr := simp)]
lemma genericFiberIsoFiberGenericPoint_inv_hom :
    (genericFiberIsoFiberGenericPoint toBase).inv ≫
        pullback.snd toBase
          (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
        (specFractionRingIsoResidueFieldGenericPoint R K).hom =
      toBase.fiberToSpecResidueField (genericPoint (Spec R)) :=
  (isPullback_genericFiber_genericPoint toBase).isoIsPullback_inv_snd _ _
    (IsPullback.of_hasPullback toBase
      ((Spec R).fromSpecResidueField (genericPoint (Spec R))))

end GenericPoint

section Tower

variable (R K L : Type u) [CommRing R] [CommRing K] [CommRing L]
variable [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
variable {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R))

/-- Direct scalar extension from `R` to `L` is naturally isomorphic to scalar extension first to
`K` and then to `L`. -/
noncomputable def genericFiberTowerNatIso :
    Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≅
      Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⋙
        Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  eqToIso (by
    congr 2
    ext r
    exact IsScalarTower.algebraMap_apply R K L r) ≪≫
    TauCeti.AlgebraicGeometry.Over.pullbackSpecMapComp
      (CommRingCat.ofHom (algebraMap R K)) (CommRingCat.ofHom (algebraMap K L))

/-- Iterated scalar extension from `R` through `K` to `L` is a pullback of the direct map from
`R` to `L`. -/
lemma isPullback_genericFiberTower :
    IsPullback
      (genericFiberι K L (genericFiber R K toBase).hom ≫ genericFiberι R K toBase)
      (genericFiber K L (genericFiber R K toBase).hom).hom toBase
      (Spec.map (CommRingCat.ofHom (algebraMap R L))) := by
  have h := (isPullback_genericFiber K L (genericFiber R K toBase).hom).paste_horiz
    (isPullback_genericFiber R K toBase)
  refine h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
  · have hMap :
        Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R K)) =
          Spec.map (CommRingCat.ofHom (algebraMap R L)) := by
      rw [← Spec.map_comp]
      congr 1
      ext r
      exact (IsScalarTower.algebraMap_apply R K L r).symm
    simpa using hMap

/-- Iterated scalar extension is canonically isomorphic to direct scalar extension. -/
noncomputable def genericFiberTowerIso :
    (genericFiber K L (genericFiber R K toBase).hom).left ≅
      (genericFiber R L toBase).left :=
  (isPullback_genericFiberTower R K L toBase).isoIsPullback X (Spec (.of L))
    (isPullback_genericFiber R L toBase)

/-- The scalar-extension tower isomorphism commutes with the projections to the total space. -/
@[reassoc (attr := simp)]
lemma genericFiberTowerIso_hom_genericFiberι :
    (genericFiberTowerIso R K L toBase).hom ≫ genericFiberι R L toBase =
      genericFiberι K L (genericFiber R K toBase).hom ≫ genericFiberι R K toBase :=
  (isPullback_genericFiberTower R K L toBase).isoIsPullback_hom_fst _ _
    (isPullback_genericFiber R L toBase)

/-- The scalar-extension tower isomorphism commutes with the projections to `Spec L`. -/
@[reassoc (attr := simp)]
lemma genericFiberTowerIso_hom_hom :
    (genericFiberTowerIso R K L toBase).hom ≫
        pullback.snd toBase
          (Spec.map (CommRingCat.ofHom (algebraMap R L))) =
      (genericFiber K L (genericFiber R K toBase).hom).hom :=
  (isPullback_genericFiberTower R K L toBase).isoIsPullback_hom_snd _ _
    (isPullback_genericFiber R L toBase)

/-- The inverse scalar-extension tower isomorphism commutes with the projections to the total
space. -/
@[reassoc (attr := simp)]
lemma genericFiberTowerIso_inv_genericFiberι :
    (genericFiberTowerIso R K L toBase).inv ≫
        genericFiberι K L
          (pullback.snd toBase
            (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ≫
        genericFiberι R K toBase =
      genericFiberι R L toBase :=
  (isPullback_genericFiberTower R K L toBase).isoIsPullback_inv_fst _ _
    (isPullback_genericFiber R L toBase)

/-- The inverse scalar-extension tower isomorphism commutes with the projections to `Spec L`. -/
@[reassoc (attr := simp)]
lemma genericFiberTowerIso_inv_hom :
    (genericFiberTowerIso R K L toBase).inv ≫
        pullback.snd
          (pullback.snd toBase
            (Spec.map (CommRingCat.ofHom (algebraMap R K))))
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
      (genericFiber R L toBase).hom :=
  (isPullback_genericFiberTower R K L toBase).isoIsPullback_inv_snd _ _
    (isPullback_genericFiber R L toBase)

end Tower

end TauCeti
