/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import TauCeti.AlgebraicGeometry.Fibers

/-!
# The special fibre as the fibre at the closed point

For a scheme over a local ring, base change to the ring's residue field agrees with the
scheme-theoretic fibre at the closed point. The two residue fields are constructed differently:
one is the quotient by the maximal ideal, while the other is the residue field of the scheme
point. This file gives their canonical equivalence and the resulting comparison of fibres,
including its projection identities.

The comparison lets statements about the special fibre be transported between its base-change
presentation and the fibre over the closed point, while preserving both projections.

Every point of the spectrum of a local domain of Krull dimension at most one, such as a discrete
valuation ring, is its generic point or its closed point, which coincide when the ring is a field
(`IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top`). Combined with the generic-point comparison of
`TauCeti.AlgebraicGeometry.Fibers`, a property of morphisms invariant under isomorphism therefore
holds on every fibre of a scheme over such a ring exactly when it holds on the generic and the
special fibre (`TauCeti.forall_fiberToSpecResidueField_iff`). This turns
fibrewise criteria, such as the one for nodal curves, into conditions on these two fibres.
-/

public section

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry IsLocalRing

namespace TauCeti

universe u

section ClosedPoint

variable (R : CommRingCat.{u}) [IsLocalRing R]
variable {X : Scheme.{u}} (toBase : X ⟶ Spec R)

-- The construction uses Mathlib's `Scheme.Spec.residueFieldIso` and
-- `Ideal.bijective_algebraMap_quotient_residueField`.
/-- The two constructions of the residue field at a local ring's closed point agree. -/
noncomputable def localResidueFieldEquiv :
    ResidueField R ≃+* (Spec R).residueField (closedPoint R) :=
  (RingEquiv.ofBijective (algebraMap (R ⧸ maximalIdeal R) (maximalIdeal R).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))).trans
      (Scheme.Spec.residueFieldIso R (closedPoint R)).commRingCatIsoToRingEquiv.symm

/-- The closed-point residue-field equivalence respects the map from the local ring. -/
@[simp]
lemma localResidueFieldEquiv_algebraMap (r : R) :
    localResidueFieldEquiv R (residue R r) =
      (Scheme.Spec.residueFieldIso R (closedPoint R)).inv
        (algebraMap R (maximalIdeal R).ResidueField r) := by
  rw [← ResidueField.algebraMap_eq]
  simp only [localResidueFieldEquiv]
  rw [← Ideal.algebraMap_quotient_residueField_mk (maximalIdeal R) r]
  rfl

/-- The spectrum of a local ring's residue field is the spectrum of the residue field at its
closed point. -/
noncomputable def specLocalResidueFieldIso :
    Spec (.of (ResidueField R)) ≅
      Spec (.of ((Spec R).residueField (closedPoint R))) :=
  Scheme.Spec.mapIso (localResidueFieldEquiv R).toCommRingCatIso.symm.op

/-- The residue-field map from a local ring is the canonical map from its closed point,
after identifying the two presentations of the residue field. -/
@[reassoc (attr := simp)]
lemma specLocalResidueFieldIso_hom_fromSpecResidueField :
    (specLocalResidueFieldIso R).hom ≫
        (Spec R).fromSpecResidueField (closedPoint R) =
      Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R))) := by
  erw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
  dsimp [specLocalResidueFieldIso]
  rw [← Spec.map_comp_assoc]
  have h : CommRingCat.ofHom (algebraMap R (maximalIdeal R).ResidueField) ≫
      (Scheme.Spec.residueFieldIso R (closedPoint R)).inv ≫
      (localResidueFieldEquiv R).toCommRingCatIso.inv =
        CommRingCat.ofHom (algebraMap R (ResidueField R)) := by
    ext r
    -- `CommRingCat` composition obscures the two residue-field equivalences.
    change (localResidueFieldEquiv R).symm
      ((Scheme.Spec.residueFieldIso R (closedPoint R)).inv
        (algebraMap R (maximalIdeal R).ResidueField r)) =
      algebraMap R (ResidueField R) r
    exact (localResidueFieldEquiv R).symm_apply_eq.mpr
      (localResidueFieldEquiv_algebraMap R r).symm
  exact (Scheme.Spec.map_comp _ _).symm.trans (congrArg Spec.map h)

-- The projection comparison follows the generic-point pattern in
-- `TauCeti/AlgebraicGeometry/Fibers.lean`.
/-- The square defining the special fibre is the scheme-theoretic fibre square over the
closed point of the base. -/
lemma isPullback_specialFiber_closedPoint :
    IsPullback (specialFiberι R toBase)
      ((specialFiber R toBase).hom ≫
        (specLocalResidueFieldIso R).hom)
      toBase ((Spec R).fromSpecResidueField (closedPoint R)) := by
  refine (isPullback_specialFiber R toBase).of_iso (Iso.refl _) (Iso.refl _)
    (specLocalResidueFieldIso R)
    (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · rfl
  · simp
  · exact (Category.comp_id _).trans
      (specLocalResidueFieldIso_hom_fromSpecResidueField R).symm

/-- The special fibre over the residue field of a local ring is canonically isomorphic to
Mathlib's fibre at the closed point. -/
noncomputable def specialFiberIsoFiberClosedPoint :
    (specialFiber R toBase).left ≅ toBase.fiber (closedPoint R) :=
  (isPullback_specialFiber_closedPoint R toBase).isoIsPullback X
    (Spec (.of ((Spec R).residueField (closedPoint R))))
    (IsPullback.of_hasPullback toBase
      ((Spec R).fromSpecResidueField (closedPoint R)))

/-- The closed-point fibre comparison preserves the maps to the total space. -/
@[reassoc (attr := simp)]
lemma specialFiberIsoFiberClosedPoint_hom_fiberι :
    (specialFiberIsoFiberClosedPoint R toBase).hom ≫
        toBase.fiberι (closedPoint R) = specialFiberι R toBase :=
  (isPullback_specialFiber_closedPoint R toBase).isoIsPullback_hom_fst _ _
    (IsPullback.of_hasPullback toBase
      ((Spec R).fromSpecResidueField (closedPoint R)))

/-- The closed-point fibre comparison preserves the maps to the residue-field spectrum. -/
@[reassoc (attr := simp)]
lemma specialFiberIsoFiberClosedPoint_hom_fiberToSpecResidueField :
    (specialFiberIsoFiberClosedPoint R toBase).hom ≫
        toBase.fiberToSpecResidueField (closedPoint R) =
      (specialFiber R toBase).hom ≫
        (specLocalResidueFieldIso R).hom :=
  (isPullback_specialFiber_closedPoint R toBase).isoIsPullback_hom_snd _ _
    (IsPullback.of_hasPullback toBase
      ((Spec R).fromSpecResidueField (closedPoint R)))

/-- The inverse closed-point fibre comparison preserves the maps to the total space. -/
@[reassoc (attr := simp)]
lemma specialFiberIsoFiberClosedPoint_inv_specialFiberι :
    (specialFiberIsoFiberClosedPoint R toBase).inv ≫ specialFiberι R toBase =
      toBase.fiberι (closedPoint R) :=
  (isPullback_specialFiber_closedPoint R toBase).isoIsPullback_inv_fst _ _
    (IsPullback.of_hasPullback toBase
      ((Spec R).fromSpecResidueField (closedPoint R)))

/-- The inverse closed-point fibre comparison preserves the maps to the residue-field
spectrum. The structure morphism `(specialFiber R toBase).hom` is written in its simp normal
form, the pullback projection given by `specialFiber_hom`. -/
@[simp, reassoc]
lemma specialFiberIsoFiberClosedPoint_inv_fiberToSpecResidueField :
    (specialFiberIsoFiberClosedPoint R toBase).inv ≫
        pullback.snd toBase (Spec.map (CommRingCat.ofHom (residue R))) ≫
          (specLocalResidueFieldIso R).hom =
      toBase.fiberToSpecResidueField (closedPoint R) := by
  have h := (isPullback_specialFiber_closedPoint R toBase).isoIsPullback_inv_snd _ _
    (IsPullback.of_hasPullback toBase ((Spec R).fromSpecResidueField (closedPoint R)))
  simp only [specialFiber_hom, ResidueField.algebraMap_eq] at h
  exact h

end ClosedPoint

section DimensionLEOne

variable {R : CommRingCat.{u}} [IsLocalRing R] [IsDomain R] [Ring.DimensionLEOne R]
variable (K : Type u) [CommRing K] [Algebra R K] [IsFractionRing R K]
variable {X : Scheme.{u}} (toBase : X ⟶ Spec R)

/-- **Fibrewise properties over a local domain of dimension at most one.** A property of
morphisms invariant under isomorphism holds for every fibre `X_y ⟶ Spec κ(y)` of a scheme over
such a ring `R`, for instance a discrete valuation ring, exactly when it holds for the generic
fibre over the fraction field and for the special fibre over the residue field. -/
theorem forall_fiberToSpecResidueField_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso] :
    (∀ y, P (toBase.fiberToSpecResidueField y)) ↔
      P (genericFiber R K toBase).hom ∧ P (specialFiber R toBase).hom := by
  have hη : P (toBase.fiberToSpecResidueField (genericPoint (Spec R))) ↔
      P (genericFiber R K toBase).hom := by
    rw [← MorphismProperty.cancel_left_of_respectsIso P
      (genericFiberIsoFiberGenericPoint (K := K) toBase).hom,
      genericFiberIsoFiberGenericPoint_hom_fiberToSpecResidueField,
      MorphismProperty.cancel_right_of_respectsIso P]
  have hs : P (toBase.fiberToSpecResidueField (closedPoint R)) ↔
      P (specialFiber R toBase).hom := by
    rw [← MorphismProperty.cancel_left_of_respectsIso P
      (specialFiberIsoFiberClosedPoint R toBase).hom,
      specialFiberIsoFiberClosedPoint_hom_fiberToSpecResidueField,
      MorphismProperty.cancel_right_of_respectsIso P]
  refine ⟨fun h ↦ ⟨hη.mp (h _), hs.mp (h _)⟩, fun ⟨hg, hc⟩ y ↦ ?_⟩
  obtain rfl | rfl := IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top y
  exacts [genericPoint_eq_bot_of_affine R ▸ hη.mpr hg, hs.mpr hc]

end DimensionLEOne

end TauCeti
