/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import TauCeti.RingTheory.DiscreteValuationRing.FractionRing

/-!
# Generic and special fibres

For a scheme over a ring `R`, this file defines its scalar-extension fibre along a ring map
`R → K`. For a local ring, it also defines the special fibre obtained by base change to the
residue field. The projection identities and pullback witnesses expose the defining squares.

When `R` is a discrete valuation ring and `K` is a fraction ring, the generic fibre is an open
subscheme of the total space. The special fibre over any local ring is a closed subscheme.
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

end TauCeti
