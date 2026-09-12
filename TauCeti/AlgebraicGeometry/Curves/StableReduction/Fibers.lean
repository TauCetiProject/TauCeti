/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model
public import TauCeti.RingTheory.DiscreteValuationRing.FractionRing

/-!
# Generic and special fibres over a discrete valuation ring

For a scheme over a discrete valuation ring `R` with fraction field `K`, this file records the
canonical inclusions of its generic and special fibres into the total space. The generic fibre is
an open subscheme because `K` is obtained by inverting a uniformizer. The special fibre is a
closed subscheme because the residue map `R → κ` is surjective.

The generic-fibre object is the one used by `TauCeti.Model`, while the special-fibre object is its
parallel pullback along `Spec κ → Spec R`. The projection lemmas expose both pullback squares to
later model and reduction arguments.
-/

public section

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry IsLocalRing

namespace TauCeti

universe u

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
lemma genericFiber_hom (R K : Type u) [CommRing R] [Field K] [Algebra R K]
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

/-- The generic-fibre inclusion and structure morphism form the defining pullback square. -/
@[reassoc (attr := simp)]
lemma genericFiberι_toBase (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) :
    genericFiberι R K toBase ≫ toBase =
      (genericFiber R K toBase).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K)) :=
  pullback.condition

/-- The special-fibre inclusion and structure morphism form the defining pullback square. -/
@[reassoc (attr := simp)]
lemma specialFiberι_toBase (R : Type u) [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) :
    specialFiberι R toBase ≫ toBase =
      (specialFiber R toBase).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R))) :=
  pullback.condition

/-- The morphism from the spectrum of a DVR's fraction field is an open immersion. -/
lemma isOpenImmersion_Spec_map_fractionRing (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] :
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
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
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

namespace Model

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

/-- The chosen generic fibre of a model, included into its total space. -/
noncomputable def genericι (M : Model R K C toK) : C ⟶ M.total :=
  M.genericFiberIso.inv.left ≫ genericFiberι R K M.toBase

/-- The inclusion of a model's chosen generic fibre lies over the fraction-field morphism. -/
@[reassoc (attr := simp)]
lemma genericι_toBase (M : Model R K C toK) :
    M.genericι ≫ M.toBase =
      toK ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  rw [genericι, Category.assoc, genericFiberι_toBase, ← Category.assoc, Over.w]
  rfl

/-- A model's chosen generic fibre is an open subscheme of its total space. -/
lemma isOpenImmersion_genericι (M : Model R K C toK) : IsOpenImmersion M.genericι := by
  let : IsOpenImmersion (genericFiberι R K M.toBase) :=
    isOpenImmersion_genericFiberι R K M.toBase
  let : IsIso M.genericFiberIso.inv.left :=
    inferInstanceAs (IsIso ((Over.forget _).map M.genericFiberIso.inv))
  change IsOpenImmersion (M.genericFiberIso.inv.left ≫ genericFiberι R K M.toBase)
  exact inferInstance

end Model

end TauCeti
