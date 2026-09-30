/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.PresentationLimit
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Hom
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Spectral

/-!
# Affinoid pre-adic spaces

An affinoid pre-adic space is an object of `𝒱^pre` isomorphic, in that category, to the adic
spectrum of a Huber pair with its presentation-limit structure presheaf and point valuations.
The isomorphism therefore remembers the complete topological rings on every open and the
residue-field valuations, not only a homeomorphism of the underlying spaces.

The predicate is independent of the chosen representative by construction and is registered as
closed under isomorphisms. Canonical presentation-limit spectra are affinoid, and every affinoid
pre-adic space has a spectral underlying topological space. The latter is the quasi-compactness
input used to distinguish genuinely non-affinoid spaces later.

The further condition defining a pre-adic space in Wedhorn's sense is local: it asks for an
affinoid open cover and for the structure presheaf to be adapted to the basis of all affinoid open
subspaces. That condition is not imposed here.

## Main definitions

* `TauCeti.PreAdicSpace.isAffinoid`: the isomorphism-invariant object property of being an
  affinoid pre-adic space.
* `TauCeti.AffinoidPreAdicSpace`: the full subcategory of affinoid pre-adic spaces.
* `TauCeti.AffinoidPreAdicSpace.ofPresentation`: the canonical affinoid object attached to a
  Huber pair, a compatible pair of definition, and its presentation-limit presheaf.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Remark and Definition 8.10.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace TauCeti

open Huber ValuationSpectrum

universe u

namespace PreAdicSpace

private def isAffinoidModel : ObjectProperty PreAdicSpace.{u} := fun X ↦
  ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
    (_ : IsHuberRing A) (S : Pair A) (P : PairOfDefinition A)
    (hP : P.ringOfDefinition ≤ S.plus),
    X = presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP

/-- An object of `𝒱^pre` is affinoid when it is isomorphic to the presentation-limit pre-adic
space of a Huber pair. The pair of definition is required to lie in the plus ring, as in the
construction of `presentationLimitPreAdicSpace`.

The existentially quantified type carries all of its topological-ring and Huber instances. This
keeps the property at the natural universe of `PreAdicSpace` and does not choose a global plus
ring or pair of definition. -/
def isAffinoid : ObjectProperty PreAdicSpace.{u} :=
  isAffinoidModel.isoClosure

/-- Characterisation of an affinoid pre-adic space by an affinoid presentation and an
isomorphism in `𝒱^pre`. -/
theorem isAffinoid_iff (X : PreAdicSpace.{u}) : isAffinoid X ↔
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsHuberRing A) (S : Pair A) (P : PairOfDefinition A)
      (hP : P.ringOfDefinition ≤ S.plus),
      Nonempty (X ≅ presentationLimitPreAdicSpace P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hP) := by
  rw [isAffinoid, ObjectProperty.prop_isoClosure_iff]
  constructor
  · rintro ⟨Y, ⟨A, iA, tA, htA, hA, S, P, hP, hY⟩, ⟨e⟩⟩
    exact ⟨A, iA, tA, htA, hA, S, P, hP, ⟨e.trans (eqToIso hY)⟩⟩
  · rintro ⟨A, iA, tA, htA, hA, S, P, hP, ⟨e⟩⟩
    exact ⟨_, ⟨A, iA, tA, htA, hA, S, P, hP, rfl⟩, ⟨e⟩⟩

/-- The presentation-limit pre-adic space of a Huber pair is affinoid. -/
theorem isAffinoid_presentationLimitPreAdicSpace {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A] (S : Pair A)
    (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus) :
    isAffinoid (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP) := by
  rw [isAffinoid_iff]
  exact ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, S, P, hP,
    ⟨Iso.refl _⟩⟩

/-- The underlying topological space of an affinoid pre-adic space is spectral. -/
theorem spectralSpace_of_isAffinoid {X : PreAdicSpace.{u}} (hX : isAffinoid X) :
    SpectralSpace X := by
  rw [isAffinoid_iff] at hX
  obtain ⟨A, iA, tA, htA, hA, S, P, hP, ⟨e⟩⟩ := hX
  let h : X ≃ₜ spa S.plus :=
    (TopCat.homeoOfIso (forgetToTop.mapIso e)).trans <|
      TopCat.homeoOfIso (eqToIso (presentationLimitPreAdicSpace_carrier P S.plus _ hP))
  let _ : CompactSpace X := h.symm.compactSpace
  exact h.isOpenEmbedding.spectralSpace

end PreAdicSpace

/-- The full subcategory of affinoid pre-adic spaces. -/
abbrev AffinoidPreAdicSpace : Type (u + 1) :=
  PreAdicSpace.isAffinoid.{u}.FullSubcategory

namespace AffinoidPreAdicSpace

/-- The canonical affinoid pre-adic space associated to a Huber pair and a compatible pair of
definition. -/
noncomputable def ofPresentation {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsHuberRing A] (S : Pair A) (P : PairOfDefinition A)
    (hP : P.ringOfDefinition ≤ S.plus) : AffinoidPreAdicSpace.{u} :=
  ⟨presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP,
    PreAdicSpace.isAffinoid_presentationLimitPreAdicSpace S P hP⟩

/-- The underlying pre-adic space of the canonical affinoid object is the presentation-limit
adic spectrum. -/
@[simp]
theorem ofPresentation_obj {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsHuberRing A] (S : Pair A) (P : PairOfDefinition A)
    (hP : P.ringOfDefinition ≤ S.plus) :
    (ofPresentation S P hP).obj = presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP :=
  (rfl)

/-- Affinoid pre-adic spaces have spectral underlying topological spaces. -/
instance (X : AffinoidPreAdicSpace.{u}) : SpectralSpace X.obj :=
  PreAdicSpace.spectralSpace_of_isAffinoid X.property

end AffinoidPreAdicSpace

end TauCeti

end
