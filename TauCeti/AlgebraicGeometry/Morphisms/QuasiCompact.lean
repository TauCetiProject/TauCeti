/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

import TauCeti.CategoryTheory.MorphismProperty.Limits

/-!
# Quasi-compact morphisms

A morphism is quasi-compact if its restrictions to the members of a finite open cover of its
source are quasi-compact. This allows quasi-compact morphisms to be glued along open subschemes.
Finiteness is essential: an infinite union of quasi-compact pieces need not be quasi-compact.

Every point of the target of a quasi-compact morphism of schemes has an open neighbourhood whose
preimage is quasi-compact (`Scheme.Hom.exists_isOpen_mem_isCompact_preimage`): an affine open
neighbourhood will do.

A morphism of `S`-schemes from a scheme with quasi-compact structure map to one with
quasi-separated structure map is quasi-compact
(`AlgebraicGeometry.quasiCompact_left_of_quasiCompact_hom`).

Quasi-compactness descends along surjections, and quasi-separatedness along quasi-compact
surjections: if `f ≫ g` has the property and `f` is surjective (and quasi-compact), then so does
`g` (`AlgebraicGeometry.QuasiCompact.of_comp_surjective`,
`AlgebraicGeometry.QuasiSeparated.of_comp_surjective`), recorded as instances of Mathlib's
`MorphismProperty.HasOfPrecompProperty`. Mathlib's `QuasiCompact.of_comp` and
`QuasiSeparated.of_comp` are the cancellations on the other side.

Quasi-compactness and quasi-separatedness are local on the target, as instances that instance
search can use (`AlgebraicGeometry.isZariskiLocalAtTarget_quasiCompact`,
`AlgebraicGeometry.isZariskiLocalAtTarget_quasiSeparated`). Mathlib proves this through instances
`HasAffineProperty @QuasiCompact (fun X _ _ _ ↦ CompactSpace X)` and
`HasAffineProperty @QuasiSeparated (fun X _ _ _ ↦ QuasiSeparatedSpace X)`, but instance search
cannot use them: the affine property is stored as a lambda whose type is a dependent function
type, not `AffineTargetMorphismProperty`, so it cannot be assigned to the out-parameter of
`HasAffineProperty`. Restating the two affine properties as constants of type
`AffineTargetMorphismProperty` (`AlgebraicGeometry.compactSpaceAffineTarget`,
`AlgebraicGeometry.quasiSeparatedSpaceAffineTarget`) and registering the instances through them
(`AlgebraicGeometry.hasAffineProperty_quasiCompact`,
`AlgebraicGeometry.hasAffineProperty_quasiSeparated`) makes lemmas such as
`IsZariskiLocalAtTarget.of_openCover` and `HasAffineProperty.of_iSup_eq_top` available for these
properties.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- A morphism is quasi-compact if its restrictions to a finite open cover of the source are
quasi-compact. -/
theorem QuasiCompact.of_openCover {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : X.OpenCover)
    [Finite 𝒰.I₀] (H : ∀ i, QuasiCompact (𝒰.f i ≫ f)) : QuasiCompact f := by
  constructor
  intro V hV hVc
  have he : f ⁻¹' V = ⋃ i, (𝒰.f i) '' ((𝒰.f i ≫ f) ⁻¹' V) := by
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp,
      Set.image_preimage_eq_inter_range]
    rw [← Set.inter_iUnion, 𝒰.iUnion_range, Set.inter_univ]
  rw [he]
  exact isCompact_iUnion fun i ↦ by
    have := H i
    exact (QuasiCompact.isCompact_preimage (f := 𝒰.f i ≫ f) V hV hVc).image (𝒰.f i).continuous

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]

/-- Every point of the target of a quasi-compact morphism has an open neighbourhood, for instance
an affine one, whose preimage is quasi-compact. -/
lemma exists_isOpen_mem_isCompact_preimage (y : Y) :
    ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ IsCompact (f ⁻¹' U) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  exact ⟨U, U.isOpen, hyU, QuasiCompact.isCompact_preimage (f := f) _ U.isOpen hU.isCompact⟩

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry

open CategoryTheory Limits

/-- A morphism of `S`-schemes from a scheme with quasi-compact structure map to one with
quasi-separated structure map has quasi-compact underlying map. -/
theorem quasiCompact_left_of_quasiCompact_hom {S : Scheme.{u}} {T U : Over S} (f : T ⟶ U)
    [QuasiCompact T.hom] [QuasiSeparated U.hom] : QuasiCompact f.left := by
  have : QuasiCompact (f.left ≫ U.hom) := by
    rw [Over.w f]
    infer_instance
  exact QuasiCompact.of_comp f.left U.hom

section OfCompSurjective

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **Quasi-compactness descends along surjections**: if `f ≫ g` is quasi-compact and `f` is
surjective, then `g` is quasi-compact, since the preimage under `g` of a compact open is the image
under `f` of its compact preimage under `f ≫ g`. -/
theorem QuasiCompact.of_comp_surjective [QuasiCompact (f ≫ g)] [Surjective f] :
    QuasiCompact g where
  isCompact_preimage U hU hU' := by
    rw [← Set.image_preimage_eq (g ⁻¹' U) f.surjective]
    exact (QuasiCompact.isCompact_preimage (f := f ≫ g) U hU hU').image f.continuous

/-- **Quasi-separatedness descends along quasi-compact surjections**: if `f ≫ g` is
quasi-separated and `f` is quasi-compact and surjective, then `g` is quasi-separated. Indeed
`f ≫ Δ_g` is the diagonal of `f ≫ g` followed by the quasi-compact map `f ×_Z f`, so it is
quasi-compact, and quasi-compactness descends along the surjection `f`. -/
theorem QuasiSeparated.of_comp_surjective [QuasiSeparated (f ≫ g)] [QuasiCompact f]
    [Surjective f] : QuasiSeparated g :=
  have : QuasiCompact (f ≫ pullback.diagonal g) :=
    MorphismProperty.comp_diagonal f g ‹_› inferInstance
  ⟨.of_comp_surjective f (pullback.diagonal g)⟩

end OfCompSurjective

/-- Quasi-compactness descends along surjections (`QuasiCompact.of_comp_surjective`). -/
instance : MorphismProperty.HasOfPrecompProperty @QuasiCompact @Surjective.{u} where
  of_precomp f g _ (_ : QuasiCompact (f ≫ g)) := .of_comp_surjective f g

/-- Quasi-separatedness descends along quasi-compact surjections
(`QuasiSeparated.of_comp_surjective`). -/
instance : MorphismProperty.HasOfPrecompProperty @QuasiSeparated
    (@QuasiCompact.{u} ⊓ @Surjective) where
  of_precomp f g hf (_ : QuasiSeparated (f ≫ g)) :=
    have : QuasiCompact f := hf.1
    have : Surjective f := hf.2
    .of_comp_surjective f g

/-- The affine target property of quasi-compact morphisms: the source is quasi-compact. -/
abbrev compactSpaceAffineTarget : AffineTargetMorphismProperty.{u} :=
  fun X _ _ _ ↦ CompactSpace X

/-- The affine target property of quasi-separated morphisms: the source is quasi-separated. -/
abbrev quasiSeparatedSpaceAffineTarget : AffineTargetMorphismProperty.{u} :=
  fun X _ _ _ ↦ QuasiSeparatedSpace X

/-- A morphism to an affine scheme is quasi-compact exactly when its source is, as an instance
that instance search can use. -/
instance hasAffineProperty_quasiCompact :
    HasAffineProperty @QuasiCompact.{u} compactSpaceAffineTarget :=
  instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat

/-- A morphism to an affine scheme is quasi-separated exactly when its source is, as an instance
that instance search can use. -/
instance hasAffineProperty_quasiSeparated :
    HasAffineProperty @QuasiSeparated.{u} quasiSeparatedSpaceAffineTarget :=
  instHasAffinePropertyQuasiSeparatedQuasiSeparatedSpaceCarrierCarrierCommRingCat

/-- **Quasi-compactness is local on the target.** -/
instance isZariskiLocalAtTarget_quasiCompact : IsZariskiLocalAtTarget @QuasiCompact.{u} :=
  HasAffineProperty.instIsZariskiLocalAtTarget (Q := compactSpaceAffineTarget)

/-- **Quasi-separatedness is local on the target.** -/
instance isZariskiLocalAtTarget_quasiSeparated : IsZariskiLocalAtTarget @QuasiSeparated.{u} :=
  HasAffineProperty.instIsZariskiLocalAtTarget (Q := quasiSeparatedSpaceAffineTarget)

end AlgebraicGeometry
