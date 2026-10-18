/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-!
# Universal homeomorphisms of schemes

A universal homeomorphism is a scheme morphism whose every base change is a homeomorphism on
underlying spaces. Such maps are surjective, universally injective and universally closed.
Conversely, these three properties suffice. In particular an integral, universally injective,
surjective morphism is a universal homeomorphism.

This criterion applies to Frobenius without imposing finiteness or reducedness assumptions.

## References

* The Stacks Project, [Tag 04DD](https://stacks.math.columbia.edu/tag/04DD), universal
  homeomorphisms.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {X Y Z S : Scheme.{u}}

/-- Every base change of a universal homeomorphism is a homeomorphism on underlying spaces. -/
@[mk_iff]
class IsUniversalHomeomorphism (f : X ⟶ Y) : Prop where
  universally_isHomeomorph : (topologically IsHomeomorph).universally f

/-- Universal homeomorphisms are the universal closure of the homeomorphism property. -/
theorem isUniversalHomeomorphism_eq :
    @IsUniversalHomeomorphism.{u} =
      (topologically IsHomeomorph : MorphismProperty Scheme.{u}).universally := by
  ext X Y f
  exact isUniversalHomeomorphism_iff f

instance isUniversalHomeomorphism_respectsIso :
    MorphismProperty.RespectsIso @IsUniversalHomeomorphism.{u} := by
  rw [isUniversalHomeomorphism_eq]
  infer_instance

instance isUniversalHomeomorphism_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @IsUniversalHomeomorphism.{u} := by
  rw [isUniversalHomeomorphism_eq]
  infer_instance

/-- A universal homeomorphism induces a homeomorphism before any base change. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.isHomeomorph_of_isUniversalHomeomorphism
    (f : X ⟶ Y) [IsUniversalHomeomorphism f] : IsHomeomorph f :=
  MorphismProperty.universally_le _ _ IsUniversalHomeomorphism.universally_isHomeomorph

instance (f : X ⟶ Y) [IsUniversalHomeomorphism f] : Surjective f :=
  ⟨f.isHomeomorph_of_isUniversalHomeomorphism.surjective⟩

instance (f : X ⟶ Y) [IsUniversalHomeomorphism f] : UniversallyClosed f := by
  rw [universallyClosed_eq]
  have h : topologically IsHomeomorph ≤ topologically IsClosedMap := by
    intro X Y f hf
    exact hf.isClosedMap
  exact MorphismProperty.universally_mono h f
    IsUniversalHomeomorphism.universally_isHomeomorph

instance (f : X ⟶ Y) [IsUniversalHomeomorphism f] : UniversallyInjective f := by
  rw [universallyInjective_eq]
  have h : topologically IsHomeomorph ≤ topologically Function.Injective := by
    intro X Y f hf
    exact hf.injective
  exact MorphismProperty.universally_mono h f
    IsUniversalHomeomorphism.universally_isHomeomorph

instance (f : X ⟶ S) (g : Y ⟶ S) [IsUniversalHomeomorphism f] :
    IsUniversalHomeomorphism (pullback.snd f g) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsUniversalHomeomorphism.{u}) (IsPullback.of_hasPullback f g) inferInstance

instance (f : X ⟶ S) (g : Y ⟶ S) [IsUniversalHomeomorphism g] :
    IsUniversalHomeomorphism (pullback.fst f g) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsUniversalHomeomorphism.{u}) (IsPullback.of_hasPullback f g).flip inferInstance

/-- Universally closed, universally injective, surjective scheme maps are precisely the
universal homeomorphisms. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.isUniversalHomeomorphism_iff_universallyClosed
    (f : X ⟶ Y) :
    IsUniversalHomeomorphism f ↔
      UniversallyClosed f ∧ UniversallyInjective f ∧ Surjective f := by
  constructor
  · intro h
    let := h
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  · rintro ⟨hclosed, hinj, hsurj⟩
    let := hclosed
    let := hinj
    let := hsurj
    constructor
    intro X' Y' i₁ i₂ f' H
    have : UniversallyClosed f' := MorphismProperty.of_isPullback H.flip hclosed
    have : UniversallyInjective f' := MorphismProperty.of_isPullback H.flip hinj
    have : Surjective f' := MorphismProperty.of_isPullback H.flip hsurj
    exact isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
      ⟨f'.continuous, f'.isClosedMap, f'.injective, f'.surjective⟩

/-- Composites of universal homeomorphisms are universal homeomorphisms. -/
instance isUniversalHomeomorphism_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @IsUniversalHomeomorphism.{u} where
  comp_mem f g hf hg := by
    let := hf
    let := hg
    apply ((f ≫ g).isUniversalHomeomorphism_iff_universallyClosed).mpr
    exact ⟨inferInstance,
      MorphismProperty.comp_mem @UniversallyInjective f g inferInstance inferInstance,
      inferInstance⟩

instance (f : X ⟶ Y) (g : Y ⟶ Z) [IsUniversalHomeomorphism f]
    [IsUniversalHomeomorphism g] : IsUniversalHomeomorphism (f ≫ g) :=
  MorphismProperty.comp_mem @IsUniversalHomeomorphism f g inferInstance inferInstance

instance (f : X ⟶ Y) [IsIso f] : IsUniversalHomeomorphism f :=
  f.isUniversalHomeomorphism_iff_universallyClosed.mpr
    ⟨inferInstance, inferInstance, inferInstance⟩

/-- The homeomorphism of underlying spaces induced by a universal homeomorphism of schemes. -/
noncomputable def _root_.AlgebraicGeometry.Scheme.Hom.homeomorphOfIsUniversalHomeomorphism
    (f : X ⟶ Y) [IsUniversalHomeomorphism f] : X ≃ₜ Y :=
  f.isHomeomorph_of_isUniversalHomeomorphism.homeomorph f

@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Hom.homeomorphOfIsUniversalHomeomorphism_apply
    (f : X ⟶ Y) [IsUniversalHomeomorphism f] (x : X) :
    f.homeomorphOfIsUniversalHomeomorphism x = f x :=
  (rfl)

/-- The inverse underlying homeomorphism sends the image of a point back to that point. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Hom.homeomorphOfIsUniversalHomeomorphism_symm_apply_apply
    (f : X ⟶ Y) [IsUniversalHomeomorphism f] (x : X) :
    f.homeomorphOfIsUniversalHomeomorphism.symm (f x) = x := by
  simpa only [Scheme.Hom.homeomorphOfIsUniversalHomeomorphism_apply] using
    f.homeomorphOfIsUniversalHomeomorphism.symm_apply_apply x

/-- Mapping the point supplied by the inverse homeomorphism recovers the original point. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Hom.homeomorphOfIsUniversalHomeomorphism_apply_symm_apply
    (f : X ⟶ Y) [IsUniversalHomeomorphism f] (y : Y) :
    f (f.homeomorphOfIsUniversalHomeomorphism.symm y) = y := by
  simpa only [Scheme.Hom.homeomorphOfIsUniversalHomeomorphism_apply] using
    f.homeomorphOfIsUniversalHomeomorphism.apply_symm_apply y

end TauCeti.AlgebraicGeometry
