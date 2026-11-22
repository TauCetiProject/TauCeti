/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
public import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Maximally dominating morphisms

A *maximal point* of a scheme is the generic point of one of its irreducible components; these
are Mathlib's `genericPoints`. A morphism of schemes `f : X ⟶ Y` is *maximally dominating*
(`AlgebraicGeometry.IsMaximallyDominating`) if it sends every maximal point of `X` to a maximal
point of `Y`.

This is the form of dominance used for alterations of possibly reducible schemes. For reducible
targets it differs from Mathlib's `AlgebraicGeometry.IsDominant`, which asks for dense image:
the inclusion of a closed point into the affine line, together with the identity of the affine
line, gives a surjective morphism `𝔸¹ ⊔ Spec k ⟶ 𝔸¹` that is dominant but not maximally
dominating, because the extra point is a maximal point of the source sent to the origin. Between
irreducible schemes the two notions agree (`isMaximallyDominating_iff_isDominant`).

The preimage `f ⁻¹' genericPoints Y` is the underlying set of the generic fibre of `f`, the
fibre over the maximal points of `Y`. It is stable under generalization, since a maximal point
has no proper generization. When `X` is locally Noetherian, a set stable under generalization is
dense exactly when it contains every maximal point, so `f` is maximally dominating exactly when
its generic fibre is dense in `X` (`isMaximallyDominating_iff_dense_preimage_genericPoints`).
Density alone does not suffice for arbitrary sets: the closed points of the affine line over a
field are dense, but miss its maximal point.

## Main definitions

* `AlgebraicGeometry.IsMaximallyDominating`: a morphism sending maximal points to maximal points.

## Main results

* `AlgebraicGeometry.IsMaximallyDominating.comp`: composites of maximally dominating morphisms are
  maximally dominating. Open immersions, in particular isomorphisms and the identity, are
  maximally dominating, and so is any morphism from the empty scheme.
* `AlgebraicGeometry.IsMaximallyDominating.of_comp_of_isOpenImmersion`: maximal domination of a
  composite with an open immersion descends to the first factor. Hence the restriction
  `f ∣_ U` of a maximally dominating morphism over an open `U ⊆ Y` is maximally dominating, and
  so is the restriction `U.ι ≫ f` to an open subscheme `U` of `X`.
* `AlgebraicGeometry.isMaximallyDominating_iff_dense_preimage_genericPoints`: for locally
  Noetherian `X`, maximal domination is density of the generic fibre.
* `AlgebraicGeometry.isMaximallyDominating_iff_genericPoint_mem`: for irreducible `X`, maximal
  domination says the generic point of `X` maps to a maximal point.
* `AlgebraicGeometry.isMaximallyDominating_iff_isDominant`: between irreducible schemes, maximal
  domination is dominance.
* `AlgebraicGeometry.isMaximallyDominating_fromSpecResidueField_iff`: the residue-field point
  `Spec κ(y) ⟶ Y` is maximally dominating exactly when `y` is a maximal point.

## References

* L. Illusie, Y. Laszlo, F. Orgogozo (eds.), *Travaux de Gabber sur l'uniformisation locale et
  la cohomologie étale des schémas quasi-excellents*, Astérisque 363–364 (2014), Exposé II,
  Définition 1.1.2, and Exposé X, §2.
* M. Temkin, *Tame distillation and desingularization by p-alterations*, Ann. of Math. 186
  (2017), §4.1.1.
-/

public section

open CategoryTheory Set Topology

namespace AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism of schemes is *maximally dominating* if it maps every maximal point of the source,
the generic point of an irreducible component, to a maximal point of the target. -/
@[mk_iff]
class IsMaximallyDominating : Prop where
  mapsTo_genericPoints : MapsTo f (genericPoints X) (genericPoints Y)

/-- A maximally dominating morphism maps maximal points to maximal points. -/
theorem Scheme.Hom.mapsTo_genericPoints [IsMaximallyDominating f] :
    MapsTo f (genericPoints X) (genericPoints Y) :=
  IsMaximallyDominating.mapsTo_genericPoints

/-- An open immersion is maximally dominating: the maximal points of an open subscheme are the
maximal points of the ambient scheme lying in it. This covers isomorphisms, the identity, and the
inclusion of a dense open subscheme. -/
instance (priority := 100) IsMaximallyDominating.of_isOpenImmersion [IsOpenImmersion f] :
    IsMaximallyDominating f :=
  ⟨fun x hx ↦ (f.isOpenEmbedding.mem_genericPoints_iff x).mpr hx⟩

/-- A morphism from the empty scheme is maximally dominating. -/
instance (priority := 100) IsMaximallyDominating.of_isEmpty [IsEmpty X] :
    IsMaximallyDominating f :=
  ⟨fun x ↦ isEmptyElim x⟩

/-- A composite of maximally dominating morphisms is maximally dominating. -/
instance IsMaximallyDominating.comp [IsMaximallyDominating f] [IsMaximallyDominating g] :
    IsMaximallyDominating (f ≫ g) :=
  ⟨fun x hx ↦ by
    rw [Scheme.Hom.comp_apply]
    exact g.mapsTo_genericPoints (f.mapsTo_genericPoints hx)⟩

instance IsMaximallyDominating.isMultiplicative :
    MorphismProperty.IsMultiplicative @IsMaximallyDominating where
  id_mem _ := inferInstance
  comp_mem _ _ _ _ := inferInstance

instance IsMaximallyDominating.respectsIso : MorphismProperty.RespectsIso @IsMaximallyDominating :=
  have := IsMaximallyDominating.isMultiplicative.toIsStableUnderComposition
  MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ _ (_ : IsIso _) ↦
    inferInstance

/-- If the composite of `f` with an open immersion is maximally dominating, then so is `f`: a
point of `Y` is maximal exactly when its image under the open immersion is. -/
theorem IsMaximallyDominating.of_comp_of_isOpenImmersion [IsOpenImmersion g]
    [IsMaximallyDominating (f ≫ g)] : IsMaximallyDominating f :=
  ⟨fun x hx ↦ by
    rw [← g.isOpenEmbedding.mem_genericPoints_iff, ← Scheme.Hom.comp_apply]
    exact (f ≫ g).mapsTo_genericPoints hx⟩

/-- Composing with an open immersion neither creates nor destroys maximal domination. -/
theorem IsMaximallyDominating.comp_iff_of_isOpenImmersion [IsOpenImmersion g] :
    IsMaximallyDominating (f ≫ g) ↔ IsMaximallyDominating f :=
  ⟨fun _ ↦ of_comp_of_isOpenImmersion f g, fun _ ↦ inferInstance⟩

/-- Maximal domination is local on the source: a maximal point of the source is a maximal point of
every open subscheme containing it. -/
instance IsMaximallyDominating.isZariskiLocalAtSource :
    IsZariskiLocalAtSource @IsMaximallyDominating :=
  IsZariskiLocalAtSource.mk' (fun _ _ _ ↦ inferInstance) fun f _ U hU hf ↦ ⟨fun x hx ↦ by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU ▸ trivial : x ∈ iSup U)
    obtain ⟨a, rfl⟩ : x ∈ range (U i).ι := by rwa [Scheme.Opens.range_ι]
    rw [← Scheme.Hom.comp_apply]
    exact ((U i).ι ≫ f).mapsTo_genericPoints
      (((U i).ι.isOpenEmbedding.mem_genericPoints_iff a).mp hx)⟩

/-- Maximal domination is local on the target. -/
instance IsMaximallyDominating.isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget @IsMaximallyDominating :=
  IsZariskiLocalAtSource.isZariskiLocalAtTarget fun f g _ _ ↦ of_comp_of_isOpenImmersion f g

/-- The restriction `f ∣_ U : f ⁻¹ᵁ U ⟶ U` of a maximally dominating morphism over an open
subset `U` of the target is maximally dominating. -/
instance IsMaximallyDominating.morphismRestrict [IsMaximallyDominating f] (U : Y.Opens) :
    IsMaximallyDominating (f ∣_ U) :=
  IsZariskiLocalAtTarget.restrict ‹_› U

/-- The generic fibre `f ⁻¹' genericPoints Y` of a maximally dominating morphism is dense, since it
contains every maximal point of the source. -/
theorem Scheme.Hom.dense_preimage_genericPoints [IsMaximallyDominating f] :
    Dense (f ⁻¹' genericPoints Y) :=
  (dense_iff_closure_eq.mpr genericPoints.closure).mono
    (mapsTo_iff_subset_preimage.mp f.mapsTo_genericPoints)

/-- A morphism from a locally Noetherian scheme is maximally dominating exactly when its generic
fibre `f ⁻¹' genericPoints Y`, the preimage of the set of maximal points of the target, is dense.
-/
theorem isMaximallyDominating_iff_dense_preimage_genericPoints [IsLocallyNoetherian X] :
    IsMaximallyDominating f ↔ Dense (f ⁻¹' genericPoints Y) :=
  ⟨fun _ ↦ f.dense_preimage_genericPoints, fun h ↦ ⟨fun _ hx ↦
    (genericPoints.stableUnderGeneralization.preimage f.continuous).mem_of_dense h
      (TauCeti.AlgebraicGeometry.nonempty_interior_closure_of_mem_genericPoints hx)⟩⟩

/-- A morphism from an irreducible scheme is maximally dominating exactly when it maps the generic
point of the source to a maximal point of the target. -/
theorem isMaximallyDominating_iff_genericPoint_mem [IrreducibleSpace X] :
    IsMaximallyDominating f ↔ f (genericPoint X) ∈ genericPoints Y := by
  rw [isMaximallyDominating_iff, genericPoints_eq_singleton, mapsTo_singleton]

/-- Between irreducible schemes, a morphism is maximally dominating exactly when it is
dominant. -/
theorem isMaximallyDominating_iff_isDominant [IrreducibleSpace X] [IrreducibleSpace Y] :
    IsMaximallyDominating f ↔ IsDominant f := by
  rw [isMaximallyDominating_iff_genericPoint_mem, genericPoints_eq_singleton, mem_singleton_iff,
    isDominant_iff_genericPoint_eq]

/-- A dominant morphism between irreducible schemes is maximally dominating. -/
instance (priority := 100) IsMaximallyDominating.of_isDominant [IrreducibleSpace X]
    [IrreducibleSpace Y] [IsDominant f] : IsMaximallyDominating f :=
  (isMaximallyDominating_iff_isDominant f).mpr inferInstance

/-- The canonical morphism `Spec κ(y) ⟶ Y` from the spectrum of the residue field at `y` is
maximally dominating exactly when `y` is a maximal point of `Y`. For instance the inclusion of the
origin of the affine line over a field is not maximally dominating. -/
theorem isMaximallyDominating_fromSpecResidueField_iff (y : Y) :
    IsMaximallyDominating (Y.fromSpecResidueField y) ↔ y ∈ genericPoints Y := by
  rw [isMaximallyDominating_iff_genericPoint_mem, Scheme.fromSpecResidueField_apply]

end AlgebraicGeometry
