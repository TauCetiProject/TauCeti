/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.Scheme.GenericPoint.Coproduct

import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import TauCeti.AlgebraicGeometry.Noetherian
import TauCeti.Topology.Irreducible
import TauCeti.Topology.Sober

/-!
# Maximally dominating morphisms

The scheme of generic points of a scheme is the disjoint union of the spectra of the residue
fields at its component-generic points. Its structural map to the original scheme is a
monomorphism. Maximal domination is equivalent to admitting a unique commuting map between
the schemes of generic points. If every irreducible component of the source has nonempty
interior, maximal domination is also equivalent to the first projection from the pullback of
the target's scheme of generic points having dense image in the source. In particular, this
equivalence holds when the source has finitely many irreducible components or is locally
Noetherian. The implication
from maximal domination to density holds for every source. Dominance alone permits vertical
components of the source whose generic points do not map to component-generic points of the target.

Maximal domination is local on the source and on the target, so it passes to the restriction
`f ∣_ U` over an open `U` of the target by `IsZariskiLocalAtTarget.restrict`, and it descends
along composition with an open immersion. For an
irreducible source it says that the generic point maps to a component-generic point, so dominant
morphisms from irreducible schemes are maximally dominating. The residue-field point
`Spec κ(y) ⟶ Y` is maximally dominating exactly when `y` is a component-generic point.

This follows M. Temkin, *Tame distillation and desingularization by p-alterations* (2017),
§4.1.1. The construction uses Mathlib's `genericPoints`, scheme coproducts, and canonical
morphisms from spectra of residue fields.
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Set

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- A morphism is maximally dominating if every component-generic point of its source maps to
one of its target. -/
def IsMaximallyDominating {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  MapsTo f (genericPoints X) (genericPoints Y)

/-- Maximal domination is the pointwise preservation of component-generic points. -/
theorem isMaximallyDominating_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsMaximallyDominating f ↔ ∀ x, x ∈ genericPoints X → f x ∈ genericPoints Y := Iff.rfl

variable {X Y Z : Scheme.{u}}

/-- A maximally dominating morphism induces a map between the schemes of generic points. -/
noncomputable def IsMaximallyDominating.genericPointSchemeMap {f : X ⟶ Y}
    (hf : f.IsMaximallyDominating) : X.genericPointScheme ⟶ Y.genericPointScheme :=
  Sigma.map' (Set.MapsTo.restrict (⇑f) _ _ hf)
    (fun x ↦ Spec.map (f.residueFieldMap x))

/-- On each component, the induced map of generic-point schemes uses the residue-field map. -/
@[reassoc (attr := simp)]
theorem IsMaximallyDominating.ι_genericPointSchemeMap {f : X ⟶ Y}
    (hf : f.IsMaximallyDominating) (x : genericPoints X) :
    Sigma.ι (fun x : genericPoints X ↦ Spec (X.residueField x)) x ≫ hf.genericPointSchemeMap =
      Spec.map (f.residueFieldMap x) ≫
        Sigma.ι (fun y : genericPoints Y ↦ Spec (Y.residueField y))
          ⟨f x, (f.isMaximallyDominating_iff.mp hf) x x.property⟩ := by
  unfold genericPointSchemeMap
  exact Sigma.ι_comp_map' _ _ _

/-- The induced map on generic-point schemes commutes with the maps to the original schemes. -/
@[reassoc (attr := simp)]
theorem IsMaximallyDominating.genericPointSchemeMap_fromGenericPointScheme {f : X ⟶ Y}
    (hf : f.IsMaximallyDominating) :
    hf.genericPointSchemeMap ≫ Y.fromGenericPointScheme = X.fromGenericPointScheme ≫ f := by
  apply Sigma.hom_ext
  intro x
  simp

/-- Maximal domination is equivalent to a unique commuting map between the generic-point schemes. -/
theorem isMaximallyDominating_iff_existsUnique_genericPointSchemeMap (f : X ⟶ Y) :
    f.IsMaximallyDominating ↔ ∃! g : X.genericPointScheme ⟶ Y.genericPointScheme,
      g ≫ Y.fromGenericPointScheme = X.fromGenericPointScheme ≫ f := by
  constructor
  · intro hf
    refine ⟨hf.genericPointSchemeMap, hf.genericPointSchemeMap_fromGenericPointScheme, ?_⟩
    intro g hg
    apply (cancel_mono Y.fromGenericPointScheme).mp
    exact hg.trans hf.genericPointSchemeMap_fromGenericPointScheme.symm
  · rintro ⟨g, hg, _⟩
    rw [IsMaximallyDominating, ← Scheme.range_fromGenericPointScheme,
      ← Scheme.range_fromGenericPointScheme, Set.mapsTo_range_iff]
    intro t
    exact ⟨g t, by rw [← Hom.comp_apply, hg, Hom.comp_apply]⟩

/-- A composite of maximally dominating morphisms is maximally dominating. -/
theorem IsMaximallyDominating.comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hg : IsMaximallyDominating g) (hf : IsMaximallyDominating f) :
    IsMaximallyDominating (f ≫ g) :=
  MapsTo.comp (f := ⇑f) (g := ⇑g) hg hf

/-- The identity morphism preserves all component-generic points. -/
theorem _root_.AlgebraicGeometry.Scheme.isMaximallyDominating_id (X : Scheme.{u}) :
    IsMaximallyDominating (𝟙 X) :=
  mapsTo_id _

/-- The generic-point map of the identity is the identity. -/
@[simp]
theorem IsMaximallyDominating.genericPointSchemeMap_id
    (h : IsMaximallyDominating (𝟙 X)) : h.genericPointSchemeMap = 𝟙 X.genericPointScheme := by
  apply (cancel_mono X.fromGenericPointScheme).mp
  simp

/-- Generic-point maps preserve composition. -/
@[simp]
theorem IsMaximallyDominating.genericPointSchemeMap_comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hg : IsMaximallyDominating g) (hf : IsMaximallyDominating f) :
    (hg.comp hf).genericPointSchemeMap = hf.genericPointSchemeMap ≫ hg.genericPointSchemeMap := by
  apply (cancel_mono Z.fromGenericPointScheme).mp
  simp [Category.assoc]

/-- Every generalizing morphism is maximally dominating. -/
theorem isMaximallyDominating_of_generalizingMap (f : X ⟶ Y) (hf : GeneralizingMap f) :
    IsMaximallyDominating f :=
  hf.mapsTo_genericPoints f.continuous

/-- Every flat morphism is maximally dominating. -/
theorem isMaximallyDominating_of_flat (f : X ⟶ Y) [Flat f] :
    IsMaximallyDominating f :=
  f.isMaximallyDominating_of_generalizingMap (Flat.generalizingMap f)

/-- Every open immersion is maximally dominating, including an empty open immersion. -/
@[simp]
theorem isMaximallyDominating_of_isOpenImmersion (f : X ⟶ Y) [IsOpenImmersion f] :
    IsMaximallyDominating f :=
  f.isMaximallyDominating_of_generalizingMap f.isOpenEmbedding.generalizingMap

/-- Restricting the source of a maximally dominating morphism to an open preserves the property. -/
theorem IsMaximallyDominating.restrictSource {f : X ⟶ Y} (hf : IsMaximallyDominating f)
    (U : X.Opens) : IsMaximallyDominating (U.ι ≫ f) :=
  hf.comp U.ι.isMaximallyDominating_of_isOpenImmersion

/-- Maximal domination makes the projection from the generic fibre dominant. -/
theorem IsMaximallyDominating.isDominant_pullback_fst_fromGenericPointScheme {f : X ⟶ Y}
    (hf : f.IsMaximallyDominating) : IsDominant (pullback.fst f Y.fromGenericPointScheme) := by
  rw [isDominant_iff, DenseRange, range_pullback_fst_fromGenericPointScheme]
  exact (dense_iff_closure_eq.mpr genericPoints.closure).mono hf

/-- If every irreducible component of the source has nonempty interior, maximal domination is
equivalent to the projection from the generic fibre having dense image. -/
theorem isMaximallyDominating_iff_isDominant_pullback_fst_fromGenericPointScheme
    (f : X ⟶ Y) (hinterior : ∀ C ∈ irreducibleComponents X, (interior C).Nonempty) :
    f.IsMaximallyDominating ↔ IsDominant (pullback.fst f Y.fromGenericPointScheme) := by
  rw [isMaximallyDominating_iff, isDominant_iff, DenseRange,
    range_pullback_fst_fromGenericPointScheme]
  exact (TauCeti.dense_iff_genericPoints_subset_of_nonempty_interior (fun _ hx ↦ hinterior _ hx)
    (TauCeti.stableUnderGeneralization_genericPoints.preimage f.continuous)).symm

/-- If the source has finitely many irreducible components, maximal domination is equivalent
to the projection from the generic fibre having dense image. -/
theorem
    isMaximallyDominating_iff_isDominant_pullback_fst_fromGenericPointScheme_of_finite
    (f : X ⟶ Y) (hfin : (irreducibleComponents X).Finite) :
    f.IsMaximallyDominating ↔ IsDominant (pullback.fst f Y.fromGenericPointScheme) :=
  f.isMaximallyDominating_iff_isDominant_pullback_fst_fromGenericPointScheme
    (fun _ hC ↦ hfin.nonempty_interior_of_mem_irreducibleComponents hC)

/-- Between irreducible schemes, maximal domination agrees with dominance. -/
theorem isMaximallyDominating_iff_isDominant [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) : IsMaximallyDominating f ↔ IsDominant f := by
  rw [isMaximallyDominating_iff, genericPoints_eq_singleton, genericPoints_eq_singleton]
  simp only [mem_singleton_iff, forall_eq, isDominant_iff_genericPoint_eq]

/-- If the source is locally Noetherian, maximal domination is equivalent to the projection from
the generic fibre having dense image. -/
theorem
    isMaximallyDominating_iff_isDominant_pullback_fst_fromGenericPointScheme_of_isLocallyNoetherian
    (f : X ⟶ Y) [IsLocallyNoetherian X] :
    f.IsMaximallyDominating ↔ IsDominant (pullback.fst f Y.fromGenericPointScheme) :=
  f.isMaximallyDominating_iff_isDominant_pullback_fst_fromGenericPointScheme
    fun _ hC ↦ TauCeti.AlgebraicGeometry.nonempty_interior_of_mem_irreducibleComponents hC

/-- A morphism from the empty scheme is maximally dominating. -/
theorem isMaximallyDominating_of_isEmpty (f : X ⟶ Y) [IsEmpty X] : f.IsMaximallyDominating :=
  fun x ↦ isEmptyElim x

/-- If the composite of `f` with an open immersion is maximally dominating, then so is `f`: a
point of `Y` is component-generic exactly when its image under the open immersion is. -/
theorem IsMaximallyDominating.of_comp_of_isOpenImmersion {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsOpenImmersion g] (h : (f ≫ g).IsMaximallyDominating) : f.IsMaximallyDominating :=
  fun x hx ↦ by
    rw [← g.isOpenEmbedding.mem_genericPoints_iff, ← Hom.comp_apply]
    exact h hx

/-- Composing with an open immersion neither creates nor destroys maximal domination. -/
@[simp]
theorem isMaximallyDominating_comp_iff_of_isOpenImmersion (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion g] : (f ≫ g).IsMaximallyDominating ↔ f.IsMaximallyDominating :=
  ⟨.of_comp_of_isOpenImmersion, g.isMaximallyDominating_of_isOpenImmersion.comp⟩

instance isMultiplicative_isMaximallyDominating :
    MorphismProperty.IsMultiplicative @IsMaximallyDominating where
  id_mem X := X.isMaximallyDominating_id
  comp_mem _ _ hf hg := hg.comp hf

instance respectsIso_isMaximallyDominating :
    MorphismProperty.RespectsIso @IsMaximallyDominating :=
  have := isMultiplicative_isMaximallyDominating.toIsStableUnderComposition
  MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ f (_ : IsIso f) ↦
    f.isMaximallyDominating_of_isOpenImmersion

/-- Maximal domination is local on the source: a component-generic point of the source is a
component-generic point of every open subscheme containing it. -/
instance isZariskiLocalAtSource_isMaximallyDominating :
    IsZariskiLocalAtSource @IsMaximallyDominating :=
  IsZariskiLocalAtSource.mk' (fun _ U hf ↦ hf.restrictSource U) fun _ _ U hU hf x hx ↦ by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hU ▸ trivial : x ∈ iSup U)
    obtain ⟨a, rfl⟩ : x ∈ range (U i).ι := by rwa [Scheme.Opens.range_ι]
    rw [← Hom.comp_apply]
    exact hf i (((U i).ι.isOpenEmbedding.mem_genericPoints_iff a).mp hx)

/-- Maximal domination is local on the target. -/
instance isZariskiLocalAtTarget_isMaximallyDominating :
    IsZariskiLocalAtTarget @IsMaximallyDominating :=
  IsZariskiLocalAtSource.isZariskiLocalAtTarget fun _ _ _ h ↦ h.of_comp_of_isOpenImmersion

/-- A morphism from an irreducible scheme is maximally dominating exactly when it maps the generic
point of the source to a component-generic point of the target. -/
theorem isMaximallyDominating_iff_genericPoint_mem [IrreducibleSpace X] (f : X ⟶ Y) :
    f.IsMaximallyDominating ↔ f (genericPoint X) ∈ genericPoints Y := by
  rw [IsMaximallyDominating, genericPoints_eq_singleton, mapsTo_singleton]

/-- A dominant morphism from an irreducible scheme is maximally dominating; its target is then
irreducible as well. -/
theorem isMaximallyDominating_of_isDominant [IrreducibleSpace X] (f : X ⟶ Y) [IsDominant f] :
    f.IsMaximallyDominating :=
  have := f.irreducibleSpace_of_isDominant
  (isMaximallyDominating_iff_isDominant f).mpr inferInstance

/-- The canonical morphism `Spec κ(y) ⟶ Y` from the spectrum of the residue field at `y` is
maximally dominating exactly when `y` is a component-generic point of `Y`. For instance the
inclusion of the origin of the affine line over a field is not maximally dominating. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.isMaximallyDominating_fromSpecResidueField_iff (y : Y) :
    (Y.fromSpecResidueField y).IsMaximallyDominating ↔ y ∈ genericPoints Y := by
  rw [isMaximallyDominating_iff_genericPoint_mem, Scheme.fromSpecResidueField_apply]

end AlgebraicGeometry.Scheme.Hom
