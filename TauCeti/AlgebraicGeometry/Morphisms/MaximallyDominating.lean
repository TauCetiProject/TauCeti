/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import TauCeti.AlgebraicGeometry.Scheme.GenericPoint.Coproduct

import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import TauCeti.AlgebraicGeometry.Morphisms.Dominant
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
equivalence holds when the source has finitely many irreducible components. The implication
from maximal domination to density holds for every source. Dominance alone permits vertical
components of the source whose generic points do not map to component-generic points of the target.

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

end AlgebraicGeometry.Scheme.Hom
