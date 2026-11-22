/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.ResidueField

import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import TauCeti.Topology.Sober

/-!
# Maximally dominating morphisms

The scheme of generic points of a scheme is the disjoint union of the spectra of the residue
fields at its component-generic points. Its structural map to the original scheme is a
monomorphism. Maximal domination is equivalent to admitting a unique commuting map between
the schemes of generic points. For a source with finitely many irreducible components, maximal
domination is also equivalent to density of the pullback of the target's scheme of generic points;
the implication from maximal domination to density holds without this finiteness assumption.

This follows M. Temkin, *Tame distillation and desingularization by p-alterations* (2017),
§4.1.1. The construction uses Mathlib's `genericPoints`, scheme coproducts, and canonical
morphisms from spectra of residue fields.
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Set

namespace AlgebraicGeometry

universe u

namespace Scheme

/-- The disjoint union of the spectra of the residue fields at the component-generic points. -/
noncomputable abbrev genericPointScheme (X : Scheme.{u}) : Scheme.{u} :=
  ∐ fun x : genericPoints X ↦ Spec (X.residueField x)

/-- For an irreducible scheme, each generic-point summand is the whole generic-point scheme. -/
instance (X : Scheme.{u}) [IrreducibleSpace X] (x : genericPoints X) :
    IsIso (Sigma.ι (fun x : genericPoints X ↦ Spec (X.residueField x)) x) := by
  have : Subsingleton (genericPoints X) := by
    rw [genericPoints_eq_singleton]
    infer_instance
  let : Unique (genericPoints X) := { default := x, uniq := fun _ ↦ Subsingleton.elim _ _ }
  exact inferInstanceAs (IsIso (coproductUniqueIso
    (fun x : genericPoints X ↦ Spec (X.residueField x))).inv)

/-- The canonical morphism from the scheme of generic points to the original scheme. -/
noncomputable def fromGenericPointScheme (X : Scheme.{u}) : X.genericPointScheme ⟶ X :=
  Sigma.desc fun x ↦ X.fromSpecResidueField x

/-- On each component the structural morphism is the canonical residue-field morphism. -/
@[reassoc (attr := simp)]
theorem ι_fromGenericPointScheme (X : Scheme.{u}) (x : genericPoints X) :
    Sigma.ι (fun x : genericPoints X ↦ Spec (X.residueField x)) x ≫
      X.fromGenericPointScheme = X.fromSpecResidueField x := by
  unfold fromGenericPointScheme
  exact Sigma.ι_comp_desc _ x

/-- Every point of a residue-field component maps to its indexing generic point. -/
@[simp]
theorem fromGenericPointScheme_ι_apply (X : Scheme.{u})
    (x : genericPoints X) (t : Spec (X.residueField x)) :
    X.fromGenericPointScheme
      (Sigma.ι (fun x : genericPoints X ↦ Spec (X.residueField x)) x t) = x := by
  rw [← Hom.comp_apply, ι_fromGenericPointScheme, fromSpecResidueField_apply]

/-- The image of the scheme of generic points is precisely the set of component-generic points. -/
@[simp]
theorem range_fromGenericPointScheme (X : Scheme.{u}) :
    range X.fromGenericPointScheme = genericPoints X := by
  rw [← (sigmaMk _).surjective.range_comp (⇑X.fromGenericPointScheme),
    range_sigma_eq_iUnion_range]
  simp_rw [Function.comp_apply, sigmaMk_mk, ← Hom.comp_apply, ι_fromGenericPointScheme,
    range_fromSpecResidueField, iUnion_singleton_eq_range, Subtype.range_val]

/-- The structural morphism from the scheme of generic points is a monomorphism. -/
instance (X : Scheme.{u}) : Mono X.fromGenericPointScheme := by
  have : SurjectiveOnStalks X.fromGenericPointScheme :=
    IsZariskiLocalAtSource.sigmaDesc (P := @SurjectiveOnStalks) fun _ ↦ inferInstance
  apply SurjectiveOnStalks.mono_of_injective
  apply Function.Injective.of_comp_right (g := sigmaMk _) _ (sigmaMk _).surjective
  have hcomp : ⇑X.fromGenericPointScheme ∘ sigmaMk _ =
      Subtype.val ∘ (Sigma.fst : (Σ x : genericPoints X, Spec (X.residueField x)) → _) := by
    funext ⟨x, t⟩
    simp
  rw [hcomp]
  exact Subtype.val_injective.comp Sigma.fst_injective

/-- The scheme of generic points has dense image in the original scheme. -/
instance (X : Scheme.{u}) : IsDominant X.fromGenericPointScheme := by
  rw [isDominant_iff, DenseRange, range_fromGenericPointScheme, dense_iff_closure_eq]
  exact genericPoints.closure

end Scheme

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

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
  exact Sigma.ι_comp_map' _ _ x

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
theorem isMaximallyDominating_id (X : Scheme.{u}) : IsMaximallyDominating (𝟙 X) :=
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

/-- Every open immersion is maximally dominating, including an empty open immersion. -/
@[simp]
theorem isMaximallyDominating_of_isOpenImmersion (f : X ⟶ Y) [IsOpenImmersion f] :
    IsMaximallyDominating f :=
  fun x hx ↦ (f.isOpenEmbedding.mem_genericPoints_iff x).mpr hx

/-- Restricting the source of a maximally dominating morphism to an open preserves the property. -/
theorem IsMaximallyDominating.restrictSource {f : X ⟶ Y} (hf : IsMaximallyDominating f)
    (U : X.Opens) : IsMaximallyDominating (U.ι ≫ f) :=
  hf.comp U.ι.isMaximallyDominating_of_isOpenImmersion

/-- The actual pullback of the target's generic-point scheme has as image the points lying
over component-generic points. -/
@[simp]
theorem range_genericPointScheme_pullback_fst (f : X ⟶ Y) :
    range (pullback.fst f Y.fromGenericPointScheme) = f ⁻¹' genericPoints Y := by
  rw [Scheme.Pullback.range_fst, Scheme.range_fromGenericPointScheme]

/-- Maximal domination makes the projection from the generic fibre dominant. -/
theorem IsMaximallyDominating.isDominant_genericPointScheme_pullback {f : X ⟶ Y}
    (hf : f.IsMaximallyDominating) : IsDominant (pullback.fst f Y.fromGenericPointScheme) := by
  rw [isDominant_iff, DenseRange, range_genericPointScheme_pullback_fst]
  exact (dense_iff_closure_eq.mpr genericPoints.closure).mono hf

/-- If the source has finitely many irreducible components, maximal domination is equivalent
to the projection from the generic fibre having dense image. -/
theorem isMaximallyDominating_iff_isDominant_genericPointScheme_pullback
    (f : X ⟶ Y) (hfin : (irreducibleComponents X).Finite) :
    f.IsMaximallyDominating ↔ IsDominant (pullback.fst f Y.fromGenericPointScheme) := by
  rw [isMaximallyDominating_iff, isDominant_iff, DenseRange,
    range_genericPointScheme_pullback_fst]
  exact (TauCeti.dense_iff_genericPoints_subset_of_finite_irreducibleComponents hfin
    (TauCeti.stableUnderGeneralization_genericPoints.preimage f.continuous)).symm

/-- Between irreducible schemes, maximal domination agrees with dominance. -/
theorem isMaximallyDominating_iff_isDominant [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) : IsMaximallyDominating f ↔ IsDominant f := by
  rw [isMaximallyDominating_iff, genericPoints_eq_singleton, genericPoints_eq_singleton]
  simp only [mem_singleton_iff, forall_eq, isDominant_iff_genericPoint_eq]

end AlgebraicGeometry.Scheme.Hom
