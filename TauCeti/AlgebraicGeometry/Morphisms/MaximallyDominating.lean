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
fields at its component-generic points. A maximally dominating morphism induces a map between
these schemes by sending each component-generic point to a component-generic point. For a
source with finitely many irreducible components, maximal domination is equivalent to density
of the pullback of the target's scheme of generic points.

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
noncomputable def genericPointScheme (X : Scheme.{u}) : Scheme.{u} :=
  ∐ fun x : genericPoints X ↦ Spec (X.residueField x)

/-- The coproduct presentation of the scheme of generic points. -/
theorem genericPointScheme_eq (X : Scheme.{u}) :
    X.genericPointScheme = ∐ fun x : genericPoints X ↦ Spec (X.residueField x) := (rfl)

/-- The inclusion of the residue field of a component-generic point in the generic-point scheme. -/
noncomputable def genericPointSchemeι (X : Scheme.{u}) (x : genericPoints X) :
    Spec (X.residueField x) ⟶ X.genericPointScheme :=
  Sigma.ι (fun x : genericPoints X ↦ Spec (X.residueField x)) x

/-- The morphism out of the generic-point scheme determined by morphisms on its components. -/
noncomputable def genericPointSchemeDesc (X : Scheme.{u}) {Y : Scheme.{u}}
    (f : ∀ x : genericPoints X, Spec (X.residueField x) ⟶ Y) : X.genericPointScheme ⟶ Y :=
  Sigma.desc f

/-- The universal morphism has the prescribed restriction on each component. -/
@[reassoc (attr := simp)]
theorem genericPointSchemeι_desc (X : Scheme.{u}) {Y : Scheme.{u}}
    (f : ∀ x : genericPoints X, Spec (X.residueField x) ⟶ Y) (x : genericPoints X) :
    X.genericPointSchemeι x ≫ X.genericPointSchemeDesc f = f x := by
  unfold genericPointSchemeι genericPointSchemeDesc
  exact Sigma.ι_comp_desc _ _

/-- Every point of the generic-point scheme comes from a residue-field component. -/
theorem exists_genericPointSchemeι_eq (X : Scheme.{u}) (z : X.genericPointScheme) :
    ∃ (x : genericPoints X) (t : Spec (X.residueField x)), X.genericPointSchemeι x t = z := by
  obtain ⟨⟨x, t⟩, rfl⟩ := (sigmaMk _).surjective z
  exact ⟨x, t, (sigmaMk_mk _ _ _).symm⟩

/-- Morphisms out of the scheme of generic points agree if they agree on each residue-field
component. -/
@[ext]
theorem genericPointScheme_hom_ext (X : Scheme.{u}) {Y : Scheme.{u}}
    {f g : X.genericPointScheme ⟶ Y}
    (h : ∀ x, X.genericPointSchemeι x ≫ f = X.genericPointSchemeι x ≫ g) : f = g := by
  apply Sigma.hom_ext
  exact h

/-- The canonical morphism from the scheme of generic points to the original scheme. -/
noncomputable def fromGenericPointScheme (X : Scheme.{u}) : X.genericPointScheme ⟶ X :=
  X.genericPointSchemeDesc fun x ↦ X.fromSpecResidueField x

/-- On each component the structural morphism is the canonical residue-field morphism. -/
@[reassoc (attr := simp)]
theorem genericPointSchemeι_fromGenericPointScheme (X : Scheme.{u}) (x : genericPoints X) :
    X.genericPointSchemeι x ≫ X.fromGenericPointScheme = X.fromSpecResidueField x := by
  unfold fromGenericPointScheme
  exact X.genericPointSchemeι_desc _ x

/-- Every point of a residue-field component maps to its indexing generic point. -/
@[simp]
theorem fromGenericPointScheme_genericPointSchemeι_apply (X : Scheme.{u})
    (x : genericPoints X) (t : Spec (X.residueField x)) :
    X.fromGenericPointScheme (X.genericPointSchemeι x t) = x := by
  rw [← Hom.comp_apply, genericPointSchemeι_fromGenericPointScheme,
    fromSpecResidueField_apply]

/-- The image of the scheme of generic points is precisely the set of component-generic points. -/
@[simp]
theorem range_fromGenericPointScheme (X : Scheme.{u}) :
    range X.fromGenericPointScheme = genericPoints X := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨y, t, rfl⟩ := X.exists_genericPointSchemeι_eq z
    rw [fromGenericPointScheme_genericPointSchemeι_apply]
    exact y.property
  · intro hx
    let y : genericPoints X := ⟨x, hx⟩
    exact ⟨X.genericPointSchemeι y (IsLocalRing.closedPoint (X.residueField y)),
      X.fromGenericPointScheme_genericPointSchemeι_apply y _⟩

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
  X.genericPointSchemeDesc fun x ↦ Spec.map (f.residueFieldMap x) ≫
    Y.genericPointSchemeι ⟨f x, (f.isMaximallyDominating_iff.mp hf) x x.property⟩

/-- On each component, the induced map of generic-point schemes uses the residue-field map. -/
@[reassoc (attr := simp)]
theorem IsMaximallyDominating.genericPointSchemeι_genericPointSchemeMap {f : X ⟶ Y}
    (hf : f.IsMaximallyDominating) (x : genericPoints X) :
    X.genericPointSchemeι x ≫ hf.genericPointSchemeMap = Spec.map (f.residueFieldMap x) ≫
      Y.genericPointSchemeι ⟨f x, (f.isMaximallyDominating_iff.mp hf) x x.property⟩ := by
  simp [IsMaximallyDominating.genericPointSchemeMap]

/-- The induced map on generic-point schemes commutes with the maps to the original schemes. -/
@[reassoc]
theorem IsMaximallyDominating.genericPointSchemeMap_fromGenericPointScheme {f : X ⟶ Y}
    (hf : f.IsMaximallyDominating) :
    hf.genericPointSchemeMap ≫ Y.fromGenericPointScheme = X.fromGenericPointScheme ≫ f := by
  apply X.genericPointScheme_hom_ext
  intro x
  simp

/-- A composite of maximally dominating morphisms is maximally dominating. -/
theorem IsMaximallyDominating.comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hg : IsMaximallyDominating g) (hf : IsMaximallyDominating f) :
    IsMaximallyDominating (f ≫ g) := by
  rw [isMaximallyDominating_iff] at *
  intro x hx
  rw [Hom.comp_apply]
  exact hg _ (hf _ hx)

/-- The identity morphism preserves all component-generic points. -/
@[simp]
theorem isMaximallyDominating_id (X : Scheme.{u}) : IsMaximallyDominating (𝟙 X) :=
  fun _ hx ↦ hx

/-- Every open immersion is maximally dominating, including an empty open immersion. -/
theorem isMaximallyDominating_of_isOpenImmersion (f : X ⟶ Y) [IsOpenImmersion f] :
    IsMaximallyDominating f :=
  fun x hx ↦ (f.isOpenEmbedding.mem_genericPoints_iff x).mpr hx

/-- Restricting the source of a maximally dominating morphism to an open preserves the property. -/
theorem IsMaximallyDominating.restrictSource {f : X ⟶ Y} (hf : IsMaximallyDominating f)
    (U : X.Opens) : IsMaximallyDominating (U.ι ≫ f) :=
  hf.comp U.ι.isMaximallyDominating_of_isOpenImmersion

/-- The actual pullback of the target's generic-point scheme has as image the points lying
over component-generic points. -/
theorem range_genericPointScheme_pullback_fst (f : X ⟶ Y) :
    range (pullback.fst f Y.fromGenericPointScheme) = f ⁻¹' genericPoints Y := by
  rw [Scheme.Pullback.range_fst, Scheme.range_fromGenericPointScheme]

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
