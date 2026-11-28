/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.NoetherianAlteration
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal

/-!
# The category of alterations over a scheme

For a base scheme `S`, `S.Alt` is the full subcategory of schemes over `S` that are reduced,
of finite type, maximally dominating and finite over the generic points of `S`.
This is the category alt/S of ILO, Exposé II, §1.2. It does not require its structure
maps to be proper or surjective. Generic finiteness is expressed by finiteness of the
base change to the disjoint union of the spectra of the component-generic residue fields.

Every morphism in this category is itself maximally dominating and finite over generic
points. The reduction of the base is a terminal object, including for a nonreduced or empty
base. These constructions do not require the base to be noetherian.

The category supplies the objects and arrows on which the alteration topologies are defined.
Its fibre products require discarding the vertical components of ordinary scheme products.

## References

* F. Orgogozo, *Topologies adaptées à l'uniformisation locale*, Exposé II,
  Definitions 1.1.2 and 1.2.2, Lemma 1.1.10 and Proposition 1.2.3,
  in *Travaux de Gabber*, Astérisque **363–364** (2014).
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- The reduced finite-type schemes over a base that are maximally dominating and finite
over its component-generic points. -/
def alterationProperty (S : Scheme.{u}) : ObjectProperty (Over S) :=
  fun X ↦ IsReduced X.left ∧ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom ∧
    X.hom.IsMaximallyDominating ∧ X.hom.IsFiniteOverGenericPoints

/-- The defining conditions for an object of the alteration category. -/
@[simp]
theorem alterationProperty_iff (S : Scheme.{u}) (X : Over S) :
    alterationProperty S X ↔ IsReduced X.left ∧ LocallyOfFiniteType X.hom ∧
      QuasiCompact X.hom ∧ X.hom.IsMaximallyDominating ∧ X.hom.IsFiniteOverGenericPoints :=
  Iff.rfl

/-- The category alt/S, with all morphisms over `S` between its objects. -/
protected abbrev Alt (S : Scheme.{u}) := (alterationProperty S).FullSubcategory

namespace Alt

variable {S : Scheme.{u}}

/-- The underlying scheme of an alteration object. -/
abbrev left (X : S.Alt) : Scheme.{u} := X.obj.left

/-- The structure morphism of an alteration object. -/
abbrev hom (X : S.Alt) : X.left ⟶ S := X.obj.hom

instance (X : S.Alt) : IsReduced X.left := X.property.1

instance (X : S.Alt) : LocallyOfFiniteType X.hom := X.property.2.1

instance (X : S.Alt) : QuasiCompact X.hom := X.property.2.2.1

/-- Structure morphisms in alt/S preserve component-generic points. -/
theorem isMaximallyDominating (X : S.Alt) : X.hom.IsMaximallyDominating :=
  X.property.2.2.2.1

/-- Structure morphisms in alt/S have finite generic fibres. -/
theorem isFiniteOverGenericPoints (X : S.Alt) : X.hom.IsFiniteOverGenericPoints :=
  X.property.2.2.2.2

/-- Regard a reduced finite-type scheme with the two generic-point properties as an
object of alt/S. -/
@[simps! obj_left obj_hom]
abbrev mk {X : Scheme.{u}} (f : X ⟶ S) [IsReduced X] [LocallyOfFiniteType f]
    [QuasiCompact f] (hdom : f.IsMaximallyDominating) (hfin : f.IsFiniteOverGenericPoints) :
    S.Alt :=
  ⟨Over.mk f, (alterationProperty_iff S _).mpr
    ⟨‹IsReduced X›, ‹LocallyOfFiniteType f›, ‹QuasiCompact f›, hdom, hfin⟩⟩

/-- The full inclusion of alt/S into schemes over `S`. -/
abbrev forget (S : Scheme.{u}) : S.Alt ⥤ Over S := (alterationProperty S).ι

/-- Morphisms of alteration objects are the scheme morphisms commuting with the structure
maps; no extra condition is imposed on them. -/
abbrev homMk {X Y : S.Alt} (f : X.left ⟶ Y.left) (hf : f ≫ Y.hom = X.hom) : X ⟶ Y :=
  ObjectProperty.homMk (Over.homMk f hf)

/-- Two morphisms of alteration objects agree if their underlying scheme morphisms agree. -/
@[ext]
theorem hom_ext {X Y : S.Alt} {f g : X ⟶ Y} (h : f.hom.left = g.hom.left) : f = g :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext h)

/-- Every morphism of alteration objects is locally of finite type. -/
instance {X Y : S.Alt} (f : X ⟶ Y) : LocallyOfFiniteType f.hom.left := by
  have : LocallyOfFiniteType (f.hom.left ≫ Y.hom) := by
    rw [Over.w f.hom]
    infer_instance
  exact locallyOfFiniteType_of_comp f.hom.left Y.hom

/-- Every morphism of alteration objects preserves component-generic points. -/
theorem hom_isMaximallyDominating {X Y : S.Alt} (f : X ⟶ Y) :
    f.hom.left.IsMaximallyDominating := by
  have h : (f.hom.left ≫ Y.hom).IsMaximallyDominating := by
    rw [Over.w f.hom]
    exact X.isMaximallyDominating
  exact h.of_comp_of_isFiniteOverGenericPoints Y.isFiniteOverGenericPoints

/-- Every morphism of alteration objects has finite generic fibres. -/
theorem hom_isFiniteOverGenericPoints {X Y : S.Alt} (f : X ⟶ Y) :
    f.hom.left.IsFiniteOverGenericPoints := by
  have h : (f.hom.left ≫ Y.hom).IsFiniteOverGenericPoints := by
    rw [Over.w f.hom]
    exact X.isFiniteOverGenericPoints
  exact h.of_comp_of_isMaximallyDominating Y.isMaximallyDominating

/-- The reduction of the base, viewed as an object of alt/S. -/
noncomputable abbrev reduction (S : Scheme.{u}) : S.Alt :=
  mk S.nilradical.subschemeι
    (S.nilradical.subschemeι.isMaximallyDominating_of_generalizingMap
      ((S.nilradical.subschemeι.isClosedEmbedding.isEmbedding.isOpenEmbedding_of_surjective
        (by
          rw [← Set.range_eq_univ, IdealSheafData.range_subschemeι, support_nilradical]
          rfl)).generalizingMap))
    S.nilradical.subschemeι.isFiniteOverGenericPoints_of_isFinite

/-- The canonical morphism from an alteration object to the reduction of its base. -/
noncomputable def toReduction (X : S.Alt) : X ⟶ reduction S :=
  homMk (IsClosedImmersion.lift S.nilradical.subschemeι X.hom
    (by simpa using X.hom.nilradical_le_ker)) (IsClosedImmersion.lift_fac _ _ _)

/-- The reduction of the base is terminal in alt/S. -/
noncomputable def isTerminalReduction (S : Scheme.{u}) : IsTerminal (reduction S) :=
  IsTerminal.ofUniqueHom toReduction fun X f ↦ by
    apply hom_ext
    apply (cancel_mono S.nilradical.subschemeι).mp
    exact (Over.w f.hom).trans (Over.w (toReduction X).hom).symm

instance (S : Scheme.{u}) : HasTerminal S.Alt :=
  (isTerminalReduction S).hasTerminal

end Alt

end AlgebraicGeometry.Scheme
