/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Groupoid
public import TauCeti.CategoryTheory.Monoidal.Core
public import TauCeti.CategoryTheory.Monoidal.Scalar

/-!
# Picard groupoids

A *Picard groupoid* is a symmetric monoidal groupoid in which every object is invertible for the
tensor product: for every `X` there is a `Y` with `X ⊗ Y ≅ 𝟙_ C`. The prototype is the groupoid of
line bundles on a scheme and their isomorphisms, under tensor product.

A Picard groupoid `C` has two invariants, both commutative groups:

* `π₀ C`, the set of isomorphism classes, is the monoidal skeleton `Skeleton C`
  (`TauCeti.PicardGroupoid.pi0`), whose monoid structure Mathlib already provides and in which
  invertibility of objects provides inverses. The inverse of the class of `X` is the class of any
  `Y` with `X ⊗ Y ≅ 𝟙_ C` (`TauCeti.PicardGroupoid.inv_toSkeleton_eq_toSkeleton_iff`).
* `π₁ C`, the automorphism group `Aut (𝟙_ C)` of the unit (`TauCeti.PicardGroupoid.pi1`). It is
  commutative in any monoidal category, because endomorphisms of the unit commute
  (`TauCeti.scalar_comm`).

For a symmetric monoidal category `C`, the core `Core C` is a Picard groupoid exactly when every
object of `C` has a tensor inverse up to isomorphism
(`TauCeti.picardGroupoid_core_iff`). This is how the Picard groupoid of a scheme is built from
its symmetric monoidal category of line bundles.

## Main declarations

* `TauCeti.PicardGroupoid`: the class of Picard groupoids;
* `TauCeti.PicardGroupoid.pi0` and its commutative group structure;
* `TauCeti.PicardGroupoid.pi1` and its commutative group structure;
* `TauCeti.picardGroupoid_core_iff`: when the core of a symmetric monoidal category is a Picard
  groupoid.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*, Invent. Math.
  209 (2017), Definition 12.14 and Proposition 12.15.
* P. Deligne, *La formule de dualité globale*, SGA 4, Exposé XVIII, §1.4.
-/

public section

open CategoryTheory MonoidalCategory

universe v u

namespace TauCeti

/-- A *Picard groupoid* is a symmetric monoidal groupoid in which every object has a tensor
inverse up to isomorphism: every morphism is an isomorphism, and for every object `X` there is an
object `Y` with `X ⊗ Y ≅ 𝟙_ C`. -/
class PicardGroupoid (C : Type u) [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] :
    Prop extends IsGroupoid C where
  /-- Every object has a tensor inverse up to isomorphism. -/
  exists_tensor_iso_unit (X : C) : ∃ Y : C, Nonempty (X ⊗ Y ≅ 𝟙_ C)

namespace PicardGroupoid

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/-- The group `π₀ C` of isomorphism classes of objects of a Picard groupoid, with the
multiplication induced by the tensor product. -/
abbrev pi0 : Type u :=
  Skeleton C

/-- The group `π₁ C` of automorphisms of the unit of a Picard groupoid. -/
abbrev pi1 : Type v :=
  Aut (𝟙_ C)

variable {C} [SymmetricCategory C] [PicardGroupoid C]

/-- The isomorphism classes of objects of a Picard groupoid form a commutative group: the class
of `X` is inverted by the class of any `Y` with `X ⊗ Y ≅ 𝟙_ C`. -/
noncomputable instance : CommGroup (pi0 C) where
  __ := (inferInstance : CommMonoid (Skeleton C))
  __ := groupOfIsUnit fun x ↦ by
    rw [← toSkeleton_fromSkeleton_obj x]
    obtain ⟨Y, ⟨e⟩⟩ := exists_tensor_iso_unit ((fromSkeleton C).obj x)
    refine isUnit_iff_exists_inv.mpr ⟨toSkeleton Y, ?_⟩
    rw [← Skeleton.toSkeleton_tensorObj, Skeleton.one_eq]
    exact congr_toSkeleton_of_iso e

/-- In the group of isomorphism classes of a Picard groupoid, the inverse of the class of `X` is
the class of `Y` exactly when `X ⊗ Y ≅ 𝟙_ C`. -/
lemma inv_toSkeleton_eq_toSkeleton_iff {X Y : C} :
    (toSkeleton X : pi0 C)⁻¹ = toSkeleton Y ↔ Nonempty (X ⊗ Y ≅ 𝟙_ C) := by
  rw [inv_eq_iff_mul_eq_one, ← Skeleton.toSkeleton_tensorObj, Skeleton.one_eq,
    toSkeleton_eq_toSkeleton_iff]

end PicardGroupoid

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The core of a symmetric monoidal category is a Picard groupoid exactly when every object has
a tensor inverse up to isomorphism. -/
lemma picardGroupoid_core_iff :
    PicardGroupoid (Core C) ↔ ∀ X : C, ∃ Y : C, Nonempty (X ⊗ Y ≅ 𝟙_ C) := by
  refine ⟨fun _ X ↦ ?_, fun h ↦ { exists_tensor_iso_unit X := ?_ }⟩
  · obtain ⟨Y, ⟨e⟩⟩ := PicardGroupoid.exists_tensor_iso_unit (⟨X⟩ : Core C)
    exact ⟨Y.of, ⟨(Core.inclusion C).mapIso e⟩⟩
  · obtain ⟨Y, ⟨e⟩⟩ := h X.of
    exact ⟨⟨Y⟩, ⟨Core.isoMk e⟩⟩

end TauCeti
