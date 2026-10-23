/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.SchemePoints

/-!
# The prime-field F₄ carrier and its named simple roots

The short-root carrier over `𝔽₂` has numbered positive and negative simple-root subgroups and a
split weight torus. Their conjugation law in `PrimeField.PointsFunctor` uses the Cartan-matrix
weights of the Serre generators. Here the positive weight is identified with the corresponding
root of `DynkinType.F4.simplyConnectedRootDatum`, and the negative weight with its negative.
The resulting equations hold on points over every commutative `𝔽₂`-algebra, including nonreduced
ones, and on the corresponding scheme-valued points. They identify the numbering and torus
characters that a pinned-group comparison must preserve.

The carrier and the pinned Chevalley--Demazure group are not identified here.

The root conventions are those of N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*,
Plate VIII; the construction of the carrier follows R. W. Carter, *Simple Groups of Lie Type*,
§§4.4 and 7.1.
The corresponding integral construction is
`TauCeti.Algebra.Lie.F4.ShortRoot.RootDatum`.
-/

public section

universe v

namespace TauCeti.F4ShortRoot.PrimeField

open TauCeti.DynkinType
open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

/-- The weight-torus character of a positive numbered simple-root subgroup of the prime-field
carrier is the matching simple root of the simply connected type-`F₄` datum. -/
theorem weightTorusPoints_conj_rootSubgroupPoints_root_simpleIndex
    (ht : F4.Valid) (i : Fin 4) (A : Type v) [CommRing A] [Algebra (ZMod 2) A]
    (s : Fin 4 → Aˣ) (u : Multiplicative A) :
    weightTorusPoints A s * rootSubgroupPoints (.inl i) A u *
        (weightTorusPoints A s)⁻¹ =
      rootSubgroupPoints (.inl i) A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s
              ((F4.simplyConnectedRootDatum ht).root (F4.simpleIndex ht i)) : A) *
            Multiplicative.toAdd u)) := by
  have hroot : F4.rootGeneratorWeight valid_F4 (.inl i) =
      (F4.simplyConnectedRootDatum ht).root (F4.simpleIndex ht i) := by
    simpa only [rank_F4] using F4.rootGeneratorWeight_inl_eq_root_simpleIndex ht i
  rw [← hroot]
  exact weightTorusPoints_conj_rootSubgroupPoints (.inl i) A s u

/-- The weight-torus character of a negative numbered simple-root subgroup of the prime-field
carrier is the negative of the matching simple root of the simply connected type-`F₄` datum. -/
theorem weightTorusPoints_conj_rootSubgroupPoints_neg_root_simpleIndex
    (ht : F4.Valid) (i : Fin 4) (A : Type v) [CommRing A] [Algebra (ZMod 2) A]
    (s : Fin 4 → Aˣ) (u : Multiplicative A) :
    weightTorusPoints A s * rootSubgroupPoints (.inr i) A u *
        (weightTorusPoints A s)⁻¹ =
      rootSubgroupPoints (.inr i) A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s
              (-(F4.simplyConnectedRootDatum ht).root (F4.simpleIndex ht i)) : A) *
            Multiplicative.toAdd u)) := by
  have hroot : F4.rootGeneratorWeight valid_F4 (.inr i) =
      -(F4.simplyConnectedRootDatum ht).root (F4.simpleIndex ht i) := by
    simpa only [rank_F4] using F4.rootGeneratorWeight_inr_eq_neg_root_simpleIndex ht i
  rw [← hroot]
  exact weightTorusPoints_conj_rootSubgroupPoints (.inr i) A s u

/-- Conjugation by the weight torus rescales a positive numbered simple-root subgroup by the
matching root of the simply connected `F₄` datum, on scheme-valued points. -/
theorem weightTorus_conj_rootSubgroup_root_simpleIndex
    (ht : F4.Valid) (i : Fin 4) (A : Type) [CommRing A] [Algebra (ZMod 2) A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of (ZMod 2))) ⟶
      (SplitTorus.groupScheme (ZMod 2) (Fin 4)).X) (u : A) :
    (s ≫ weightTorus.hom.hom) *
        ((AdditiveGroup.schemePointsMulEquiv A).symm (Multiplicative.ofAdd u) ≫
          (rootSubgroup (.inl i)).hom.hom) *
        (s ≫ weightTorus.hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((TauCeti.torusCharacter (SplitTorus.schemePointsMulEquiv s)
                ((F4.simplyConnectedRootDatum ht).root
                  (F4.simpleIndex ht i)) : A) * u)) ≫
        (rootSubgroup (.inl i)).hom.hom := by
  have hroot : F4.rootGeneratorWeight valid_F4 (.inl i) =
      (F4.simplyConnectedRootDatum ht).root (F4.simpleIndex ht i) := by
    simpa only [rank_F4] using F4.rootGeneratorWeight_inl_eq_root_simpleIndex ht i
  rw [← hroot]
  exact weightTorus_conj_rootSubgroup (.inl i) A s u

/-- Conjugation by the weight torus rescales a negative numbered simple-root subgroup by the
negative of the matching root of the simply connected `F₄` datum, on scheme-valued points. -/
theorem weightTorus_conj_rootSubgroup_neg_root_simpleIndex
    (ht : F4.Valid) (i : Fin 4) (A : Type) [CommRing A] [Algebra (ZMod 2) A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of (ZMod 2))) ⟶
      (SplitTorus.groupScheme (ZMod 2) (Fin 4)).X) (u : A) :
    (s ≫ weightTorus.hom.hom) *
        ((AdditiveGroup.schemePointsMulEquiv A).symm (Multiplicative.ofAdd u) ≫
          (rootSubgroup (.inr i)).hom.hom) *
        (s ≫ weightTorus.hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((TauCeti.torusCharacter (SplitTorus.schemePointsMulEquiv s)
                (-(F4.simplyConnectedRootDatum ht).root
                  (F4.simpleIndex ht i)) : A) * u)) ≫
        (rootSubgroup (.inr i)).hom.hom := by
  have hroot : F4.rootGeneratorWeight valid_F4 (.inr i) =
      -(F4.simplyConnectedRootDatum ht).root (F4.simpleIndex ht i) := by
    simpa only [rank_F4] using F4.rootGeneratorWeight_inr_eq_neg_root_simpleIndex ht i
  rw [← hroot]
  exact weightTorus_conj_rootSubgroup (.inr i) A s u

end TauCeti.F4ShortRoot.PrimeField
