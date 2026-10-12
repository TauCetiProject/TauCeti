/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PointsFunctor

/-!
# Simple-root weights of the prime-field short-root type-G2 carrier

`TauCeti.G2ShortRoot.PrimeField.groupScheme` is the type-`G₂` carrier over `𝔽₃` generated
by the reductions of the four numbered simple root subgroups and the rank-two weight torus.  The
carrier's matrix-valued torus-conjugation equation is initially expressed through
`DynkinType.G2.rootGeneratorWeight DynkinType.valid_G2`, the Cartan-row character attached to a
signed simple-root index.

This file rewrites the scheme-point and matrix-point equations against
`DynkinType.G2.simplyConnectedRootDatum`, identifying the carrier's generator weights with the
named positive and negative simple roots in Bourbaki numbering.  The corresponding integral
equations live in
`TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.RootDatum`; the results here concern the
separately generated carrier over `𝔽₃`, whose defining ideal can be strictly larger than the
reduction of the integral defining ideal.

No reductivity, maximality of the torus, or identification with an independently constructed
pinned group scheme is asserted.

## Main results

* `TauCeti.G2ShortRoot.PrimeField.weightTorus_conj_rootSubgroup`: the torus-conjugation equation on
  scheme-valued points of the prime-field carrier.
* `TauCeti.G2ShortRoot.PrimeField.weightTorus_conj_rootSubgroup_root_simpleIndex` and its
  negative-root counterpart: the scheme-point equations against the named root datum.
* `TauCeti.G2ShortRoot.PrimeField.weightTorusPoints_conj_rootSubgroupPoints_root_simpleIndex`
  and its negative-root counterpart: the same equations on matrix-valued points.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Sections 4.4 and 7.1.
* J. E. Humphreys, *Linear Algebraic Groups*, Sections 26--27.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.

The formal organization follows
`TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.RootDatum`.

-/

public section

universe v

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

namespace TauCeti.G2ShortRoot.PrimeField

open DynkinType

local notation "rootWeight" =>
  DynkinType.G2.rootGeneratorWeight DynkinType.valid_G2

/-! ## The named simply connected root datum -/

/-- **The torus conjugation equation at a named positive simple root.** A scheme-valued point of
the prime-field weight torus conjugates the raising-subgroup element at node `i` through the
corresponding root of the uniform simply connected type-`G₂` datum. -/
theorem weightTorus_conj_rootSubgroup_root_simpleIndex (ht : G2.Valid) (i : Fin 2)
    (A : Type) [CommRing A] [Algebra (ZMod 3) A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of (ZMod 3))) ⟶
      (SplitTorus.groupScheme (ZMod 3) (Fin 2)).X)
    (u : A) :
    (s ≫ weightTorus.hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ZMod 3) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫ (rootSubgroup (.inl i)).hom.hom) *
        (s ≫ weightTorus.hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((TauCeti.torusCharacter
                (SplitTorus.schemePointsMulEquiv (R := ZMod 3) (A := A) s)
                ((G2.simplyConnectedRootDatum ht).root
                  (G2.simpleIndex ht i)) : A) * u)) ≫
        (rootSubgroup (.inl i)).hom.hom := by
  have hroot : rootWeight (.inl i) =
      (G2.simplyConnectedRootDatum ht).root (G2.simpleIndex ht i) := by
    simpa only [rank_G2] using
      G2.rootGeneratorWeight_inl_eq_root_simpleIndex ht i
  rw [← hroot]
  exact weightTorus_conj_rootSubgroup (.inl i) A s u

/-- **The torus conjugation equation at a named negative simple root.** A scheme-valued point of
the prime-field weight torus conjugates the lowering-subgroup element at node `i` through the
negative of the corresponding root of the uniform simply connected type-`G₂` datum. -/
theorem weightTorus_conj_rootSubgroup_neg_root_simpleIndex (ht : G2.Valid) (i : Fin 2)
    (A : Type) [CommRing A] [Algebra (ZMod 3) A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of (ZMod 3))) ⟶
      (SplitTorus.groupScheme (ZMod 3) (Fin 2)).X)
    (u : A) :
    (s ≫ weightTorus.hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ZMod 3) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫ (rootSubgroup (.inr i)).hom.hom) *
        (s ≫ weightTorus.hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((TauCeti.torusCharacter
                (SplitTorus.schemePointsMulEquiv (R := ZMod 3) (A := A) s)
                (-(G2.simplyConnectedRootDatum ht).root
                  (G2.simpleIndex ht i)) : A) * u)) ≫
        (rootSubgroup (.inr i)).hom.hom := by
  have hroot : rootWeight (.inr i) =
      -(G2.simplyConnectedRootDatum ht).root (G2.simpleIndex ht i) := by
    simpa only [rank_G2] using
      G2.rootGeneratorWeight_inr_eq_neg_root_simpleIndex ht i
  rw [← hroot]
  exact weightTorus_conj_rootSubgroup (.inr i) A s u

/-! ## The named equations on matrix-valued points -/

/-- **The prime-field torus-conjugation equation at a named positive simple root, on matrix-valued
points.** The root character is the corresponding root of the uniform simply connected type-`G₂`
datum. -/
theorem weightTorusPoints_conj_rootSubgroupPoints_root_simpleIndex
    (ht : G2.Valid) (i : Fin 2) (A : Type v) [CommRing A] [Algebra (ZMod 3) A]
    (s : Fin 2 → Aˣ) (u : Multiplicative A) :
    weightTorusPoints A s * rootSubgroupPoints (.inl i) A u *
        (weightTorusPoints A s)⁻¹ =
      rootSubgroupPoints (.inl i) A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s
              ((G2.simplyConnectedRootDatum ht).root (G2.simpleIndex ht i)) : A) *
            Multiplicative.toAdd u)) := by
  have hroot : rootWeight (.inl i) =
      (G2.simplyConnectedRootDatum ht).root (G2.simpleIndex ht i) := by
    simpa only [rank_G2] using
      G2.rootGeneratorWeight_inl_eq_root_simpleIndex ht i
  rw [← hroot]
  exact weightTorusPoints_conj_rootSubgroupPoints (.inl i) A s u

/-- **The prime-field torus-conjugation equation at a named negative simple root, on matrix-valued
points.** The root character is the negative of the corresponding root of the uniform simply
connected type-`G₂` datum. -/
theorem weightTorusPoints_conj_rootSubgroupPoints_neg_root_simpleIndex
    (ht : G2.Valid) (i : Fin 2) (A : Type v) [CommRing A] [Algebra (ZMod 3) A]
    (s : Fin 2 → Aˣ) (u : Multiplicative A) :
    weightTorusPoints A s * rootSubgroupPoints (.inr i) A u *
        (weightTorusPoints A s)⁻¹ =
      rootSubgroupPoints (.inr i) A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s
              (-(G2.simplyConnectedRootDatum ht).root (G2.simpleIndex ht i)) : A) *
            Multiplicative.toAdd u)) := by
  have hroot : rootWeight (.inr i) =
      -(G2.simplyConnectedRootDatum ht).root (G2.simpleIndex ht i) := by
    simpa only [rank_G2] using
      G2.rootGeneratorWeight_inr_eq_neg_root_simpleIndex ht i
  rw [← hroot]
  exact weightTorusPoints_conj_rootSubgroupPoints (.inr i) A s u

end TauCeti.G2ShortRoot.PrimeField
