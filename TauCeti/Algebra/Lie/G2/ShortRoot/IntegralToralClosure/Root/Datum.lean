/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic

/-!
# Torus characters of the type-G₂ short-root carrier in its named root datum

`TauCeti.G2ShortRoot.IntegralToralClosure.groupScheme` is the integral toral closure of the
seven-dimensional short-root representation of the type-`G₂` Serre presentation. Its four
numbered simple root subgroups and rank-two split weight torus are explicit. Its conjugation
equation describes the root character as
`DynkinType.G2.rootGeneratorWeight DynkinType.valid_G2`, hence as a Cartan-matrix row.

This file rewrites that equation against the uniform simply connected root datum used by
downstream consumers. The identities
`DynkinType.rootGeneratorWeight_inl_eq_root_simpleIndex` and
`DynkinType.rootGeneratorWeight_inr_eq_neg_root_simpleIndex` identify the character of the
`i`-th raising subgroup with

```text
(G2.simplyConnectedRootDatum ht).root (G2.simpleIndex ht i)
```

and the lowering character with its negative. The results below substitute those identities into
the carrier's integral scheme-level conjugation equation. They therefore certify that the explicit
short-root carrier and `DynkinType.simplyConnectedRootDatum` use the same Bourbaki numbering and
the same character lattice.

This file does not assert reductivity, maximality of the weight torus, existence of all root
subgroups, or an identification of the carrier with an independently defined algebraic group. It
packages only the named simple-root pinning equations already justified by the construction.

## Main results

* `weightTorus_conj_rootSubgroup_root_simpleIndex`: the positive simple-root equation in the
  uniform simply connected `G₂` datum.
* `weightTorus_conj_rootSubgroup_neg_root_simpleIndex`: the negative simple-root equation.
* `weightTorusPoints_conj_rootSubgroupPoints_root_simpleIndex` and its negative-root counterpart:
  the equations on matrix-valued points.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Sections 4.4 and 7.1.
* J. E. Humphreys, *Linear Algebraic Groups*, Sections 26--27.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.
* The formal pattern follows `TauCeti.Algebra.Lie.F4.ShortRoot.RootDatum`.

-/

public section

universe v

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

namespace TauCeti.G2ShortRoot.IntegralToralClosure

open DynkinType

/-! ## Torus conjugation equations against the named simple roots -/

/-- **The torus conjugation equation at a named positive simple root.** A point `s` of the split
weight torus conjugates the raising-subgroup element of parameter `u` at node `i` to the same
subgroup with parameter `αᵢ(s)u`, where `αᵢ` is the corresponding root of the uniform simply
connected type-`G₂` datum. -/
theorem weightTorus_conj_rootSubgroup_root_simpleIndex (ht : G2.Valid) (i : Fin 2)
    (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin 2)).X)
    (u : A) :
    (s ≫ weightTorus.hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫ (rootSubgroup (.inl i)).hom.hom) *
        (s ≫ weightTorus.hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((TauCeti.torusCharacter
                (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s)
                ((G2.simplyConnectedRootDatum ht).root
                  (G2.simpleIndex ht i)) : A) * u)) ≫
        (rootSubgroup (.inl i)).hom.hom := by
  have hroot : G2.rootGeneratorWeight valid_G2 (.inl i) =
      (G2.simplyConnectedRootDatum ht).root (G2.simpleIndex ht i) := by
    simpa only [rank_G2] using
      G2.rootGeneratorWeight_inl_eq_root_simpleIndex ht i
  rw [← hroot]
  exact weightTorus_conj_rootSubgroup (.inl i) A s u

/-- **The torus conjugation equation at a named negative simple root.** A point `s` of the split
weight torus conjugates the lowering-subgroup element of parameter `u` at node `i` to the same
subgroup with parameter `(-αᵢ)(s)u`. -/
theorem weightTorus_conj_rootSubgroup_neg_root_simpleIndex (ht : G2.Valid) (i : Fin 2)
    (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin 2)).X)
    (u : A) :
    (s ≫ weightTorus.hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫ (rootSubgroup (.inr i)).hom.hom) *
        (s ≫ weightTorus.hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((TauCeti.torusCharacter
                (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s)
                (-(G2.simplyConnectedRootDatum ht).root
                  (G2.simpleIndex ht i)) : A) * u)) ≫
        (rootSubgroup (.inr i)).hom.hom := by
  have hroot : G2.rootGeneratorWeight valid_G2 (.inr i) =
      -(G2.simplyConnectedRootDatum ht).root (G2.simpleIndex ht i) := by
    simpa only [rank_G2] using
      G2.rootGeneratorWeight_inr_eq_neg_root_simpleIndex ht i
  rw [← hroot]
  exact weightTorus_conj_rootSubgroup (.inr i) A s u

/-! ## Torus conjugation equations on matrix-valued points -/

/-- **The pinning equation at a named positive simple root, on matrix-valued points.** A point `s`
of the split weight torus conjugates the raising-subgroup element of parameter `u` at node `i` to
the same subgroup with parameter `αᵢ(s)u`, where `αᵢ` is the corresponding root of the uniform
simply connected type-`G₂` datum. -/
theorem weightTorusPoints_conj_rootSubgroupPoints_root_simpleIndex (ht : G2.Valid) (i : Fin 2)
    (A : Type v) [CommRing A] (s : Fin 2 → Aˣ) (u : Multiplicative A) :
    weightTorusPoints A s * rootSubgroupPoints (.inl i) A u * (weightTorusPoints A s)⁻¹ =
      rootSubgroupPoints (.inl i) A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s
              ((G2.simplyConnectedRootDatum ht).root (G2.simpleIndex ht i)) : A) *
            Multiplicative.toAdd u)) := by
  have hroot : G2.rootGeneratorWeight valid_G2 (.inl i) =
      (G2.simplyConnectedRootDatum ht).root (G2.simpleIndex ht i) := by
    simpa only [rank_G2] using
      G2.rootGeneratorWeight_inl_eq_root_simpleIndex ht i
  rw [← hroot]
  exact weightTorusPoints_conj_rootSubgroupPoints (.inl i) A s u

/-- **The pinning equation at a named negative simple root, on matrix-valued points.** A point `s`
of the split weight torus conjugates the lowering-subgroup element of parameter `u` at node `i` to
the same subgroup with parameter `(-αᵢ)(s)u`. -/
theorem weightTorusPoints_conj_rootSubgroupPoints_neg_root_simpleIndex (ht : G2.Valid) (i : Fin 2)
    (A : Type v) [CommRing A] (s : Fin 2 → Aˣ) (u : Multiplicative A) :
    weightTorusPoints A s * rootSubgroupPoints (.inr i) A u * (weightTorusPoints A s)⁻¹ =
      rootSubgroupPoints (.inr i) A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s
              (-(G2.simplyConnectedRootDatum ht).root (G2.simpleIndex ht i)) : A) *
            Multiplicative.toAdd u)) := by
  have hroot : G2.rootGeneratorWeight valid_G2 (.inr i) =
      -(G2.simplyConnectedRootDatum ht).root (G2.simpleIndex ht i) := by
    simpa only [rank_G2] using
      G2.rootGeneratorWeight_inr_eq_neg_root_simpleIndex ht i
  rw [← hroot]
  exact weightTorusPoints_conj_rootSubgroupPoints (.inr i) A s u

end TauCeti.G2ShortRoot.IntegralToralClosure
