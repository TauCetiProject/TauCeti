/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Carrier

/-!
# Torus characters of the type-F4 short-root carrier in its named root datum

`TauCeti.F4ShortRoot.groupScheme` is the full-weight Chevalley carrier obtained from the
26-dimensional short-root representation of the type-`F₄` Serre presentation. Its eight
numbered simple root subgroups and rank-four split weight torus are explicit. The carrier's
conjugation equation initially describes the root character as
`DynkinType.F4.rootGeneratorWeight DynkinType.valid_F4`, hence as a Cartan-matrix row.

This file rewrites that equation against the uniform simply connected root datum used by
downstream consumers. The identities
`DynkinType.rootGeneratorWeight_inl_eq_root_simpleIndex` and
`DynkinType.rootGeneratorWeight_inr_eq_neg_root_simpleIndex` identify the character of the
`i`-th raising subgroup with

```text
(F4.simplyConnectedRootDatum ht).root (F4.simpleIndex ht i)
```

and the lowering character with its negative. The results below substitute those identities into
the carrier's scheme-level conjugation equation. They therefore certify that the explicit
short-root carrier and `DynkinType.simplyConnectedRootDatum` use the same Bourbaki numbering and
the same character lattice.

This file does not assert reductivity, maximality of the weight torus, existence of all root
subgroups, or an identification of the carrier with an independently defined algebraic group. It
packages only the named simple-root pinning equations already justified by the construction.

## Main results

* `TauCeti.F4ShortRoot.weightTorus_conj_rootSubgroup_root_simpleIndex`: conjugation by the
  weight torus on a positive simple root subgroup is governed by the corresponding root of the
  uniform simply connected `F₄` datum.
* `TauCeti.F4ShortRoot.weightTorus_conj_rootSubgroup_neg_root_simpleIndex`: the analogous
  equation for a negative simple root.
* `TauCeti.F4ShortRoot.weightTorusPoints_conj_rootSubgroupPoints_root_simpleIndex` and
  `TauCeti.F4ShortRoot.weightTorusPoints_conj_rootSubgroupPoints_neg_root_simpleIndex`: the same
  two equations on matrix-valued points, which is the form a consumer working with a group of
  points rather than with scheme morphisms uses.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Sections 4.4 and 7.1.
* J. E. Humphreys, *Linear Algebraic Groups*, Sections 26--27.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VIII.
* The corresponding formal type-`E₇` construction in
  `TauCeti.Algebra.Lie.E7.Minuscule.RootDatum`.

-/

public section

universe v

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

namespace TauCeti.F4ShortRoot

open DynkinType

/-! ## Torus conjugation equations against the named simple roots -/

/-- **The torus conjugation equation at a named positive simple root.** A point `s` of the split
weight torus conjugates the raising-subgroup element of parameter `u` at node `i` to the same
subgroup with parameter `αᵢ(s)u`, where `αᵢ` is the corresponding root of the uniform simply
connected type-`F₄` datum. -/
theorem weightTorus_conj_rootSubgroup_root_simpleIndex (ht : F4.Valid) (i : Fin 4)
    (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin 4)).X)
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
                ((F4.simplyConnectedRootDatum ht).root
                  (F4.simpleIndex ht i)) : A) * u)) ≫
        (rootSubgroup (.inl i)).hom.hom := by
  have hroot : F4.rootGeneratorWeight valid_F4 (.inl i) =
      (F4.simplyConnectedRootDatum ht).root (F4.simpleIndex ht i) := by
    simpa only [rank_F4] using
      F4.rootGeneratorWeight_inl_eq_root_simpleIndex ht i
  rw [← hroot]
  exact weightTorus_conj_rootSubgroup (.inl i) A s u

/-- **The torus conjugation equation at a named negative simple root.** A point `s` of the split
weight torus conjugates the lowering-subgroup element of parameter `u` at node `i` to the same
subgroup with parameter `(-αᵢ)(s)u`. -/
theorem weightTorus_conj_rootSubgroup_neg_root_simpleIndex (ht : F4.Valid) (i : Fin 4)
    (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin 4)).X)
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
                (-(F4.simplyConnectedRootDatum ht).root
                  (F4.simpleIndex ht i)) : A) * u)) ≫
        (rootSubgroup (.inr i)).hom.hom := by
  have hroot : F4.rootGeneratorWeight valid_F4 (.inr i) =
      -(F4.simplyConnectedRootDatum ht).root (F4.simpleIndex ht i) := by
    simpa only [rank_F4] using
      F4.rootGeneratorWeight_inr_eq_neg_root_simpleIndex ht i
  rw [← hroot]
  exact weightTorus_conj_rootSubgroup (.inr i) A s u

/-! ## Torus conjugation equations on matrix-valued points -/

/-- **The pinning equation at a named positive simple root, on matrix-valued points.** A point `s`
of the split weight torus conjugates the raising-subgroup element of parameter `u` at node `i` to
the same subgroup with parameter `αᵢ(s)u`, where `αᵢ` is the corresponding root of the uniform
simply connected type-`F₄` datum. -/
theorem weightTorusPoints_conj_rootSubgroupPoints_root_simpleIndex (ht : F4.Valid) (i : Fin 4)
    (A : Type v) [CommRing A] (s : Fin 4 → Aˣ) (u : Multiplicative A) :
    weightTorusPoints A s * rootSubgroupPoints (.inl i) A u * (weightTorusPoints A s)⁻¹ =
      rootSubgroupPoints (.inl i) A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s
              ((F4.simplyConnectedRootDatum ht).root (F4.simpleIndex ht i)) : A) *
            Multiplicative.toAdd u)) := by
  have hroot : F4.rootGeneratorWeight valid_F4 (.inl i) =
      (F4.simplyConnectedRootDatum ht).root (F4.simpleIndex ht i) := by
    simpa only [rank_F4] using
      F4.rootGeneratorWeight_inl_eq_root_simpleIndex ht i
  rw [← hroot]
  exact weightTorusPoints_conj_rootSubgroupPoints (.inl i) A s u

/-- **The pinning equation at a named negative simple root, on matrix-valued points.** A point `s`
of the split weight torus conjugates the lowering-subgroup element of parameter `u` at node `i` to
the same subgroup with parameter `(-αᵢ)(s)u`. -/
theorem weightTorusPoints_conj_rootSubgroupPoints_neg_root_simpleIndex (ht : F4.Valid) (i : Fin 4)
    (A : Type v) [CommRing A] (s : Fin 4 → Aˣ) (u : Multiplicative A) :
    weightTorusPoints A s * rootSubgroupPoints (.inr i) A u * (weightTorusPoints A s)⁻¹ =
      rootSubgroupPoints (.inr i) A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s
              (-(F4.simplyConnectedRootDatum ht).root (F4.simpleIndex ht i)) : A) *
            Multiplicative.toAdd u)) := by
  have hroot : F4.rootGeneratorWeight valid_F4 (.inr i) =
      -(F4.simplyConnectedRootDatum ht).root (F4.simpleIndex ht i) := by
    simpa only [rank_F4] using
      F4.rootGeneratorWeight_inr_eq_neg_root_simpleIndex ht i
  rw [← hroot]
  exact weightTorusPoints_conj_rootSubgroupPoints (.inr i) A s u

end TauCeti.F4ShortRoot
