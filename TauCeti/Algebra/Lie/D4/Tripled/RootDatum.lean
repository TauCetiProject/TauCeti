/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.GroupScheme

/-!
# Torus characters of the tripled type-D4 carrier in its named root datum

`TauCeti.D4Tripled.groupScheme` is the full-weight Chevalley carrier obtained from the
twenty-four-dimensional representation `V(ϖ₁) ⊕ V(ϖ₃) ⊕ V(ϖ₄)` of the type-`D₄` Serre
presentation. Its eight numbered simple-root subgroups and rank-four split weight torus are
explicit. The carrier's conjugation equation initially describes the root character as
`TauCeti.TypeDStd.rootGeneratorWeight 4`, hence as a row of the type-`D₄` Cartan matrix.

This file rewrites that equation against the uniform simply connected root datum used by
downstream consumers. The identities
`TauCeti.TypeDStd.rootGeneratorWeight_inl_eq_root_simpleIndex` and
`TauCeti.TypeDStd.rootGeneratorWeight_inr_eq_neg_root_simpleIndex` identify the character of the
`i`-th raising subgroup with

```text
((DynkinType.D 4).simplyConnectedRootDatum ht).root
  ((DynkinType.D 4).simpleIndex ht i)
```

and the lowering character with its negative. The results below substitute these identities into
the carrier's conjugation equations. They therefore certify that the tripled carrier and
`DynkinType.simplyConnectedRootDatum` use the same Bourbaki numbering and character lattice.

This file does not assert reductivity, maximality of the weight torus, existence of all root
subgroups, or an identification of the carrier with an independently defined algebraic group. It
packages only the named simple-root pinning equations already justified by the construction.

## Main results

* `TauCeti.D4Tripled.weightTorus_conj_rootSubgroup_root_simpleIndex`: conjugation by the weight
  torus on a positive simple-root subgroup is governed by the corresponding root of the uniform
  simply connected type-`D₄` datum.
* `TauCeti.D4Tripled.weightTorus_conj_rootSubgroup_neg_root_simpleIndex`: the analogous equation
  for a negative simple root.
* `TauCeti.D4Tripled.weightTorusPoints_conj_rootSubgroupPoints_root_simpleIndex` and
  `TauCeti.D4Tripled.weightTorusPoints_conj_rootSubgroupPoints_neg_root_simpleIndex`: the same
  equations on matrix-valued points.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Sections 4.4, 7.1, and 12.2.
* J. E. Humphreys, *Linear Algebraic Groups*, Sections 26--27.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* The interface follows `TauCeti.Algebra.Lie.F4.ShortRoot.RootDatum` and
  `TauCeti.Algebra.Lie.E7.Minuscule.RootDatum`.
-/

public section

universe v

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

namespace TauCeti.D4Tripled

open DynkinType

/-! ## Torus conjugation equations against the named simple roots -/

/-- **The torus conjugation equation at a named positive simple root.** A point `s` of the split
weight torus conjugates the raising-subgroup element of parameter `u` at node `i` to the same
subgroup with parameter `αᵢ(s)u`, where `αᵢ` is the corresponding root of the uniform simply
connected type-`D₄` datum. -/
theorem weightTorus_conj_rootSubgroup_root_simpleIndex (ht : (D 4).Valid) (i : Fin 4)
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
                (((D 4).simplyConnectedRootDatum ht).root
                  ((D 4).simpleIndex ht i)) : A) * u)) ≫
        (rootSubgroup (.inl i)).hom.hom := by
  rw [← TypeDStd.rootGeneratorWeight_inl_eq_root_simpleIndex 4 (by omega)]
  exact weightTorus_conj_rootSubgroup (.inl i) A s u

/-- **The torus conjugation equation at a named negative simple root.** A point `s` of the split
weight torus conjugates the lowering-subgroup element of parameter `u` at node `i` to the same
subgroup with parameter `(-αᵢ)(s)u`. -/
theorem weightTorus_conj_rootSubgroup_neg_root_simpleIndex (ht : (D 4).Valid) (i : Fin 4)
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
                (-((D 4).simplyConnectedRootDatum ht).root
                  ((D 4).simpleIndex ht i)) : A) * u)) ≫
        (rootSubgroup (.inr i)).hom.hom := by
  rw [← TypeDStd.rootGeneratorWeight_inr_eq_neg_root_simpleIndex 4 (by omega)]
  exact weightTorus_conj_rootSubgroup (.inr i) A s u

/-! ## Torus conjugation equations on matrix-valued points -/

/-- **The pinning equation at a named positive simple root, on matrix-valued points.** A point
`s` of the split weight torus conjugates the raising-subgroup element of parameter `u` at node
`i` to the same subgroup with parameter `αᵢ(s)u`. -/
theorem weightTorusPoints_conj_rootSubgroupPoints_root_simpleIndex
    (ht : (D 4).Valid) (i : Fin 4) (A : Type v) [CommRing A]
    (s : Fin 4 → Aˣ) (u : Multiplicative A) :
    weightTorusPoints A s * rootSubgroupPoints (.inl i) A u * (weightTorusPoints A s)⁻¹ =
      rootSubgroupPoints (.inl i) A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s
              (((D 4).simplyConnectedRootDatum ht).root ((D 4).simpleIndex ht i)) : A) *
            Multiplicative.toAdd u)) := by
  rw [← TypeDStd.rootGeneratorWeight_inl_eq_root_simpleIndex 4 (by omega)]
  exact weightTorusPoints_conj_rootSubgroupPoints (.inl i) A s u

/-- **The pinning equation at a named negative simple root, on matrix-valued points.** A point
`s` of the split weight torus conjugates the lowering-subgroup element of parameter `u` at node
`i` to the same subgroup with parameter `(-αᵢ)(s)u`. -/
theorem weightTorusPoints_conj_rootSubgroupPoints_neg_root_simpleIndex
    (ht : (D 4).Valid) (i : Fin 4) (A : Type v) [CommRing A]
    (s : Fin 4 → Aˣ) (u : Multiplicative A) :
    weightTorusPoints A s * rootSubgroupPoints (.inr i) A u * (weightTorusPoints A s)⁻¹ =
      rootSubgroupPoints (.inr i) A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s
              (-((D 4).simplyConnectedRootDatum ht).root ((D 4).simpleIndex ht i)) : A) *
            Multiplicative.toAdd u)) := by
  rw [← TypeDStd.rootGeneratorWeight_inr_eq_neg_root_simpleIndex 4 (by omega)]
  exact weightTorusPoints_conj_rootSubgroupPoints (.inr i) A s u

end TauCeti.D4Tripled
