/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.InnerConjugation
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.RootSubgroup

/-!
# Root-subgroup morphisms at every root of the Geck carrier

The pinned Geck carrier has group-scheme morphisms for its numbered simple positive and negative
root subgroups. A Weyl word `l` also determines an integral point `n_l` of the carrier. Inner
conjugation by that point transports the positive simple-root morphism at a node `i` to a
group-scheme morphism

```text
x_{l,i} : 𝔾ₐ ⟶ G,    u ↦ n_l x_i(u) n_l⁻¹
```

at the root `w α_i`, where `w` is the Weyl-group element spelled by `l`. Thus every root of the
pinned simply connected root datum is represented by an actual closed root-subgroup scheme, not
only by a homomorphism on points.

The construction remains indexed by a Weyl word and a simple node. Different presentations of the
same root are not identified here; their parametrizations can differ by a sign. Establishing that
presentation independence and fixing those signs is separate input to the Chevalley commutator
relations.

## Main definitions

* `TauCeti.DynkinType.geckWeylWordInnerConjugation`: inner conjugation by the integral Weyl-word
  point, as an automorphism of the Geck group scheme.
* `TauCeti.DynkinType.geckWeylRootSubgroup`: the transported root-subgroup morphism.
* `TauCeti.DynkinType.geckRootSubgroupAt`: a chosen closed root-subgroup morphism indexed directly
  by every root.

## Main results

* `TauCeti.DynkinType.geckWeylRootSubgroup_nil`: the empty word recovers the numbered positive
  simple-root morphism.
* `TauCeti.DynkinType.geckSchemePointsMulEquiv_comp_geckWeylRootSubgroup_eq_conj`: the transported
  morphism is conjugation by the Weyl-word point on every commutative-ring-valued point.
* `TauCeti.DynkinType.geckSchemePointsMulEquiv_comp_geckWeylRootSubgroup`: evaluation agrees
  directly with the existing all-root point homomorphism.
* `TauCeti.DynkinType.isClosedImmersion_geckWeylRootSubgroup`: every transported root subgroup is
  a closed immersion.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
* J. E. Humphreys, *Linear Algebraic Groups*, §26.3.
-/

public section

open AlgebraicGeometry CategoryTheory WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.DynkinType

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

/-- **Inner conjugation by the integral Weyl-word point**, as an automorphism of the Geck group
scheme. On points over a commutative ring it sends `g` to `n_l g n_l⁻¹`. -/
def geckWeylWordInnerConjugation (l : List (Fin t.rank)) : Aut (t.geckGroupScheme ht) :=
  t.geckInnerConjugation ht (t.geckWeylWordPoint ht l ℤ)

/-- `geckWeylWordInnerConjugation` is inner conjugation by the integral Weyl-word point. -/
theorem geckWeylWordInnerConjugation_def (l : List (Fin t.rank)) :
    t.geckWeylWordInnerConjugation ht l =
      t.geckInnerConjugation ht (t.geckWeylWordPoint ht l ℤ) :=
  (rfl)

/-- **On scheme-valued points, the Weyl-word automorphism is conjugation by the existing
matrix-valued Weyl-word point.** -/
@[simp]
theorem geckSchemePointsMulEquiv_comp_geckWeylWordInnerConjugation
    (l : List (Fin t.rank)) (A : Type) [CommRing A]
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (t.geckGroupScheme ht).X) :
    t.geckSchemePointsMulEquiv ht A
        (p ≫ (t.geckWeylWordInnerConjugation ht l).hom.hom.hom) =
      t.geckWeylWordPoint ht l A * t.geckSchemePointsMulEquiv ht A p *
        (t.geckWeylWordPoint ht l A)⁻¹ := by
  rw [geckWeylWordInnerConjugation_def,
    t.geckSchemePointsMulEquiv_comp_geckInnerConjugation ht,
    map_geckWeylWordPoint]

/-- Inner conjugation by the empty Weyl word is the identity group-scheme automorphism. -/
@[simp]
theorem geckWeylWordInnerConjugation_nil :
    t.geckWeylWordInnerConjugation ht [] = Iso.refl _ := by
  rw [geckWeylWordInnerConjugation_def, geckWeylWordPoint_nil, geckInnerConjugation_one]

/-- **The root-subgroup morphism attached to a Weyl word and a simple node**: conjugate the
positive simple-root subgroup at `i` by the integral Weyl-word point. Its root in the pinned root
datum is `geckWeylRootIndex l i`. -/
def geckWeylRootSubgroup (l : List (Fin t.rank)) (i : Fin t.rank) :
    AdditiveGroup.groupScheme ℤ ⟶ t.geckGroupScheme ht :=
  t.geckRootSubgroup ht (.inl i) ≫ (t.geckWeylWordInnerConjugation ht l).hom

/-- A Weyl-transported root subgroup is the positive simple-root subgroup followed by the
corresponding inner automorphism. -/
theorem geckWeylRootSubgroup_def (l : List (Fin t.rank)) (i : Fin t.rank) :
    t.geckWeylRootSubgroup ht l i =
      t.geckRootSubgroup ht (.inl i) ≫ (t.geckWeylWordInnerConjugation ht l).hom :=
  (rfl)

/-- The empty Weyl word recovers the numbered positive simple-root morphism. -/
@[simp]
theorem geckWeylRootSubgroup_nil (i : Fin t.rank) :
    t.geckWeylRootSubgroup ht [] i = t.geckRootSubgroup ht (.inl i) := by
  rw [geckWeylRootSubgroup_def, geckWeylWordInnerConjugation_nil, Iso.refl_hom,
    Category.comp_id]

/-- **On scheme-valued points, the transported root-subgroup morphism is conjugation of the
numbered positive simple-root morphism by the Weyl-word point.** -/
theorem geckSchemePointsMulEquiv_comp_geckWeylRootSubgroup_eq_conj
    (l : List (Fin t.rank)) (i : Fin t.rank) (A : Type) [CommRing A]
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (AdditiveGroup.groupScheme ℤ).X) :
    t.geckSchemePointsMulEquiv ht A
        (p ≫ (t.geckWeylRootSubgroup ht l i).hom.hom) =
      t.geckWeylWordPoint ht l A *
          t.geckSchemePointsMulEquiv ht A
            (p ≫ (t.geckRootSubgroup ht (.inl i)).hom.hom) *
        (t.geckWeylWordPoint ht l A)⁻¹ := by
  rw [geckWeylRootSubgroup_def]
  simp only [Grp.comp', Mon.comp_hom']
  exact t.geckSchemePointsMulEquiv_comp_geckWeylWordInnerConjugation ht l A
    (p ≫ (t.geckRootSubgroup ht (.inl i)).hom.hom)

/-- **The scheme morphism at an arbitrary root induces the existing all-root point
homomorphism.** -/
@[simp]
theorem geckSchemePointsMulEquiv_comp_geckWeylRootSubgroup
    (l : List (Fin t.rank)) (i : Fin t.rank) (A : Type) [CommRing A]
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (AdditiveGroup.groupScheme ℤ).X) :
    t.geckSchemePointsMulEquiv ht A
        (p ≫ (t.geckWeylRootSubgroup ht l i).hom.hom) =
      t.geckWeylRootSubgroupPoints ht l i A
        (AdditiveGroup.schemePointsMulEquiv A p) := by
  rw [t.geckSchemePointsMulEquiv_comp_geckWeylRootSubgroup_eq_conj ht l i A p,
    t.geckSchemePointsMulEquiv_comp_geckRootSubgroup ht (.inl i) A p,
    geckWeylRootSubgroupPoints_apply]

/-! ## The root-indexed family -/

/-- **The selected root-subgroup morphism at a root index.** Its Weyl-word presentation is fixed
by `geckRootSubgroupPresentation`; no presentation-independence claim is made. -/
def geckRootSubgroupAt (k : Fin t.numRoots) :
    AdditiveGroup.groupScheme ℤ ⟶ t.geckGroupScheme ht :=
  t.geckWeylRootSubgroup ht (t.geckRootSubgroupPresentation ht k).1
    (t.geckRootSubgroupPresentation ht k).2

/-- The root-indexed subgroup uses the fixed Weyl-word presentation of that root. -/
theorem geckRootSubgroupAt_def (k : Fin t.numRoots) :
    t.geckRootSubgroupAt ht k =
      t.geckWeylRootSubgroup ht (t.geckRootSubgroupPresentation ht k).1
        (t.geckRootSubgroupPresentation ht k).2 :=
  (rfl)

/-- At a positive simple-root index, the root-indexed family recovers the pinned root-subgroup
morphism. -/
@[simp]
theorem geckRootSubgroupAt_simpleIndex (i : Fin t.rank) :
    t.geckRootSubgroupAt ht (t.simpleIndex ht i) =
      t.geckRootSubgroup ht (.inl i) := by
  rw [geckRootSubgroupAt_def, geckRootSubgroupPresentation_simpleIndex,
    geckWeylRootSubgroup_nil]

/-- Evaluation of the root-indexed morphism agrees with the point-level subgroup at its selected
presentation. -/
@[simp]
theorem geckSchemePointsMulEquiv_comp_geckRootSubgroupAt
    (k : Fin t.numRoots) (A : Type) [CommRing A]
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (AdditiveGroup.groupScheme ℤ).X) :
    t.geckSchemePointsMulEquiv ht A (p ≫ (t.geckRootSubgroupAt ht k).hom.hom) =
      t.geckWeylRootSubgroupPoints ht (t.geckRootSubgroupPresentation ht k).1
        (t.geckRootSubgroupPresentation ht k).2 A
        (AdditiveGroup.schemePointsMulEquiv A p) := by
  exact t.geckSchemePointsMulEquiv_comp_geckWeylRootSubgroup ht
    (t.geckRootSubgroupPresentation ht k).1 (t.geckRootSubgroupPresentation ht k).2 A p

/-- Every Weyl-transported root-subgroup morphism is a closed immersion. -/
instance isClosedImmersion_geckWeylRootSubgroup (l : List (Fin t.rank)) (i : Fin t.rank) :
    IsClosedImmersion (t.geckWeylRootSubgroup ht l i).hom.hom.left := by
  let _ : IsIso (t.geckWeylWordInnerConjugation ht l).hom :=
    (t.geckWeylWordInnerConjugation ht l).isIso_hom
  rw [← closedSubgroupMorphismProperty_iff]
  rw [geckWeylRootSubgroup_def,
    (closedSubgroupMorphismProperty _).cancel_right_of_respectsIso]
  rw [closedSubgroupMorphismProperty_iff]
  infer_instance

/-- Every root-indexed subgroup morphism is a closed immersion. -/
instance isClosedImmersion_geckRootSubgroupAt (k : Fin t.numRoots) :
    IsClosedImmersion (t.geckRootSubgroupAt ht k).hom.hom.left := by
  rw [geckRootSubgroupAt_def]
  infer_instance

end

end TauCeti.DynkinType
