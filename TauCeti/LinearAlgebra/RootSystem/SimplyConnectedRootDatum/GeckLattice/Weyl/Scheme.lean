/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.InnerConjugation
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

## Main results

* `TauCeti.DynkinType.geckWeylRootSubgroup_nil`: the empty word recovers the numbered positive
  simple-root morphism.
* `TauCeti.DynkinType.geckSchemePointsMulEquiv_comp_geckWeylRootSubgroup_eq_conj`: the transported
  morphism is conjugation by the Weyl-word point on every commutative-ring-valued point.
* `TauCeti.DynkinType.geckSchemePointsMulEquiv_comp_geckWeylRootSubgroup`: evaluation agrees
  directly with the existing all-root point homomorphism.
* `TauCeti.DynkinType.isClosedImmersion_geckWeylRootSubgroup`: every transported root subgroup is
  a closed immersion.
* `TauCeti.DynkinType.geckRootSubgroupAt`: a chosen closed root-subgroup morphism indexed directly
  by every root.

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

/-- The integral Weyl-word point, read intrinsically as a point of the carrier's coordinate Hopf
algebra. -/
def geckWeylWordCoordinatePoint (l : List (Fin t.rank)) :
    HopfAlgebra.points (R := ℤ) (H := t.geckCoordinateHopfAlgebra ht) (CommAlgCat.of ℤ ℤ) :=
  (t.geckPointsPresentation ht (CommAlgCat.of ℤ ℤ)).mulEquiv.symm
    (t.geckWeylWordPoint ht l ℤ)

/-- **Inner conjugation by the integral Weyl-word point**, as an automorphism of the Geck group
scheme. On points over a commutative ring it sends `g` to `n_l g n_l⁻¹`. -/
def geckWeylWordInnerConjugation (l : List (Fin t.rank)) : Aut (t.geckGroupScheme ht) :=
  (eqToIso (by simpa only [geckCoordinateHopfAlgebra] using
    t.geckGroupScheme_def ht)).trans
    ((hopfSpec (CommRingCat.of ℤ)).mapIso
      (CommHopfAlgCat.innerConjugationIso (t.geckCoordinateHopfAlgebra ht)
        (t.geckWeylWordCoordinatePoint ht l)).op) |>.trans
    (eqToIso (by simpa only [geckCoordinateHopfAlgebra] using
      t.geckGroupScheme_def ht)).symm

/-- Forgetting the group-object and over-category structure of the Weyl-word automorphism
recovers its underlying scheme automorphism. This localizes the definitional behavior of the two
concrete forgetful functors. -/
private theorem geckWeylWordInnerConjugation_forget_mapIso_hom (l : List (Fin t.rank)) :
    ((Over.forget _).mapIso
      ((Grp.forget _).mapIso (t.geckWeylWordInnerConjugation ht l))).hom =
      (t.geckWeylWordInnerConjugation ht l).hom.hom.hom.left :=
  rfl

/-- On presented scheme-valued points, `geckWeylWordInnerConjugation` is induced by the coordinate
inner automorphism. -/
theorem geckGroupSchemePointMulEquiv_comp_geckWeylWordInnerConjugation
    (l : List (Fin t.rank)) (A : Type) [CommRing A]
    (q : HopfAlgebra.points (R := ℤ) (H := t.geckCoordinateHopfAlgebra ht)
      (CommAlgCat.of ℤ A)) :
    t.geckGroupSchemePointMulEquiv ht A q ≫
        (t.geckWeylWordInnerConjugation ht l).hom.hom.hom =
      t.geckGroupSchemePointMulEquiv ht A
        ((CommHopfAlgCat.mapPointsFunctor
          (CommHopfAlgCat.innerConjugationIso (t.geckCoordinateHopfAlgebra ht)
            (t.geckWeylWordCoordinatePoint ht l)).hom).app (CommAlgCat.of ℤ A) q) := by
  have hG : t.geckGroupScheme ht =
      (hopfSpec (CommRingCat.of ℤ)).obj
        (Opposite.op (t.geckCoordinateHopfAlgebra ht)) := by
    simpa only [geckCoordinateHopfAlgebra] using t.geckGroupScheme_def ht
  rw [geckWeylWordInnerConjugation]
  exact CommHopfAlgCat.pointMulEquivOfPresentation_mapDomain (R := ℤ) A
    hG hG
    (t.geckGroupSchemePointMulEquiv ht A) (t.geckGroupSchemePointMulEquiv ht A)
    (t.geckGroupSchemePointMulEquiv_apply_left ht A)
    (t.geckGroupSchemePointMulEquiv_apply_left ht A)
    (CommHopfAlgCat.innerConjugationIso (t.geckCoordinateHopfAlgebra ht)
      (t.geckWeylWordCoordinatePoint ht l)).hom q

/-- The empty Weyl word gives the identity coordinate point. -/
@[simp]
theorem geckWeylWordCoordinatePoint_nil : t.geckWeylWordCoordinatePoint ht [] = 1 := by
  apply (t.geckPointsPresentation ht (CommAlgCat.of ℤ ℤ)).mulEquiv.injective
  rw [geckWeylWordCoordinatePoint, MulEquiv.apply_symm_apply, map_one,
    geckWeylWordPoint_nil]

/-- Extending the integral coordinate point of a Weyl word to a commutative ring recovers the
existing matrix-valued Weyl-word point. -/
@[simp]
theorem geckPointsPresentation_mulEquiv_extend_geckWeylWordCoordinatePoint
    (l : List (Fin t.rank)) (A : Type) [CommRing A] :
    (t.geckPointsPresentation ht A).mulEquiv
        (HopfAlgebra.extendPoint (t.geckCoordinateHopfAlgebra ht) (CommAlgCat.of ℤ A)
          (t.geckWeylWordCoordinatePoint ht l)) =
      t.geckWeylWordPoint ht l A := by
  rw [← HopfAlgebra.mapValue_extendPoint _ (A := CommAlgCat.of ℤ ℤ)
    (Algebra.ofId ℤ (CommAlgCat.of ℤ A)), HopfAlgebra.extendPoint_self]
  -- `mapValue` and the categorical `mapPoints` have definitionally equal applications but no
  -- proposition-level comparison lemma; expose that application before using naturality.
  change (t.geckPointsPresentation ht (CommAlgCat.of ℤ A)).mulEquiv
      (HopfAlgebra.mapPoints
        (CommAlgCat.ofHom (Algebra.ofId ℤ (CommAlgCat.of ℤ A)))
        (t.geckWeylWordCoordinatePoint ht l)) = _
  rw [(t.geckPointsPresentation ht (CommAlgCat.of ℤ ℤ)).mulEquiv_mapPoints
    (t.geckPointsPresentation ht (CommAlgCat.of ℤ A))
    (CommAlgCat.ofHom (Algebra.ofId ℤ (CommAlgCat.of ℤ A)))]
  rw [geckWeylWordCoordinatePoint, MulEquiv.apply_symm_apply,
    map_geckWeylWordPoint]

/-- **On scheme-valued points, the Weyl-word automorphism is conjugation by the existing
matrix-valued Weyl-word point.** -/
theorem geckSchemePointsMulEquiv_comp_geckWeylWordInnerConjugation
    (l : List (Fin t.rank)) (A : Type) [CommRing A]
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (t.geckGroupScheme ht).X) :
    t.geckSchemePointsMulEquiv ht A
        (p ≫ (t.geckWeylWordInnerConjugation ht l).hom.hom.hom) =
      t.geckWeylWordPoint ht l A * t.geckSchemePointsMulEquiv ht A p *
        (t.geckWeylWordPoint ht l A)⁻¹ := by
  obtain ⟨q, rfl⟩ := (t.geckGroupSchemePointMulEquiv ht A).surjective p
  rw [t.geckGroupSchemePointMulEquiv_comp_geckWeylWordInnerConjugation ht l A]
  rw [CommHopfAlgCat.mapPointsFunctor_innerConjugationIso_hom,
    HopfAlgebra.innerConjugationPointNatIso_hom_app_apply]
  rw [geckSchemePointsMulEquiv_groupSchemePointMulEquiv,
    geckSchemePointsMulEquiv_groupSchemePointMulEquiv]
  rw [map_mul, map_mul, map_inv,
    t.geckPointsPresentation_mulEquiv_extend_geckWeylWordCoordinatePoint ht l A]

/-- Inner conjugation by the empty Weyl word is the identity group-scheme automorphism. -/
@[simp]
theorem geckWeylWordInnerConjugation_nil :
    t.geckWeylWordInnerConjugation ht [] = Iso.refl _ := by
  rw [geckWeylWordInnerConjugation, geckWeylWordCoordinatePoint_nil,
    CommHopfAlgCat.innerConjugationIso_one]
  apply Iso.ext
  simp

/-- **The root-subgroup morphism attached to a Weyl word and a simple node**: conjugate the
positive simple-root subgroup at `i` by the integral Weyl-word point. Its root in the pinned root
datum is `geckWeylRootIndex l i`. -/
def geckWeylRootSubgroup (l : List (Fin t.rank)) (i : Fin t.rank) :
    AdditiveGroup.groupScheme ℤ ⟶ t.geckGroupScheme ht :=
  t.geckRootSubgroup ht (.inl i) ≫ (t.geckWeylWordInnerConjugation ht l).hom

/-- The underlying scheme map of a transported root subgroup is the composite of the numbered
root subgroup with the forgotten Weyl-word automorphism. -/
private theorem geckWeylRootSubgroup_hom_left
    (l : List (Fin t.rank)) (i : Fin t.rank) :
    (t.geckWeylRootSubgroup ht l i).hom.hom.left =
      (t.geckRootSubgroup ht (.inl i)).hom.hom.left ≫
        (t.geckWeylWordInnerConjugation ht l).hom.hom.hom.left := by
  rw [geckWeylRootSubgroup]
  rfl

/-- The empty Weyl word recovers the numbered positive simple-root morphism. -/
@[simp]
theorem geckWeylRootSubgroup_nil (i : Fin t.rank) :
    t.geckWeylRootSubgroup ht [] i = t.geckRootSubgroup ht (.inl i) := by
  rw [geckWeylRootSubgroup, geckWeylWordInnerConjugation_nil, Iso.refl_hom, Category.comp_id]

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
  rw [geckWeylRootSubgroup]
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

/-- A selected Weyl-word presentation `(l, i)` of each root index. At a positive simple-root
index this is the pinned presentation `([], i)`; elsewhere the selection fixes a usable
root-indexed family without asserting that different presentations give the same parametrization. -/
def geckRootSubgroupPresentation (k : Fin t.numRoots) :
    List (Fin t.rank) × Fin t.rank :=
  if hk : (k : ℕ) < t.rank then
    ([], ⟨k, hk⟩)
  else
    Classical.choose (show ∃ p : List (Fin t.rank) × Fin t.rank,
        t.geckWeylRootIndex ht p.1 p.2 = k by
      obtain ⟨l, i, hli⟩ := t.exists_geckWeylRootIndex_eq ht k
      exact ⟨(l, i), hli⟩)

/-- The selected presentation at a positive simple-root index is the pinned empty-word
presentation. -/
@[simp]
theorem geckRootSubgroupPresentation_simpleIndex (i : Fin t.rank) :
    t.geckRootSubgroupPresentation ht (t.simpleIndex ht i) = ([], i) := by
  simp [geckRootSubgroupPresentation]

/-- The selected presentation of `k` represents `k`. -/
@[simp]
theorem geckRootSubgroupPresentation_index (k : Fin t.numRoots) :
    t.geckWeylRootIndex ht (t.geckRootSubgroupPresentation ht k).1
        (t.geckRootSubgroupPresentation ht k).2 = k := by
  rw [geckRootSubgroupPresentation]
  split_ifs with hk
  · rw [geckWeylRootIndex_nil]
    apply Fin.ext
    exact t.simpleIndex_val ht ⟨k, hk⟩
  · exact Classical.choose_spec (show ∃ p : List (Fin t.rank) × Fin t.rank,
        t.geckWeylRootIndex ht p.1 p.2 = k by
      obtain ⟨l, i, hli⟩ := t.exists_geckWeylRootIndex_eq ht k
      exact ⟨(l, i), hli⟩)

/-- **The selected root-subgroup morphism at a root index.** Its Weyl-word presentation is fixed
by `geckRootSubgroupPresentation`; no presentation-independence claim is made. -/
def geckRootSubgroupAt (k : Fin t.numRoots) :
    AdditiveGroup.groupScheme ℤ ⟶ t.geckGroupScheme ht :=
  t.geckWeylRootSubgroup ht (t.geckRootSubgroupPresentation ht k).1
    (t.geckRootSubgroupPresentation ht k).2

/-- At a positive simple-root index, the root-indexed family recovers the pinned root-subgroup
morphism. -/
@[simp]
theorem geckRootSubgroupAt_simpleIndex (i : Fin t.rank) :
    t.geckRootSubgroupAt ht (t.simpleIndex ht i) =
      t.geckRootSubgroup ht (.inl i) := by
  rw [geckRootSubgroupAt, geckRootSubgroupPresentation_simpleIndex,
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
  let c := (t.geckRootSubgroup ht (.inl i)).hom.hom.left
  let e : (t.geckGroupScheme ht).X.left ≅ (t.geckGroupScheme ht).X.left :=
    (Over.forget _).mapIso ((Grp.forget _).mapIso (t.geckWeylWordInnerConjugation ht l))
  have hc : IsClosedImmersion c := inferInstance
  have hce : IsClosedImmersion (c ≫ e.hom) :=
    (MorphismProperty.cancel_right_of_respectsIso _ c e.hom).2 hc
  rw [geckWeylRootSubgroup_hom_left,
    ← geckWeylWordInnerConjugation_forget_mapIso_hom]
  exact hce

/-- Every root-indexed subgroup morphism is a closed immersion. -/
instance isClosedImmersion_geckRootSubgroupAt (k : Fin t.numRoots) :
    IsClosedImmersion (t.geckRootSubgroupAt ht k).hom.hom.left := by
  rw [geckRootSubgroupAt]
  infer_instance

end

end TauCeti.DynkinType
