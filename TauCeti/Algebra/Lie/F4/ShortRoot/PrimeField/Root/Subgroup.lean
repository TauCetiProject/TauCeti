/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Weyl
public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.ClosedGenerators
public import TauCeti.Algebra.Lie.F4.ShortRoot.Weyl.RootSubgroup
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.InnerConjugation

/-!
# Closed root subgroups of the short-root F₄ carrier over 𝔽₂

Conjugating the numbered positive simple-root subgroups by pinned Weyl words gives closed
copies of the additive group at all forty-eight roots. The construction takes place in the
carrier generated over 𝔽₂, not in the possibly larger reduction of the integral carrier.
Its matrices agree with the integral Weyl-transported formulas over every commutative
𝔽₂-algebra, including nonreduced algebras. The torus acts through the integral root character.

The coordinate maps are surjective: they are composites of a coordinate automorphism for
inner conjugation with a surjective numbered root map. Thus these are actual closed
subgroup-scheme morphisms, not just homomorphisms on field-valued points.

The root-indexed family uses `F4ShortRoot.rootSubgroupPresentation`, hence recovers the pinned
positive simple-root maps. No independence of the chosen Weyl presentation, equality with a
full adjoint root space, or identification with the pinned simply connected group is asserted.

## Main declarations

* `rootSubgroupAt` and `isClosedImmersion_rootSubgroupAt`: closed additive subgroup schemes.
* `rootSubgroupCoordinateMapAt` and `coordinatePointsEquiv_rootSubgroupCoordinateMapAt`:
  their coordinate maps and matrix-valued points.
* `weightTorusPoints_conj_rootSubgroupPointsAt`: the root character at every index.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
* J. E. Humphreys, *Linear Algebraic Groups*, §26.3.

The point formulas follow `TauCeti.Algebra.Lie.F4.ShortRoot.Weyl.RootSubgroup`.
Their representability uses `HopfAlgebra.pointConjugationBialgEquiv`.
-/

public section

open AlgebraicGeometry CategoryTheory WithConv

namespace TauCeti.F4ShortRoot.PrimeField

open DynkinType

universe v w

noncomputable section

local notation "H₂₆" => GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26
local notation "J" => CommHopfAlgCat.commonKernelHopfIdeal generator
local notation "Q" => CommHopfAlgCat.quotient H₂₆ J

/-- The root homomorphism obtained by transporting a numbered positive root along a Weyl word. -/
def weylRootSubgroupPoints (l : List (Fin 4)) (i : Fin 4) (A : Type v) [CommRing A]
    [Algebra (ZMod 2) A] : Multiplicative A →* points A :=
  (MulAut.conj (weylWordPoint l A)).toMonoidHom.comp (rootSubgroupPoints (.inl i) A)

/-- A transported root point is the specified conjugate of a numbered root point. -/
@[simp]
theorem weylRootSubgroupPoints_apply (l : List (Fin 4)) (i : Fin 4) (A : Type v)
    [CommRing A] [Algebra (ZMod 2) A] (u : Multiplicative A) :
    weylRootSubgroupPoints l i A u =
      weylWordPoint l A * rootSubgroupPoints (.inl i) A u * (weylWordPoint l A)⁻¹ :=
  (rfl)

/-- The empty word gives the pinned positive simple-root homomorphism. -/
@[simp]
theorem weylRootSubgroupPoints_nil (i : Fin 4) (A : Type v) [CommRing A]
    [Algebra (ZMod 2) A] :
    weylRootSubgroupPoints [] i A = rootSubgroupPoints (.inl i) A := by
  ext u
  simp

/-- Prepending a node conjugates by its simple Weyl representative. -/
theorem weylRootSubgroupPoints_cons (j : Fin 4) (l : List (Fin 4)) (i : Fin 4)
    (A : Type v) [CommRing A] [Algebra (ZMod 2) A] (u : Multiplicative A) :
    weylRootSubgroupPoints (j :: l) i A u =
      simpleWeylPoint j A * weylRootSubgroupPoints l i A u * (simpleWeylPoint j A)⁻¹ := by
  simp only [weylRootSubgroupPoints_apply, weylWordPoint_cons]
  group

/-- The transported point has the same matrix as its integral counterpart. -/
-- Preserve the integral root homomorphism before the pointwise conjugation formula expands.
@[simp↓]
theorem coe_weylRootSubgroupPoints (l : List (Fin 4)) (i : Fin 4) (A : Type v)
    [CommRing A] [Algebra (ZMod 2) A] (u : Multiplicative A) :
    (weylRootSubgroupPoints l i A u : Matrix.GeneralLinearGroup (Fin 26) A) =
      (F4ShortRoot.weylRootSubgroupPoints l i A u :
        Matrix.GeneralLinearGroup (Fin 26) A) := by
  simp

/-- Transported root homomorphisms are natural over all coefficient algebras. -/
@[simp↓]
theorem pointsMap_weylRootSubgroupPoints {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    [Algebra (ZMod 2) A] [Algebra (ZMod 2) B] (f : A →ₐ[ZMod 2] B)
    (l : List (Fin 4)) (i : Fin 4) (u : Multiplicative A) :
    pointsMap f (weylRootSubgroupPoints l i A u) =
      weylRootSubgroupPoints l i B (Multiplicative.ofAdd (f u.toAdd)) := by
  simp

/-- The torus character of a transported root subgroup is the corresponding reflected root. -/
theorem weightTorusPoints_conj_weylRootSubgroupPoints (l : List (Fin 4)) (i : Fin 4)
    (A : Type v) [CommRing A] [Algebra (ZMod 2) A] (s : Fin 4 → Aˣ)
    (u : Multiplicative A) :
    weightTorusPoints A s * weylRootSubgroupPoints l i A u * (weightTorusPoints A s)⁻¹ =
      weylRootSubgroupPoints l i A (Multiplicative.ofAdd
        ((TauCeti.torusCharacter s ((F4.simplyConnectedRootDatum valid_F4).root
          (F4.geckWeylRootIndex valid_F4 l i)) : A) * u.toAdd)) := by
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_weightTorusPoints,
    coe_weylRootSubgroupPoints] using congrArg Subtype.val
      (F4ShortRoot.weightTorusPoints_conj_weylRootSubgroupPoints l i A s u)

/-- Pullback of the Weyl-transported root subgroup, obtained by inner conjugation in the
prime-field carrier followed by its numbered root-coordinate map. -/
def weylRootSubgroupCoordinateMap (l : List (Fin 4)) (i : Fin 4) :
    Q ⟶ AdditiveGroup.coordinateHopfAlgebra (ZMod 2) :=
  (CommHopfAlgCat.innerConjugationIso Q
    ((coordinatePointsEquiv (ZMod 2)).symm (weylWordPoint l (ZMod 2)))).hom ≫
      CommHopfAlgCat.commonKernelLift generator (.inl (.inl i))

/-- The empty Weyl word recovers the numbered positive simple-root coordinate map. -/
@[simp]
theorem weylRootSubgroupCoordinateMap_nil (i : Fin 4) :
    weylRootSubgroupCoordinateMap [] i =
      CommHopfAlgCat.commonKernelLift generator (.inl (.inl i)) := by
  simp [weylRootSubgroupCoordinateMap]

/-- The transported coordinate map is surjective, so it parametrizes a closed copy of `𝔾ₐ`. -/
theorem weylRootSubgroupCoordinateMap_surjective (l : List (Fin 4)) (i : Fin 4) :
    Function.Surjective (weylRootSubgroupCoordinateMap l i).hom := by
  rw [weylRootSubgroupCoordinateMap, CommHopfAlgCat.hom_comp]
  exact (CommHopfAlgCat.commonKernelLift_surjective_of_surjective generator (.inl (.inl i))
    (generator_surjective _)).comp
      (by
        rw [← CommHopfAlgCat.coe_ofIso]
        exact (_root_.CommHopfAlgCat.ofIso
          (CommHopfAlgCat.innerConjugationIso Q
            ((coordinatePointsEquiv (ZMod 2)).symm
              (weylWordPoint l (ZMod 2))))).surjective)

/-- The coordinate map represents exactly the displayed Weyl conjugation on every value algebra. -/
theorem coordinatePointsEquiv_weylRootSubgroupCoordinateMap (l : List (Fin 4)) (i : Fin 4)
    (A : Type v) [CommRing A] [Algebra (ZMod 2) A]
    (q : HopfAlgebra.points (H := AdditiveGroup.coordinateHopfAlgebra (ZMod 2))
      (CommAlgCat.of (ZMod 2) A)) :
    coordinatePointsEquiv A ((CommHopfAlgCat.Hom.mapPointsFunctor
      (weylRootSubgroupCoordinateMap l i)).app (CommAlgCat.of (ZMod 2) A) q) =
        weylRootSubgroupPoints l i A (AdditiveGroup.gaPointsMulEquiv q) := by
  rw [weylRootSubgroupCoordinateMap, CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply,
    CommHopfAlgCat.mapPointsFunctor_innerConjugationIso_hom]
  -- Composition changes the presentation of the point functor's group instances.
  erw [HopfAlgebra.innerConjugationPointNatIso_hom_app_apply, map_mul, map_mul, map_inv]
  erw [HopfAlgebra.extendPoint_apply, coordinatePointsEquiv_mapPoints,
    MulEquiv.apply_symm_apply, pointsMap_weylWordPoint]
  apply Subtype.ext
  simp only [weylRootSubgroupPoints_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  erw [coe_coordinatePointsEquiv_commonKernelLift,
    coe_rootSubgroupPoints_gaPointsMulEquiv]

/-- A closed root subgroup at each of the forty-eight named roots. The chosen Weyl presentation
is shared with the integral carrier and is empty at positive simple roots. -/
def rootSubgroupCoordinateMapAt (k : Fin F4.numRoots) :
    Q ⟶ AdditiveGroup.coordinateHopfAlgebra (ZMod 2) :=
  weylRootSubgroupCoordinateMap (F4ShortRoot.rootSubgroupPresentation k).1
    (F4ShortRoot.rootSubgroupPresentation k).2

/-- The selected coordinate map uses the chosen integral Weyl presentation. -/
theorem rootSubgroupCoordinateMapAt_def (k : Fin F4.numRoots) :
    rootSubgroupCoordinateMapAt k =
      weylRootSubgroupCoordinateMap (F4ShortRoot.rootSubgroupPresentation k).1
        (F4ShortRoot.rootSubgroupPresentation k).2 :=
  (rfl)

/-- At a positive simple root the selected coordinate map is the pinned generator. -/
@[simp]
theorem rootSubgroupCoordinateMapAt_simpleIndex (i : Fin 4) :
    rootSubgroupCoordinateMapAt (Fin.castAdd 44 i) =
      CommHopfAlgCat.commonKernelLift generator (.inl (.inl i)) := by
  simp [rootSubgroupCoordinateMapAt]

/-- Each root-indexed coordinate map is surjective. -/
theorem rootSubgroupCoordinateMapAt_surjective (k : Fin F4.numRoots) :
    Function.Surjective (rootSubgroupCoordinateMapAt k).hom :=
  weylRootSubgroupCoordinateMap_surjective _ _

/-- The selected closed root subgroup, as a group-scheme morphism into the prime-field carrier. -/
def rootSubgroupAt (k : Fin F4.numRoots) :
    AdditiveGroup.groupScheme (ZMod 2) ⟶ groupScheme :=
  eqToHom (AdditiveGroup.groupScheme_def (ZMod 2)) ≫
    (hopfSpec (CommRingCat.of (ZMod 2))).map (rootSubgroupCoordinateMapAt k).op ≫
      eqToHom (by rw [groupScheme_def, definingIdeal_def])

/-- The selected scheme morphism is the contravariant spectrum of its coordinate map,
with the standard presentations of source and target. -/
theorem rootSubgroupAt_def (k : Fin F4.numRoots) :
    rootSubgroupAt k =
      eqToHom (AdditiveGroup.groupScheme_def (ZMod 2)) ≫
        (hopfSpec (CommRingCat.of (ZMod 2))).map (rootSubgroupCoordinateMapAt k).op ≫
          eqToHom (by rw [groupScheme_def, definingIdeal_def]) :=
  (rfl)

/-- The selected scheme morphism at a positive simple root is the original pinned root map. -/
@[simp]
theorem rootSubgroupAt_simpleIndex (i : Fin 4) :
    rootSubgroupAt (Fin.castAdd 44 i) = rootSubgroup (.inl i) := by
  rw [rootSubgroupAt_def (Fin.castAdd 44 i), rootSubgroupCoordinateMapAt_simpleIndex,
    rootSubgroup_def, GeneralLinear.generatorToGeneratedGroupScheme_def]

/-- Every selected root subgroup is a closed immersion, including in characteristic two. -/
instance isClosedImmersion_rootSubgroupAt (k : Fin F4.numRoots) :
    IsClosedImmersion (rootSubgroupAt k).hom.hom.left := by
  rw [rootSubgroupAt]
  exact (CommHopfAlgCat.isClosedImmersion_eqToHom_comp_hopfSpec_map_comp_eqToHom_iff
    (AdditiveGroup.groupScheme_def (ZMod 2))
    (by rw [groupScheme_def, definingIdeal_def]) (rootSubgroupCoordinateMapAt k)).2
      (rootSubgroupCoordinateMapAt_surjective k)

/-- The selected root homomorphism on matrix-valued points. -/
def rootSubgroupPointsAt (k : Fin F4.numRoots) (A : Type v) [CommRing A]
    [Algebra (ZMod 2) A] : Multiplicative A →* points A :=
  weylRootSubgroupPoints (F4ShortRoot.rootSubgroupPresentation k).1
    (F4ShortRoot.rootSubgroupPresentation k).2 A

/-- The selected point homomorphism uses the chosen integral Weyl presentation. -/
theorem rootSubgroupPointsAt_def (k : Fin F4.numRoots) (A : Type v) [CommRing A]
    [Algebra (ZMod 2) A] :
    rootSubgroupPointsAt k A =
      weylRootSubgroupPoints (F4ShortRoot.rootSubgroupPresentation k).1
        (F4ShortRoot.rootSubgroupPresentation k).2 A :=
  (rfl)

/-- The root-indexed coordinate map represents the selected matrix-valued homomorphism. -/
theorem coordinatePointsEquiv_rootSubgroupCoordinateMapAt (k : Fin F4.numRoots)
    (A : Type v) [CommRing A] [Algebra (ZMod 2) A]
    (q : HopfAlgebra.points (H := AdditiveGroup.coordinateHopfAlgebra (ZMod 2))
      (CommAlgCat.of (ZMod 2) A)) :
    coordinatePointsEquiv A ((CommHopfAlgCat.Hom.mapPointsFunctor
      (rootSubgroupCoordinateMapAt k)).app (CommAlgCat.of (ZMod 2) A) q) =
        rootSubgroupPointsAt k A (AdditiveGroup.gaPointsMulEquiv q) :=
  coordinatePointsEquiv_weylRootSubgroupCoordinateMap _ _ A q

/-- Each selected root homomorphism is injective on points over every coefficient algebra. -/
theorem rootSubgroupPointsAt_injective (k : Fin F4.numRoots) (A : Type v) [CommRing A]
    [Algebra (ZMod 2) A] : Function.Injective (rootSubgroupPointsAt k A) := by
  intro u v huv
  apply (AdditiveGroup.gaPointsMulEquiv (R := ZMod 2) (A := A)).symm.injective
  apply CommHopfAlgCat.Hom.mapPointsFunctor_app_injective_of_surjective
    (rootSubgroupCoordinateMapAt k) (rootSubgroupCoordinateMapAt_surjective k)
    (CommAlgCat.of (ZMod 2) A)
  apply (coordinatePointsEquiv A).injective
  rw [coordinatePointsEquiv_rootSubgroupCoordinateMapAt k A,
    coordinatePointsEquiv_rootSubgroupCoordinateMapAt k A,
    MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  exact huv

/-- The selected root family retains the pinned positive simple-root homomorphisms. -/
@[simp]
theorem rootSubgroupPointsAt_simpleIndex (i : Fin 4) (A : Type v) [CommRing A]
    [Algebra (ZMod 2) A] :
    rootSubgroupPointsAt (Fin.castAdd 44 i) A = rootSubgroupPoints (.inl i) A := by
  simp [rootSubgroupPointsAt]

/-- The selected root homomorphisms commute with every change of coefficient algebra. -/
@[simp↓]
theorem pointsMap_rootSubgroupPointsAt {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    [Algebra (ZMod 2) A] [Algebra (ZMod 2) B] (f : A →ₐ[ZMod 2] B)
    (k : Fin F4.numRoots) (u : Multiplicative A) :
    pointsMap f (rootSubgroupPointsAt k A u) =
      rootSubgroupPointsAt k B (Multiplicative.ofAdd (f u.toAdd)) := by
  exact pointsMap_weylRootSubgroupPoints f _ _ u

/-- The selected family has the integral root-subgroup matrices. -/
@[simp]
theorem coe_rootSubgroupPointsAt (k : Fin F4.numRoots) (A : Type v) [CommRing A]
    [Algebra (ZMod 2) A] (u : Multiplicative A) :
    (rootSubgroupPointsAt k A u : Matrix.GeneralLinearGroup (Fin 26) A) =
      (F4ShortRoot.rootSubgroupPointsAt k A u : Matrix.GeneralLinearGroup (Fin 26) A) := by
  rw [rootSubgroupPointsAt, F4ShortRoot.rootSubgroupPointsAt_def,
    coe_weylRootSubgroupPoints]

/-- The torus acts on every selected root subgroup through that root's integral character. -/
theorem weightTorusPoints_conj_rootSubgroupPointsAt (k : Fin F4.numRoots)
    (A : Type v) [CommRing A] [Algebra (ZMod 2) A] (s : Fin 4 → Aˣ) (u : Multiplicative A) :
    weightTorusPoints A s * rootSubgroupPointsAt k A u * (weightTorusPoints A s)⁻¹ =
      rootSubgroupPointsAt k A (Multiplicative.ofAdd
        ((TauCeti.torusCharacter s ((F4.simplyConnectedRootDatum valid_F4).root k) : A) *
          u.toAdd)) := by
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_weightTorusPoints,
    coe_rootSubgroupPointsAt] using congrArg Subtype.val
      (F4ShortRoot.weightTorusPoints_conj_rootSubgroupPointsAt k A s u)

end

end TauCeti.F4ShortRoot.PrimeField
