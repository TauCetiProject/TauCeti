/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.ClosedGenerators
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PointsFunctor
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.InnerConjugation

/-!
# Positive nonsimple long-root subgroups of the short-root G₂ carrier

Conjugating the positive simple long-root subgroup by explicit rank-one words gives closed
additive subgroups at `3α₁ + α₂` and `3α₁ + 2α₂`. Their matrices are respectively
`1 + t(E₀₄ - E₂₆)` and `1 - t(E₀₅ + E₁₆)` in the ordered seven-dimensional weight basis.
The formulas hold over every commutative `𝔽₃`-algebra, not just over the prime field.

The coordinate maps, closed immersions and matrix-valued point homomorphisms describe the
same subgroups. The torus-conjugation equations identify their integral characters and the
parameter is injective even over nonreduced value algebras. These results concern the explicit
carrier, not an identification with an independently pinned simply connected group scheme.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 5.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.

The coordinate construction follows the Weyl-transported root subgroups in
`TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Root.Subgroup`.
-/

public section

open AlgebraicGeometry CategoryTheory
open scoped Matrix

namespace TauCeti.G2ShortRoot.PrimeField

universe v w

noncomputable section

/-- The conjugating root word for the first (index zero) or second (index one) nonsimple
positive long root. The rank-one words are `xⱼ(1) x₋ⱼ(-1) xⱼ(1)`. -/
def positiveLongRootConjugator (i : Fin 2) (A : Type v) [CommRing A] [Algebra (ZMod 3) A] :
    points A :=
  let n := fun j : Fin 2 =>
    rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd 1) *
      rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd 1)
  if i = 0 then n 0 else n 1 * n 0

/-- The conjugator consists of the displayed rank-one root words, in multiplication order. -/
theorem positiveLongRootConjugator_def (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] :
    positiveLongRootConjugator i A =
      let n := fun j : Fin 2 =>
        rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd 1) *
          rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd (-1)) *
            rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd 1)
      if i = 0 then n 0 else n 1 * n 0 :=
  (rfl)

/-- Coefficient change preserves the specified conjugating word. -/
@[simp↓]
theorem pointsMap_positiveLongRootConjugator {A : Type v} {B : Type w}
    [CommRing A] [CommRing B] [Algebra (ZMod 3) A] [Algebra (ZMod 3) B]
    (f : A →ₐ[ZMod 3] B) (i : Fin 2) :
    pointsMap f (positiveLongRootConjugator i A) = positiveLongRootConjugator i B := by
  fin_cases i <;> simp [positiveLongRootConjugator]

/-- The positive long-root homomorphism at `3α₁ + α₂` (index zero) or `3α₁ + 2α₂`
(index one), normalized by the displayed conjugating word. -/
def positiveLongRootSubgroupPoints (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] : Multiplicative A →* points A :=
  (MulAut.conj (positiveLongRootConjugator i A)).toMonoidHom.comp
    (rootSubgroupPoints (.inl 1) A)

/-- The long-root homomorphism is the specified conjugate of the simple long-root map. -/
theorem positiveLongRootSubgroupPoints_apply (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] (u : Multiplicative A) :
    positiveLongRootSubgroupPoints i A u =
      positiveLongRootConjugator i A * rootSubgroupPoints (.inl 1) A u *
        (positiveLongRootConjugator i A)⁻¹ :=
  (rfl)

private theorem conjugate_raisingMatrix (i : Fin 2) :
    let g := (positiveLongRootConjugator i (ZMod 3) : Matrix.GeneralLinearGroup (Fin 7) (ZMod 3))
    (g : Matrix (Fin 7) (Fin 7) (ZMod 3)) * (raisingMatrix 1).map (Int.cast : ℤ → ZMod 3) *
        (g⁻¹ : Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) =
      if i = 0 then Matrix.single 0 4 1 - Matrix.single 2 6 1
      else -(Matrix.single 0 5 1 + Matrix.single 1 6 1) := by
  dsimp only
  rw [← Subgroup.coe_inv]
  unfold positiveLongRootConjugator
  split_ifs <;>
    simp only [mul_inv_rev, ← map_inv (rootSubgroupPoints _ (ZMod 3)),
      ← ofAdd_neg, neg_neg] <;>
    simp only [Subgroup.coe_mul, Units.val_mul, coe_rootSubgroupPoints,
      IntegralToralClosure.coe_rootSubgroupPoints, toAdd_ofAdd, rootMatrix_inl,
      rootMatrix_inr, rootDividedSquareMatrix_inl, rootDividedSquareMatrix_inr] <;>
    decide +kernel

private theorem conjugate_raisingMatrix_algebra (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] :
    let g := (positiveLongRootConjugator i A : Matrix.GeneralLinearGroup (Fin 7) A)
    (g : Matrix (Fin 7) (Fin 7) A) * (raisingMatrix 1).map (Int.cast : ℤ → A) *
        (g⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A) =
      if i = 0 then Matrix.single 0 4 1 - Matrix.single 2 6 1
      else -(Matrix.single 0 5 1 + Matrix.single 1 6 1) := by
  let f : ZMod 3 →ₐ[ZMod 3] A := Algebra.ofId (ZMod 3) A
  have hg := congrArg Subtype.val (pointsMap_positiveLongRootConjugator f i)
  rw [coe_pointsMap] at hg
  have h := congrArg (fun X : Matrix (Fin 7) (Fin 7) (ZMod 3) => X.map f)
    (conjugate_raisingMatrix i)
  dsimp only at h ⊢
  simp only [Matrix.map_mul, Matrix.map_map, Function.comp_def, map_intCast] at h
  rw [← hg, ← map_inv]
  fin_cases i <;>
    simpa [Matrix.GeneralLinearGroup.map, Matrix.map_sub _ (map_sub f),
      Matrix.map_add _ (map_add f), Matrix.map_neg _ (map_neg f)] using h

/-- The two normalized long-root matrices are linear in their parameters. -/
@[simp]
theorem coe_positiveLongRootSubgroupPoints (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] (t : A) :
    ((positiveLongRootSubgroupPoints i A (Multiplicative.ofAdd t) :
        Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
      if i = 0 then 1 + t • (Matrix.single 0 4 1 - Matrix.single 2 6 1)
      else 1 - t • (Matrix.single 0 5 1 + Matrix.single 1 6 1) := by
  have hconj := conjugate_raisingMatrix_algebra i A
  rw [positiveLongRootSubgroupPoints_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, coe_rootSubgroupPoints,
    IntegralToralClosure.coe_rootSubgroupPoints, toAdd_ofAdd, rootMatrix_inl]
  simp only [rootDividedSquareMatrix_inl, Fin.isValue, Matrix.cons_val_one,
    Matrix.cons_val_zero, Matrix.map_zero _ Int.cast_zero, smul_zero, add_zero]
  rw [mul_add, add_mul, mul_one, Matrix.mul_smul, Matrix.smul_mul, Units.mul_inv,
    hconj]
  split_ifs <;> simp only [smul_neg, sub_eq_add_neg]

/-- The positive long-root parameter is injective over every coefficient algebra. -/
theorem positiveLongRootSubgroupPoints_injective (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] : Function.Injective (positiveLongRootSubgroupPoints i A) := by
  intro u v h
  have hm := congrArg (fun g : points A =>
    ((g : Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A)) h
  rw [← ofAdd_toAdd u, ← ofAdd_toAdd v, coe_positiveLongRootSubgroupPoints,
    coe_positiveLongRootSubgroupPoints] at hm
  apply Multiplicative.toAdd.injective
  fin_cases i
  · simpa [Matrix.single_apply] using congrFun (congrFun hm 0) 4
  · simpa [Matrix.single_apply] using congrFun (congrFun hm 0) 5

/-- Conjugation by the weight torus rescales each long-root parameter by its integral
character, `(3,-1)` or `(0,1)` in fundamental-weight coordinates. -/
theorem weightTorusPoints_conj_positiveLongRootSubgroupPoints (i : Fin 2)
    (A : Type v) [CommRing A] [Algebra (ZMod 3) A] (s : Fin 2 → Aˣ) (t : A) :
    weightTorusPoints A s * positiveLongRootSubgroupPoints i A (Multiplicative.ofAdd t) *
        (weightTorusPoints A s)⁻¹ =
      positiveLongRootSubgroupPoints i A (Multiplicative.ofAdd
        ((torusCharacter s (if i = 0 then ![3, -1] else ![0, 1]) : A) * t)) := by
  have hc (a b : Fin 7) (μ : Fin 2 → ℤ) (h : weight a = μ + weight b) :
      (torusCharacter s (weight a) : A) =
        (torusCharacter s μ : A) * (torusCharacter s (weight b) : A) := by
    rw [h, torusCharacter_add, Units.val_mul]
  have h04 := hc 0 4 ![3, -1] (by decide)
  have h26 := hc 2 6 ![3, -1] (by decide)
  have h05 := hc 0 5 ![0, 1] (by decide)
  have h16 := hc 1 6 ![0, 1] (by decide)
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_weightTorusPoints,
    IntegralToralClosure.coe_weightTorusPoints_eq_diagonal,
    coe_positiveLongRootSubgroupPoints]
  fin_cases i
  · ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal, h04, h26,
        mul_assoc, mul_comm, mul_left_comm]
  · ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal, h05, h16,
        mul_assoc, mul_comm, mul_left_comm]

/-- Coefficient change carries the root parameter along the algebra homomorphism. -/
@[simp↓]
theorem pointsMap_positiveLongRootSubgroupPoints {A : Type v} {B : Type w}
    [CommRing A] [CommRing B] [Algebra (ZMod 3) A] [Algebra (ZMod 3) B]
    (f : A →ₐ[ZMod 3] B) (i : Fin 2) (u : Multiplicative A) :
    pointsMap f (positiveLongRootSubgroupPoints i A u) =
      positiveLongRootSubgroupPoints i B (Multiplicative.ofAdd (f u.toAdd)) := by
  simp only [positiveLongRootSubgroupPoints_apply, map_mul, map_inv,
    pointsMap_positiveLongRootConjugator, pointsMap_rootSubgroupPoints]

/-- The coordinate pullback of the positive long-root subgroup, formed by inner conjugation
followed by the positive simple long-root coordinate map. -/
def positiveLongRootSubgroupCoordinateMap (i : Fin 2) :
    carrierAlgebra ⟶ AdditiveGroup.coordinateHopfAlgebra (ZMod 3) :=
  (CommHopfAlgCat.innerConjugationIso carrierAlgebra
    ((pointsMulEquiv (CommAlgCat.of (ZMod 3) (ZMod 3))).symm
      (positiveLongRootConjugator i (ZMod 3)))).hom ≫
    CommHopfAlgCat.commonKernelLift generator (.inl (.inl 1))

/-- The coordinate pullback is inner conjugation followed by the simple long-root pullback. -/
theorem positiveLongRootSubgroupCoordinateMap_def (i : Fin 2) :
    positiveLongRootSubgroupCoordinateMap i =
      (CommHopfAlgCat.innerConjugationIso carrierAlgebra
        ((pointsMulEquiv (CommAlgCat.of (ZMod 3) (ZMod 3))).symm
          (positiveLongRootConjugator i (ZMod 3)))).hom ≫
        CommHopfAlgCat.commonKernelLift generator (.inl (.inl 1)) :=
  (rfl)

/-- Each coordinate map is surjective, so its spectrum is a closed additive subgroup. -/
theorem positiveLongRootSubgroupCoordinateMap_surjective (i : Fin 2) :
    Function.Surjective (positiveLongRootSubgroupCoordinateMap i).hom := by
  rw [positiveLongRootSubgroupCoordinateMap, CommHopfAlgCat.hom_comp]
  refine (CommHopfAlgCat.commonKernelLift_surjective_of_surjective generator (.inl (.inl 1))
    (generator_surjective _)).comp ?_
  rw [← CommHopfAlgCat.coe_ofIso]
  exact (_root_.CommHopfAlgCat.ofIso (CommHopfAlgCat.innerConjugationIso carrierAlgebra
    ((pointsMulEquiv (CommAlgCat.of (ZMod 3) (ZMod 3))).symm
      (positiveLongRootConjugator i (ZMod 3))))).surjective

/-- The coordinate pullback represents exactly the specified matrix-valued root map. -/
theorem pointsMulEquiv_positiveLongRootSubgroupCoordinateMap (i : Fin 2)
    (A : Type v) [CommRing A] [Algebra (ZMod 3) A]
    (q : HopfAlgebra.points (H := AdditiveGroup.coordinateHopfAlgebra (ZMod 3))
      (CommAlgCat.of (ZMod 3) A)) :
    pointsMulEquiv (CommAlgCat.of (ZMod 3) A)
        ((CommHopfAlgCat.Hom.mapPointsFunctor
          (positiveLongRootSubgroupCoordinateMap i)).app (CommAlgCat.of (ZMod 3) A) q) =
      positiveLongRootSubgroupPoints i A (AdditiveGroup.gaPointsMulEquiv q) := by
  rw [positiveLongRootSubgroupCoordinateMap,
    CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply,
    CommHopfAlgCat.mapPointsFunctor_innerConjugationIso_hom]
  -- The functor composite and the native point group use definitionally equal group instances.
  erw [HopfAlgebra.innerConjugationPointNatIso_hom_app_apply, map_mul, map_mul, map_inv]
  erw [pointsMulEquiv_extendPoint, MulEquiv.apply_symm_apply,
    pointsMap_positiveLongRootConjugator, pointsMulEquiv_commonKernelLift_root]
  exact (positiveLongRootSubgroupPoints_apply i A _).symm

/-- The positive long-root subgroup as a morphism of group schemes over `𝔽₃`. -/
def positiveLongRootSubgroup (i : Fin 2) :
    AdditiveGroup.groupScheme (ZMod 3) ⟶ groupScheme :=
  eqToHom (AdditiveGroup.groupScheme_def (ZMod 3)) ≫
    (hopfSpec (CommRingCat.of (ZMod 3))).map (positiveLongRootSubgroupCoordinateMap i).op ≫
      eqToHom groupScheme_eq_commonKernelSpec.symm

/-- The group-scheme map is the contravariant spectrum of the root-coordinate map. -/
theorem positiveLongRootSubgroup_def (i : Fin 2) :
    positiveLongRootSubgroup i =
      eqToHom (AdditiveGroup.groupScheme_def (ZMod 3)) ≫
        (hopfSpec (CommRingCat.of (ZMod 3))).map (positiveLongRootSubgroupCoordinateMap i).op ≫
          eqToHom groupScheme_eq_commonKernelSpec.symm :=
  (rfl)

/-- Both nonsimple positive long-root maps are closed immersions. -/
instance isClosedImmersion_positiveLongRootSubgroup (i : Fin 2) :
    IsClosedImmersion (positiveLongRootSubgroup i).hom.hom.left := by
  rw [positiveLongRootSubgroup]
  exact (CommHopfAlgCat.isClosedImmersion_eqToHom_comp_hopfSpec_map_comp_eqToHom_iff
    (AdditiveGroup.groupScheme_def (ZMod 3)) groupScheme_eq_commonKernelSpec
    (positiveLongRootSubgroupCoordinateMap i)).2
      (positiveLongRootSubgroupCoordinateMap_surjective i)

end

end TauCeti.G2ShortRoot.PrimeField
