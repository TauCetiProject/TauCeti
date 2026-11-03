/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PointsFunctor
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.ClosedGenerators
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.InnerConjugation

/-!
# Nonsimple positive short-root subgroups of the short-root G₂ carrier

The roots `α₁ + α₂` and `2α₁ + α₂` have closed additive subgroup maps in the carrier
generated over `𝔽₃`. They are conjugates of the positive short simple-root map by explicit
rank-one words. Their matrix formulas retain the quadratic divided-power term; these are
identities over arbitrary commutative `𝔽₃`-algebras, not just over the prime field.

The construction concerns the explicit seven-dimensional carrier. It does not identify that
carrier with an independently pinned simply connected group scheme. These constructions
transfer to that group only along such an identification, once one is proved.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 6.4.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.

The coordinate construction follows the Weyl-transported closed subgroups in
`TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Root.Subgroup`.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.G2ShortRoot.PrimeField.PositiveShort

universe v w

noncomputable section

private def rankOneWord (j : Fin 2) (A : Type v) [CommRing A] [Algebra (ZMod 3) A] :
    points A :=
  rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd 1) *
    rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd (-1)) *
      rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd 1)

private def conjugator (i : Fin 2) (A : Type v) [CommRing A] [Algebra (ZMod 3) A] :
    points A :=
  if i = 0 then rankOneWord 1 A else rankOneWord 0 A * rankOneWord 1 A

private theorem pointsMap_conjugator {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    [Algebra (ZMod 3) A] [Algebra (ZMod 3) B] (f : A →ₐ[ZMod 3] B) (i : Fin 2) :
    pointsMap f (conjugator i A) = conjugator i B := by
  unfold conjugator
  split_ifs <;> simp [rankOneWord, pointsMap_rootSubgroupPoints]

/-- The subgroup at `α₁ + α₂` (index zero) or `2α₁ + α₂` (index one), with normalization
specified by the displayed rank-one words. -/
def subgroupPoints (i : Fin 2) (A : Type v) [CommRing A] [Algebra (ZMod 3) A] :
    Multiplicative A →* points A :=
  (MulAut.conj (conjugator i A)).toMonoidHom.comp (rootSubgroupPoints (.inl 0) A)

/-- The point parametrization is conjugation of the positive short simple-root subgroup. -/
theorem subgroupPoints_apply (i : Fin 2) (A : Type v) [CommRing A] [Algebra (ZMod 3) A]
    (u : Multiplicative A) :
    let n := fun j : Fin 2 =>
      rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd (-1)) *
          rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd 1)
    subgroupPoints i A u =
      (if i = 0 then n 1 else n 0 * n 1) * rootSubgroupPoints (.inl 0) A u *
        (if i = 0 then n 1 else n 0 * n 1)⁻¹ :=
  (rfl)

/-- Coefficient change preserves the transported short-root points. -/
@[simp]
theorem pointsMap_subgroupPoints {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    [Algebra (ZMod 3) A] [Algebra (ZMod 3) B] (f : A →ₐ[ZMod 3] B)
    (i : Fin 2) (u : Multiplicative A) :
    pointsMap f (subgroupPoints i A u) =
      subgroupPoints i B (Multiplicative.ofAdd (f u.toAdd)) := by
  simp only [subgroupPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, map_mul, map_inv, pointsMap_conjugator, pointsMap_rootSubgroupPoints]

local notation "Q" => CommHopfAlgCat.quotient
  (GeneralLinear.coordinateHopfAlgebra (ZMod 3) 7)
  (CommHopfAlgCat.commonKernelHopfIdeal generator)

/-- Pullback of a nonsimple positive short-root subgroup: inner conjugation followed by the
numbered short-root coordinate map. -/
def subgroupCoordinateMap (i : Fin 2) : Q ⟶ AdditiveGroup.coordinateHopfAlgebra (ZMod 3) :=
  (CommHopfAlgCat.innerConjugationIso Q
    ((pointsMulEquiv (CommAlgCat.of (ZMod 3) (ZMod 3))).symm
      (conjugator i (ZMod 3)))).hom ≫
        CommHopfAlgCat.commonKernelLift generator (.inl (.inl 0))

/-- The coordinate pullback induces the stated conjugation homomorphism on every value
algebra, under the existing additive-group and carrier point equivalences. -/
theorem pointsMulEquiv_subgroupCoordinateMap (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A]
    (q : HopfAlgebra.points (H := AdditiveGroup.coordinateHopfAlgebra (ZMod 3))
      (CommAlgCat.of (ZMod 3) A)) :
    pointsMulEquiv (CommAlgCat.of (ZMod 3) A)
      ((CommHopfAlgCat.Hom.mapPointsFunctor (subgroupCoordinateMap i)).app
        (CommAlgCat.of (ZMod 3) A) q) =
      subgroupPoints i A (AdditiveGroup.gaPointsMulEquiv q) := by
  rw [subgroupCoordinateMap, CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply,
    CommHopfAlgCat.mapPointsFunctor_innerConjugationIso_hom]
  -- The point-functor presentation carries the same group law, but its instances differ.
  erw [HopfAlgebra.innerConjugationPointNatIso_hom_app_apply, map_mul, map_mul, map_inv]
  apply Subtype.ext
  simp only [subgroupPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  have hconstant :
      (pointsMulEquiv (CommAlgCat.of (ZMod 3) A)
        (HopfAlgebra.extendPoint Q (CommAlgCat.of (ZMod 3) A)
          ((pointsMulEquiv (CommAlgCat.of (ZMod 3) (ZMod 3))).symm
            (conjugator i (ZMod 3))))).val = (conjugator i A).val := by
    conv_rhs => rw [← pointsMap_conjugator (Algebra.ofId (ZMod 3) A) i,
      coe_pointsMap, ← (pointsMulEquiv (CommAlgCat.of (ZMod 3) (ZMod 3))).apply_symm_apply
        (conjugator i (ZMod 3))]
    rw [HopfAlgebra.extendPoint_apply, coe_pointsMulEquiv_apply, coe_pointsMulEquiv_apply]
    erw [CommHopfAlgCat.quotientPointsHom_apply, CommHopfAlgCat.quotientPointsHom_apply]
    rw [← GeneralLinear.pointsMulEquiv_mapValue]
    simp only [AlgHom.mapValue_apply, AlgHom.comp_assoc]
  erw [hconstant, pointsMulEquiv_commonKernelLift_root]

/-- Each coordinate parametrization is surjective. -/
theorem subgroupCoordinateMap_surjective (i : Fin 2) :
    Function.Surjective (subgroupCoordinateMap i).hom := by
  rw [subgroupCoordinateMap, CommHopfAlgCat.hom_comp]
  exact (CommHopfAlgCat.commonKernelLift_surjective_of_surjective generator (.inl (.inl 0))
    (generator_surjective _)).comp (by
      rw [← CommHopfAlgCat.coe_ofIso]
      exact (CommHopfAlgCat.ofIso (CommHopfAlgCat.innerConjugationIso Q
        ((pointsMulEquiv (CommAlgCat.of (ZMod 3) (ZMod 3))).symm
          (conjugator i (ZMod 3))))).surjective)

/-- The closed additive subgroup at either nonsimple positive short root. -/
def subgroup (i : Fin 2) : AdditiveGroup.groupScheme (ZMod 3) ⟶ groupScheme :=
  eqToHom (AdditiveGroup.groupScheme_def (ZMod 3)) ≫
    (hopfSpec (CommRingCat.of (ZMod 3))).map (subgroupCoordinateMap i).op ≫
      eqToHom (by rw [groupScheme_def, definingIdeal_def])

/-- The subgroup morphism is the spectrum of the specified coordinate pullback. -/
theorem subgroup_def (i : Fin 2) :
    subgroup i = eqToHom (AdditiveGroup.groupScheme_def (ZMod 3)) ≫
      (hopfSpec (CommRingCat.of (ZMod 3))).map (subgroupCoordinateMap i).op ≫
        eqToHom (by rw [groupScheme_def, definingIdeal_def]) :=
  (rfl)

/-- Both parametrizations are closed immersions, including on nonreduced value algebras. -/
instance isClosedImmersion_subgroup (i : Fin 2) :
    IsClosedImmersion (subgroup i).hom.hom.left := by
  rw [subgroup_def]
  exact (CommHopfAlgCat.isClosedImmersion_eqToHom_comp_hopfSpec_map_comp_eqToHom_iff
    (AdditiveGroup.groupScheme_def (ZMod 3))
    (by rw [groupScheme_def, definingIdeal_def]) (subgroupCoordinateMap i)).2
      (subgroupCoordinateMap_surjective i)

/-- The linear coefficient of the two short-root polynomials, with the normalization fixed by
`subgroupPoints_apply`. -/
def linearMatrix (i : Fin 2) : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  if i = 0 then
    Matrix.single 0 2 (-1) + Matrix.single 1 3 2 + Matrix.single 3 5 (-1) +
      Matrix.single 4 6 1
  else
    Matrix.single 0 3 (-2) + Matrix.single 1 4 1 + Matrix.single 2 5 1 +
      Matrix.single 3 6 (-1)

/-- The quadratic divided-power coefficient of the two short-root polynomials. -/
def quadraticMatrix (i : Fin 2) : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  if i = 0 then Matrix.single 1 5 (-1) else Matrix.single 0 6 1

/-- The first linear coefficient has the four entries displayed by the root string. -/
@[simp] theorem linearMatrix_zero : linearMatrix 0 =
    Matrix.single 0 2 (-1) + Matrix.single 1 3 2 + Matrix.single 3 5 (-1) +
      Matrix.single 4 6 1 := by simp [linearMatrix]

/-- The second linear coefficient has the four entries displayed by the root string. -/
@[simp] theorem linearMatrix_one : linearMatrix 1 =
    Matrix.single 0 3 (-2) + Matrix.single 1 4 1 + Matrix.single 2 5 1 +
      Matrix.single 3 6 (-1) := by simp [linearMatrix]

/-- The first quadratic coefficient is minus the `(1,5)` matrix unit. -/
@[simp] theorem quadraticMatrix_zero : quadraticMatrix 0 = Matrix.single 1 5 (-1) := by
  simp [quadraticMatrix]

/-- The second quadratic coefficient is the `(0,6)` matrix unit. -/
@[simp] theorem quadraticMatrix_one : quadraticMatrix 1 = Matrix.single 0 6 1 := by
  simp [quadraticMatrix]

private theorem conjugator_coefficients (i : Fin 2) :
    let W := ((conjugator i (ZMod 3) : Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) :
      Matrix (Fin 7) (Fin 7) (ZMod 3))
    let V := (((conjugator i (ZMod 3))⁻¹).val :
      Matrix (Fin 7) (Fin 7) (ZMod 3))
    W * (rootMatrix (.inl 0)).map (Int.cast : ℤ → ZMod 3) * V = linearMatrix i ∧
      W * (rootDividedSquareMatrix (.inl 0)).map (Int.cast : ℤ → ZMod 3) * V =
        quadraticMatrix i := by
  dsimp only
  unfold conjugator
  split_ifs <;>
    simp only [rankOneWord, Subgroup.coe_mul, Units.val_mul,
      mul_inv_rev, ← map_inv (rootSubgroupPoints _ (ZMod 3)), ← ofAdd_neg, neg_neg,
      coe_rootSubgroupPoints, IntegralToralClosure.coe_rootSubgroupPoints, toAdd_ofAdd]
  all_goals simp_all only [linearMatrix, quadraticMatrix, rootMatrix_inl,
    rootDividedSquareMatrix_inl, rootMatrix_inr, rootDividedSquareMatrix_inr]
  all_goals decide +kernel

/-- The full matrix formula for either short-root subgroup. The quadratic term is essential
in characteristic three and remains present over polynomial and nonreduced algebras. -/
theorem coe_subgroupPoints (i : Fin 2) (A : Type v) [CommRing A] [Algebra (ZMod 3) A]
    (t : A) :
    ((subgroupPoints i A (Multiplicative.ofAdd t) : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) =
        1 + t • (linearMatrix i).map (algebraMap (ZMod 3) A) +
          t ^ 2 • (quadraticMatrix i).map (algebraMap (ZMod 3) A) := by
  let f : ZMod 3 →ₐ[ZMod 3] A := Algebra.ofId (ZMod 3) A
  let W := ((conjugator i (ZMod 3) : Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) :
    Matrix (Fin 7) (Fin 7) (ZMod 3))
  let V := (((conjugator i (ZMod 3))⁻¹).val :
    Matrix (Fin 7) (Fin 7) (ZMod 3))
  have hW : ((conjugator i A : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) = W.map f := by
    rw [← pointsMap_conjugator f i, coe_pointsMap]
    -- The general-linear coefficient map acts entrywise on the underlying matrix.
    rfl
  have hV : (((conjugator i A)⁻¹).val :
      Matrix (Fin 7) (Fin 7) A) = V.map f := by
    rw [← pointsMap_conjugator f i, ← map_inv, coe_pointsMap]
    -- The same entrywise coefficient map is now applied to the inverse point.
    rfl
  have hWV : W * V = 1 := by
    exact congrArg (fun g : points (ZMod 3) => (g.val : Matrix (Fin 7) (Fin 7) (ZMod 3)))
      (mul_inv_cancel (conjugator i (ZMod 3)))
  have hlin := congrArg (fun M : Matrix (Fin 7) (Fin 7) (ZMod 3) => M.map f)
    (conjugator_coefficients i).1
  have hquad := congrArg (fun M : Matrix (Fin 7) (Fin 7) (ZMod 3) => M.map f)
    (conjugator_coefficients i).2
  have hcast (M : Matrix (Fin 7) (Fin 7) ℤ) :
      (M.map (Int.cast : ℤ → ZMod 3)).map f = M.map (Int.cast : ℤ → A) := by
    ext a b
    exact map_intCast f _
  simp only [Matrix.map_mul, hcast] at hlin hquad
  dsimp only [W, V] at hW hV hWV
  -- The bundled inner automorphism is matrix conjugation by W, with inverse matrix V.
  simp only [subgroupPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, Subgroup.coe_mul, Units.val_mul]
  rw [hW, hV, coe_rootSubgroupPoints, IntegralToralClosure.coe_rootSubgroupPoints]
  simp only [toAdd_ofAdd, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one]
  rw [hlin, hquad, ← Matrix.map_mul, hWV, Matrix.map_one _ (map_zero f) (map_one f)]
  -- The coefficient map f is the canonical algebra map.
  rfl

/-- Both short-root homomorphisms are injective over every coefficient algebra. -/
theorem subgroupPoints_injective (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] : Function.Injective (subgroupPoints i A) := by
  intro u v h
  apply (AdditiveGroup.gaPointsMulEquiv (R := ZMod 3) (A := A)).symm.injective
  apply CommHopfAlgCat.Hom.mapPointsFunctor_app_injective_of_surjective
    (subgroupCoordinateMap i) (subgroupCoordinateMap_surjective i) (CommAlgCat.of (ZMod 3) A)
  apply (pointsMulEquiv (CommAlgCat.of (ZMod 3) A)).injective
  rw [pointsMulEquiv_subgroupCoordinateMap, pointsMulEquiv_subgroupCoordinateMap,
    MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  exact h

private theorem coefficient_weight (i d : Fin 2) (a b : Fin 7) :
    let M := if d = 0 then linearMatrix i else quadraticMatrix i
    M a b ≠ 0 → ∀ j : Fin 2, weight a j = (weight b +
      (d.val + 1) • (if i = 0 then ![-1, 1] else ![1, 0] : Fin 2 → ℤ)) j := by
  dsimp only
  fin_cases i <;> fin_cases d <;> fin_cases a <;> fin_cases b <;>
    norm_num [linearMatrix, quadraticMatrix, Matrix.single_apply]

private theorem torus_mul_coefficient (i d : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] (s : Fin 2 → Aˣ) :
    let M := if d = 0 then linearMatrix i else quadraticMatrix i
    let D := Matrix.diagonal fun a : Fin 7 => (torusCharacter s (weight a) : A)
    D * M.map (algebraMap (ZMod 3) A) =
      (torusCharacter s (if i = 0 then ![-1, 1] else ![1, 0]) : A) ^ (d.val + 1) •
        (M.map (algebraMap (ZMod 3) A) * D) := by
  dsimp only
  ext a b
  by_cases h : (if d = 0 then linearMatrix i else quadraticMatrix i) a b = 0
  · simp [Matrix.diagonal_mul, Matrix.mul_diagonal, h]
  · rw [Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_mul, Matrix.mul_diagonal,
      funext (coefficient_weight i d a b h), torusCharacter_add, torusCharacter_nsmul,
      Units.val_mul, Units.val_pow_eq_pow_val]
    ac_rfl

/-- The torus acts through the integral characters `α₁ + α₂ = (-1,1)` and
`2α₁ + α₂ = (1,0)`, respectively. -/
theorem weightTorusPoints_conj_subgroupPoints (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] (s : Fin 2 → Aˣ) (t : A) :
    weightTorusPoints A s * subgroupPoints i A (Multiplicative.ofAdd t) *
        (weightTorusPoints A s)⁻¹ =
      subgroupPoints i A (Multiplicative.ofAdd
        ((torusCharacter s (if i = 0 then ![-1, 1] else ![1, 0]) : A) * t)) := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_weightTorusPoints,
    IntegralToralClosure.coe_weightTorusPoints_eq_diagonal, coe_subgroupPoints,
    mul_add, add_mul, mul_one, one_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hlinear := torus_mul_coefficient i 0 A s
  have hquadratic := torus_mul_coefficient i 1 A s
  simp only [Fin.val_zero, Fin.val_one, zero_add, pow_one, Fin.isValue, ↓reduceIte,
    Fin.reduceEq, Nat.reduceAdd] at hlinear hquadratic
  rw [hlinear, hquadratic, smul_smul, smul_smul, mul_pow, mul_comm t, mul_comm (t ^ 2)]

end

end TauCeti.G2ShortRoot.PrimeField.PositiveShort
