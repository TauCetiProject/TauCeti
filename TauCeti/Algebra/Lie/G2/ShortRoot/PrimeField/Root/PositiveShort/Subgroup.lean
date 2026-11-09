/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PointsFunctor
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.Matrix

/-!
# Positive nonsimple short-root homomorphisms of the short-root G₂ carrier

The roots `α₁ + α₂` and `2α₁ + α₂` have additive one-parameter subgroups in the
short-root carrier over `𝔽₃`. Conjugating the positive simple short-root homomorphism by
explicit rank-one root words constructs them inside the generated carrier, over every
commutative `𝔽₃`-algebra. Their matrices have nonzero quadratic terms. The torus acts through
the integral root characters, including over nonreduced algebras.

This file supplies matrix-valued homomorphisms, their injective parameters and coefficient
naturality, not closed subgroup-scheme morphisms or an identification with an independently
pinned simply connected group scheme. Such scheme comparisons must retain the displayed
parameter normalizations.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 5.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.

The rank-one words follow the negative-long-root construction in
`TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Root.NegativeLong`.
-/

public section

namespace TauCeti.G2ShortRoot.PrimeField

universe v w

noncomputable section

private def shortRootConjugator (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] : points A :=
  if i = 0 then rankOneWord 1 A else rankOneWord 0 A * rankOneWord 1 A

/-- The additive root homomorphism at `α₁ + α₂` (index zero) or `2α₁ + α₂` (index one).
Its normalization is fixed by the displayed matrix formula. -/
def positiveShortRootSubgroupPoints (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] : Multiplicative A →* points A :=
  (MulAut.conj (shortRootConjugator i A)).toMonoidHom.comp (rootSubgroupPoints (.inl 0) A)

/-- The two root homomorphisms are conjugates by explicit words in the numbered root groups. -/
theorem positiveShortRootSubgroupPoints_eq_conjugate (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] (u : Multiplicative A) :
    let n := fun j : Fin 2 => rankOneWord j A
    let g := if i = 0 then n 1 else n 0 * n 1
    positiveShortRootSubgroupPoints i A u = g * rootSubgroupPoints (.inl 0) A u * g⁻¹ :=
  (rfl)

private theorem pointsMap_shortRootConjugator {A : Type v} {B : Type w}
    [CommRing A] [CommRing B] [Algebra (ZMod 3) A] [Algebra (ZMod 3) B]
    (f : A →ₐ[ZMod 3] B) (i : Fin 2) :
    pointsMap f (shortRootConjugator i A) = shortRootConjugator i B := by
  fin_cases i <;> simp [shortRootConjugator, rankOneWord_def, map_mul]

private def shortRootConjugatorMatrix (i : Fin 2) : Matrix (Fin 7) (Fin 7) ℤ :=
  if i = 0 then
    !![1, 0, 0, 0, 0, 0, 0;
       0, 0, -1, 0, 0, 0, 0;
       0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, -1, 0;
       0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 1]
  else
    !![0, 0, 1, 0, 0, 0, 0;
       1, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, -1, 0;
       0, 0, 0, -1, 0, 0, 0;
       0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, -1;
       0, 0, 0, 0, 1, 0, 0]

private theorem coe_shortRootConjugator_prime (i : Fin 2) :
    ((shortRootConjugator i (ZMod 3) : Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) :
      Matrix (Fin 7) (Fin 7) (ZMod 3)) =
        (shortRootConjugatorMatrix i).map (Int.cast : ℤ → ZMod 3) := by
  unfold shortRootConjugator shortRootConjugatorMatrix
  split_ifs <;>
    simp only [rankOneWord_def, Subgroup.coe_mul, Units.val_mul,
      coe_rootSubgroupPoints, IntegralToralClosure.coe_rootSubgroupPoints,
      toAdd_ofAdd, rootMatrix_inr, rootMatrix_inl,
      rootDividedSquareMatrix_inl, rootDividedSquareMatrix_inr] <;>
    decide +kernel

private theorem shortRootConjugatorMatrix_mul_transpose (i : Fin 2) :
    shortRootConjugatorMatrix i * (shortRootConjugatorMatrix i).transpose = 1 := by
  fin_cases i <;> decide +kernel

private theorem coe_shortRootConjugator (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] :
    ((shortRootConjugator i A : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) =
        (shortRootConjugatorMatrix i).map (Int.cast : ℤ → A) := by
  rw [← pointsMap_shortRootConjugator (Algebra.ofId (ZMod 3) A) i, coe_pointsMap]
  -- The general-linear coefficient map acts entrywise on the constant conjugator.
  have h := congrArg (fun M : Matrix (Fin 7) (Fin 7) (ZMod 3) =>
    M.map (algebraMap (ZMod 3) A)) (coe_shortRootConjugator_prime i)
  rw [Matrix.GeneralLinearGroup.val_map_apply]
  ext a b
  have he := congrFun (congrFun h a) b
  simpa only [Matrix.map_apply, map_intCast, AlgHom.coe_toRingHom, Algebra.ofId_apply] using he

private theorem coe_shortRootConjugator_inv (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] :
    (((shortRootConjugator i A)⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) =
        (shortRootConjugatorMatrix i).transpose.map (Int.cast : ℤ → A) := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [coe_shortRootConjugator]
  have h := congrArg (fun M : Matrix (Fin 7) (Fin 7) ℤ => M.map (Int.castRingHom A))
    (shortRootConjugatorMatrix_mul_transpose i)
  rw [Matrix.map_mul] at h
  simpa only [Int.coe_castRingHom,
    Matrix.map_one _ (Int.cast_zero) (Int.cast_one)] using h

private def shortRootLinearMatrix (i : Fin 2) : Matrix (Fin 7) (Fin 7) ℤ :=
  if i = 0 then
    Matrix.single 0 2 1 + Matrix.single 1 3 (-2) + Matrix.single 3 5 1 + Matrix.single 4 6 (-1)
  else
    Matrix.single 0 3 (-2) + Matrix.single 1 4 1 + Matrix.single 2 5 1 + Matrix.single 3 6 (-1)

private def shortRootQuadraticMatrix (i : Fin 2) : Matrix (Fin 7) (Fin 7) ℤ :=
  if i = 0 then Matrix.single 1 5 (-1) else Matrix.single 0 6 1

/-- Fundamental-weight coordinates of `α₁ + α₂` (index zero) and `2α₁ + α₂` (index one). -/
def positiveShortRootWeight (i : Fin 2) : Fin 2 → ℤ :=
  if i = 0 then ![-1, 1] else ![1, 0]

/-- The first positive nonsimple short root has coordinates `(-1, 1)`. -/
@[simp]
theorem positiveShortRootWeight_zero : positiveShortRootWeight 0 = ![-1, 1] := (rfl)

/-- The second positive nonsimple short root has coordinates `(1, 0)`. -/
@[simp]
theorem positiveShortRootWeight_one : positiveShortRootWeight 1 = ![1, 0] := (rfl)

/-- The character labels are the indicated sums of Bourbaki numbered simple roots. -/
theorem positiveShortRootWeight_eq_simpleRoots (i : Fin 2) :
    positiveShortRootWeight i =
      (if i = 0 then 1 else 2) •
          DynkinType.G2.rootGeneratorWeight DynkinType.valid_G2 (.inl (0 : Fin 2)) +
        DynkinType.G2.rootGeneratorWeight DynkinType.valid_G2 (.inl (1 : Fin 2)) := by
  rw [DynkinType.G2.rootGeneratorWeight_inl_eq, DynkinType.G2.rootGeneratorWeight_inl_eq]
  simp only [funext_iff]
  fin_cases i <;> decide

private theorem shortRootCoefficient_support (i : Fin 2) :
    (∀ a b, shortRootLinearMatrix i a b ≠ 0 →
      weight a = positiveShortRootWeight i + weight b) ∧
    (∀ a b, shortRootQuadraticMatrix i a b ≠ 0 →
      weight a = 2 • positiveShortRootWeight i + weight b) := by
  fin_cases i <;> constructor <;> intro a b hab <;> funext j <;>
    revert hab <;> fin_cases a <;> fin_cases b <;> fin_cases j <;> decide +kernel

private theorem shortRootConjugator_coefficients (i : Fin 2) :
    shortRootConjugatorMatrix i * (shortRootConjugatorMatrix i).transpose = 1 ∧
      shortRootConjugatorMatrix i * raisingMatrix 0 *
        (shortRootConjugatorMatrix i).transpose = shortRootLinearMatrix i ∧
      shortRootConjugatorMatrix i * Matrix.single 2 4 1 *
        (shortRootConjugatorMatrix i).transpose = shortRootQuadraticMatrix i := by
  refine ⟨shortRootConjugatorMatrix_mul_transpose i, ?_⟩
  fin_cases i <;> decide +kernel

private theorem coe_positiveShortRootSubgroupPoints_polynomial (i : Fin 2) (A : Type v)
    [CommRing A] [Algebra (ZMod 3) A] (t : A) :
    ((positiveShortRootSubgroupPoints i A (Multiplicative.ofAdd t) :
        Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
      1 + t • (shortRootLinearMatrix i).map (Int.cast : ℤ → A) +
        t ^ 2 • (shortRootQuadraticMatrix i).map (Int.cast : ℤ → A) := by
  simp only [positiveShortRootSubgroupPoints, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Units.val_mul,
    Subgroup.coe_inv, coe_shortRootConjugator, coe_shortRootConjugator_inv,
    coe_rootSubgroupPoints, IntegralToralClosure.coe_rootSubgroupPoints, toAdd_ofAdd]
  rw [rootMatrix_inl, rootDividedSquareMatrix_inl]
  simp only [Matrix.cons_val_zero]
  simp only [mul_add, add_mul, mul_one, Matrix.mul_smul, Matrix.smul_mul]
  -- Bundle the integer coefficient map before collecting the three conjugated coefficients.
  simp only [← Int.coe_castRingHom (α := A), ← Matrix.map_mul,
    (shortRootConjugator_coefficients i).1,
    (shortRootConjugator_coefficients i).2.1,
    (shortRootConjugator_coefficients i).2.2,
    Matrix.map_one _ (map_zero (Int.castRingHom A)) (map_one (Int.castRingHom A))]

private theorem coe_positiveShortRootSubgroupPoints_explicit (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] (t : A) :
    ((positiveShortRootSubgroupPoints i A (Multiplicative.ofAdd t) :
        Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
      if i = 0 then
        !![1, 0, t, 0, 0, 0, 0;
           0, 1, 0, -2 * t, 0, -t ^ 2, 0;
           0, 0, 1, 0, 0, 0, 0;
           0, 0, 0, 1, 0, t, 0;
           0, 0, 0, 0, 1, 0, -t;
           0, 0, 0, 0, 0, 1, 0;
           0, 0, 0, 0, 0, 0, 1]
      else
        !![1, 0, 0, -2 * t, 0, 0, t ^ 2;
           0, 1, 0, 0, t, 0, 0;
           0, 0, 1, 0, 0, t, 0;
           0, 0, 0, 1, 0, 0, -t;
           0, 0, 0, 0, 1, 0, 0;
           0, 0, 0, 0, 0, 1, 0;
           0, 0, 0, 0, 0, 0, 1] := by
  rw [coe_positiveShortRootSubgroupPoints_polynomial]
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [shortRootLinearMatrix, shortRootQuadraticMatrix, Matrix.single, smul_eq_mul, mul_comm]

/-- Exact polynomial matrix at `α₁ + α₂`, including its quadratic term. -/
theorem coe_positiveShortRootSubgroupPoints_zero (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] (t : A) :
    ((positiveShortRootSubgroupPoints 0 A (Multiplicative.ofAdd t) :
        Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
      !![1, 0, t, 0, 0, 0, 0;
         0, 1, 0, -2 * t, 0, -t ^ 2, 0;
         0, 0, 1, 0, 0, 0, 0;
         0, 0, 0, 1, 0, t, 0;
         0, 0, 0, 0, 1, 0, -t;
         0, 0, 0, 0, 0, 1, 0;
         0, 0, 0, 0, 0, 0, 1] := by
  simpa only [↓reduceIte] using coe_positiveShortRootSubgroupPoints_explicit 0 A t

/-- Exact polynomial matrix at `2α₁ + α₂`, including its quadratic term. -/
theorem coe_positiveShortRootSubgroupPoints_one (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] (t : A) :
    ((positiveShortRootSubgroupPoints 1 A (Multiplicative.ofAdd t) :
        Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
      !![1, 0, 0, -2 * t, 0, 0, t ^ 2;
         0, 1, 0, 0, t, 0, 0;
         0, 0, 1, 0, 0, t, 0;
         0, 0, 0, 1, 0, 0, -t;
         0, 0, 0, 0, 1, 0, 0;
         0, 0, 0, 0, 0, 1, 0;
         0, 0, 0, 0, 0, 0, 1] := by
  simpa only [Fin.one_eq_zero_iff, Nat.reduceEqDiff, ↓reduceIte] using
    coe_positiveShortRootSubgroupPoints_explicit 1 A t

/-- The parameter at `α₁ + α₂` is recovered from matrix entry `(0,2)`. -/
@[simp]
theorem positiveShortRootSubgroupPoints_zero_parameter (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] (u : Multiplicative A) :
    ((positiveShortRootSubgroupPoints 0 A u :
        Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) 0 2 = u.toAdd := by
  rw [← ofAdd_toAdd u, coe_positiveShortRootSubgroupPoints_zero]
  simp

/-- The parameter at `2α₁ + α₂` is recovered from matrix entry `(1,4)`. -/
@[simp]
theorem positiveShortRootSubgroupPoints_one_parameter (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] (u : Multiplicative A) :
    ((positiveShortRootSubgroupPoints 1 A u :
        Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) 1 4 = u.toAdd := by
  rw [← ofAdd_toAdd u, coe_positiveShortRootSubgroupPoints_one]
  simp

/-- The positive nonsimple short-root homomorphisms are injective over every value algebra. -/
theorem positiveShortRootSubgroupPoints_injective (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] : Function.Injective (positiveShortRootSubgroupPoints i A) := by
  intro u v huv
  have he := congrArg (fun g : points A =>
    ((g : Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A)
      (if i = 0 then 0 else 1) (if i = 0 then 2 else 4)) huv
  apply Multiplicative.toAdd.injective
  fin_cases i <;> simpa using he

/-- Changing the coefficient algebra changes the root parameter by that algebra map. -/
@[simp↓]
theorem pointsMap_positiveShortRootSubgroupPoints {A : Type v} {B : Type w}
    [CommRing A] [CommRing B] [Algebra (ZMod 3) A] [Algebra (ZMod 3) B]
    (f : A →ₐ[ZMod 3] B) (i : Fin 2) (u : Multiplicative A) :
    pointsMap f (positiveShortRootSubgroupPoints i A u) =
      positiveShortRootSubgroupPoints i B (Multiplicative.ofAdd (f u.toAdd)) := by
  simp only [positiveShortRootSubgroupPoints, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  rw [pointsMap_shortRootConjugator, pointsMap_rootSubgroupPoints]

/-- Conjugation by the weight torus rescales the two short-root parameters through their
integral characters, not merely through their reductions modulo three. -/
@[simp]
theorem weightTorusPoints_conj_positiveShortRootSubgroupPoints (i : Fin 2) (A : Type v)
    [CommRing A] [Algebra (ZMod 3) A] (s : Fin 2 → Aˣ) (u : Multiplicative A) :
    weightTorusPoints A s * positiveShortRootSubgroupPoints i A u *
        (weightTorusPoints A s)⁻¹ =
      positiveShortRootSubgroupPoints i A (Multiplicative.ofAdd
        ((torusCharacter s (positiveShortRootWeight i) : A) * u.toAdd)) := by
  rw [← ofAdd_toAdd u]
  simp only [toAdd_ofAdd]
  apply (mul_inv_eq_iff_eq_mul).2
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_weightTorusPoints,
    IntegralToralClosure.coe_weightTorusPoints_eq_diagonal,
    coe_positiveShortRootSubgroupPoints_polynomial]
  have hx := Matrix.diagonal_torusCharacter_mul_of_support
    ((shortRootLinearMatrix i).map (Int.cast : ℤ → A)) weight (positiveShortRootWeight i)
    (fun a b hab => (shortRootCoefficient_support i).1 a b
      (fun hz => hab (by simp only [Matrix.map_apply, hz, Int.cast_zero]))) s
  have hy := Matrix.diagonal_torusCharacter_mul_of_support
    ((shortRootQuadraticMatrix i).map (Int.cast : ℤ → A)) weight
    (2 • positiveShortRootWeight i)
    (fun a b hab => (shortRootCoefficient_support i).2 a b
      (fun hz => hab (by simp only [Matrix.map_apply, hz, Int.cast_zero]))) s
  rw [torusCharacter_nsmul, Units.val_pow_eq_pow_val] at hy
  simp only [mul_add, add_mul, mul_one, one_mul, Matrix.mul_smul]
  rw [hx, hy]
  simp only [Matrix.smul_mul, smul_smul, mul_pow, mul_comm]

end

end TauCeti.G2ShortRoot.PrimeField
