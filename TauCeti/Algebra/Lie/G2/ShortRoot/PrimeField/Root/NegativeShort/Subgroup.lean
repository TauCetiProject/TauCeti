/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PointsFunctor

/-!
# Negative nonsimple short-root subgroups of the characteristic-three G₂ carrier

Conjugating the negative short simple-root subgroup by rank-one root words gives the
subgroups at `-(α₁ + α₂)` and `-(2α₁ + α₂)`. Their matrices are quadratic in the additive
parameter, not just the identity plus a tangent vector. The formulas and parameter recovery
hold over every commutative `𝔽₃`-algebra, including nonreduced algebras.

These are subgroups of the carrier generated over `𝔽₃`. No identification with the pinned
simply connected group scheme, or with the reduction of the integral toral closure, is asserted.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 5.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.

The rank-one-word construction follows the negative long-root tangent construction in
`TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Root.NegativeLong`. The coefficient matrices
use the weight basis of `TauCeti.Algebra.Lie.G2.ShortRoot.Basic`.
-/

public section

open scoped Matrix

namespace TauCeti.G2ShortRoot.PrimeField

universe v w

noncomputable section

private def shortRankOneWord (j : Fin 2) (A : Type v) [CommRing A] [Algebra (ZMod 3) A] :
    points A :=
  rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd 1) *
    rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd (-1)) *
      rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd 1)

private def shortConjugator (i : Fin 2) (A : Type v) [CommRing A] [Algebra (ZMod 3) A] :
    points A :=
  if i = 0 then shortRankOneWord 1 A else shortRankOneWord 0 A * shortRankOneWord 1 A

/-- The negative short-root homomorphism at `-(α₁ + α₂)` (index zero) or
`-(2α₁ + α₂)` (index one), normalized by the displayed rank-one conjugation. -/
def negativeShortRootSubgroupPoints (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] : Multiplicative A →* points A :=
  (MulAut.conj (shortConjugator i A)).toMonoidHom.comp (rootSubgroupPoints (.inr 0) A)

/-- The chosen normalization is conjugation of the negative short simple-root subgroup. -/
theorem negativeShortRootSubgroupPoints_apply (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] (u : Multiplicative A) :
    let w := fun j : Fin 2 =>
      rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd (-1)) *
          rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd 1)
    let c := if i = 0 then w 1 else w 0 * w 1
    negativeShortRootSubgroupPoints i A u = c * rootSubgroupPoints (.inr 0) A u * c⁻¹ :=
  (rfl)

/-- The linear coefficient of the two negative short-root parametrizations in the weight basis. -/
def negativeShortRootMatrix (i : Fin 2) : Matrix (Fin 7) (Fin 7) ℤ :=
  if i = 0 then
    Matrix.single 2 0 1 - Matrix.single 3 1 1 +
      Matrix.single 5 3 2 - Matrix.single 6 4 1
  else
    -Matrix.single 3 0 1 + Matrix.single 4 1 1 +
      Matrix.single 5 2 1 - Matrix.single 6 3 2

/-- The quadratic coefficient (the integral divided square) of each negative short root. -/
def negativeShortRootDividedSquareMatrix (i : Fin 2) : Matrix (Fin 7) (Fin 7) ℤ :=
  if i = 0 then -Matrix.single 5 1 1 else Matrix.single 6 0 1

/-- The linear coefficient is explicit at both indices. -/
theorem negativeShortRootMatrix_def (i : Fin 2) :
    negativeShortRootMatrix i =
      if i = 0 then
        Matrix.single 2 0 1 - Matrix.single 3 1 1 +
          Matrix.single 5 3 2 - Matrix.single 6 4 1
      else
        -Matrix.single 3 0 1 + Matrix.single 4 1 1 +
          Matrix.single 5 2 1 - Matrix.single 6 3 2 :=
  (rfl)

/-- The quadratic coefficient is explicit at both indices. -/
theorem negativeShortRootDividedSquareMatrix_def (i : Fin 2) :
    negativeShortRootDividedSquareMatrix i =
      if i = 0 then -Matrix.single 5 1 1 else Matrix.single 6 0 1 :=
  (rfl)

private def shortWordMatrix (j : Fin 2) : Matrix (Fin 7) (Fin 7) ℤ :=
  (1 + rootMatrix (.inr j) + rootDividedSquareMatrix (.inr j)) *
    (1 - rootMatrix (.inl j) + rootDividedSquareMatrix (.inl j)) *
      (1 + rootMatrix (.inr j) + rootDividedSquareMatrix (.inr j))

private def shortConjugatorMatrix (i : Fin 2) : Matrix (Fin 7) (Fin 7) ℤ :=
  if i = 0 then shortWordMatrix 1 else shortWordMatrix 0 * shortWordMatrix 1

private theorem shortConjugatorMatrix_orthogonal (i : Fin 2) :
    shortConjugatorMatrix i * (shortConjugatorMatrix i).transpose = 1 := by
  simp only [shortConjugatorMatrix, shortWordMatrix, rootMatrix_inl, rootMatrix_inr,
    rootDividedSquareMatrix_inl, rootDividedSquareMatrix_inr]
  fin_cases i <;> decide +kernel

private theorem shortConjugatorMatrix_coefficients (i : Fin 2) :
    shortConjugatorMatrix i * rootMatrix (.inr 0) * (shortConjugatorMatrix i).transpose =
        negativeShortRootMatrix i ∧
      shortConjugatorMatrix i * rootDividedSquareMatrix (.inr 0) *
        (shortConjugatorMatrix i).transpose = negativeShortRootDividedSquareMatrix i := by
  simp only [shortConjugatorMatrix, shortWordMatrix, rootMatrix_inl, rootMatrix_inr,
    rootDividedSquareMatrix_inl, rootDividedSquareMatrix_inr, negativeShortRootMatrix,
    negativeShortRootDividedSquareMatrix]
  fin_cases i <;> decide +kernel

private theorem coe_shortRankOneWord (j : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] :
    ((shortRankOneWord j A : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) = (shortWordMatrix j).map (Int.castRingHom A) := by
  simp only [shortRankOneWord, Subgroup.coe_mul, Units.val_mul, coe_rootSubgroupPoints,
    IntegralToralClosure.coe_rootSubgroupPoints, toAdd_ofAdd,
    neg_one_sq, one_pow, one_smul, neg_smul, shortWordMatrix,
    Matrix.map_mul, Matrix.map_add _ (map_add _), Matrix.map_sub _ (map_sub _),
    Matrix.map_one _ (map_zero _) (map_one _)]
  simp only [Int.coe_castRingHom, sub_eq_add_neg]

private theorem coe_shortConjugator (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] :
    ((shortConjugator i A : Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
      (shortConjugatorMatrix i).map (Int.castRingHom A) := by
  unfold shortConjugator shortConjugatorMatrix
  split_ifs <;> simp only [Subgroup.coe_mul, Units.val_mul, coe_shortRankOneWord, Matrix.map_mul]

private theorem coe_shortConjugator_inv (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] :
    (((shortConjugator i A)⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) =
      (shortConjugatorMatrix i).transpose.map (Int.castRingHom A) := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [coe_shortConjugator, ← Matrix.map_mul, shortConjugatorMatrix_orthogonal,
    Matrix.map_one _ (map_zero _) (map_one _)]

/-- The exact quadratic root formula over every commutative coefficient algebra. -/
@[simp↓]
theorem coe_negativeShortRootSubgroupPoints (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] (u : Multiplicative A) :
    ((negativeShortRootSubgroupPoints i A u : Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) =
      1 + u.toAdd • (negativeShortRootMatrix i).map (Int.castRingHom A) +
        u.toAdd ^ 2 • (negativeShortRootDividedSquareMatrix i).map (Int.castRingHom A) := by
  have hX := congrArg (fun M : Matrix (Fin 7) (Fin 7) ℤ => M.map (Int.castRingHom A))
    (shortConjugatorMatrix_coefficients i).1
  have hY := congrArg (fun M : Matrix (Fin 7) (Fin 7) ℤ => M.map (Int.castRingHom A))
    (shortConjugatorMatrix_coefficients i).2
  have hI := congrArg (fun M : Matrix (Fin 7) (Fin 7) ℤ => M.map (Int.castRingHom A))
    (shortConjugatorMatrix_orthogonal i)
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at hX hY hI
  -- The bundled inner automorphism is multiplication on both sides by the constant conjugator.
  change ((shortConjugator i A : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) *
    ((rootSubgroupPoints (.inr 0) A u : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) *
    (((shortConjugator i A)⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) = _
  rw [coe_shortConjugator, coe_shortConjugator_inv, coe_rootSubgroupPoints,
    IntegralToralClosure.coe_rootSubgroupPoints]
  simp only [Int.coe_castRingHom] at hX hY hI ⊢
  simp only [mul_add, add_mul, mul_one, mul_smul_comm, smul_mul_assoc, hX, hY, hI]

/-- An entry recovers the additive parameter, with no nontriviality assumption on the algebra. -/
-- Read the parameter before the complete matrix formula expands.
@[simp↓]
theorem negativeShortRootSubgroupPoints_entry (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] (u : Multiplicative A) :
    ((negativeShortRootSubgroupPoints i A u : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) (if i = 0 then 2 else 4) (if i = 0 then 0 else 1) = u.toAdd := by
  rw [coe_negativeShortRootSubgroupPoints]
  fin_cases i <;>
    simp [negativeShortRootMatrix_def, negativeShortRootDividedSquareMatrix_def]

/-- Each negative short-root parametrization is injective over every coefficient algebra. -/
theorem negativeShortRootSubgroupPoints_injective (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] : Function.Injective (negativeShortRootSubgroupPoints i A) := by
  intro u v huv
  have h := congrArg (fun g : points A =>
    (g.val.val : Matrix (Fin 7) (Fin 7) A)
      (if i = 0 then 2 else 4) (if i = 0 then 0 else 1)) huv
  exact Multiplicative.toAdd.injective (by
    simpa only [negativeShortRootSubgroupPoints_entry] using h)

/-- Changing coefficients preserves the chosen negative short-root parameters. -/
@[simp↓]
theorem pointsMap_negativeShortRootSubgroupPoints {A : Type v} {B : Type w}
    [CommRing A] [CommRing B] [Algebra (ZMod 3) A] [Algebra (ZMod 3) B]
    (f : A →ₐ[ZMod 3] B) (i : Fin 2) (u : Multiplicative A) :
    pointsMap f (negativeShortRootSubgroupPoints i A u) =
      negativeShortRootSubgroupPoints i B (Multiplicative.ofAdd (f u.toAdd)) := by
  fin_cases i <;>
    simp [negativeShortRootSubgroupPoints, shortConjugator, shortRankOneWord, map_mul, map_inv]

private def shortCoefficient (i n : Fin 2) : Matrix (Fin 7) (Fin 7) ℤ :=
  if n = 0 then negativeShortRootMatrix i else negativeShortRootDividedSquareMatrix i

private theorem shortCoefficient_support (i n : Fin 2) :
    ∀ a b, shortCoefficient i n a b ≠ 0 →
      weight a - weight b = (n.val + 1) • weight (if i = 0 then 5 else 6) := by
  intro a b h
  ext j
  revert h
  fin_cases i <;> fin_cases n <;> fin_cases a <;> fin_cases b <;> fin_cases j <;>
    simp only [shortCoefficient, negativeShortRootMatrix, negativeShortRootDividedSquareMatrix] <;>
    decide +kernel

private theorem diagonal_mul_shortCoefficient (i n : Fin 2) (A : Type v) [CommRing A]
    (s : Fin 2 → Aˣ) :
    Matrix.diagonal (fun a => (torusCharacter s (weight a) : A)) *
        (shortCoefficient i n).map (Int.castRingHom A) =
      (torusCharacter s (weight (if i = 0 then 5 else 6)) : A) ^ (n.val + 1) •
        (shortCoefficient i n).map (Int.castRingHom A) *
          Matrix.diagonal (fun a => (torusCharacter s (weight a) : A)) := by
  ext a b
  by_cases h : shortCoefficient i n a b = 0
  · simp [Matrix.diagonal_mul, Matrix.mul_diagonal, h]
  · have hw := eq_add_of_sub_eq (shortCoefficient_support i n a b h)
    have hc : torusCharacter s (weight a) =
        torusCharacter s (weight (if i = 0 then 5 else 6)) ^ (n.val + 1) *
          torusCharacter s (weight b) := by
      rw [hw, torusCharacter_add, torusCharacter_nsmul]
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply,
      smul_eq_mul, Matrix.map_apply, hc, Units.val_mul, Units.val_pow_eq_pow_val]
    ac_rfl

/-- The torus acts by the integral root character `-(α₁ + α₂)` or `-(2α₁ + α₂)`.
These are entries five and six of the existing short-root weight diagram. -/
theorem weightTorusPoints_conj_negativeShortRootSubgroupPoints (i : Fin 2) (A : Type v)
    [CommRing A] [Algebra (ZMod 3) A] (s : Fin 2 → Aˣ) (u : Multiplicative A) :
    weightTorusPoints A s * negativeShortRootSubgroupPoints i A u *
        (weightTorusPoints A s)⁻¹ =
      negativeShortRootSubgroupPoints i A (Multiplicative.ofAdd
        ((torusCharacter s (weight (if i = 0 then 5 else 6)) : A) * u.toAdd)) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  apply Units.ext
  have hX := diagonal_mul_shortCoefficient i 0 A s
  have hY := diagonal_mul_shortCoefficient i 1 A s
  simp only [shortCoefficient, Fin.isValue, Fin.one_eq_zero_iff, Nat.reduceEqDiff, ↓reduceIte,
    Fin.val_zero, Fin.val_one, zero_add, pow_one, Nat.reduceAdd] at hX hY
  simp only [Subgroup.coe_mul, Units.val_mul, coe_negativeShortRootSubgroupPoints,
    coe_weightTorusPoints, IntegralToralClosure.coe_weightTorusPoints_eq_diagonal,
    toAdd_ofAdd, mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc,
    hX, hY, smul_smul, mul_pow, mul_comm (u.toAdd), mul_comm (u.toAdd ^ 2)]

end

end TauCeti.G2ShortRoot.PrimeField
