/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic

/-!
# Negative nonsimple short-root subgroups of the integral G₂ toral closure

Rank-one conjugation constructs the subgroups at `-(α₁ + α₂)` and `-(2α₁ + α₂)`.
Their exact quadratic matrices, parameter recovery and torus action hold over every
commutative ring, including nonreduced rings. These are points of the explicit integral
toral closure, not an identification with an independently pinned group scheme.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 5.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.

The rank-one-word construction follows
`TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Root.NegativeLong`.
The coefficient matrices use the weight basis of `TauCeti.Algebra.Lie.G2.ShortRoot.Basic`.
-/

public section

open scoped Matrix

namespace TauCeti.G2ShortRoot

universe v

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

/-- The linear coefficient at `-(α₁ + α₂)`. -/
@[simp]
theorem negativeShortRootMatrix_zero :
    negativeShortRootMatrix 0 = Matrix.single 2 0 1 - Matrix.single 3 1 1 +
      Matrix.single 5 3 2 - Matrix.single 6 4 1 := by
  rfl

/-- The linear coefficient at `-(2α₁ + α₂)`. -/
@[simp]
theorem negativeShortRootMatrix_one :
    negativeShortRootMatrix 1 = -Matrix.single 3 0 1 + Matrix.single 4 1 1 +
      Matrix.single 5 2 1 - Matrix.single 6 3 2 := by
  rfl

/-- The divided square at `-(α₁ + α₂)`. -/
@[simp]
theorem negativeShortRootDividedSquareMatrix_zero :
    negativeShortRootDividedSquareMatrix 0 = -Matrix.single 5 1 1 := by
  rfl

/-- The divided square at `-(2α₁ + α₂)`. -/
@[simp]
theorem negativeShortRootDividedSquareMatrix_one :
    negativeShortRootDividedSquareMatrix 1 = Matrix.single 6 0 1 := by
  rfl

namespace IntegralToralClosure

noncomputable section

private def shortConjugator (i : Fin 2) (A : Type v) [CommRing A] : points A :=
  if i = 0 then rankOneWordPoints 1 A else rankOneWordPoints 0 A * rankOneWordPoints 1 A

/-- The negative short-root homomorphism at `-(α₁ + α₂)` (index zero) or
`-(2α₁ + α₂)` (index one). Conjugate `rootSubgroupPoints (.inr 0)` by `w₂` or `w₁w₂`,
respectively, where `w₁ = rankOneWordPoints 0 A` and `w₂ = rankOneWordPoints 1 A`.
See `negativeShortRootSubgroupPoints_apply` for the normalization. -/
def negativeShortRootSubgroupPoints (i : Fin 2) (A : Type v) [CommRing A] :
    Multiplicative A →* points A :=
  (MulAut.conj (shortConjugator i A)).toMonoidHom.comp (rootSubgroupPoints (.inr 0) A)

/-- The chosen normalization is conjugation of the negative short simple-root subgroup. -/
theorem negativeShortRootSubgroupPoints_apply (i : Fin 2) (A : Type v) [CommRing A]
    (u : Multiplicative A) :
    let c := if i = 0 then rankOneWordPoints 1 A else rankOneWordPoints 0 A * rankOneWordPoints 1 A
    negativeShortRootSubgroupPoints i A u = c * rootSubgroupPoints (.inr 0) A u * c⁻¹ := by
  rfl

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

private theorem coe_rankOneWordPoints_matrix (j : Fin 2) (A : Type v) [CommRing A] :
    ((rankOneWordPoints j A : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) = (shortWordMatrix j).map (Int.castRingHom A) := by
  rw [coe_rankOneWordPoints, UniversalEnvelopingAlgebra.kostantToralWeylPoint_def]
  simp only [Subgroup.coe_mul,
    UniversalEnvelopingAlgebra.coe_kostantToralRootSubgroupPoints,
    ← coe_rootSubgroupPoints_eq_kostantRootSubgroupMatrix, Units.val_mul, coe_rootSubgroupPoints,
    toAdd_ofAdd, neg_one_sq, one_pow, one_smul, neg_smul, shortWordMatrix,
    Matrix.map_mul, Matrix.map_add _ (map_add _), Matrix.map_sub _ (map_sub _),
    Matrix.map_one _ (map_zero _) (map_one _)]
  simp only [Int.coe_castRingHom, sub_eq_add_neg]

private theorem coe_shortConjugator (i : Fin 2) (A : Type v) [CommRing A] :
    ((shortConjugator i A : Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
      (shortConjugatorMatrix i).map (Int.castRingHom A) := by
  unfold shortConjugator shortConjugatorMatrix
  split_ifs <;>
    simp only [Subgroup.coe_mul, Units.val_mul, coe_rankOneWordPoints_matrix, Matrix.map_mul]

private theorem coe_shortConjugator_inv (i : Fin 2) (A : Type v) [CommRing A] :
    (((shortConjugator i A)⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) =
      (shortConjugatorMatrix i).transpose.map (Int.castRingHom A) := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [coe_shortConjugator, ← Matrix.map_mul, shortConjugatorMatrix_orthogonal,
    Matrix.map_one _ (map_zero _) (map_one _)]

private theorem coe_conj_apply (i : Fin 2) (A : Type v) [CommRing A] (g : points A) :
    (((shortConjugator i A * g * (shortConjugator i A)⁻¹ : points A) :
        Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
      (shortConjugatorMatrix i).map (Int.castRingHom A) *
        (g : Matrix.GeneralLinearGroup (Fin 7) A).val *
          (shortConjugatorMatrix i).transpose.map (Int.castRingHom A) := by
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul,
    coe_shortConjugator_inv, coe_shortConjugator]

/-- The exact quadratic root formula over every commutative coefficient ring. -/
@[simp↓]
theorem coe_negativeShortRootSubgroupPoints (i : Fin 2) (A : Type v) [CommRing A]
    (u : Multiplicative A) :
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
  simp only [negativeShortRootSubgroupPoints, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, coe_conj_apply, coe_rootSubgroupPoints]
  simp only [Int.coe_castRingHom] at hX hY hI ⊢
  simp only [mul_add, add_mul, mul_one, mul_smul_comm, smul_mul_assoc, hX, hY, hI]

/-- An entry recovers the additive parameter without a nontriviality assumption. -/
theorem negativeShortRootSubgroupPoints_entry (i : Fin 2) (A : Type v) [CommRing A]
    (u : Multiplicative A) :
    ((negativeShortRootSubgroupPoints i A u : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) (if i = 0 then 2 else 4) (if i = 0 then 0 else 1) = u.toAdd := by
  rw [coe_negativeShortRootSubgroupPoints]
  fin_cases i <;> simp

/-- Entry `(2, 0)` recovers the parameter at `-(α₁ + α₂)`. -/
@[simp↓]
theorem negativeShortRootSubgroupPoints_zero_entry (A : Type v) [CommRing A]
    (u : Multiplicative A) :
    ((negativeShortRootSubgroupPoints 0 A u : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) 2 0 = u.toAdd :=
  negativeShortRootSubgroupPoints_entry 0 A u

/-- Entry `(4, 1)` recovers the parameter at `-(2α₁ + α₂)`. -/
@[simp↓]
theorem negativeShortRootSubgroupPoints_one_entry (A : Type v) [CommRing A]
    (u : Multiplicative A) :
    ((negativeShortRootSubgroupPoints 1 A u : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) 4 1 = u.toAdd :=
  negativeShortRootSubgroupPoints_entry 1 A u

/-- Each negative short-root parametrization is injective over every commutative ring. -/
theorem negativeShortRootSubgroupPoints_injective (i : Fin 2) (A : Type v) [CommRing A] :
    Function.Injective (negativeShortRootSubgroupPoints i A) := by
  intro u v huv
  have h := congrArg (fun g : points A =>
    (g.val.val : Matrix (Fin 7) (Fin 7) A)
      (if i = 0 then 2 else 4) (if i = 0 then 0 else 1)) huv
  exact Multiplicative.toAdd.injective (by
    simpa only [negativeShortRootSubgroupPoints_entry] using h)

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

private theorem diagonal_mul_of_shortRoot_support (i : Fin 2)
    (X : Matrix (Fin 7) (Fin 7) ℤ) (n : ℕ)
    (hX : ∀ a b, X a b ≠ 0 → weight a - weight b = n • weight (if i = 0 then 5 else 6))
    (A : Type v) [CommRing A] (s : Fin 2 → Aˣ) :
    Matrix.diagonal (fun a => (torusCharacter s (weight a) : A)) *
        X.map (Int.castRingHom A) =
      (torusCharacter s (weight (if i = 0 then 5 else 6)) : A) ^ n •
        X.map (Int.castRingHom A) *
          Matrix.diagonal (fun a => (torusCharacter s (weight a) : A)) := by
  ext a b
  by_cases h : X a b = 0
  · simp [Matrix.diagonal_mul, Matrix.mul_diagonal, h]
  · have hw := eq_add_of_sub_eq (hX a b h)
    have hc : torusCharacter s (weight a) =
        torusCharacter s (weight (if i = 0 then 5 else 6)) ^ n *
          torusCharacter s (weight b) := by
      rw [hw, torusCharacter_add, torusCharacter_nsmul]
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply,
      smul_eq_mul, Matrix.map_apply, hc, Units.val_mul, Units.val_pow_eq_pow_val]
    ac_rfl

/-- The torus acts by `-(α₁ + α₂)` or `-(2α₁ + α₂)`, entries five and six of the weight diagram. -/
@[simp]
theorem weightTorusPoints_conj_negativeShortRootSubgroupPoints (i : Fin 2) (A : Type v)
    [CommRing A] (s : Fin 2 → Aˣ) (u : Multiplicative A) :
    weightTorusPoints A s * negativeShortRootSubgroupPoints i A u *
        (weightTorusPoints A s)⁻¹ =
      negativeShortRootSubgroupPoints i A (Multiplicative.ofAdd
        ((torusCharacter s (weight (if i = 0 then 5 else 6)) : A) * u.toAdd)) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  apply Units.ext
  have hX := diagonal_mul_of_shortRoot_support i (negativeShortRootMatrix i) 1
    (shortCoefficient_support i 0) A s
  have hY := diagonal_mul_of_shortRoot_support i (negativeShortRootDividedSquareMatrix i) 2
    (shortCoefficient_support i 1) A s
  simp only [pow_one] at hX
  simp only [Subgroup.coe_mul, Units.val_mul, coe_negativeShortRootSubgroupPoints,
    coe_weightTorusPoints_eq_diagonal, toAdd_ofAdd, mul_add, add_mul, mul_one, one_mul,
    mul_smul_comm, smul_mul_assoc, hX, hY, smul_smul, mul_pow,
    mul_comm (u.toAdd), mul_comm (u.toAdd ^ 2)]

end

end IntegralToralClosure

end TauCeti.G2ShortRoot
