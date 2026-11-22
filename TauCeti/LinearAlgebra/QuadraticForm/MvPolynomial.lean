/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Multivariate polynomial representation of coordinate quadratic forms

Any quadratic form `Q : QuadraticForm R (ι → R)` on a finitely indexed coordinate module over a
commutative ring `R` evaluates as a homogeneous polynomial of degree at most two in the coordinates:
`Q x = ∑ i, Q (eᵢ) xᵢ² + ∑_{i ≠ j} polar Q eᵢ eⱼ · xᵢ xⱼ`, where `eᵢ = Pi.single i 1` and unordered
off-diagonal pairs are indexed by `Sym2 ι`. This representation holds in every characteristic,
including characteristic two where off-diagonal polar coefficients cannot be halved into a symmetric
Gram matrix.

## Main definitions and results

* `QuadraticMap.toMvPolynomial`: the multivariate polynomial in `MvPolynomial ι R` representing a
  coordinate quadratic form `Q : QuadraticForm R (ι → R)`.
* `QuadraticMap.eval_toMvPolynomial`: evaluating `Q.toMvPolynomial` at `x : ι → R` recovers `Q x`.
* `QuadraticMap.totalDegree_toMvPolynomial_le`: `Q.toMvPolynomial` has total degree at most `2`.
* `QuadraticMap.toMvPolynomial_injective`: `toMvPolynomial` is injective.
* `QuadraticMap.toMvPolynomialLinearMap`: `toMvPolynomial` bundled as an `R`-linear map.
* `QuadraticMap.toMvPolynomial_weightedSumSquares`: on a diagonal form `weightedSumSquares R w`,
  the off-diagonal polar terms vanish and `toMvPolynomial` reduces to `∑ i, C (w i) * X i ^ 2`.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter I, §1–§2.
-/

public section

noncomputable section

open MvPolynomial

namespace QuadraticMap

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Off-diagonal cross-term monomial `polar Q eᵢ eⱼ · Xᵢ Xⱼ` attached to an unordered pair in
`Sym2 ι`. -/
private def offDiagMonomial (Q : QuadraticForm R (ι → R)) : Sym2 ι → MvPolynomial ι R :=
  Sym2.lift ⟨fun i j ↦ C (polar Q (Pi.single i 1) (Pi.single j 1)) * X i * X j,
    fun i j ↦ by dsimp only; rw [polar_comm]; ring⟩

/-- The multivariate polynomial representing a coordinate quadratic form
`Q : QuadraticForm R (ι → R)`, assembled from the diagonal squares `Q (eᵢ) Xᵢ²` and the
off-diagonal polar cross terms `polar Q eᵢ eⱼ · Xᵢ Xⱼ`. -/
def toMvPolynomial (Q : QuadraticForm R (ι → R)) : MvPolynomial ι R :=
  ∑ i : ι, C (Q (Pi.single i 1)) * X i ^ 2 +
    ∑ ij ∈ (Finset.univ : Finset ι).sym2 with ¬ ij.IsDiag, offDiagMonomial Q ij

/-- Explicit expansion of `QuadraticMap.toMvPolynomial` into diagonal and off-diagonal sums. -/
theorem toMvPolynomial_def (Q : QuadraticForm R (ι → R)) :
    Q.toMvPolynomial = ∑ i : ι, C (Q (Pi.single i 1)) * X i ^ 2 +
      ∑ ij ∈ (Finset.univ : Finset ι).sym2 with ¬ ij.IsDiag,
        Sym2.lift ⟨fun i j ↦ C (polar Q (Pi.single i 1) (Pi.single j 1)) * X i * X j,
          fun i j ↦ by dsimp only; rw [polar_comm]; ring⟩ ij := (rfl)

/-- Evaluating `Q.toMvPolynomial` at a coordinate tuple `x : ι → R` recovers `Q x`. -/
@[simp]
theorem eval_toMvPolynomial (Q : QuadraticForm R (ι → R)) (x : ι → R) :
    eval x Q.toMvPolynomial = Q x := by
  have hx : (∑ i : ι, x i • Pi.single i (1 : R)) = x := by
    ext j
    simp [Pi.single_apply]
  conv_rhs => rw [← hx, QuadraticMap.map_sum]
  rw [toMvPolynomial, map_add, map_sum, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, eval_C, map_pow, eval_X, QuadraticMap.map_smul, smul_eq_mul, _root_.sq]
    ring
  · refine Finset.sum_congr rfl fun ij _ ↦ ?_
    induction ij using Sym2.ind with
    | _ i j =>
      simp only [offDiagMonomial, Sym2.lift_mk, map_mul, eval_C, eval_X, Sym2.map_mk,
        polarSym2_sym2Mk, polar_smul_left, polar_smul_right, smul_eq_mul]
      ring

/-- Every coordinate quadratic form is represented by a polynomial of total degree at most two. -/
theorem totalDegree_toMvPolynomial_le (Q : QuadraticForm R (ι → R)) :
    Q.toMvPolynomial.totalDegree ≤ 2 := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · simp [Subsingleton.elim Q.toMvPolynomial 0]
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine totalDegree_finsetSum_le fun i _ ↦ ?_
    exact (totalDegree_mul _ _).trans (by simp)
  · refine totalDegree_finsetSum_le fun ij _ ↦ ?_
    induction ij using Sym2.ind with
    | _ i j =>
      dsimp only [offDiagMonomial, Sym2.lift_mk]
      refine (totalDegree_mul _ _).trans ?_
      have h1 : (C (polar Q (Pi.single i 1) (Pi.single j 1)) * X i).totalDegree ≤ 1 :=
        (totalDegree_mul _ _).trans (by simp)
      simpa using Nat.add_le_add_right h1 1

/-- The polynomial of a coordinate quadratic form has zero constant coefficient. -/
@[simp]
theorem constantCoeff_toMvPolynomial (Q : QuadraticForm R (ι → R)) :
    constantCoeff Q.toMvPolynomial = 0 := by
  rw [← eval_zero, eval_toMvPolynomial, map_zero]

/-- Two coordinate quadratic forms with the same polynomial are equal. -/
theorem toMvPolynomial_injective :
    Function.Injective (toMvPolynomial (R := R) (ι := ι)) := by
  intro Q₁ Q₂ h
  ext x
  rw [← eval_toMvPolynomial, ← eval_toMvPolynomial, h]

/-- The zero quadratic form maps to the zero polynomial. -/
@[simp]
theorem toMvPolynomial_zero : (0 : QuadraticForm R (ι → R)).toMvPolynomial = 0 := by
  rw [toMvPolynomial]
  have h1 : (∑ i : ι, C ((0 : QuadraticForm R (ι → R)) (Pi.single i 1)) * X i ^ 2 :
      MvPolynomial ι R) = 0 := by simp
  have h2 : (∑ ij ∈ (Finset.univ : Finset ι).sym2 with ¬ ij.IsDiag,
      offDiagMonomial (0 : QuadraticForm R (ι → R)) ij) = 0 := by
    refine Finset.sum_eq_zero fun ij _ ↦ ?_
    induction ij using Sym2.ind with
    | _ i j => simp [offDiagMonomial, polar]
  rw [h1, h2, add_zero]

/-- The polynomial of a coordinate quadratic form vanishes if and only if the form vanishes. -/
@[simp]
theorem toMvPolynomial_eq_zero_iff (Q : QuadraticForm R (ι → R)) :
    Q.toMvPolynomial = 0 ↔ Q = 0 :=
  ⟨fun h ↦ toMvPolynomial_injective (h.trans toMvPolynomial_zero.symm),
    fun h ↦ h ▸ toMvPolynomial_zero⟩

/-- `toMvPolynomial` preserves addition of quadratic forms. -/
@[simp]
theorem toMvPolynomial_add (Q₁ Q₂ : QuadraticForm R (ι → R)) :
    (Q₁ + Q₂).toMvPolynomial = Q₁.toMvPolynomial + Q₂.toMvPolynomial := by
  rw [toMvPolynomial, toMvPolynomial, toMvPolynomial]
  have h1 : (∑ i : ι, C ((Q₁ + Q₂) (Pi.single i 1)) * X i ^ 2) =
      (∑ i : ι, C (Q₁ (Pi.single i 1)) * X i ^ 2) +
        ∑ i : ι, C (Q₂ (Pi.single i 1)) * X i ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [add_mul]
  have h2 : (∑ ij ∈ (Finset.univ : Finset ι).sym2 with ¬ ij.IsDiag,
      offDiagMonomial (Q₁ + Q₂) ij) =
      (∑ ij ∈ (Finset.univ : Finset ι).sym2 with ¬ ij.IsDiag, offDiagMonomial Q₁ ij) +
        ∑ ij ∈ (Finset.univ : Finset ι).sym2 with ¬ ij.IsDiag, offDiagMonomial Q₂ ij := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij _ ↦ ?_
    induction ij using Sym2.ind with
    | _ i j =>
      simp only [offDiagMonomial, Sym2.lift_mk, polar, add_apply, map_add, map_sub]
      ring
  rw [h1, h2]
  abel

/-- `toMvPolynomial` commutes with scalar multiplication. -/
@[simp]
theorem toMvPolynomial_smul (a : R) (Q : QuadraticForm R (ι → R)) :
    (a • Q).toMvPolynomial = a • Q.toMvPolynomial := by
  rw [toMvPolynomial, toMvPolynomial, smul_add, Finset.smul_sum, Finset.smul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [Algebra.smul_def, mul_assoc]
  · refine Finset.sum_congr rfl fun ij _ ↦ ?_
    induction ij using Sym2.ind with
    | _ i j =>
      simp only [offDiagMonomial, Sym2.lift_mk, polar, smul_apply, smul_eq_mul,
        map_sub, map_mul, Algebra.smul_def, C_eq_algebraMap]
      ring

/-- `toMvPolynomial` bundled as an `R`-linear map. -/
def toMvPolynomialLinearMap (R ι : Type*) [CommRing R] [Fintype ι] [DecidableEq ι] :
    QuadraticForm R (ι → R) →ₗ[R] MvPolynomial ι R where
  toFun := toMvPolynomial
  map_add' := toMvPolynomial_add
  map_smul' := toMvPolynomial_smul

/-- Applying `QuadraticMap.toMvPolynomialLinearMap` to `Q` evaluates to `Q.toMvPolynomial`. -/
@[simp]
theorem toMvPolynomialLinearMap_apply (Q : QuadraticForm R (ι → R)) :
    toMvPolynomialLinearMap R ι Q = Q.toMvPolynomial := (rfl)

/-- `toMvPolynomial` commutes with negation. -/
@[simp]
theorem toMvPolynomial_neg (Q : QuadraticForm R (ι → R)) :
    (-Q).toMvPolynomial = -Q.toMvPolynomial :=
  map_neg (toMvPolynomialLinearMap R ι) Q

/-- `toMvPolynomial` commutes with subtraction. -/
@[simp]
theorem toMvPolynomial_sub (Q₁ Q₂ : QuadraticForm R (ι → R)) :
    (Q₁ - Q₂).toMvPolynomial = Q₁.toMvPolynomial - Q₂.toMvPolynomial :=
  map_sub (toMvPolynomialLinearMap R ι) Q₁ Q₂

/-- On a diagonal form `weightedSumSquares R w`, all off-diagonal polar coefficients vanish, so
`toMvPolynomial` reduces to `∑ i, C (w i) * X i ^ 2`. -/
@[simp]
theorem toMvPolynomial_weightedSumSquares (w : ι → R) :
    (weightedSumSquares R w).toMvPolynomial = ∑ i : ι, C (w i) * X i ^ 2 := by
  rw [toMvPolynomial]
  have hdiag : (∑ i : ι, C ((weightedSumSquares R w) (Pi.single i 1)) * X i ^ 2) =
      ∑ i : ι, C (w i) * X i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [weightedSumSquares_apply, Pi.single_apply]
  have hoff : (∑ ij ∈ (Finset.univ : Finset ι).sym2 with ¬ ij.IsDiag,
      offDiagMonomial (weightedSumSquares R w) ij) = 0 := by
    refine Finset.sum_eq_zero fun ij hij ↦ ?_
    rw [Finset.mem_filter] at hij
    induction ij using Sym2.ind with
    | _ i j =>
      have hne : i ≠ j := by simpa [Sym2.mk_isDiag_iff] using hij.2
      have hpol : polar (weightedSumSquares R w) (Pi.single i 1) (Pi.single j 1) = 0 := by
        simp [polar, weightedSumSquares_apply, Pi.single_apply, hne, hne.symm, mul_add,
          Finset.sum_add_distrib]
      simp [offDiagMonomial, hpol]
  rw [hdiag, hoff, add_zero]

end QuadraticMap
