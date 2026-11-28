/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Polynomial.Module.Basic
public import Mathlib.Data.Nat.Choose.Basic
import TauCeti.Algebra.Polynomial.Module.Division
import TauCeti.Algebra.Polynomial.Module.Eval

/-!
# Coefficient transfer for a Hecke polynomial identity

An identity relating two Hecke polynomials by a scalar factor of constant term `1`
expresses each rescaled source operator as a linear combination of target operators
of no higher index. The coefficients depend only on the scalar polynomial and the
residue norm, so the same combination works for every lift with that identity.

The coefficient transfer is `New.Data.IsWeakChainDatum.exists_sum_heckeSplit_lift_eq_smul`
in `New/UpperBound/Divisibility/ValuationAtNonSplitPrimes.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean) (revision `72fead1`).
-/

public section

open Finset
open scoped Polynomial PowerSeries

namespace TauCeti

/-- The constant-term convention for the Hecke polynomial of operators `T`, after
rescaling the variable by `a`. Its degree-`i` coefficient is `(-a)^i * q^(i.choose 2)`
times `T i`, for `i ≤ n`. The polynomial is module-valued: the operators need not commute. -/
noncomputable def heckeOperatorPolynomial {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (n : ℕ) (q a : R) (T : ℕ → M) : PolynomialModule R M :=
  ∑ j ∈ range (n + 1), PolynomialModule.single R j (((-a) ^ j * q ^ j.choose 2) • T j)

/-- The weighted operator coefficient, zero beyond the truncation degree. -/
@[simp] theorem coeff_heckeOperatorPolynomial {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (n : ℕ) (q a : R) (T : ℕ → M) (i : ℕ) :
    (heckeOperatorPolynomial n q a T).coeff i =
      if i ≤ n then ((-a) ^ i * q ^ i.choose 2) • T i else 0 := by
  classical
  simp [heckeOperatorPolynomial, Finsupp.single_apply]

/-- Evaluating at `x` gives the finite Hecke operator sum at the rescaled variable `a * x`. -/
@[simp] theorem eval_heckeOperatorPolynomial {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (n : ℕ) (q a x : R) (T : ℕ → M) :
    PolynomialModule.eval x (heckeOperatorPolynomial n q a T) =
      ∑ j ∈ range (n + 1), ((-(a * x)) ^ j * q ^ j.choose 2) • T j := by
  rw [heckeOperatorPolynomial, map_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [PolynomialModule.eval_single, ← mul_smul, ← neg_mul, mul_pow, mul_left_comm, mul_assoc]

/-- In a family of Hecke polynomial identities with the same scalar factor `P`, recover
an individual source operator, multiplied by its rescaling and residue-norm weights.
The coefficients of the target operators are uniform over the family of lift maps `L`. -/
theorem exists_sum_heckeOperator_comp_eq_smul {R V W ι : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (L : ι → V →ₗ[R] W) (T : ℕ → Module.End R V) (U : ℕ → Module.End R W)
    {q a : R} {P : R[X]} (hP : IsUnit (P.coeff 0)) {n m i : ℕ} (hin : i ≤ n)
    (h : ∀ x, heckeOperatorPolynomial m q 1 (fun j ↦ (U j).comp (L x)) =
      P • heckeOperatorPolynomial n q a (fun j ↦ (L x).comp (T j))) :
    ∃ c : Fin (i + 1) → R, ∀ x,
      (∑ j, c j • (U j).comp (L x)) = (a ^ i * q ^ i.choose 2) • (L x).comp (T i) := by
  obtain ⟨u, hu⟩ := hP
  let g := PowerSeries.invOfUnit (P : R⟦X⟧) u
  refine ⟨fun j ↦ if j.val ≤ m then (-1) ^ i * PowerSeries.coeff (i - j.val) g *
    ((-1) ^ j.val * q ^ j.val.choose 2) else 0, fun x ↦ ?_⟩
  have heq := PolynomialModule.coeff_eq_sum_smul_coeff_smul
    (heckeOperatorPolynomial n q a (fun j ↦ (L x).comp (T j))) P u hu.symm i
  rw [← h x, coeff_heckeOperatorPolynomial, ite_eq_left hin] at heq
  calc
    _ = (-1 : R) ^ i • ∑ j : Fin (i + 1), PowerSeries.coeff (i - j.val) g •
        (heckeOperatorPolynomial m q 1 (fun k ↦ (U k).comp (L x))).coeff j := by
      rw [Finset.smul_sum]
      refine sum_congr rfl fun j _ ↦ ?_
      rw [coeff_heckeOperatorPolynomial]
      by_cases hj : j.val ≤ m <;> simp [hj, mul_smul]
    _ = _ := by
      rw [← heq, ← mul_smul, ← mul_assoc, ← mul_pow]
      simp

/-- A pointwise Hecke polynomial identity implies the same uniform coefficient transfer
when the scalar ring is an infinite domain and the target module is torsion-free. -/
theorem exists_sum_heckeOperator_comp_eq_smul_of_eval {R V W ι : Type*} [CommRing R]
    [IsDomain R] [Infinite R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [Module.IsTorsionFree R W]
    (L : ι → V →ₗ[R] W) (T : ℕ → Module.End R V) (U : ℕ → Module.End R W)
    {q a : R} {P : R[X]} (hP : IsUnit (P.coeff 0)) {n m i : ℕ} (hin : i ≤ n)
    (h : ∀ x (z : R),
      (∑ j ∈ range (m + 1), ((-z) ^ j * q ^ j.choose 2) • (U j).comp (L x)) =
        P.eval z • ∑ j ∈ range (n + 1), ((-(a * z)) ^ j * q ^ j.choose 2) • (L x).comp (T j)) :
    ∃ c : Fin (i + 1) → R, ∀ x,
      (∑ j, c j • (U j).comp (L x)) = (a ^ i * q ^ i.choose 2) • (L x).comp (T i) := by
  refine exists_sum_heckeOperator_comp_eq_smul L T U hP (m := m) hin fun x ↦
    PolynomialModule.eq_of_forall_eval_eq fun z ↦ ?_
  simpa only [PolynomialModule.eval_smul, eval_heckeOperatorPolynomial, one_mul] using h x z

end TauCeti
