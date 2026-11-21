/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative
public import TauCeti.RingTheory.Derivation.Matrix
import Mathlib.Algebra.Module.Rat
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Regular formal connections are determined by their fibre at the origin

Write `t` for the variable `X` of `R⟦X⟧`. A connection `d + A dt` on the trivial rank-`n` bundle
over the formal disc `Spf R⟦t⟧` is given by a matrix `A : Matrix n n R⟦X⟧`. A gauge transformation
`g : GL n R⟦X⟧` acts on it by `Derivation.matrixGauge` along the formal derivative,
`g • A = g A g⁻¹ - (dg/dt) g⁻¹`. By `Derivation.matrixGauge_eq_iff`, `g` carries `A` to `B` exactly
when `g` solves the linear differential equation `g' = g A - B g`.

Over a `ℚ`-algebra `R`, possibly nonreduced, such equations are solved uniquely by coefficient
recursion: writing `Y = ∑ Yₖ tᵏ`, the equation `Y' = Y A - B Y` reads

```text
(k + 1) Yₖ₊₁ = ∑_{i + j = k} (Yᵢ Aⱼ - Bⱼ Yᵢ),
```

which determines every coefficient from `Y₀` after dividing by `k + 1`. Hence taking the constant
term is a bijection from the gauge transformations carrying `A` to `B` onto `GL n R`
(`PowerSeries.matrixGauge_constantCoeff_bijective`): a connection without poles is determined, up
to unique isomorphism, by its fibre at `t = 0`. For `B = 0` this is the existence and uniqueness of
a horizontal frame with a prescribed value at the origin.

Some division is needed: over `ZMod p` both `1 + t ^ p` and `1` solve `g' = 0` with constant term
`1`. Uniqueness only needs `R` to have unique division by positive integers (`HasUniqueDiv R`);
existence needs the division by `k + 1`, so a `ℚ`-algebra structure.

## Main results

* `PowerSeries.map_coeff_matrix_mul`: the coefficients of a product of matrices of power series.
* `PowerSeries.map_coeff_map_derivative`: the coefficients of the entrywise derivative.
* `PowerSeries.eq_of_map_derivative_eq_mul_sub_mul`: two solutions of `Y' = Y A - B Y` with the
  same constant term are equal, if `R` has unique division by positive integers.
* `PowerSeries.exists_map_derivative_eq_mul_sub_mul`: over a `ℚ`-algebra, `Y' = Y A - B Y` has a
  solution with any prescribed constant term.
* `PowerSeries.matrixGauge_constantCoeff_bijective`: over a `ℚ`-algebra, taking the constant term
  is a bijection from the gauge transformations carrying `A` to `B` onto `GL n R`.

## References

* E. Frenkel, D. Gaitsgory, *Local geometric Langlands correspondence and affine Kac–Moody
  algebras*, Lemma 4.4.2, in the form stated at the start of its proof, for `G`-bundles over
  `ℂ`-algebras; the coefficient recursion is the same over every `ℚ`-algebra.
-/

public section

namespace PowerSeries

open Finset Matrix

variable {R : Type*} {l m n : Type*}

section Semiring

variable [Semiring R]

/-- Two matrices of power series are equal if all their coefficient matrices are. -/
theorem matrix_ext {M N : Matrix m n R⟦X⟧} (h : ∀ k, M.map (coeff k) = N.map (coeff k)) :
    M = N := by
  ext i j k
  exact congrFun (congrFun (h k) i) j

/-- The `k`-th coefficient matrix of a product of matrices of power series is the Cauchy product
`∑_{i + j = k} Mᵢ Nⱼ` of the coefficient matrices. -/
theorem map_coeff_matrix_mul [Fintype m] (M : Matrix l m R⟦X⟧) (N : Matrix m n R⟦X⟧) (k : ℕ) :
    (M * N).map (coeff k) = ∑ p ∈ antidiagonal k, M.map (coeff p.1) * N.map (coeff p.2) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, coeff_mul, Matrix.sum_apply]
  exact Finset.sum_comm

end Semiring

section CommSemiring

variable [CommSemiring R]

/-- The `k`-th coefficient matrix of the entrywise derivative of `M` is `(k + 1) Mₖ₊₁`. -/
theorem map_coeff_map_derivative (M : Matrix m n R⟦X⟧) (k : ℕ) :
    (M.map d⁄dX).map (coeff k) = (k + 1) • M.map (coeff (k + 1)) := by
  ext i j
  simp [coeff_derivative, nsmul_eq_mul, mul_comm]

end CommSemiring

section CommRing

variable [CommRing R] [Fintype m] [Fintype n]

/-- The coefficient form of `Y' = Y A - B Y`:
`(k + 1) Yₖ₊₁ = ∑_{i + j = k} (Yᵢ Aⱼ - Bⱼ Yᵢ)`. -/
private theorem nsmul_map_coeff_succ_eq_sum {A : Matrix m m R⟦X⟧} {B : Matrix n n R⟦X⟧}
    {Y : Matrix n m R⟦X⟧} (hY : Y.map d⁄dX = Y * A - B * Y) (k : ℕ) :
    (k + 1) • Y.map (coeff (k + 1)) = ∑ p ∈ antidiagonal k,
      (Y.map (coeff p.1) * A.map (coeff p.2) - B.map (coeff p.2) * Y.map (coeff p.1)) := by
  rw [← map_coeff_map_derivative, hY, Matrix.map_sub _ (map_sub _), map_coeff_matrix_mul,
    map_coeff_matrix_mul,
    ← Nat.sum_antidiagonal_swap (f := fun p ↦ B.map (coeff p.1) * Y.map (coeff p.2)),
    ← sum_sub_distrib]
  simp only [Prod.fst_swap, Prod.snd_swap]

/-- A solution of `Y' = Y A - B Y` with vanishing constant term vanishes, if `R` has unique
division by positive integers. -/
private theorem eq_zero_of_map_derivative_eq_mul_sub_mul [HasUniqueDiv R]
    {A : Matrix m m R⟦X⟧} {B : Matrix n n R⟦X⟧} {Y : Matrix n m R⟦X⟧}
    (hY : Y.map d⁄dX = Y * A - B * Y) (h0 : Y.map constantCoeff = 0) : Y = 0 := by
  suffices h : ∀ k, Y.map (coeff k) = 0 from matrix_ext fun k ↦ by rw [h k]; ext; simp
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · rwa [coeff_zero_eq_constantCoeff]
    · have h := nsmul_map_coeff_succ_eq_sum hY k
      rw [sum_eq_zero fun p hp ↦ by
        rw [ih p.1 (by grind [mem_antidiagonal]), Matrix.zero_mul, Matrix.mul_zero, sub_zero]] at h
      ext i j
      exact nsmul_right_injective k.succ_ne_zero (by simpa using congrFun (congrFun h i) j)

/-- **Uniqueness for `Y' = Y A - B Y`.** Two solutions of the linear differential equation
`Y' = Y A - B Y` for matrices of power series with the same constant term are equal, provided `R`
has unique division by positive integers. -/
theorem eq_of_map_derivative_eq_mul_sub_mul [HasUniqueDiv R]
    {A : Matrix m m R⟦X⟧} {B : Matrix n n R⟦X⟧} {Y Z : Matrix n m R⟦X⟧}
    (hY : Y.map d⁄dX = Y * A - B * Y) (hZ : Z.map d⁄dX = Z * A - B * Z)
    (h0 : Y.map constantCoeff = Z.map constantCoeff) : Y = Z := by
  refine sub_eq_zero.mp (eq_zero_of_map_derivative_eq_mul_sub_mul (A := A) (B := B) ?_ ?_)
  · rw [Matrix.map_sub _ (map_sub _), hY, hZ, Matrix.sub_mul, Matrix.mul_sub]
    abel
  · rw [Matrix.map_sub _ (map_sub _), h0, sub_self]

variable [Algebra ℚ R]

/-- The coefficient matrices of the solution of `Y' = Y A - B Y` with constant term `Y₀`, by the
recursion `Yₖ₊₁ = (k + 1)⁻¹ ∑_{i ≤ k} (Yᵢ Aₖ₋ᵢ - Bₖ₋ᵢ Yᵢ)`. -/
private noncomputable def solutionCoeff (A : Matrix m m R⟦X⟧) (B : Matrix n n R⟦X⟧)
    (Y₀ : Matrix n m R) : ℕ → Matrix n m R
  | 0 => Y₀
  | k + 1 => ((k + 1 : ℕ) : ℚ)⁻¹ • ∑ i : Fin (k + 1),
      (solutionCoeff A B Y₀ i * A.map (coeff (k - i)) -
        B.map (coeff (k - i)) * solutionCoeff A B Y₀ i)

private theorem nsmul_solutionCoeff_succ (A : Matrix m m R⟦X⟧) (B : Matrix n n R⟦X⟧)
    (Y₀ : Matrix n m R) (k : ℕ) :
    (k + 1) • solutionCoeff A B Y₀ (k + 1) = ∑ p ∈ antidiagonal k,
      (solutionCoeff A B Y₀ p.1 * A.map (coeff p.2) -
        B.map (coeff p.2) * solutionCoeff A B Y₀ p.1) := by
  rw [solutionCoeff, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
    mul_inv_cancel₀ (by positivity), one_smul, Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← Fin.sum_univ_eq_sum_range (fun i ↦ solutionCoeff A B Y₀ i * A.map (coeff (k - i)) -
      B.map (coeff (k - i)) * solutionCoeff A B Y₀ i)]

/-- **Existence for `Y' = Y A - B Y`.** Over a `ℚ`-algebra, the linear differential equation
`Y' = Y A - B Y` for matrices of power series has a solution with any prescribed constant term. -/
theorem exists_map_derivative_eq_mul_sub_mul (A : Matrix m m R⟦X⟧) (B : Matrix n n R⟦X⟧)
    (Y₀ : Matrix n m R) :
    ∃ Y : Matrix n m R⟦X⟧, Y.map d⁄dX = Y * A - B * Y ∧ Y.map constantCoeff = Y₀ := by
  set Y : Matrix n m R⟦X⟧ := of fun i j ↦ mk fun k ↦ solutionCoeff A B Y₀ k i j
  have hY (k : ℕ) : Y.map (coeff k) = solutionCoeff A B Y₀ k := by
    ext i j
    simp [Y]
  refine ⟨Y, matrix_ext fun k ↦ ?_, by rw [← coeff_zero_eq_constantCoeff, hY 0, solutionCoeff]⟩
  rw [map_coeff_map_derivative, Matrix.map_sub _ (map_sub _), map_coeff_matrix_mul,
    map_coeff_matrix_mul,
    ← Nat.sum_antidiagonal_swap (f := fun p ↦ B.map (coeff p.1) * Y.map (coeff p.2)),
    ← sum_sub_distrib, hY, nsmul_solutionCoeff_succ]
  simp only [hY, Prod.fst_swap, Prod.snd_swap]

/-- **Regular formal connections are determined by their fibre at the origin.** Over a
`ℚ`-algebra `R`, possibly nonreduced, let `A` and `B` be connection matrices over `R⟦X⟧`. Taking
the constant term is a bijection from the gauge transformations `g : GL n R⟦X⟧` carrying `d + A dt`
to `d + B dt` onto `GL n R`. For `B = 0` this says that `d + A dt` has a unique horizontal frame
with any prescribed invertible value at `t = 0`. -/
theorem matrixGauge_constantCoeff_bijective [DecidableEq n] (A B : Matrix n n R⟦X⟧) :
    Function.Bijective fun g : {g : GL n R⟦X⟧ // (d⁄dX).matrixGauge g A = B} ↦
      GeneralLinearGroup.map constantCoeff g.val := by
  have := HasUniqueDiv.of_module_rat R
  refine ⟨fun ⟨g, hg⟩ ⟨h, hh⟩ hgh ↦ Subtype.ext (Units.ext ?_), fun g₀ ↦ ?_⟩
  · refine eq_of_map_derivative_eq_mul_sub_mul (Derivation.matrixGauge_eq_iff _ |>.mp hg)
      (Derivation.matrixGauge_eq_iff _ |>.mp hh) ?_
    simpa [GeneralLinearGroup.val_map_apply] using congrArg Units.val hgh
  · obtain ⟨Y, hY, hY₀⟩ := exists_map_derivative_eq_mul_sub_mul A B (g₀ : Matrix n n R)
    have hunit : IsUnit Y := by
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_constantCoeff, RingHom.map_det,
        RingHom.mapMatrix_apply, hY₀, ← Matrix.isUnit_iff_isUnit_det]
      exact g₀.isUnit
    refine ⟨⟨hunit.unit, Derivation.matrixGauge_eq_iff _ |>.mpr hY⟩, Units.ext ?_⟩
    simpa [GeneralLinearGroup.val_map_apply] using hY₀

end CommRing

end PowerSeries
