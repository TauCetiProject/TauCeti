/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.PowerSeries.Exp
public import TauCeti.LinearAlgebra.Matrix.PowerSeries
public import TauCeti.RingTheory.Derivation.Determinant
public import TauCeti.RingTheory.PowerSeries.Derivative

/-!
# Regular formal connections and gauge classification by the constant-term fibre

Let `R` be a commutative ring and `R⟦X⟧` the ring of univariate formal power series over `R`. A
regular formal connection on the trivial rank-`n` bundle `R⟦X⟧^n` is represented by a connection
matrix `A : Matrix n n R⟦X⟧`, standing for the first-order differential operator `d⁄dX + A`. An
intertwining (horizontal) morphism from `(R⟦X⟧^n, d⁄dX + A)` to `(R⟦X⟧^m, d⁄dX + B)` is a
rectangular matrix `M : Matrix m n R⟦X⟧` satisfying the formal Sylvester differential equation

`M.map d⁄dX = M * A - B * M`.

When `m = n` and `g : GL n R⟦X⟧` is invertible, this linear differential equation is equivalent to
the gauge transformation equation `g.regularGauge A = B`, where

`g.regularGauge A = g * A * g⁻¹ - g.map d⁄dX * g⁻¹`

is the left gauge action of `GL n R⟦X⟧` on regular connection matrices (`(d⁄dX).matrixGauge g A`).

This file establishes uniqueness, existence, and functoriality for horizontal morphisms and gauge
transformations of regular formal connections:

1. **Uniqueness under torsion-freeness (`HasUniqueDiv R`).** Comparing degree-`k` coefficients of
   `M.map d⁄dX = M * A - B * M` expresses `(k + 1) • coeff (k + 1) M` in terms of lower-degree
   coefficients of `M`. Whenever `R` has no additive `ℕ⁺`-torsion (`[HasUniqueDiv R]`, for example
   `R = ℤ` or any `ℚ`-algebra), a horizontal morphism is uniquely determined by its constant-term
   matrix `M.map constantCoeff : Matrix m n R` at `X = 0`
   (`Matrix.eq_of_map_derivative_eq_mul_sub_mul_of_map_constantCoeff_eq`), so taking the constant
   term is injective on gauge transformations carrying `A` to `B`
   (`Matrix.GeneralLinearGroup.regularGauge_constantCoeff_injective`). Moreover, when
   `A.trace = B.trace`, the Abel–Jacobi–Liouville formula forces `(g : Matrix n n R⟦X⟧).det` to be
   constant (`Matrix.GeneralLinearGroup.det_eq_C_of_regularGauge_eq`), so `SL_n`-valued initial
   frames lift to `SL_n`-valued gauge transformations.
2. **Existence and classification over `ℚ`-algebras (`Algebra ℚ R`).** Over any (possibly
   nonreduced) `ℚ`-algebra `R`, dividing the recursion by `k + 1` constructs the unique solution
   `Matrix.sylvesterSeries A B M₀` with prescribed constant term `M₀ : Matrix m n R`. Uniqueness
   promotes coefficientwise properties to algebraic laws without re-entering the recursion:
   `Matrix.sylvesterLinearEquiv` identifies the `R`-submodule `Matrix.sylvesterSubmodule A B` of
   horizontal morphisms with `Matrix m n R`; `Matrix.sylvesterSeries_mul` shows that horizontal
   extension commutes with matrix multiplication, upgrading `Matrix.sylvesterEndAlgEquiv` to an
   `R`-algebra isomorphism on horizontal endomorphisms; and
   `Matrix.GeneralLinearGroup.regularGaugeOfConstantCoeff` pairs `sylvesterSeries A B g₀` with
   `sylvesterSeries B A g₀⁻¹` inside `GL n R⟦X⟧`. Consequently, evaluating at `X = 0` is a
   bijection from `{g : GL n R⟦X⟧ // g.regularGauge A = B}` onto `GL n R`
   (`Matrix.GeneralLinearGroup.regularGaugeEquivConstantCoeff` and
   `Matrix.GeneralLinearGroup.regularGauge_constantCoeff_bijective`), and restricts to a group
   isomorphism on gauge stabilizers (`Matrix.GeneralLinearGroup.regularGaugeStabilizerMulEquiv`).
3. **Concrete specializations and sharpness.** For `1 × 1` matrices (`n = Unit`) with `A = 1` and
   `B = 0`, the horizontal frame with initial value `g₀` is `C (g₀ () ()) * PowerSeries.exp R`
   (`Matrix.GeneralLinearGroup.regularGaugeOfConstantCoeff_unit_one_zero_apply`). For a square-zero
   scalar `ε` (`ε * ε = 0`, e.g. in `DualNumber ℚ`), the horizontal frame for `A = scalar n (C ε)`
   is `g₀.map C * (1 + (C ε * X) • 1)`
   (`Matrix.GeneralLinearGroup.regularGaugeOfConstantCoeff_scalar_sq_zero`). Over any commutative
   ring of characteristic `p > 1`, the scalar matrix `(1 + X ^ p) • 1` has constant term `1` and
   fixes `0` under `regularGauge` while differing from `1`, showing that torsion-freeness is
   essential (`Matrix.GeneralLinearGroup.exists_regularGauge_zero_eq_zero_of_charP`).

## Main definitions

* `Matrix.sylvesterSubmodule`: the `R`-submodule of matrices `M : Matrix m n R⟦X⟧` satisfying
  `M.map d⁄dX = M * A - B * M`.
* `Matrix.sylvesterSeries`: the unique formal power-series matrix solving
  `M.map d⁄dX = M * A - B * M` with constant term `M₀`, over a `ℚ`-algebra `R`.
* `Matrix.sylvesterLinearEquiv`: the `R`-linear isomorphism
  `Matrix.sylvesterSubmodule A B ≃ₗ[R] Matrix m n R`.
* `Matrix.sylvesterEndSubalgebra`, `Matrix.sylvesterEndAlgEquiv`: the `R`-subalgebra of horizontal
  endomorphisms of `d⁄dX + A` and its `R`-algebra isomorphism with `Matrix n n R`.
* `Matrix.GeneralLinearGroup.regularGauge`: the left gauge action `g * A * g⁻¹ - g.map d⁄dX * g⁻¹`
  of `GL n R⟦X⟧` on regular connection matrices `Matrix n n R⟦X⟧`.
* `Matrix.GeneralLinearGroup.regularGaugeOfConstantCoeff`: the unique gauge transformation carrying
  `A` to `B` with prescribed constant-term matrix `g₀ : GL n R`.
* `Matrix.GeneralLinearGroup.regularGaugeEquivConstantCoeff`: the equivalence
  `{g : GL n R⟦X⟧ // g.regularGauge A = B} ≃ GL n R` given by taking the constant term.
* `Matrix.GeneralLinearGroup.regularGaugeStabilizer`,
  `Matrix.GeneralLinearGroup.regularGaugeStabilizerMulEquiv`: the stabilizer subgroup of `A` under
  `regularGauge` and its group isomorphism with `GL n R`.

## Main results

* `Matrix.eq_of_map_derivative_eq_mul_sub_mul_of_map_constantCoeff_eq`: uniqueness of solutions to
  `M.map d⁄dX = M * A - B * M` with given constant term under `[HasUniqueDiv R]`.
* `Matrix.sylvesterSeries_mul`, `Matrix.map_sylvesterSeries`: horizontal extension preserves matrix
  multiplication and commutes with base change along any ring homomorphism between `ℚ`-algebras.
* `Matrix.GeneralLinearGroup.det_eq_C_of_regularGauge_eq`: gauge transformations between connection
  matrices of equal trace have constant determinant under `[HasUniqueDiv R]`.
* `Matrix.GeneralLinearGroup.regularGauge_constantCoeff_injective`: injectivity of the constant-term
  map on gauge transformations under `[HasUniqueDiv R]`.
* `Matrix.GeneralLinearGroup.regularGauge_constantCoeff_bijective`: over any `ℚ`-algebra `R`, taking
  the constant term is a bijection from gauge transformations carrying `A` to `B` onto `GL n R`.

## References

* E. Frenkel and D. Gaitsgory, *Local geometric Langlands correspondence and affine Kac–Moody
  algebras*, Algebraic Geometry and Number Theory, Progr. Math. 253 (2006), Lemma 4.4.2, pp. 40–41.
* E. Frenkel, *Langlands Correspondence for Loop Groups*, Cambridge Studies in Advanced Mathematics
  103 (2007), §1.2 and §3.5.
-/

public section

open PowerSeries

namespace Matrix

section Uniqueness

variable {m n R : Type*} [CommRing R] [HasUniqueDiv R] [Fintype m] [Fintype n]

/-- If `M : Matrix m n R⟦X⟧` satisfies the homogeneous formal Sylvester differential equation
`M.map d⁄dX = M * A - B * M` and vanishes at `X = 0`, then `M = 0` whenever `R` has no additive
`ℕ⁺`-torsion (`[HasUniqueDiv R]`). -/
theorem eq_zero_of_map_derivative_eq_mul_sub_mul_of_map_constantCoeff_eq_zero
    {A : Matrix n n R⟦X⟧} {B : Matrix m m R⟦X⟧} {M : Matrix m n R⟦X⟧}
    (hM : M.map d⁄dX = M * A - B * M) (h0 : M.map constantCoeff = 0) :
    M = 0 := by
  have hcoeff : ∀ k : ℕ, ∀ i : m, ∀ j : n, coeff k (M i j) = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      rcases k with _ | k
      · intro i j
        have hij := congrArg (fun X : Matrix m n R => X i j) h0
        simpa [coeff_zero_eq_constantCoeff] using hij
      · intro i j
        have hstep := congrArg (fun X : Matrix m n R⟦X⟧ => coeff k (X i j)) hM
        simp only [Matrix.map_apply, coeff_derivative, Matrix.sub_apply, Matrix.mul_apply,
          map_sub, map_sum, coeff_mul] at hstep
        have hleft :
            ∑ l : n, ∑ p ∈ Finset.antidiagonal k, coeff p.1 (M i l) * coeff p.2 (A l j) = 0 :=
          Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun p hp => by
            have hp' := Finset.mem_antidiagonal.mp hp
            rw [ih p.1 (Nat.lt_succ_of_le (hp' ▸ Nat.le_add_right p.1 p.2)) i l, zero_mul]
        have hright :
            ∑ l : m, ∑ p ∈ Finset.antidiagonal k, coeff p.1 (B i l) * coeff p.2 (M l j) = 0 :=
          Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun p hp => by
            have hp' := Finset.mem_antidiagonal.mp hp
            rw [ih p.2 (Nat.lt_succ_of_le (hp' ▸ Nat.le_add_left p.2 p.1)) l j, mul_zero]
        rw [hleft, hright, sub_zero, ← Nat.cast_add_one, mul_comm, ← nsmul_eq_mul] at hstep
        exact nsmul_right_injective (Nat.succ_ne_zero k) (hstep.trans (nsmul_zero _).symm)
  exact Matrix.ext fun i j => PowerSeries.ext fun k => by simp [hcoeff k i j]

/-- **Uniqueness for the formal matrix Sylvester differential equation.** Over a commutative ring
`R` with `[HasUniqueDiv R]`, two solutions `M, N : Matrix m n R⟦X⟧` of
`X.map d⁄dX = X * A - B * X` with the same constant-term matrix at `X = 0` are equal. -/
theorem eq_of_map_derivative_eq_mul_sub_mul_of_map_constantCoeff_eq
    {A : Matrix n n R⟦X⟧} {B : Matrix m m R⟦X⟧} {M N : Matrix m n R⟦X⟧}
    (hM : M.map d⁄dX = M * A - B * M) (hN : N.map d⁄dX = N * A - B * N)
    (h0 : M.map constantCoeff = N.map constantCoeff) :
    M = N := by
  refine sub_eq_zero.mp
    (eq_zero_of_map_derivative_eq_mul_sub_mul_of_map_constantCoeff_eq_zero (A := A) (B := B) ?_ ?_)
  · have hsub : (M - N).map d⁄dX = M.map d⁄dX - N.map d⁄dX :=
      Matrix.ext fun i j => map_sub (derivative (R := R)) (M i j) (N i j)
    rw [hsub, hM, hN, Matrix.sub_mul, Matrix.mul_sub]
    abel
  · exact Matrix.ext fun i j => by
      have hij := congrArg (fun X : Matrix m n R => X i j) h0
      simpa [sub_eq_zero] using hij

end Uniqueness

section Submodule

variable {m n R : Type*} [CommRing R] [Fintype m] [Fintype n]

/-- **Submodule of horizontal morphisms** from `d⁄dX + A` to `d⁄dX + B`: rectangular matrices
`M : Matrix m n R⟦X⟧` satisfying `M.map d⁄dX = M * A - B * M`, over any commutative ring `R`. -/
noncomputable def sylvesterSubmodule (A : Matrix n n R⟦X⟧) (B : Matrix m m R⟦X⟧) :
    Submodule R (Matrix m n R⟦X⟧) where
  carrier := {M | M.map d⁄dX = M * A - B * M}
  add_mem' {M N} hM hN := by
    have hadd : (M + N).map d⁄dX = M.map d⁄dX + N.map d⁄dX :=
      Matrix.ext fun i j => map_add (derivative (R := R)) (M i j) (N i j)
    rw [Set.mem_ofPred_eq, hadd, hM, hN, Matrix.add_mul, Matrix.mul_add]
    abel
  zero_mem' := by
    have hzero : (0 : Matrix m n R⟦X⟧).map d⁄dX = 0 :=
      Matrix.ext fun _ _ => map_zero (derivative (R := R))
    rw [Set.mem_ofPred_eq, hzero, Matrix.zero_mul, Matrix.mul_zero, sub_self]
  smul_mem' r {M} hM := by
    have hsmul : (r • M).map d⁄dX = r • M.map d⁄dX :=
      Matrix.ext fun i j => Derivation.map_smul (derivative (R := R)) r (M i j)
    rw [Set.mem_ofPred_eq, hsmul, hM, smul_sub, Matrix.smul_mul, Matrix.mul_smul]

@[simp]
theorem mem_sylvesterSubmodule_iff {A : Matrix n n R⟦X⟧} {B : Matrix m m R⟦X⟧}
    {M : Matrix m n R⟦X⟧} :
    M ∈ sylvesterSubmodule A B ↔ M.map d⁄dX = M * A - B * M :=
  Iff.rfl

end Submodule

section Existence

variable {m n R : Type*} [CommRing R] [Algebra ℚ R] [Fintype m] [Fintype n]

/-- Coefficient matrices defined recursively by
`M_{k+1} = (k + 1)⁻¹ • ∑_{p ≤ k} (M_p A_{k-p} - B_{k-p} M_p)` with `M_0 = M₀`. -/
private noncomputable def sylvesterSeriesCoeff (A : Matrix n n R⟦X⟧) (B : Matrix m m R⟦X⟧)
    (M₀ : Matrix m n R) : ℕ → Matrix m n R
  | 0 => M₀
  | k + 1 =>
    (k + 1 : ℚ)⁻¹ •
      ∑ p ∈ (Finset.range (k + 1)).attach,
        (sylvesterSeriesCoeff A B M₀ p.1 * A.map (coeff (k - p.1)) -
          B.map (coeff (k - p.1)) * sylvesterSeriesCoeff A B M₀ p.1)
termination_by k => k
decreasing_by exact Finset.mem_range.mp p.2

/-- **Formal power-series solution of the matrix Sylvester differential equation.** Over a
`ℚ`-algebra `R`, `Matrix.sylvesterSeries A B M₀` is the unique matrix `M : Matrix m n R⟦X⟧` solving
`M.map d⁄dX = M * A - B * M` with initial value `M.map constantCoeff = M₀`. -/
noncomputable def sylvesterSeries (A : Matrix n n R⟦X⟧) (B : Matrix m m R⟦X⟧)
    (M₀ : Matrix m n R) : Matrix m n R⟦X⟧ :=
  Matrix.of fun i j => PowerSeries.mk fun k => sylvesterSeriesCoeff A B M₀ k i j

private theorem map_coeff_sylvesterSeries_eq (A : Matrix n n R⟦X⟧) (B : Matrix m m R⟦X⟧)
    (M₀ : Matrix m n R) (k : ℕ) :
    (sylvesterSeries A B M₀).map (coeff k) = sylvesterSeriesCoeff A B M₀ k :=
  Matrix.ext fun i j => by simp [sylvesterSeries]

@[simp]
theorem map_constantCoeff_sylvesterSeries (A : Matrix n n R⟦X⟧) (B : Matrix m m R⟦X⟧)
    (M₀ : Matrix m n R) :
    (sylvesterSeries A B M₀).map constantCoeff = M₀ :=
  Matrix.ext fun i j => by simp [sylvesterSeries, sylvesterSeriesCoeff]

@[simp]
theorem constantCoeff_sylvesterSeries_apply (A : Matrix n n R⟦X⟧) (B : Matrix m m R⟦X⟧)
    (M₀ : Matrix m n R) (i : m) (j : n) :
    constantCoeff (sylvesterSeries A B M₀ i j) = M₀ i j := by
  simpa using congrArg (fun X : Matrix m n R => X i j) (map_constantCoeff_sylvesterSeries A B M₀)

/-- Recursive degree-`(k + 1)` coefficient identity for `Matrix.sylvesterSeries`. -/
theorem map_coeff_succ_sylvesterSeries (A : Matrix n n R⟦X⟧) (B : Matrix m m R⟦X⟧)
    (M₀ : Matrix m n R) (k : ℕ) :
    (sylvesterSeries A B M₀).map (coeff (k + 1)) =
      (k + 1 : ℚ)⁻¹ •
        ∑ p ∈ Finset.range (k + 1),
          ((sylvesterSeries A B M₀).map (coeff p) * A.map (coeff (k - p)) -
            B.map (coeff (k - p)) * (sylvesterSeries A B M₀).map (coeff p)) := by
  rw [map_coeff_sylvesterSeries_eq, sylvesterSeriesCoeff,
    Finset.sum_attach (Finset.range (k + 1)) fun p =>
      sylvesterSeriesCoeff A B M₀ p * A.map (coeff (k - p)) -
        B.map (coeff (k - p)) * sylvesterSeriesCoeff A B M₀ p]
  simp only [map_coeff_sylvesterSeries_eq]

/-- `Matrix.sylvesterSeries A B M₀` satisfies `M.map d⁄dX = M * A - B * M`. -/
@[simp]
theorem map_derivative_sylvesterSeries (A : Matrix n n R⟦X⟧) (B : Matrix m m R⟦X⟧)
    (M₀ : Matrix m n R) :
    (sylvesterSeries A B M₀).map d⁄dX =
      sylvesterSeries A B M₀ * A - B * sylvesterSeries A B M₀ := by
  refine Matrix.ext fun i j => PowerSeries.ext fun k => ?_
  have hcast : ∀ x : R, ((k + 1 : ℚ)⁻¹ • x) * (k + 1 : R) = x := fun x => by
    have hk : (k + 1 : R) = algebraMap ℚ R (k + 1 : ℚ) := by simp
    rw [hk, mul_comm, ← Algebra.smul_def, smul_smul,
      mul_inv_cancel₀ (Nat.cast_add_one_ne_zero k), one_smul]
  have hc : coeff (k + 1) (sylvesterSeries A B M₀ i j) =
      ((sylvesterSeries A B M₀).map (coeff (k + 1))) i j := rfl
  rw [Matrix.map_apply, coeff_derivative, hc, map_coeff_succ_sylvesterSeries, Matrix.smul_apply,
    hcast, Matrix.sum_apply]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply, map_sub, map_sum, coeff_mul,
    Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Finset.Nat.sum_antidiagonal_swap, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rfl

/-- **Existence and uniqueness characterization of `Matrix.sylvesterSeries`.** Over a `ℚ`-algebra
`R`, `M = sylvesterSeries A B M₀` if and only if `M.map d⁄dX = M * A - B * M` and
`M.map constantCoeff = M₀`. -/
theorem eq_sylvesterSeries_iff {A : Matrix n n R⟦X⟧} {B : Matrix m m R⟦X⟧}
    {M : Matrix m n R⟦X⟧} {M₀ : Matrix m n R} :
    M = sylvesterSeries A B M₀ ↔
      M.map d⁄dX = M * A - B * M ∧ M.map constantCoeff = M₀ := by
  have : HasUniqueDiv R := .of_module_rat R
  refine ⟨?_, fun ⟨hM, h0⟩ =>
    eq_of_map_derivative_eq_mul_sub_mul_of_map_constantCoeff_eq hM
      (map_derivative_sylvesterSeries A B M₀)
      (h0.trans (map_constantCoeff_sylvesterSeries A B M₀).symm)⟩
  rintro rfl
  exact ⟨map_derivative_sylvesterSeries A B M₀, map_constantCoeff_sylvesterSeries A B M₀⟩

@[simp]
theorem sylvesterSeries_zero (A : Matrix n n R⟦X⟧) (B : Matrix m m R⟦X⟧) :
    sylvesterSeries A B 0 = 0 := by
  symm
  rw [eq_sylvesterSeries_iff]
  exact ⟨(sylvesterSubmodule A B).zero_mem, Matrix.ext fun _ _ => by simp⟩

theorem sylvesterSeries_add (A : Matrix n n R⟦X⟧) (B : Matrix m m R⟦X⟧)
    (M₀ N₀ : Matrix m n R) :
    sylvesterSeries A B (M₀ + N₀) = sylvesterSeries A B M₀ + sylvesterSeries A B N₀ := by
  symm
  rw [eq_sylvesterSeries_iff]
  refine ⟨(sylvesterSubmodule A B).add_mem
    (map_derivative_sylvesterSeries A B M₀) (map_derivative_sylvesterSeries A B N₀), ?_⟩
  exact Matrix.ext fun i j => by simp

theorem sylvesterSeries_smul (A : Matrix n n R⟦X⟧) (B : Matrix m m R⟦X⟧)
    (r : R) (M₀ : Matrix m n R) :
    sylvesterSeries A B (r • M₀) = r • sylvesterSeries A B M₀ := by
  symm
  rw [eq_sylvesterSeries_iff]
  refine ⟨(sylvesterSubmodule A B).smul_mem r (map_derivative_sylvesterSeries A B M₀), ?_⟩
  exact Matrix.ext fun i j => by simp [Algebra.smul_def, PowerSeries.algebraMap_eq]

@[simp]
theorem sylvesterSeries_self_one [DecidableEq n] (A : Matrix n n R⟦X⟧) :
    sylvesterSeries A A 1 = 1 := by
  symm
  rw [eq_sylvesterSeries_iff]
  refine ⟨by simp [Derivation.map_matrix_one (derivative (R := R))], ?_⟩
  simpa using (constantCoeff (R := R)).mapMatrix.map_one

/-- **Multiplicativity of horizontal extension.** Extending `M₀ : Matrix l m R` from `B` to `C` and
`N₀ : Matrix m n R` from `A` to `B` and multiplying the resulting formal power-series matrices gives
the extension of `M₀ * N₀` from `A` to `C`. -/
theorem sylvesterSeries_mul {l : Type*} [Fintype l] (A : Matrix n n R⟦X⟧) (B : Matrix m m R⟦X⟧)
    (C : Matrix l l R⟦X⟧) (M₀ : Matrix l m R) (N₀ : Matrix m n R) :
    sylvesterSeries B C M₀ * sylvesterSeries A B N₀ = sylvesterSeries A C (M₀ * N₀) := by
  rw [eq_sylvesterSeries_iff]
  refine ⟨(derivative (R := R)).map_matrix_mul_of_map_eq_mul_sub_mul
    (map_derivative_sylvesterSeries B C M₀) (map_derivative_sylvesterSeries A B N₀), ?_⟩
  exact Matrix.ext fun i j => by simp [Matrix.mul_apply]

/-- **Functoriality of `Matrix.sylvesterSeries` under base change.** Any ring homomorphism
`f : R →+* S` between `ℚ`-algebras intertwines `Matrix.sylvesterSeries`, without requiring an
explicit `ℚ`-algebra homomorphism structure on `f`. -/
theorem map_sylvesterSeries {S : Type*} [CommRing S] [Algebra ℚ S] (f : R →+* S)
    (A : Matrix n n R⟦X⟧) (B : Matrix m m R⟦X⟧) (M₀ : Matrix m n R) :
    (sylvesterSeries A B M₀).map (PowerSeries.map f) =
      sylvesterSeries (A.map (PowerSeries.map f)) (B.map (PowerSeries.map f)) (M₀.map f) := by
  rw [eq_sylvesterSeries_iff]
  refine ⟨?_, Matrix.ext fun i j => ?_⟩
  · have hder : ((sylvesterSeries A B M₀).map (PowerSeries.map f)).map d⁄dX =
        ((sylvesterSeries A B M₀).map d⁄dX).map (PowerSeries.map f) :=
      Matrix.ext fun i j => PowerSeries.derivative_map (sylvesterSeries A B M₀ i j) f
    rw [hder, map_derivative_sylvesterSeries]
    exact Matrix.ext fun i j => by simp [Matrix.mul_apply]
  · simp only [Matrix.map_apply]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_sylvesterSeries_apply]

/-- **Horizontal morphisms are classified by their constant term at `X = 0`.** Over a `ℚ`-algebra
`R`, taking the constant-term matrix is an `R`-linear isomorphism from
`Matrix.sylvesterSubmodule A B` onto `Matrix m n R`. -/
noncomputable def sylvesterLinearEquiv (A : Matrix n n R⟦X⟧) (B : Matrix m m R⟦X⟧) :
    sylvesterSubmodule A B ≃ₗ[R] Matrix m n R where
  toFun M := M.1.map constantCoeff
  invFun M₀ := ⟨sylvesterSeries A B M₀, map_derivative_sylvesterSeries A B M₀⟩
  left_inv M := Subtype.ext ((eq_sylvesterSeries_iff.mpr ⟨M.2, rfl⟩).symm)
  right_inv M₀ := map_constantCoeff_sylvesterSeries A B M₀
  map_add' M N := Matrix.ext fun i j => by simp
  map_smul' r M := Matrix.ext fun i j => by simp [Algebra.smul_def, PowerSeries.algebraMap_eq]

@[simp]
theorem sylvesterLinearEquiv_apply (A : Matrix n n R⟦X⟧) (B : Matrix m m R⟦X⟧)
    (M : sylvesterSubmodule A B) :
    sylvesterLinearEquiv A B M = M.1.map constantCoeff :=
  (rfl)

@[simp]
theorem coe_sylvesterLinearEquiv_symm (A : Matrix n n R⟦X⟧) (B : Matrix m m R⟦X⟧)
    (M₀ : Matrix m n R) :
    ((sylvesterLinearEquiv A B).symm M₀ : Matrix m n R⟦X⟧) = sylvesterSeries A B M₀ :=
  (rfl)

end Existence

section Endomorphisms

/-- **Subalgebra of horizontal endomorphisms** of the regular formal connection `d⁄dX + A`: square
matrices `M : Matrix n n R⟦X⟧` satisfying `M.map d⁄dX = M * A - A * M`, over any commutative ring
`R`. -/
noncomputable def sylvesterEndSubalgebra {n R : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R⟦X⟧) : Subalgebra R (Matrix n n R⟦X⟧) where
  carrier := {M | M.map d⁄dX = M * A - A * M}
  mul_mem' {M N} hM hN :=
    (derivative (R := R)).map_matrix_mul_of_map_eq_mul_sub_mul hM hN
  one_mem' := by
    rw [Set.mem_ofPred_eq, Derivation.map_matrix_one (derivative (R := R)), one_mul, mul_one,
      sub_self]
  add_mem' {M N} hM hN := (sylvesterSubmodule A A).add_mem hM hN
  zero_mem' := (sylvesterSubmodule A A).zero_mem
  algebraMap_mem' r := by
    have hder : (algebraMap R (Matrix n n R⟦X⟧) r).map d⁄dX = 0 :=
      Matrix.ext fun i j => by
        by_cases hij : i = j <;> simp [Algebra.algebraMap_eq_smul_one, hij]
    have hcomm :
        algebraMap R (Matrix n n R⟦X⟧) r * A - A * algebraMap R (Matrix n n R⟦X⟧) r = 0 :=
      sub_eq_zero.mpr (Algebra.commutes r A)
    rw [Set.mem_ofPred_eq, hder, hcomm]

@[simp]
theorem mem_sylvesterEndSubalgebra_iff {n R : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    {A M : Matrix n n R⟦X⟧} :
    M ∈ sylvesterEndSubalgebra A ↔ M.map d⁄dX = M * A - A * M :=
  Iff.rfl

/-- **Horizontal endomorphisms of a regular formal connection form an `R`-algebra isomorphic to
`Matrix n n R`** via evaluation at `X = 0`, over any `ℚ`-algebra `R`. -/
noncomputable def sylvesterEndAlgEquiv {n R : Type*} [CommRing R] [Algebra ℚ R]
    [Fintype n] [DecidableEq n] (A : Matrix n n R⟦X⟧) :
    sylvesterEndSubalgebra A ≃ₐ[R] Matrix n n R where
  toFun M := M.1.map constantCoeff
  invFun M₀ := ⟨sylvesterSeries A A M₀, map_derivative_sylvesterSeries A A M₀⟩
  left_inv M := Subtype.ext ((eq_sylvesterSeries_iff.mpr ⟨M.2, rfl⟩).symm)
  right_inv M₀ := map_constantCoeff_sylvesterSeries A A M₀
  map_mul' M N := Matrix.ext fun i j => by simp [Matrix.mul_apply]
  map_add' M N := Matrix.ext fun i j => by simp
  commutes' r := Matrix.ext fun i j => by
    simp only [Matrix.map_apply, Subalgebra.coe_algebraMap]
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    by_cases hij : i = j <;> simp [Algebra.smul_def, PowerSeries.algebraMap_eq, hij]

@[simp]
theorem sylvesterEndAlgEquiv_apply {n R : Type*} [CommRing R] [Algebra ℚ R]
    [Fintype n] [DecidableEq n] (A : Matrix n n R⟦X⟧) (M : sylvesterEndSubalgebra A) :
    sylvesterEndAlgEquiv A M = M.1.map constantCoeff :=
  (rfl)

@[simp]
theorem coe_sylvesterEndAlgEquiv_symm {n R : Type*} [CommRing R] [Algebra ℚ R]
    [Fintype n] [DecidableEq n] (A : Matrix n n R⟦X⟧) (M₀ : Matrix n n R) :
    ((sylvesterEndAlgEquiv A).symm M₀ : Matrix n n R⟦X⟧) = sylvesterSeries A A M₀ :=
  (rfl)

end Endomorphisms

namespace GeneralLinearGroup

section Gauge

variable {n R : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- **Left gauge action on regular formal connection matrices `d⁄dX + A` over `R⟦X⟧`**:
`g.regularGauge A = g * A * g⁻¹ - g.map d⁄dX * g⁻¹`, satisfying
`(h * g).regularGauge A = h.regularGauge (g.regularGauge A)`. -/
noncomputable def regularGauge (g : GeneralLinearGroup n R⟦X⟧) (A : Matrix n n R⟦X⟧) :
    Matrix n n R⟦X⟧ :=
  (derivative (R := R)).matrixGauge g A

theorem regularGauge_def (g : GeneralLinearGroup n R⟦X⟧) (A : Matrix n n R⟦X⟧) :
    g.regularGauge A =
      (g : Matrix n n R⟦X⟧) * A * (↑g⁻¹ : Matrix n n R⟦X⟧) -
        (g : Matrix n n R⟦X⟧).map d⁄dX * (↑g⁻¹ : Matrix n n R⟦X⟧) :=
  (derivative (R := R)).matrixGauge_def g A

theorem regularGauge_eq_matrixGauge (g : GeneralLinearGroup n R⟦X⟧) (A : Matrix n n R⟦X⟧) :
    g.regularGauge A = (derivative (R := R)).matrixGauge g A :=
  (rfl)

@[simp]
theorem regularGauge_one (A : Matrix n n R⟦X⟧) :
    (1 : GeneralLinearGroup n R⟦X⟧).regularGauge A = A :=
  (derivative (R := R)).matrixGauge_one A

theorem regularGauge_mul (h g : GeneralLinearGroup n R⟦X⟧) (A : Matrix n n R⟦X⟧) :
    (h * g).regularGauge A = h.regularGauge (g.regularGauge A) :=
  (derivative (R := R)).matrixGauge_mul h g A

@[simp]
theorem regularGauge_inv_cancel_left (g : GeneralLinearGroup n R⟦X⟧) (A : Matrix n n R⟦X⟧) :
    g⁻¹.regularGauge (g.regularGauge A) = A :=
  (derivative (R := R)).matrixGauge_inv_cancel_left g A

@[simp]
theorem regularGauge_inv_cancel_right (g : GeneralLinearGroup n R⟦X⟧) (A : Matrix n n R⟦X⟧) :
    g.regularGauge (g⁻¹.regularGauge A) = A :=
  (derivative (R := R)).matrixGauge_inv_cancel_right g A

/-- **Frame dictionary for regular formal connections**: `g⁻¹ A g + g⁻¹ (dg/dX)` equals the left
gauge action `(g⁻¹).regularGauge A`. -/
theorem regularGauge_inv (g : GeneralLinearGroup n R⟦X⟧) (A : Matrix n n R⟦X⟧) :
    g⁻¹.regularGauge A =
      (↑g⁻¹ : Matrix n n R⟦X⟧) * A * (g : Matrix n n R⟦X⟧) +
        (↑g⁻¹ : Matrix n n R⟦X⟧) * (g : Matrix n n R⟦X⟧).map d⁄dX :=
  (derivative (R := R)).matrixGauge_inv g A

theorem regularGauge_inv_eq_iff {g : GeneralLinearGroup n R⟦X⟧} {A B : Matrix n n R⟦X⟧} :
    g⁻¹.regularGauge B = A ↔ g.regularGauge A = B :=
  (derivative (R := R)).matrixGauge_inv_eq_iff

/-- `g.regularGauge A = B` if and only if `g` solves `g.map d⁄dX = g * A - B * g`. -/
theorem regularGauge_eq_iff {g : GeneralLinearGroup n R⟦X⟧} {A B : Matrix n n R⟦X⟧} :
    g.regularGauge A = B ↔
      (g : Matrix n n R⟦X⟧).map d⁄dX =
        (g : Matrix n n R⟦X⟧) * A - B * (g : Matrix n n R⟦X⟧) :=
  (derivative (R := R)).matrixGauge_eq_iff

/-- **Base change of `regularGauge`** along any ring homomorphism `f : R →+* S`. -/
theorem map_regularGauge {S : Type*} [CommRing S] (f : R →+* S)
    (g : GeneralLinearGroup n R⟦X⟧) (A : Matrix n n R⟦X⟧) :
    (g.regularGauge A).map (PowerSeries.map f) =
      (g.map (PowerSeries.map f)).regularGauge (A.map (PowerSeries.map f)) :=
  (derivative (R := R)).map_matrixGauge (derivative (R := S))
    (fun p => (PowerSeries.derivative_map p f).symm) g A

/-- **Stabilizer subgroup** of a connection matrix `A` under `regularGauge`. -/
noncomputable def regularGaugeStabilizer (A : Matrix n n R⟦X⟧) :
    Subgroup (GeneralLinearGroup n R⟦X⟧) where
  carrier := {g | g.regularGauge A = A}
  mul_mem' {h g} hh hg := by rw [Set.mem_ofPred_eq, regularGauge_mul, hg, hh]
  one_mem' := regularGauge_one A
  inv_mem' {g} hg := regularGauge_inv_eq_iff.mpr hg

@[simp]
theorem mem_regularGaugeStabilizer_iff {A : Matrix n n R⟦X⟧} {g : GeneralLinearGroup n R⟦X⟧} :
    g ∈ regularGaugeStabilizer A ↔ g.regularGauge A = A :=
  Iff.rfl

end Gauge

section TorsionFree

variable {n R : Type*} [CommRing R] [HasUniqueDiv R] [Fintype n] [DecidableEq n]

/-- **Uniqueness of regular formal gauge transformations with prescribed constant term.** Whenever
`[HasUniqueDiv R]` holds (e.g. `R = ℤ` or any `ℚ`-algebra), taking the constant-term matrix at
`X = 0` is injective on gauge transformations carrying `A` to `B`. -/
theorem regularGauge_constantCoeff_injective (A B : Matrix n n R⟦X⟧) :
    Function.Injective
      (fun g : {g : GeneralLinearGroup n R⟦X⟧ // g.regularGauge A = B} =>
        g.1.map (constantCoeff (R := R))) := by
  rintro ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩ h0
  refine Subtype.ext (Units.ext ?_)
  refine Matrix.eq_of_map_derivative_eq_mul_sub_mul_of_map_constantCoeff_eq
    (regularGauge_eq_iff.mp hg₁) (regularGauge_eq_iff.mp hg₂) ?_
  exact Matrix.ext fun i j => congrArg (fun u : GeneralLinearGroup n R => u i j) h0

/-- **Constant determinant for equal-trace regular gauge transformations.** If
`g.regularGauge A = B` and `A.trace = B.trace`, then `(g : Matrix n n R⟦X⟧).det` is the constant
power series given by the determinant of `g` at `X = 0`. -/
theorem det_eq_C_of_regularGauge_eq {g : GeneralLinearGroup n R⟦X⟧} {A B : Matrix n n R⟦X⟧}
    (hg : g.regularGauge A = B) (htr : A.trace = B.trace) :
    (g : Matrix n n R⟦X⟧).det = C ((g.map constantCoeff : GeneralLinearGroup n R) :
      Matrix n n R).det := by
  refine PowerSeries.derivative.ext ?_ ?_
  · rw [(derivative (R := R)).leibniz_det_eq_zero_of_matrixGauge_eq hg htr, derivative_C]
  · rw [constantCoeff_C, RingHom.map_det]
    rfl

/-- Under `g.regularGauge A = B` and `A.trace = B.trace`, `g` has determinant `1` over `R⟦X⟧`
(hence defines an `SL_n(R⟦X⟧)` gauge transformation) if and only if its constant term at `X = 0` has
determinant `1` over `R`. -/
theorem det_eq_one_iff_of_regularGauge_eq {g : GeneralLinearGroup n R⟦X⟧} {A B : Matrix n n R⟦X⟧}
    (hg : g.regularGauge A = B) (htr : A.trace = B.trace) :
    (g : Matrix n n R⟦X⟧).det = 1 ↔
      ((g.map constantCoeff : GeneralLinearGroup n R) : Matrix n n R).det = 1 := by
  rw [det_eq_C_of_regularGauge_eq hg htr]
  exact ⟨fun h => by simpa using congrArg constantCoeff h, fun h => by rw [h, map_one]⟩

end TorsionFree

section Classification

variable {n R : Type*} [CommRing R] [Algebra ℚ R] [Fintype n] [DecidableEq n]

/-- **Unique gauge transformation with prescribed constant-term fibre.** Over a `ℚ`-algebra `R`,
`regularGaugeOfConstantCoeff A B g₀` is the unique `g : GL n R⟦X⟧` carrying `A` to `B` under
`regularGauge` with `g.map constantCoeff = g₀`. -/
noncomputable def regularGaugeOfConstantCoeff (A B : Matrix n n R⟦X⟧)
    (g₀ : GeneralLinearGroup n R) : GeneralLinearGroup n R⟦X⟧ where
  val := Matrix.sylvesterSeries A B (g₀ : Matrix n n R)
  inv := Matrix.sylvesterSeries B A (↑g₀⁻¹ : Matrix n n R)
  val_inv := by rw [Matrix.sylvesterSeries_mul, Units.mul_inv, Matrix.sylvesterSeries_self_one]
  inv_val := by rw [Matrix.sylvesterSeries_mul, Units.inv_mul, Matrix.sylvesterSeries_self_one]

@[simp]
theorem coe_regularGaugeOfConstantCoeff (A B : Matrix n n R⟦X⟧)
    (g₀ : GeneralLinearGroup n R) :
    (regularGaugeOfConstantCoeff A B g₀ : Matrix n n R⟦X⟧) =
      Matrix.sylvesterSeries A B (g₀ : Matrix n n R) :=
  (rfl)

@[simp]
theorem regularGaugeOfConstantCoeff_inv (A B : Matrix n n R⟦X⟧)
    (g₀ : GeneralLinearGroup n R) :
    (regularGaugeOfConstantCoeff A B g₀)⁻¹ = regularGaugeOfConstantCoeff B A g₀⁻¹ :=
  Units.ext rfl

@[simp]
theorem regularGauge_regularGaugeOfConstantCoeff (A B : Matrix n n R⟦X⟧)
    (g₀ : GeneralLinearGroup n R) :
    (regularGaugeOfConstantCoeff A B g₀).regularGauge A = B :=
  regularGauge_eq_iff.mpr (Matrix.map_derivative_sylvesterSeries A B (g₀ : Matrix n n R))

@[simp]
theorem map_constantCoeff_regularGaugeOfConstantCoeff (A B : Matrix n n R⟦X⟧)
    (g₀ : GeneralLinearGroup n R) :
    (regularGaugeOfConstantCoeff A B g₀).map (constantCoeff (R := R)) = g₀ :=
  Units.ext (Matrix.map_constantCoeff_sylvesterSeries A B (g₀ : Matrix n n R))

@[simp]
theorem regularGaugeOfConstantCoeff_self_one (A : Matrix n n R⟦X⟧) :
    regularGaugeOfConstantCoeff A A 1 = 1 :=
  Units.ext (Matrix.sylvesterSeries_self_one A)

/-- **Groupoid composition law for `regularGaugeOfConstantCoeff`.** Composing the gauge
transformation from `A` to `B` over `g₀` with that from `B` to `C` over `h₀` yields the gauge
transformation from `A` to `C` over `h₀ * g₀`. -/
theorem regularGaugeOfConstantCoeff_mul (A B C : Matrix n n R⟦X⟧)
    (h₀ g₀ : GeneralLinearGroup n R) :
    regularGaugeOfConstantCoeff B C h₀ * regularGaugeOfConstantCoeff A B g₀ =
      regularGaugeOfConstantCoeff A C (h₀ * g₀) :=
  Units.ext (Matrix.sylvesterSeries_mul A B C (h₀ : Matrix n n R) (g₀ : Matrix n n R))

/-- **Base change of `regularGaugeOfConstantCoeff`** along any ring homomorphism `f : R →+* S`
between `ℚ`-algebras. -/
theorem map_regularGaugeOfConstantCoeff {S : Type*} [CommRing S] [Algebra ℚ S] (f : R →+* S)
    (A B : Matrix n n R⟦X⟧) (g₀ : GeneralLinearGroup n R) :
    (regularGaugeOfConstantCoeff A B g₀).map (PowerSeries.map f) =
      regularGaugeOfConstantCoeff (A.map (PowerSeries.map f)) (B.map (PowerSeries.map f))
        (g₀.map f) :=
  Units.ext (Matrix.map_sylvesterSeries f A B (g₀ : Matrix n n R))

/-- Uniqueness characterization of `regularGaugeOfConstantCoeff`:
`g = regularGaugeOfConstantCoeff A B g₀` if and only if `g.regularGauge A = B` and
`g.map constantCoeff = g₀`. -/
theorem eq_regularGaugeOfConstantCoeff_iff {A B : Matrix n n R⟦X⟧}
    {g : GeneralLinearGroup n R⟦X⟧} {g₀ : GeneralLinearGroup n R} :
    g = regularGaugeOfConstantCoeff A B g₀ ↔
      g.regularGauge A = B ∧ g.map (constantCoeff (R := R)) = g₀ := by
  have : HasUniqueDiv R := .of_module_rat R
  refine ⟨?_, fun ⟨hg, h0⟩ => ?_⟩
  · rintro rfl
    exact ⟨regularGauge_regularGaugeOfConstantCoeff A B g₀,
      map_constantCoeff_regularGaugeOfConstantCoeff A B g₀⟩
  · have hinj := regularGauge_constantCoeff_injective A B
      (a₁ := ⟨g, hg⟩)
      (a₂ := ⟨regularGaugeOfConstantCoeff A B g₀, regularGauge_regularGaugeOfConstantCoeff A B g₀⟩)
      (h0.trans (map_constantCoeff_regularGaugeOfConstantCoeff A B g₀).symm)
    exact congrArg Subtype.val hinj

/-- **Equivalence between gauge transformations `A ↦ B` and constant-term fibre automorphisms
`GL n R`.** Over any `ℚ`-algebra `R` (possibly nonreduced), evaluating at `X = 0` identifies
`{g : GL n R⟦X⟧ // g.regularGauge A = B}` with `GL n R`. -/
noncomputable def regularGaugeEquivConstantCoeff (A B : Matrix n n R⟦X⟧) :
    {g : GeneralLinearGroup n R⟦X⟧ // g.regularGauge A = B} ≃ GeneralLinearGroup n R where
  toFun g := g.1.map (constantCoeff (R := R))
  invFun g₀ := ⟨regularGaugeOfConstantCoeff A B g₀, regularGauge_regularGaugeOfConstantCoeff A B g₀⟩
  left_inv g := Subtype.ext ((eq_regularGaugeOfConstantCoeff_iff.mpr ⟨g.2, rfl⟩).symm)
  right_inv g₀ := map_constantCoeff_regularGaugeOfConstantCoeff A B g₀

@[simp]
theorem regularGaugeEquivConstantCoeff_apply (A B : Matrix n n R⟦X⟧)
    (g : {g : GeneralLinearGroup n R⟦X⟧ // g.regularGauge A = B}) :
    regularGaugeEquivConstantCoeff A B g = g.1.map (constantCoeff (R := R)) :=
  (rfl)

@[simp]
theorem coe_regularGaugeEquivConstantCoeff_symm (A B : Matrix n n R⟦X⟧)
    (g₀ : GeneralLinearGroup n R) :
    ((regularGaugeEquivConstantCoeff A B).symm g₀ : GeneralLinearGroup n R⟦X⟧) =
      regularGaugeOfConstantCoeff A B g₀ :=
  (rfl)

/-- **Regular formal connections are determined by their fibre at `X = 0`**
(Frenkel–Gaitsgory, Lemma 4.4.2): over any `ℚ`-algebra `R`, possibly nonreduced, for any two
connection matrices `A, B : Matrix n n R⟦X⟧`, taking the constant term is a bijection from gauge
transformations carrying `A` to `B` onto `GL n R`. -/
theorem regularGauge_constantCoeff_bijective (A B : Matrix n n R⟦X⟧) :
    Function.Bijective
      (fun g : {g : GeneralLinearGroup n R⟦X⟧ // g.regularGauge A = B} =>
        g.1.map (constantCoeff (R := R))) :=
  (regularGaugeEquivConstantCoeff A B).bijective

/-- **Stabilizer group isomorphism for a regular formal connection.** Over a `ℚ`-algebra `R`,
evaluating at `X = 0` is a group isomorphism from the gauge stabilizer of `A` onto `GL n R`. -/
noncomputable def regularGaugeStabilizerMulEquiv (A : Matrix n n R⟦X⟧) :
    regularGaugeStabilizer A ≃* GeneralLinearGroup n R :=
  { regularGaugeEquivConstantCoeff A A with
    map_mul' h g := (GeneralLinearGroup.map (constantCoeff (R := R))).map_mul h.1 g.1 }

@[simp]
theorem regularGaugeStabilizerMulEquiv_apply (A : Matrix n n R⟦X⟧)
    (g : regularGaugeStabilizer A) :
    regularGaugeStabilizerMulEquiv A g = g.1.map (constantCoeff (R := R)) :=
  (rfl)

@[simp]
theorem coe_regularGaugeStabilizerMulEquiv_symm (A : Matrix n n R⟦X⟧)
    (g₀ : GeneralLinearGroup n R) :
    ((regularGaugeStabilizerMulEquiv A).symm g₀ : GeneralLinearGroup n R⟦X⟧) =
      regularGaugeOfConstantCoeff A A g₀ :=
  (rfl)

end Classification

section Examples

/-- **Rank-one exponential horizontal frame.** On `1 × 1` matrices (`n = Unit`) over a `ℚ`-algebra
`R`, the unique gauge transformation carrying `1` to `0` with constant term `g₀` has entry
`C (g₀ () ()) * PowerSeries.exp R`. -/
theorem regularGaugeOfConstantCoeff_unit_one_zero_apply {R : Type*} [CommRing R] [Algebra ℚ R]
    (g₀ : GeneralLinearGroup Unit R) :
    regularGaugeOfConstantCoeff (1 : Matrix Unit Unit R⟦X⟧) 0 g₀ () () =
      C (g₀ () ()) * PowerSeries.exp R := by
  have hM : Matrix.sylvesterSeries (1 : Matrix Unit Unit R⟦X⟧) 0 (g₀ : Matrix Unit Unit R) =
      Matrix.of fun _ _ => C (g₀ () ()) * PowerSeries.exp R := by
    symm
    rw [Matrix.eq_sylvesterSeries_iff]
    exact ⟨Matrix.ext fun ⟨⟩ ⟨⟩ => by simp [PowerSeries.derivative_exp],
      Matrix.ext fun ⟨⟩ ⟨⟩ => by simp⟩
  exact congrArg (fun M : Matrix Unit Unit R⟦X⟧ => M () ()) hM

private theorem unipotentLinearGauge_mul_eq_one {n R : Type*} [CommRing R]
    [Fintype n] [DecidableEq n] {f : R⟦X⟧} (hf : f * f = 0) :
    (1 + f • (1 : Matrix n n R⟦X⟧)) * (1 - f • (1 : Matrix n n R⟦X⟧)) = 1 := by
  simp only [mul_sub, add_mul, one_mul, mul_one, Matrix.mul_smul, smul_smul, hf, zero_smul]
  abel

/-- Unipotent linear frame `1 + (C ε * X) • 1` associated to a square-zero scalar `ε` (`ε * ε = 0`)
over any commutative ring `R`. -/
noncomputable def unipotentLinearGauge {n R : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    {ε : R} (hε : ε * ε = 0) : GeneralLinearGroup n R⟦X⟧ where
  val := 1 + (C ε * X : R⟦X⟧) • (1 : Matrix n n R⟦X⟧)
  inv := 1 - (C ε * X : R⟦X⟧) • (1 : Matrix n n R⟦X⟧)
  val_inv := unipotentLinearGauge_mul_eq_one <| by
    calc (C ε * X : R⟦X⟧) * (C ε * X) = C (ε * ε) * (X * X) := by rw [map_mul]; ring
      _ = 0 := by simp [hε]
  inv_val := by
    simpa [sub_eq_add_neg, neg_smul] using
      unipotentLinearGauge_mul_eq_one (n := n) (f := -(C ε * X : R⟦X⟧)) <| by
        calc (-(C ε * X : R⟦X⟧)) * -(C ε * X) = C (ε * ε) * (X * X) := by rw [map_mul]; ring
          _ = 0 := by simp [hε]

@[simp]
theorem coe_unipotentLinearGauge {n R : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    {ε : R} (hε : ε * ε = 0) :
    (unipotentLinearGauge (n := n) hε : Matrix n n R⟦X⟧) =
      1 + (C ε * X : R⟦X⟧) • (1 : Matrix n n R⟦X⟧) :=
  (rfl)

/-- Over any commutative ring `R`, for a square-zero element `ε` (`ε * ε = 0`), the unipotent frame
`g₀.map C * (1 + (C ε * X) • 1)` gauges `Matrix.scalar n (C ε)` to `0`. -/
theorem regularGauge_map_C_mul_unipotentLinearGauge {n R : Type*} [CommRing R]
    [Fintype n] [DecidableEq n] {ε : R} (hε : ε * ε = 0) (g₀ : GeneralLinearGroup n R) :
    (g₀.map C * unipotentLinearGauge hε).regularGauge (Matrix.scalar n (C ε)) = 0 := by
  rw [regularGauge_eq_iff, Units.val_mul, (derivative (R := R)).map_matrix_mul]
  have hC : ((g₀.map C : GeneralLinearGroup n R⟦X⟧) : Matrix n n R⟦X⟧).map d⁄dX = 0 :=
    Matrix.ext fun i j => by simp
  have hu : (unipotentLinearGauge (n := n) hε : Matrix n n R⟦X⟧).map d⁄dX =
      (C ε : R⟦X⟧) • (1 : Matrix n n R⟦X⟧) :=
    Matrix.ext fun i j => by
      by_cases hij : i = j <;> simp [hij]
  have hsq : (C ε * X : R⟦X⟧) * C ε = 0 := by
    calc
      (C ε * X : R⟦X⟧) * C ε = C (ε * ε) * X := by rw [map_mul]; ring
      _ = 0 := by simp [hε]
  have hsc : Matrix.scalar n (C ε : R⟦X⟧) = (C ε : R⟦X⟧) • (1 : Matrix n n R⟦X⟧) :=
    Matrix.ext fun i j => by
      by_cases hij : i = j <;> simp [hij]
  rw [hC, hu, Matrix.zero_mul, zero_add, Matrix.zero_mul, sub_zero, coe_unipotentLinearGauge, hsc,
    Matrix.mul_assoc]
  congr 1
  rw [add_mul, one_mul, Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul, hsq, zero_smul,
    add_zero]

/-- **Horizontal frame over nonreduced `ℚ`-algebras** (such as `DualNumber ℚ` with
`ε = DualNumber.eps`): for `ε * ε = 0`, the unique gauge transformation carrying
`Matrix.scalar n (C ε)` to `0` with constant term `g₀` is `g₀.map C * (1 + (C ε * X) • 1)`. -/
theorem regularGaugeOfConstantCoeff_scalar_sq_zero {n R : Type*} [CommRing R] [Algebra ℚ R]
    [Fintype n] [DecidableEq n] {ε : R} (hε : ε * ε = 0) (g₀ : GeneralLinearGroup n R) :
    regularGaugeOfConstantCoeff (Matrix.scalar n (C ε)) 0 g₀ =
      g₀.map C * unipotentLinearGauge hε := by
  symm
  rw [eq_regularGaugeOfConstantCoeff_iff]
  refine ⟨regularGauge_map_C_mul_unipotentLinearGauge hε g₀, ?_⟩
  rw [map_mul]
  have hg₀ : (g₀.map (C (R := R))).map (constantCoeff (R := R)) = g₀ :=
    Units.ext <| Matrix.ext fun i j => by simp
  have hu : (unipotentLinearGauge (n := n) hε).map (constantCoeff (R := R)) = 1 :=
    Units.ext <| Matrix.ext fun i j => by
      by_cases hij : i = j <;> simp [hij]
  rw [hg₀, hu, mul_one]

/-- **Failure of constant-term uniqueness in positive characteristic.** Over a commutative ring `R`
of characteristic `p > 1` and nonempty index type `n`, the scalar matrix `(1 + X ^ p) • 1` in
`GL n R⟦X⟧` gauges `0` to `0` and has constant term `1`, yet is distinct from `1`. -/
theorem exists_regularGauge_zero_eq_zero_of_charP
    {n R : Type*} [CommRing R] [Fintype n] [DecidableEq n] [Nonempty n]
    (p : ℕ) [CharP R p] (hp : 1 < p) :
    ∃ g : GeneralLinearGroup n R⟦X⟧,
      g.regularGauge 0 = 0 ∧ g.map (constantCoeff (R := R)) = 1 ∧ g ≠ 1 := by
  have : Nontrivial R := CharP.nontrivial_of_char_ne_one (by omega)
  have hp0 : p ≠ 0 := by omega
  have hu : IsUnit (1 + X ^ p : R⟦X⟧) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [hp0])
  have hd : d⁄dX (1 + X ^ p : R⟦X⟧) = 0 := by
    rw [map_add, derivative_one, derivative_X_pow, CharP.cast_eq_zero, map_zero, zero_mul,
      add_zero]
  refine ⟨GeneralLinearGroup.scalar n hu.unit, ?_, ?_, ?_⟩
  · have hsc : (Matrix.scalar n (hu.unit : R⟦X⟧)).map d⁄dX = 0 := by
      simp [Matrix.scalar_apply, IsUnit.unit_spec, hd]
    rw [regularGauge_eq_iff, GeneralLinearGroup.coe_scalar, hsc, Matrix.mul_zero,
      Matrix.zero_mul, sub_self]
  · refine Units.ext <| Matrix.ext fun i j => ?_
    by_cases hij : i = j <;> simp [hij, hp0]
  · intro h
    obtain ⟨i⟩ := ‹Nonempty n›
    have hcoeff := congrArg (fun u : GeneralLinearGroup n R⟦X⟧ => coeff p (u i i)) h
    simp [hp0] at hcoeff

end Examples

end GeneralLinearGroup

end Matrix
