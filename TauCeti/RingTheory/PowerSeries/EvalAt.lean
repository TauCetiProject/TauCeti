/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.RingTheory.PowerSeries.GaussNorm

/-!
# Evaluation of power series as infinite sums

For a power series `f = ∑ aₙ Xⁿ` over a commutative ring `R` and an element `b` of an `R`-algebra
`A` with a topology, `PowerSeries.evalAt f b` is the infinite sum `∑ₙ aₙ • bⁿ`, with the junk
value `0` when the sum does not converge. The algebra `A` need not be commutative: the scalars
`aₙ` act centrally, so the values of `f` at `b` commute with `b`.

Unlike Mathlib's `PowerSeries.aeval`, which evaluates every power series at a topologically
nilpotent point of a complete linearly topologized algebra, `evalAt` makes sense at every point;
it is meaningful for series whose coefficients decay fast enough, such as entire series over a
normed ring (`TauCeti.RingTheory.PowerSeries.Entire.Eval`). This file records the values of
`evalAt` that need no convergence hypothesis. In an ultrametric normed algebra, `‖f(b)‖` is
bounded by the Gauss norm of `f` at every radius `r ≥ ‖b‖` at which that Gauss norm is defined.

A power series `F = ∑ Fₙ Xⁿ` whose coefficients lie in a ring `A` acted on by `R`, such as a series
of operators, is instead evaluated at a scalar `a : R`: `PowerSeries.evalScalar F a` is the
infinite sum `∑ₙ aⁿ • Fₙ`.

Over a field `𝕜`, the same sum is Mathlib's `FormalMultilinearSeries.ofScalarsSum`
(`PowerSeries.evalAt_eq_ofScalarsSum`); that construction needs a field of scalars, while the
coefficient rings here may have nilpotents.

## Main definitions

* `PowerSeries.evalAt`: the value `∑ₙ aₙ • bⁿ` of a power series at `b`.
* `PowerSeries.evalScalar`: the value `∑ₙ aⁿ • Fₙ` of a power series at a scalar `a`.

## Main results

* `PowerSeries.evalAt_coe`: on polynomials, `evalAt` is `Polynomial.aeval`.
* `PowerSeries.evalAt_map_algebraMap`: evaluation is compatible with extension of scalars.
* `PowerSeries.evalAt_rescale`: rescaling the variable rescales the point of evaluation.
* `PowerSeries.commute_evalAt`: the values of a series at `b` commute with `b`.
* `PowerSeries.norm_evalAt_le_gaussNorm`: the Gauss-norm bound in an ultrametric algebra.
* `PowerSeries.evalScalar_monomial`, `PowerSeries.evalScalar_at_zero`,
  `PowerSeries.evalScalar_add`: evaluation at a scalar of monomials, at the scalar `0`, and of
  sums.
* `PowerSeries.commute_evalScalar`: an element commuting with the coefficients of a series
  commutes with its value at a scalar.
* `PowerSeries.norm_evalScalar_le`: in an ultrametric ring, a uniform bound `c ≥ 0` on
  `‖a‖ ^ n * ‖Fₙ‖` bounds `‖F(a)‖`.
-/

public section

namespace PowerSeries

section Semiring

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [TopologicalSpace A]

/-- The value `f(b) = ∑ₙ aₙ • bⁿ` of the power series `f = ∑ aₙ Xⁿ` at an element `b` of a
topological `R`-algebra, defined as an infinite sum. It takes the junk value `0` when the sum does
not converge; for entire `f` over a normed ring it converges in every complete normed algebra
(`PowerSeries.IsEntire.hasSum_evalAt`). -/
noncomputable def evalAt (f : R⟦X⟧) (b : A) : A :=
  ∑' n, coeff n f • b ^ n

/-- The value `f(b)` is the infinite sum `∑ₙ aₙ • bⁿ`. -/
theorem evalAt_def (f : R⟦X⟧) (b : A) : f.evalAt b = ∑' n, coeff n f • b ^ n :=
  (rfl)

/-- On polynomials, evaluation is `Polynomial.aeval`. -/
@[simp]
theorem evalAt_coe (p : Polynomial R) (b : A) : (p : R⟦X⟧).evalAt b = Polynomial.aeval b p := by
  rw [evalAt_def, tsum_eq_sum (s := Finset.range (p.natDegree + 1)),
    Polynomial.aeval_eq_sum_range]
  · simp
  · intro n hn
    rw [Finset.mem_range, not_lt] at hn
    simp [Polynomial.coeff_eq_zero_of_natDegree_lt hn]

/-- The zero series evaluates to zero. -/
@[simp]
theorem evalAt_zero (b : A) : (0 : R⟦X⟧).evalAt b = 0 := by
  simpa using evalAt_coe (0 : Polynomial R) b

/-- A constant series evaluates to its constant, mapped into the algebra. -/
@[simp]
theorem evalAt_C (a : R) (b : A) : (C a).evalAt b = algebraMap R A a := by
  simpa using evalAt_coe (Polynomial.C a) b

/-- The series `1` evaluates to `1`. -/
@[simp]
theorem evalAt_one (b : A) : (1 : R⟦X⟧).evalAt b = 1 := by
  simpa using evalAt_coe (1 : Polynomial R) b

/-- The variable `X` evaluates to the point of evaluation. -/
@[simp]
theorem evalAt_X (b : A) : (X : R⟦X⟧).evalAt b = b := by
  simpa using evalAt_coe (Polynomial.X : Polynomial R) b

/-- The monomial `a Xⁿ` evaluates to `a • bⁿ`. -/
@[simp]
theorem evalAt_monomial (n : ℕ) (a : R) (b : A) : (monomial n a).evalAt b = a • b ^ n := by
  simpa [Algebra.smul_def] using evalAt_coe (Polynomial.monomial n a) b

/-- At the point `0`, a power series evaluates to its constant coefficient. -/
@[simp]
theorem evalAt_at_zero (f : R⟦X⟧) : f.evalAt (0 : A) = algebraMap R A (constantCoeff f) := by
  rw [evalAt_def, tsum_eq_single 0 fun n hn ↦ by simp [zero_pow hn]]
  simp [Algebra.smul_def]

/-- Evaluation is compatible with extension of scalars: mapping the coefficients along
`R → S` does not change the value at a point of an `S`-algebra. -/
@[simp]
theorem evalAt_map_algebraMap {S : Type*} [CommSemiring S] [Algebra R S] [Algebra S A]
    [IsScalarTower R S A] (f : R⟦X⟧) (b : A) : (map (algebraMap R S) f).evalAt b = f.evalAt b := by
  simp [evalAt_def]

/-- Rescaling the variable by `a` evaluates at the rescaled point: `f(a X)` at `b` is
`f(a • b)`. -/
@[simp]
theorem evalAt_rescale (f : R⟦X⟧) (a : R) (b : A) :
    (rescale a f).evalAt b = f.evalAt (a • b) := by
  simp only [evalAt_def, coeff_rescale, smul_pow, mul_comm (a ^ _), mul_smul]

/-- Over a field, `evalAt` is the sum `FormalMultilinearSeries.ofScalarsSum` of the scalar
series with the same coefficients. -/
theorem evalAt_eq_ofScalarsSum {𝕜 E : Type*} [Field 𝕜] [Ring E] [Algebra 𝕜 E]
    [TopologicalSpace E] [IsTopologicalRing E] (f : 𝕜⟦X⟧) (x : E) :
    f.evalAt x = FormalMultilinearSeries.ofScalarsSum (E := E) (fun n ↦ coeff n f) x :=
  (FormalMultilinearSeries.ofScalars_sum_eq _ x).symm

/-- The values of a series at `b` commute with `b`. -/
theorem commute_evalAt [IsTopologicalSemiring A] [T2Space A] (f : R⟦X⟧) (b : A) :
    Commute b (f.evalAt b) :=
  Commute.tsum_right _ fun n ↦ ((Commute.refl b).pow_right n).smul_right _

end Semiring

section Ring

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [T2Space A]

/-- Evaluation commutes with negation. -/
@[simp]
theorem evalAt_neg (f : R⟦X⟧) (b : A) : (-f).evalAt b = -f.evalAt b := by
  simp [evalAt_def, neg_smul, tsum_neg]

end Ring

section Scalar

variable {R A : Type*} [Monoid R] [Semiring A] [SMul R A] [TopologicalSpace A]

/-- The value `F(a) = ∑ₙ aⁿ • Fₙ` at a scalar `a : R` of a power series `F = ∑ Fₙ Xⁿ` whose
coefficients lie in a topological semiring `A` acted on by `R`, defined as an infinite sum. Unlike
`PowerSeries.evalAt`, the coefficients need not be scalars, so this evaluates series of operators
at scalars. It takes the junk value `0` when the sum does not converge; for entire `F` over a
complete normed ring it converges at every `a` (`PowerSeries.IsEntire.hasSum_evalScalar`). -/
noncomputable def evalScalar (F : A⟦X⟧) (a : R) : A :=
  ∑' n, a ^ n • coeff n F

/-- The value `F(a)` at a scalar is the infinite sum `∑ₙ aⁿ • Fₙ`. -/
theorem evalScalar_def (F : A⟦X⟧) (a : R) : F.evalScalar a = ∑' n, a ^ n • coeff n F :=
  (rfl)

/-- An element commuting with every coefficient of a series commutes with its value at a
scalar. -/
theorem commute_evalScalar [IsTopologicalSemiring A] [T2Space A] [SMulCommClass R A A]
    [IsScalarTower R A A] {b : A} {F : A⟦X⟧} (h : ∀ n, Commute b (coeff n F)) (a : R) :
    Commute b (F.evalScalar a) :=
  Commute.tsum_right _ fun n ↦ (h n).smul_right _

end Scalar

section ScalarAction

variable {R A : Type*} [Monoid R] [Semiring A] [DistribMulAction R A] [TopologicalSpace A]

/-- The zero series evaluates to zero at every scalar. -/
@[simp]
theorem evalScalar_zero (a : R) : (0 : A⟦X⟧).evalScalar a = 0 := by
  simp [evalScalar_def]

/-- The monomial `c Xⁿ` evaluates to `aⁿ • c` at the scalar `a`. -/
@[simp]
theorem evalScalar_monomial (n : ℕ) (c : A) (a : R) :
    (monomial n c).evalScalar a = a ^ n • c := by
  rw [evalScalar_def, tsum_eq_single n fun m hm ↦ by simp [coeff_monomial, hm]]
  simp

/-- A constant series evaluates to its constant at every scalar. -/
@[simp]
theorem evalScalar_C (c : A) (a : R) : (C c).evalScalar a = c := by
  simpa using evalScalar_monomial 0 c a

/-- The variable `X` evaluates to `a • 1` at the scalar `a`. -/
@[simp]
theorem evalScalar_X (a : R) : (X : A⟦X⟧).evalScalar a = a • 1 := by
  rw [X_eq, evalScalar_monomial, pow_one]

/-- The series `1` evaluates to `1` at every scalar. -/
@[simp]
theorem evalScalar_one (a : R) : (1 : A⟦X⟧).evalScalar a = 1 := by
  simpa using evalScalar_C (1 : A) a

/-- Evaluation at a scalar is additive on series whose defining sums converge there. -/
theorem evalScalar_add [ContinuousAdd A] [T2Space A] {F G : A⟦X⟧} {a : R}
    (hF : Summable fun n ↦ a ^ n • coeff n F) (hG : Summable fun n ↦ a ^ n • coeff n G) :
    (F + G).evalScalar a = F.evalScalar a + G.evalScalar a := by
  simp only [evalScalar_def, map_add, smul_add]
  exact hF.tsum_add hG

end ScalarAction

section ScalarZero

variable {R A : Type*} [MonoidWithZero R] [Semiring A] [MulActionWithZero R A]
  [TopologicalSpace A]

/-- At the scalar `0`, a power series evaluates to its constant coefficient. -/
@[simp]
theorem evalScalar_at_zero (F : A⟦X⟧) : F.evalScalar (0 : R) = constantCoeff F := by
  rw [evalScalar_def, tsum_eq_single 0 fun n hn ↦ by simp [zero_pow hn]]
  simp

end ScalarZero

section ScalarRing

variable {R A : Type*} [Monoid R] [Ring A] [DistribMulAction R A] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [T2Space A]

/-- Evaluation at a scalar commutes with negation. -/
@[simp]
theorem evalScalar_neg (F : A⟦X⟧) (a : R) : (-F).evalScalar a = -F.evalScalar a := by
  simp [evalScalar_def, tsum_neg]

end ScalarRing

section Normed

variable {R A : Type*} [NormedCommRing R] [NormedRing A] [Algebra R A] [IsBoundedSMul R A]
  {f : R⟦X⟧}

/-- In an ultrametric normed algebra with `‖1‖ = 1`, the value of a series at a point `b` with
`‖b‖ ≤ r` is bounded by the Gauss norm of the series at the radius `r`, whenever the latter is
defined. This needs no convergence: the junk value `0` satisfies the bound too. -/
theorem norm_evalAt_le_gaussNorm [IsUltrametricDist A] [NormOneClass A] {r : ℝ}
    (hf : f.HasGaussNorm norm r) {b : A} (hb : ‖b‖ ≤ r) :
    ‖f.evalAt b‖ ≤ gaussNorm norm r f :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (gaussNorm_nonneg _ _ _ norm_nonneg)
    fun n ↦ (norm_smul_le _ _).trans <|
      (mul_le_mul_of_nonneg_left ((norm_pow_le b n).trans
        (pow_le_pow_left₀ (norm_nonneg b) hb n)) (norm_nonneg _)).trans <|
      le_gaussNorm _ _ _ hf n

/-- In an ultrametric normed ring, if `c ≥ 0` bounds `‖a‖ ^ n * ‖Fₙ‖` for every `n`, then it
bounds the value at the scalar `a` of the series `F = ∑ Fₙ Xⁿ`. This needs no convergence: the
junk value `0` satisfies the bound too. -/
theorem norm_evalScalar_le {R A : Type*} [SeminormedRing R] [NormedRing A] [Module R A]
    [IsBoundedSMul R A] [IsUltrametricDist A] {F : A⟦X⟧} {a : R} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ n, ‖a‖ ^ n * ‖coeff n F‖ ≤ c) : ‖F.evalScalar a‖ ≤ c := by
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hc fun n ↦ ?_
  -- `‖aⁿ‖ ≤ ‖a‖ⁿ` only holds for `n ≥ 1`, so the term of index `0` is treated separately
  cases n with
  | zero => simpa using h 0
  | succ n => exact (norm_smul_le _ _).trans <|
      (mul_le_mul_of_nonneg_right (norm_pow_le' a n.succ_pos) (norm_nonneg _)).trans (h _)

end Normed

end PowerSeries
