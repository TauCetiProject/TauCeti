/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.Data.Nat.Factorial.NatCast
public import Mathlib.LinearAlgebra.Matrix.Rank
public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.JetEvaluation

/-!
# Ordinary and Hasse jets below the characteristic

The ordinary derivative of order `k` is `k!` times the Hasse derivative of order `k`
(`Polynomial.factorial_smul_hasseDeriv`, `MvPolynomial.factorial_smul_hasseDeriv_single`). So
whenever `k!` is a unit, an ordinary jet vanishes exactly when the corresponding Hasse jet
vanishes, and the jet maps built from ordinary and from Hasse derivatives have the same kernel and
the same rank: the ordinary jet matrix is the Hasse jet matrix with row `i` scaled by the unit
`(k i)!`.

In a ring of prime characteristic `p` the factorial `k!` is a unit exactly when `k < p` (Mathlib
`IsUnit.natCast_factorial_iff_of_charP`), and over a field of characteristic zero it is always a
unit (Mathlib `IsUnit.natCast_factorial_of_algebra`). The results below take the unit hypothesis,
and the `_of_lt` forms specialise them to orders below the characteristic `p`. At `k = p` the
comparison fails: `D^p` kills every polynomial in characteristic `p`, while `D^[p] X^p = 1`.

## Main results

* `Polynomial.eval_iterate_derivative_eq_zero_iff`,
  `MvPolynomial.eval_iterate_pderiv_eq_zero_iff`: if `k!` is a unit, the ordinary jet of order `k`
  vanishes at a point if and only if the Hasse jet of order `k` does.
* `MvPolynomial.toMatrix_ordinaryJetEval_eq_diagonal_mul`: the ordinary jet matrix is
  `diagonal (fun i ↦ (k i)!)` times the Hasse jet matrix.
* `MvPolynomial.ker_ordinaryJetEval`, `MvPolynomial.rank_ordinaryJetEval`,
  `MvPolynomial.rank_toMatrix_ordinaryJetEval`: when every `(k i)!` is a unit, the ordinary and
  Hasse jet maps have the same kernel, the same rank, and matrices of the same rank.
* `MvPolynomial.ker_ordinaryJetEval_of_lt`, `MvPolynomial.rank_ordinaryJetEval_of_lt`,
  `MvPolynomial.rank_toMatrix_ordinaryJetEval_of_lt`: the same in characteristic `p` for orders
  `k i < p`.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53 (2004),
  §11.6, pp. 282–283: ordinary and Hasse derivatives in characteristic `p`.
-/

public section

open Finsupp Matrix Nat

namespace Polynomial

variable {R : Type*} [Semiring R] {k : ℕ}

/-- If `k!` is a unit, the `k`-th ordinary derivative of `f` vanishes exactly when the `k`-th
Hasse derivative does. -/
theorem iterate_derivative_eq_zero_iff (hk : IsUnit (k ! : R)) (f : R[X]) :
    derivative^[k] f = 0 ↔ hasseDeriv k f = 0 := by
  rw [← factorial_smul_hasseDeriv, LinearMap.smul_apply, ← Nat.cast_smul_eq_nsmul R,
    hk.smul_eq_zero]

/-- If `k!` is a unit, the ordinary jet `D^k f (a)` vanishes exactly when the Hasse jet
`D^[k] f (a)` does. -/
theorem eval_iterate_derivative_eq_zero_iff (hk : IsUnit (k ! : R)) (f : R[X]) (a : R) :
    (derivative^[k] f).eval a = 0 ↔ (hasseDeriv k f).eval a = 0 := by
  rw [← factorial_smul_hasseDeriv, LinearMap.smul_apply, eval_smul, nsmul_eq_mul,
    hk.mul_right_eq_zero]

/-- In characteristic `p`, for `k < p` the ordinary jet `D^k f (a)` vanishes exactly when the Hasse
jet `D^[k] f (a)` does. -/
theorem eval_iterate_derivative_eq_zero_iff_of_lt {R : Type*} [Ring R] (p : ℕ) [Fact p.Prime]
    [CharP R p] (hk : k < p) (f : R[X]) (a : R) :
    (derivative^[k] f).eval a = 0 ↔ (hasseDeriv k f).eval a = 0 :=
  eval_iterate_derivative_eq_zero_iff ((IsUnit.natCast_factorial_iff_of_charP p).2 hk) f a

end Polynomial

namespace MvPolynomial

variable {σ R ι : Type*}

section Pointwise

variable [CommSemiring R] {k : ℕ}

/-- If `k!` is a unit, the `k`-th ordinary partial derivative in the variable `i` vanishes exactly
when the Hasse derivative along `k • eᵢ` does. -/
theorem iterate_pderiv_eq_zero_iff (hk : IsUnit (k ! : R)) (i : σ) (f : MvPolynomial σ R) :
    (pderiv i)^[k] f = 0 ↔ hasseDeriv (single i k) f = 0 := by
  rw [← factorial_smul_hasseDeriv_single, ← Nat.cast_smul_eq_nsmul R, hk.smul_eq_zero]

/-- If `k!` is a unit, the ordinary jet `(∂ᵢ^k f)(a)` vanishes exactly when the Hasse jet
`(∂^[k • eᵢ] f)(a)` does. -/
theorem eval_iterate_pderiv_eq_zero_iff (hk : IsUnit (k ! : R)) (i : σ) (f : MvPolynomial σ R)
    (a : σ → R) : eval a ((pderiv i)^[k] f) = 0 ↔ eval a (hasseDeriv (single i k) f) = 0 := by
  rw [← factorial_smul_hasseDeriv_single, map_nsmul, nsmul_eq_mul, hk.mul_right_eq_zero]

/-- In characteristic `p`, for `k < p` the ordinary jet `(∂ᵢ^k f)(a)` vanishes exactly when the
Hasse jet `(∂^[k • eᵢ] f)(a)` does. -/
theorem eval_iterate_pderiv_eq_zero_iff_of_lt {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime]
    [CharP R p] (hk : k < p) (i : σ) (f : MvPolynomial σ R) (a : σ → R) :
    eval a ((pderiv i)^[k] f) = 0 ↔ eval a (hasseDeriv (single i k) f) = 0 :=
  eval_iterate_pderiv_eq_zero_iff ((IsUnit.natCast_factorial_iff_of_charP p).2 hk) i f a

end Pointwise

section JetMap

variable (s : Set (σ →₀ ℕ)) (v : ι → σ) (k : ι → ℕ)

/-- The matrix of the ordinary jet map is the diagonal matrix of the factorials `(k i)!` times the
Hasse jet matrix along the multi-indices `k i • eᵥ₍ᵢ₎`. -/
theorem toMatrix_ordinaryJetEval_eq_diagonal_mul [CommSemiring R] (a : ι → σ → R) [Fintype s]
    [Fintype ι] [DecidableEq s] [DecidableEq ι] :
    LinearMap.toMatrix (basisRestrictSupport R s) (Pi.basisFun R ι) (ordinaryJetEval s a v k) =
      diagonal (fun i ↦ ((k i)! : R)) * jetMatrix s a (fun i ↦ single (v i) (k i)) := by
  rw [toMatrix_ordinaryJetEval]
  ext i μ
  simp [diagonal_mul]

variable {k}

/-- When every `(k i)!` is a unit, the ordinary jet map and the Hasse jet map along the
multi-indices `k i • eᵥ₍ᵢ₎` have the same kernel. -/
theorem ker_ordinaryJetEval [CommSemiring R] (a : ι → σ → R) (hk : ∀ i, IsUnit ((k i)! : R)) :
    LinearMap.ker (ordinaryJetEval s a v k) =
      LinearMap.ker (jetEval s a fun i ↦ single (v i) (k i)) := by
  ext f
  simp only [LinearMap.mem_ker, funext_iff, Pi.zero_apply,
    ordinaryJetEval_apply_eq_factorial_mul, (hk _).mul_right_eq_zero]

/-- When every `(k i)!` is a unit, the ordinary jet map is the Hasse jet map along the
multi-indices `k i • eᵥ₍ᵢ₎` followed by the invertible scaling of coordinate `i` by `(k i)!`. -/
theorem ordinaryJetEval_eq_comp [CommSemiring R] (a : ι → σ → R)
    (hk : ∀ i, IsUnit ((k i)! : R)) :
    ordinaryJetEval s a v k =
      (LinearEquiv.piCongrRight fun i ↦ LinearEquiv.smulOfUnit (hk i).unit).toLinearMap ∘ₗ
        jetEval s a (fun i ↦ single (v i) (k i)) := by
  ext f i
  rw [LinearMap.comp_apply, ordinaryJetEval_apply_eq_factorial_mul]
  simp [LinearEquiv.smulOfUnit, Units.smul_def]

/-- When every `(k i)!` is a unit, the ordinary jet map and the Hasse jet map along the
multi-indices `k i • eᵥ₍ᵢ₎` have the same rank. -/
theorem rank_ordinaryJetEval [CommSemiring R] (a : ι → σ → R) (hk : ∀ i, IsUnit ((k i)! : R)) :
    (ordinaryJetEval s a v k).rank = (jetEval s a fun i ↦ single (v i) (k i)).rank := by
  rw [ordinaryJetEval_eq_comp s v a hk, LinearMap.rank, LinearMap.range_comp,
    LinearEquiv.rank_map_eq]

/-- When every `(k i)!` is a unit, the matrices of the ordinary jet map and of the Hasse jet map
along the multi-indices `k i • eᵥ₍ᵢ₎` have the same rank. -/
theorem rank_toMatrix_ordinaryJetEval [CommRing R] (a : ι → σ → R) [Fintype s] [Finite ι]
    [DecidableEq s] (hk : ∀ i, IsUnit ((k i)! : R)) :
    (LinearMap.toMatrix (basisRestrictSupport R s) (Pi.basisFun R ι)
        (ordinaryJetEval s a v k)).rank =
      (jetMatrix s a fun i ↦ single (v i) (k i)).rank := by
  classical
  have := Fintype.ofFinite ι
  rw [toMatrix_ordinaryJetEval_eq_diagonal_mul, rank_mul_eq_right_of_isUnit_det]
  rw [det_diagonal]
  exact IsUnit.prod_univ_iff.2 hk

variable [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]

/-- In characteristic `p`, for orders `k i < p` the ordinary jet map and the Hasse jet map along
the multi-indices `k i • eᵥ₍ᵢ₎` have the same kernel. -/
theorem ker_ordinaryJetEval_of_lt (a : ι → σ → R) (hk : ∀ i, k i < p) :
    LinearMap.ker (ordinaryJetEval s a v k) =
      LinearMap.ker (jetEval s a fun i ↦ single (v i) (k i)) :=
  ker_ordinaryJetEval s v a fun i ↦ (IsUnit.natCast_factorial_iff_of_charP p).2 (hk i)

/-- In characteristic `p`, for orders `k i < p` the ordinary jet map and the Hasse jet map along
the multi-indices `k i • eᵥ₍ᵢ₎` have the same rank. -/
theorem rank_ordinaryJetEval_of_lt (a : ι → σ → R) (hk : ∀ i, k i < p) :
    (ordinaryJetEval s a v k).rank = (jetEval s a fun i ↦ single (v i) (k i)).rank :=
  rank_ordinaryJetEval s v a fun i ↦ (IsUnit.natCast_factorial_iff_of_charP p).2 (hk i)

/-- In characteristic `p`, for orders `k i < p` the matrices of the ordinary jet map and of the
Hasse jet map along the multi-indices `k i • eᵥ₍ᵢ₎` have the same rank. -/
theorem rank_toMatrix_ordinaryJetEval_of_lt (a : ι → σ → R) [Fintype s] [Finite ι]
    [DecidableEq s] (hk : ∀ i, k i < p) :
    (LinearMap.toMatrix (basisRestrictSupport R s) (Pi.basisFun R ι)
        (ordinaryJetEval s a v k)).rank =
      (jetMatrix s a fun i ↦ single (v i) (k i)).rank :=
  rank_toMatrix_ordinaryJetEval s v a fun i ↦ (IsUnit.natCast_factorial_iff_of_charP p).2 (hk i)

end JetMap

end MvPolynomial

/-! ### Examples -/

namespace Polynomial

/-- `p = 3`, `k = 2`, `f = X²`, `a = 0`: `D² f = 2` and `D^[2] f = 1`, both nonzero. -/
example : (derivative^[2] (X ^ 2 : (ZMod 3)[X])).eval 0 = 2 ∧
    (hasseDeriv 2 (X ^ 2 : (ZMod 3)[X])).eval 0 = 1 := by
  constructor
  · simp [iterate_derivative_X_pow_eq_smul, eval_smul]
  · simp [X_pow_eq_monomial, hasseDeriv_monomial]

/-- `p = 3`, `k = 3`: `D³ (X³) = 6 = 0` while `D^[3] (X³) = 1`, so the comparison fails exactly
at `k = p`, where `3!` is not a unit. -/
example : derivative^[3] (X ^ 3 : (ZMod 3)[X]) = 0 ∧ hasseDeriv 3 (X ^ 3 : (ZMod 3)[X]) = 1 ∧
    ¬ IsUnit ((3 ! : ℕ) : ZMod 3) := by
  refine ⟨?_, by simp [X_pow_eq_monomial, hasseDeriv_monomial], ?_⟩
  · rw [iterate_derivative_X_pow_eq_smul,
      show ((Nat.descFactorial 3 3 : ℕ) : ZMod 3) = 0 by decide, zero_smul]
  · rw [IsUnit.natCast_factorial_iff_of_charP 3]
    decide

/-- `p = 2`, `k = 1`: `1! = 1` is a unit and `D f = D^[1] f` for every `f`. -/
example (f : (ZMod 2)[X]) : IsUnit ((1 ! : ℕ) : ZMod 2) ∧ derivative f = hasseDeriv 1 f :=
  ⟨by simp, (hasseDeriv_one' f).symm⟩

end Polynomial
