/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorial.NatCast
public import Mathlib.LinearAlgebra.Matrix.Rank
public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.JetEvaluation

/-!
# Ordinary and Hasse jet maps below the characteristic

The ordinary partial derivative of order `k` in `Xᵢ` is `k!` times the Hasse derivative along
`k • eᵢ` (`MvPolynomial.factorial_smul_hasseDeriv_single`), so the ordinary jet map
`MvPolynomial.ordinaryJetEval` is the Hasse jet map `MvPolynomial.jetEval` along the multi-indices
`k i • eᵥ₍ᵢ₎` with coordinate `i` scaled by `(k i)!`, and its matrix is the Hasse jet matrix with
row `i` scaled by `(k i)!` (`MvPolynomial.toMatrix_ordinaryJetEval`). Whenever every `(k i)!` is
a unit, the two jet maps therefore have the same kernel and the same rank. The pointwise
comparison of single ordinary and Hasse jets is
`MvPolynomial.eval_iterate_pderiv_eq_zero_iff_eval_hasseDeriv_eq_zero`.

In a ring of prime characteristic `p` the factorial `k!` is a unit exactly when `k < p` (Mathlib
`IsUnit.natCast_factorial_iff_of_charP`), and over a field of characteristic zero it is always a
unit (Mathlib `IsUnit.natCast_factorial_of_algebra`). The results below take the unit hypothesis,
and the `_of_lt` forms specialise them to orders below the characteristic `p`.

## Main results

* `MvPolynomial.ker_ordinaryJetEval`, `MvPolynomial.rank_ordinaryJetEval`,
  `MvPolynomial.rank_toMatrix_ordinaryJetEval`: when every `(k i)!` is a unit, the ordinary and
  Hasse jet maps have the same kernel, the same rank, and matrices of the same rank.
* `MvPolynomial.ordinaryJetEval_eq_comp`: under the same hypothesis, the ordinary jet map is the
  Hasse jet map followed by an invertible diagonal scaling.
* `MvPolynomial.ker_ordinaryJetEval_of_lt`, `MvPolynomial.rank_ordinaryJetEval_of_lt`,
  `MvPolynomial.rank_toMatrix_ordinaryJetEval_of_lt`: the same in characteristic `p` for orders
  `k i < p`.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53 (2004),
  §11.6, pp. 282–283: ordinary and Hasse derivatives in characteristic `p`.
-/

public section

open Finsupp Matrix Nat

namespace MvPolynomial

variable {σ R ι : Type*}

section JetMap

variable (s : Set (σ →₀ ℕ)) (v : ι → σ) {k : ι → ℕ}

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
  rw [toMatrix_ordinaryJetEval, ← rank_mul_eq_right_of_isUnit_det (diagonal fun i ↦ ((k i)! : R))
    (jetMatrix s a fun i ↦ single (v i) (k i))
    (by simpa [det_diagonal] using IsUnit.prod_univ_iff.2 hk)]
  congr 1
  ext i μ
  simp [diagonal_mul]

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
