/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.Algebra.MvPolynomial.HasseDeriv.Basic
public import TauCeti.RingTheory.MvPolynomial.Box
public import TauCeti.RingTheory.MvPolynomial.RestrictSupport

import Mathlib.Data.Nat.Factorial.NatCast
import Mathlib.Data.ZMod.Basic

/-!
# The jet evaluation map on a finite polynomial space

For a set `s` of exponent vectors, a family of points `a : ι → σ → R` and one derivative
multi-index `d i` per point (repeated points allowed), the jet evaluation map sends a polynomial
`f` supported on `s` to the vector of its Hasse jets `(∂^[d i] f)(a i)`. It is `R`-linear on
`MvPolynomial.restrictSupport R s`, and its matrix in the monomial basis
`MvPolynomial.basisRestrictSupport R s` has the entry
`(∏ⱼ choose (μ j) (d i j)) · (a i) ^ (μ - d i)` in row `i` and column `μ`. This is the
interpolation matrix whose minors the arithmetic determinant method estimates.

## Main definitions

* `MvPolynomial.jetEval s a d`: the jet evaluation map `restrictSupport R s →ₗ[R] ι → R`.
* `MvPolynomial.jetMatrix s a d`: its matrix in the monomial basis, rows `ι`, columns `s`.
* `MvPolynomial.ordinaryJetEval s a v k`: the jet map of the ordinary derivatives
  `∂ᵥ₍ᵢ₎^(k i)`.

## Main results

* `MvPolynomial.jetMatrix_apply_eq_eval`, `MvPolynomial.jetMatrix_apply`: the entry in row `i` and
  column `μ` is the jet `(∂^[d i] X^μ)(a i)`, a product of binomial coefficients and powers.
* `MvPolynomial.hasseDerivRow_eq_jetMatrix`: the row `MvPolynomial.hasseDerivRow` of the degree
  box (`TauCeti/RingTheory/MvPolynomial/Box.lean`) is a row of the jet matrix of the box. So for
  points with coordinates in `R` (not in a general `R`-algebra `S`),
  `MvPolynomial.aeval_hasseDeriv_eq_sum` is the box case of `MvPolynomial.jetEval_eq_mulVec`.
* `MvPolynomial.toMatrix_jetEval`, `MvPolynomial.jetEval_eq_mulVec`: `jetMatrix` is the matrix of
  `jetEval` in the monomial basis.
* `MvPolynomial.mem_ker_jetEval`: the kernel consists of the polynomials all of whose prescribed
  jets vanish.
* `MvPolynomial.jetEval_mapRestrictSupport`, `MvPolynomial.jetMatrix_map`: naturality for a ring
  map `R →+* S`. Applied to `Ideal.Quotient.mk J`, they say that the jet map and the jet matrix
  over `R ⧸ J` are the reductions of those over `R`.
* `MvPolynomial.ordinaryJetEval_apply_eq_factorial_mul`, `MvPolynomial.toMatrix_ordinaryJetEval`,
  `MvPolynomial.toMatrix_ordinaryJetEval_eq_diagonal_mul`: the ordinary jet map along multi-indices
  `k i • eᵥ₍ᵢ₎` is the Hasse one with row `i` multiplied by `(k i)!`.
* `MvPolynomial.ker_ordinaryJetEval`, `MvPolynomial.rank_ordinaryJetEval`,
  `MvPolynomial.finrank_range_ordinaryJetEval`, `MvPolynomial.rank_toMatrix_ordinaryJetEval`: when
  every `(k i)!` is a unit (in particular when `∀ i, k i < p` in prime characteristic `p`, see the
  `_of_lt_char` specializations), the ordinary and Hasse jet maps have the same kernel and rank.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53 (2004),
  §11.6, pp. 282–283: the Hasse derivative `E^k X^n = choose n k · X^(n - k)` in one variable and
  its comparison with ordinary derivatives below and at the characteristic.
* L. Pottmeyer, *Diophantine Approximation*, lecture notes (version of 17 January 2022),
  Lemma 2.6.1 and (2.34), pp. 68–69: normalised derivatives of monomials in several variables.
-/

public section

open Finsupp Matrix

namespace MvPolynomial

section CommSemiring

variable {σ R S ι : Type*} [CommSemiring R] [CommSemiring S]

section Hasse

variable (s : Set (σ →₀ ℕ)) (a : ι → σ → R) (d : ι → σ →₀ ℕ)

/-- The jet evaluation map on the polynomials supported on `s`: a polynomial `f` goes to the vector
of its Hasse jets `(∂^[d i] f)(a i)`, `i : ι`. -/
noncomputable def jetEval : restrictSupport R s →ₗ[R] ι → R :=
  LinearMap.pi fun i ↦
    (aeval (a i)).toLinearMap ∘ₗ hasseDeriv (d i) ∘ₗ (restrictSupport R s).subtype

@[simp]
theorem jetEval_apply (f : restrictSupport R s) (i : ι) :
    jetEval s a d f i = eval (a i) (hasseDeriv (d i) (f : MvPolynomial σ R)) := by
  simp [jetEval]

/-- The matrix of the jet evaluation map in the monomial basis: row `i`, column `μ` is the jet
`(∂^[d i] X^μ)(a i)` of the monomial `X^μ`. -/
noncomputable def jetMatrix : Matrix ι s R :=
  Matrix.of fun i μ ↦ eval (a i) (hasseDeriv (d i) (monomial (μ : σ →₀ ℕ) 1))

/-- The entry of the jet matrix in row `i` and column `μ` is the jet `(∂^[d i] X^μ)(a i)`. -/
@[simp]
theorem jetMatrix_apply_eq_eval (i : ι) (μ : s) :
    jetMatrix s a d i μ = eval (a i) (hasseDeriv (d i) (monomial (μ : σ →₀ ℕ) 1)) :=
  (rfl)

/-- The entries of the jet matrix: `(∏ⱼ choose (μ j) (d i j)) · (a i) ^ (μ - d i)`. -/
theorem jetMatrix_apply (i : ι) (μ : s) :
    jetMatrix s a d i μ =
      (((d i).prod fun j k ↦ ((μ : σ →₀ ℕ) j).choose k : ℕ) : R) *
        ((μ : σ →₀ ℕ) - d i).prod fun j e ↦ a i j ^ e := by
  simp [eval_monomial]

/-- `jetMatrix` is the matrix of `jetEval` in the monomial basis of `restrictSupport R s` and the
standard basis of `ι → R`. -/
theorem toMatrix_jetEval [Fintype s] [Finite ι] [DecidableEq s] :
    LinearMap.toMatrix (basisRestrictSupport R s) (Pi.basisFun R ι) (jetEval s a d) =
      jetMatrix s a d := by
  ext i μ
  simp [LinearMap.toMatrix_apply]

/-- The jet vector of a polynomial supported on a finite `s` is the jet matrix applied to its
coefficients on `s`. -/
theorem jetEval_eq_mulVec [Fintype s] (f : restrictSupport R s) :
    jetEval s a d f = jetMatrix s a d *ᵥ fun μ ↦ (f : MvPolynomial σ R).coeff μ := by
  ext i
  conv_lhs => rw [← (basisRestrictSupport R s).sum_repr f]
  simp [mulVec, dotProduct, map_sum, basisRestrictSupport_repr_apply, mul_comm]

/-- The kernel of the jet evaluation map consists of the polynomials supported on `s` all of
whose prescribed jets vanish. -/
theorem mem_ker_jetEval {f : restrictSupport R s} :
    f ∈ LinearMap.ker (jetEval s a d) ↔
      ∀ i, eval (a i) (hasseDeriv (d i) (f : MvPolynomial σ R)) = 0 := by
  simp [funext_iff]

/-- The empty support gives the zero map. -/
@[simp]
theorem jetEval_empty : jetEval (∅ : Set (σ →₀ ℕ)) a d = 0 := by
  ext f i
  have hf : (f : MvPolynomial σ R) = 0 := by
    simpa [Set.subset_empty_iff] using (mem_restrictSupport_iff R).1 f.2
  simp [hf]

/-- Naturality of the jet evaluation map: changing coefficients along `f : R →+* S` before or
after evaluating the jets gives the same result. -/
theorem jetEval_mapRestrictSupport (f : R →+* S) (p : restrictSupport R s) :
    jetEval s (fun i ↦ f ∘ a i) d (mapRestrictSupport s f p) = f ∘ jetEval s a d p := by
  ext i
  simp [eval₂_comp]

/-- Naturality of the jet matrix: over `S` it is the entrywise image of the jet matrix over `R`.
-/
theorem jetMatrix_map (f : R →+* S) :
    jetMatrix s (fun i ↦ f ∘ a i) d = (jetMatrix s a d).map f := by
  ext i μ
  simp only [jetMatrix_apply_eq_eval, Matrix.map_apply]
  rw [eval₂_comp, ← eval_map, ← hasseDeriv_map, map_monomial, RingHom.map_one]

end Hasse

section Ordinary

variable (s : Set (σ →₀ ℕ)) (a : ι → σ → R) (v : ι → σ) (k : ι → ℕ)

/-- The jet map of ordinary derivatives: a polynomial `f` supported on `s` goes to the vector of
its ordinary jets `(∂ᵥ₍ᵢ₎^(k i) f)(a i)`, `i : ι`. -/
noncomputable def ordinaryJetEval : restrictSupport R s →ₗ[R] ι → R :=
  LinearMap.pi fun i ↦
    (aeval (a i)).toLinearMap ∘ₗ ((pderiv (v i)).toLinearMap ^ k i) ∘ₗ (restrictSupport R s).subtype

@[simp]
theorem ordinaryJetEval_apply (f : restrictSupport R s) (i : ι) :
    ordinaryJetEval s a v k f i = eval (a i) ((pderiv (v i))^[k i] (f : MvPolynomial σ R)) := by
  simp [ordinaryJetEval, pow_apply_eq_iterate]

/-- The ordinary jets along the multi-indices `k i • eᵥ₍ᵢ₎` are the Hasse jets times `(k i)!`. -/
theorem ordinaryJetEval_apply_eq_factorial_mul (f : restrictSupport R s) (i : ι) :
    ordinaryJetEval s a v k f i =
      ((k i).factorial : R) * jetEval s a (fun i ↦ single (v i) (k i)) f i := by
  rw [ordinaryJetEval_apply, jetEval_apply, ← factorial_smul_hasseDeriv_single, map_nsmul,
    nsmul_eq_mul]

/-- The matrix of the ordinary jet map is the Hasse jet matrix with row `i` multiplied by
`(k i)!`. -/
theorem toMatrix_ordinaryJetEval [Fintype s] [Finite ι] [DecidableEq s] :
    LinearMap.toMatrix (basisRestrictSupport R s) (Pi.basisFun R ι) (ordinaryJetEval s a v k) =
      Matrix.of fun i μ ↦
        ((k i).factorial : R) * jetMatrix s a (fun i ↦ single (v i) (k i)) i μ := by
  ext i μ
  rw [LinearMap.toMatrix_apply, Pi.basisFun_repr, ordinaryJetEval_apply_eq_factorial_mul,
    jetEval_apply]
  simp

/-- The matrix of the ordinary jet map is the diagonal matrix of factorials `(k i)!` multiplied on
the left with the Hasse jet matrix along `k i • eᵥ₍ᵢ₎`. -/
theorem toMatrix_ordinaryJetEval_eq_diagonal_mul [Fintype s] [Fintype ι] [DecidableEq s]
    [DecidableEq ι] :
    LinearMap.toMatrix (basisRestrictSupport R s) (Pi.basisFun R ι) (ordinaryJetEval s a v k) =
      Matrix.diagonal (fun i ↦ ((k i).factorial : R)) *
        jetMatrix s a (fun i ↦ single (v i) (k i)) := by
  ext i μ
  rw [toMatrix_ordinaryJetEval, Matrix.diagonal_mul]
  rfl

/-- The kernel of the ordinary jet evaluation map consists of the polynomials supported on `s` all
of whose prescribed ordinary jets vanish. -/
theorem mem_ker_ordinaryJetEval {f : restrictSupport R s} :
    f ∈ LinearMap.ker (ordinaryJetEval s a v k) ↔
      ∀ i, eval (a i) ((pderiv (v i))^[k i] (f : MvPolynomial σ R)) = 0 := by
  simp [funext_iff]

/-- When every `(k i)!` is a unit in `R`, the ordinary jet evaluation map is the Hasse jet
evaluation map along `k i • eᵥ₍ᵢ₎` followed by coordinatewise scaling by the units `(k i)!`. -/
theorem ordinaryJetEval_eq_comp_jetEval {s : Set (σ →₀ ℕ)} {a : ι → σ → R} {v : ι → σ}
    {k : ι → ℕ} (hk : ∀ i, IsUnit ((k i).factorial : R)) :
    ordinaryJetEval s a v k =
      (LinearEquiv.piCongrRight fun i ↦
        DistribMulAction.toLinearEquiv R R (hk i).unit).toLinearMap ∘ₗ
        jetEval s a (fun i ↦ single (v i) (k i)) := by
  ext f i
  exact ordinaryJetEval_apply_eq_factorial_mul s a v k f i

/-- When every `(k i)!` is a unit in `R`, the ordinary and Hasse jet evaluation maps have the same
kernel. -/
theorem ker_ordinaryJetEval {s : Set (σ →₀ ℕ)} {a : ι → σ → R} {v : ι → σ} {k : ι → ℕ}
    (hk : ∀ i, IsUnit ((k i).factorial : R)) :
    LinearMap.ker (ordinaryJetEval s a v k) =
      LinearMap.ker (jetEval s a fun i ↦ single (v i) (k i)) := by
  rw [ordinaryJetEval_eq_comp_jetEval hk, LinearEquiv.ker_comp]

/-- When every `(k i)!` is a unit in `R`, coordinatewise scaling by `(k i)!` restricts to an
`R`-linear equivalence from the range of the Hasse jet map along `k i • eᵥ₍ᵢ₎` to the range of
the ordinary jet map. -/
noncomputable def rangeOrdinaryJetEvalEquiv {s : Set (σ →₀ ℕ)} {a : ι → σ → R} {v : ι → σ}
    {k : ι → ℕ} (hk : ∀ i, IsUnit ((k i).factorial : R)) :
    LinearMap.range (jetEval s a fun i ↦ single (v i) (k i)) ≃ₗ[R]
      LinearMap.range (ordinaryJetEval s a v k) :=
  (LinearEquiv.piCongrRight fun i ↦
    DistribMulAction.toLinearEquiv R R (hk i).unit).ofSubmodules _ _
      (by rw [← LinearMap.range_comp, ← ordinaryJetEval_eq_comp_jetEval hk])

/-- On coordinates, `rangeOrdinaryJetEvalEquiv` scales the `i`-th entry by `(k i)!`. -/
@[simp]
theorem coe_rangeOrdinaryJetEvalEquiv_apply {s : Set (σ →₀ ℕ)} {a : ι → σ → R} {v : ι → σ}
    {k : ι → ℕ} (hk : ∀ i, IsUnit ((k i).factorial : R))
    (x : LinearMap.range (jetEval s a fun i ↦ single (v i) (k i))) (i : ι) :
    (rangeOrdinaryJetEvalEquiv hk x : ι → R) i = ((k i).factorial : R) * (x : ι → R) i :=
  (rfl)

/-- When every `(k i)!` is a unit in `R`, the ordinary and Hasse jet evaluation maps have the same
rank. -/
theorem rank_ordinaryJetEval {s : Set (σ →₀ ℕ)} {a : ι → σ → R} {v : ι → σ} {k : ι → ℕ}
    (hk : ∀ i, IsUnit ((k i).factorial : R)) :
    LinearMap.rank (ordinaryJetEval s a v k) =
      LinearMap.rank (jetEval s a fun i ↦ single (v i) (k i)) :=
  (rangeOrdinaryJetEvalEquiv hk).symm.rank_eq

/-- When every `(k i)!` is a unit in `R`, the ranges of the ordinary and Hasse jet evaluation maps
have the same `finrank`. -/
theorem finrank_range_ordinaryJetEval {s : Set (σ →₀ ℕ)} {a : ι → σ → R} {v : ι → σ} {k : ι → ℕ}
    (hk : ∀ i, IsUnit ((k i).factorial : R)) :
    Module.finrank R (LinearMap.range (ordinaryJetEval s a v k)) =
      Module.finrank R (LinearMap.range (jetEval s a fun i ↦ single (v i) (k i))) :=
  (rangeOrdinaryJetEvalEquiv hk).symm.finrank_eq

end Ordinary

section Box

variable [Fintype σ]

/-- The row `hasseDerivRow d α μ` of the degree box `{ν | ∀ j, ν j ≤ d j}` is the jet matrix of the
box for the single point `α` and the single multi-index `μ`, read at the exponent
`boxMonomial d I`. -/
theorem hasseDerivRow_eq_jetMatrix (d : σ → ℕ) (α : σ → R) (μ : σ →₀ ℕ)
    (I : ∀ j, Fin (d j + 1)) :
    hasseDerivRow d α μ I =
      jetMatrix {ν | ∀ j, ν j ≤ d j} (fun _ : Unit ↦ α) (fun _ ↦ μ) ()
        ⟨boxMonomial d I, boxMonomial_le d I⟩ := by
  rw [hasseDerivRow_def, Finset.prod_mul_distrib, jetMatrix_apply]
  simp only [Finsupp.prod_fintype _ _ (fun _ ↦ Nat.choose_zero_right _),
    Finsupp.prod_fintype _ _ (fun j ↦ pow_zero (α j)), Finsupp.tsub_apply, boxMonomial_apply,
    Nat.cast_prod]

end Box

end CommSemiring

section OrdinaryCommRing

variable {σ R ι : Type*} [CommRing R]

/-- Over a commutative ring, when every `(k i)!` is a unit, the matrix of the ordinary jet map has
the same rank as the Hasse jet matrix along `k i • eᵥ₍ᵢ₎`. -/
theorem rank_toMatrix_ordinaryJetEval {s : Set (σ →₀ ℕ)} {a : ι → σ → R} {v : ι → σ} {k : ι → ℕ}
    [Fintype s] [Finite ι] [DecidableEq s] (hk : ∀ i, IsUnit ((k i).factorial : R)) :
    (LinearMap.toMatrix (basisRestrictSupport R s) (Pi.basisFun R ι)
      (ordinaryJetEval s a v k)).rank =
      (jetMatrix s a fun i ↦ single (v i) (k i)).rank := by
  classical
  cases nonempty_fintype ι
  rw [toMatrix_ordinaryJetEval_eq_diagonal_mul,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _
      (by rw [Matrix.det_diagonal]; exact IsUnit.prod_univ_iff.2 hk)]

section CharP

variable {p : ℕ} [Fact p.Prime] [CharP R p]

/-- In prime characteristic `p`, when every jet order satisfies `k i < p`, the ordinary and Hasse
jet evaluation maps have the same kernel. -/
theorem ker_ordinaryJetEval_of_lt_char {s : Set (σ →₀ ℕ)} {a : ι → σ → R} {v : ι → σ} {k : ι → ℕ}
    (hk : ∀ i, k i < p) :
    LinearMap.ker (ordinaryJetEval s a v k) =
      LinearMap.ker (jetEval s a fun i ↦ single (v i) (k i)) :=
  ker_ordinaryJetEval fun i ↦ (IsUnit.natCast_factorial_iff_of_charP p).2 (hk i)

/-- In prime characteristic `p`, when every jet order satisfies `k i < p`, the ordinary and Hasse
jet evaluation maps have the same rank. -/
theorem rank_ordinaryJetEval_of_lt_char {s : Set (σ →₀ ℕ)} {a : ι → σ → R} {v : ι → σ}
    {k : ι → ℕ} (hk : ∀ i, k i < p) :
    LinearMap.rank (ordinaryJetEval s a v k) =
      LinearMap.rank (jetEval s a fun i ↦ single (v i) (k i)) :=
  rank_ordinaryJetEval fun i ↦ (IsUnit.natCast_factorial_iff_of_charP p).2 (hk i)

/-- In prime characteristic `p`, when every jet order satisfies `k i < p`, the ranges of the
ordinary and Hasse jet evaluation maps have the same `finrank`. -/
theorem finrank_range_ordinaryJetEval_of_lt_char {s : Set (σ →₀ ℕ)} {a : ι → σ → R} {v : ι → σ}
    {k : ι → ℕ} (hk : ∀ i, k i < p) :
    Module.finrank R (LinearMap.range (ordinaryJetEval s a v k)) =
      Module.finrank R (LinearMap.range (jetEval s a fun i ↦ single (v i) (k i))) :=
  finrank_range_ordinaryJetEval fun i ↦ (IsUnit.natCast_factorial_iff_of_charP p).2 (hk i)

/-- In prime characteristic `p`, when every jet order satisfies `k i < p`, the matrix of the
ordinary jet map has the same rank as the Hasse jet matrix along `k i • eᵥ₍ᵢ₎`. -/
theorem rank_toMatrix_ordinaryJetEval_of_lt_char {s : Set (σ →₀ ℕ)} {a : ι → σ → R} {v : ι → σ}
    {k : ι → ℕ} [Fintype s] [Finite ι] [DecidableEq s] (hk : ∀ i, k i < p) :
    (LinearMap.toMatrix (basisRestrictSupport R s) (Pi.basisFun R ι)
      (ordinaryJetEval s a v k)).rank =
      (jetMatrix s a fun i ↦ single (v i) (k i)).rank :=
  rank_toMatrix_ordinaryJetEval fun i ↦ (IsUnit.natCast_factorial_iff_of_charP p).2 (hk i)

end CharP

end OrdinaryCommRing

/-! ### Examples -/

/-- In one variable, the entry of the jet matrix for the monomial `X²`, the multi-index `d = 1` and
the point `1` is the first Hasse jet `(D^[1] X²)(1) = choose 2 1 = 2`. Dropping the binomial
coefficient from the entry formula would give `1`. -/
example : jetMatrix {single (0 : Fin 1) 2} (fun _ : Unit ↦ fun _ ↦ (1 : ℤ))
    (fun _ ↦ single 0 1) () ⟨_, rfl⟩ = 2 := by
  simp [eval_monomial]

/-- `∂_Z^[1] (Z W) = W` evaluated at `(2, 3)` is `3`. -/
example : jetMatrix {single (0 : Fin 2) 1 + single 1 1} (fun _ : Unit ↦ ![(2 : ℤ), 3])
    (fun _ ↦ single 0 1) () ⟨_, rfl⟩ = 3 := by
  simp [eval_monomial]

/-- `∂_Z^[2] (Z W) = 0`. -/
example : jetMatrix {single (0 : Fin 2) 1 + single 1 1} (fun _ : Unit ↦ ![(2 : ℤ), 3])
    (fun _ ↦ single 0 2) () ⟨_, rfl⟩ = 0 := by
  simp

/-- In characteristic `2` the Hasse jet `D^[2] X²` at `0` is `1` while the ordinary jet `D² X²` is
`2 = 0`: the ordinary jet map is not the Hasse jet map. -/
example : jetMatrix {single (0 : Fin 1) 2} (fun _ : Unit ↦ fun _ ↦ (0 : ZMod 2))
    (fun _ ↦ single 0 2) () ⟨_, rfl⟩ = 1 := by
  simp

/-- A zero multi-index gives plain evaluation. -/
example {σ R ι : Type*} [CommSemiring R] (s : Set (σ →₀ ℕ)) (a : ι → σ → R) (d : ι → σ →₀ ℕ)
    {i : ι} (hi : d i = 0) (f : restrictSupport R s) :
    jetEval s a d f i = eval (a i) (f : MvPolynomial σ R) := by
  simp [hi]

example : ordinaryJetEval {single (0 : Fin 1) 2} (fun _ : Unit ↦ fun _ ↦ (0 : ZMod 2))
    (fun _ ↦ 0) (fun _ ↦ 2) ⟨X 0 ^ 2, by simp [X_pow_eq_monomial]⟩ () = 0 := by
  have h2 : ((Nat.factorial 2 : ℕ) : ZMod 2) = 0 := by decide
  rw [ordinaryJetEval_apply_eq_factorial_mul, h2, zero_mul]

/-- Over `ZMod 3`, at orders `0, 1, 2 < 3`, the ordinary and Hasse jet maps have equal kernels and
equal ranks; at order `3 = p`, the kernel comparison fails since `X₀³` lies in the kernel of the
ordinary jet map at `0` but has Hasse jet `1`. -/
example :
    LinearMap.ker (ordinaryJetEval {μ : Fin 1 →₀ ℕ | μ 0 ≤ 2}
        (fun _ : Fin 3 ↦ fun _ ↦ (0 : ZMod 3)) (fun _ ↦ 0) ![0, 1, 2]) =
      LinearMap.ker (jetEval {μ : Fin 1 →₀ ℕ | μ 0 ≤ 2}
        (fun _ : Fin 3 ↦ fun _ ↦ (0 : ZMod 3)) (fun i ↦ Finsupp.single 0 (![0, 1, 2] i))) ∧
    LinearMap.ker (ordinaryJetEval {Finsupp.single (0 : Fin 1) 3}
        (fun _ : Unit ↦ fun _ ↦ (0 : ZMod 3)) (fun _ ↦ 0) (fun _ ↦ 3)) ≠
      LinearMap.ker (jetEval {Finsupp.single (0 : Fin 1) 3}
        (fun _ : Unit ↦ fun _ ↦ (0 : ZMod 3)) (fun _ ↦ Finsupp.single 0 3)) := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  refine ⟨ker_ordinaryJetEval_of_lt_char fun i ↦ by fin_cases i <;> decide, fun h ↦ ?_⟩
  let f : restrictSupport (ZMod 3) {Finsupp.single (0 : Fin 1) 3} :=
    ⟨X 0 ^ 3, by simp [X_pow_eq_monomial]⟩
  have hf_ord : f ∈ LinearMap.ker (ordinaryJetEval {Finsupp.single (0 : Fin 1) 3}
      (fun _ : Unit ↦ fun _ ↦ (0 : ZMod 3)) (fun _ ↦ 0) (fun _ ↦ 3)) := by
    rw [mem_ker_ordinaryJetEval]
    intro
    rw [iterate_pderiv_eq_zero_of_char_le (p := 3) (by decide) 0 le_rfl, map_zero]
  have hf_hasse := (mem_ker_jetEval _ _ _).1 (h ▸ hf_ord) ()
  simp [f, X_pow_eq_monomial] at hf_hasse

end MvPolynomial
