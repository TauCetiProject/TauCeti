/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Linear changes of variables in multivariate polynomials

For a square matrix `M` indexed by the variables, `MvPolynomial.linearSubst M` is the
`R`-algebra endomorphism of `R[Xᵢ : i ∈ σ]` substituting `Xᵢ ↦ ∑ⱼ Mᵢⱼ Xⱼ`. Evaluated at a
point `x`, the polynomial `linearSubst M p` is `p` evaluated at `M *ᵥ x`: the substitution is
the pullback of polynomial functions along `M`. It is therefore a *right* action of the matrix
monoid, `linearSubst (M * N) = (linearSubst N).comp (linearSubst M)`.

The substitution preserves homogeneity, and on forms of degree `n` a scalar matrix `c • 1`
acts by `cⁿ`. Restricted to the forms of a fixed degree `n` it is the representation
`MvPolynomial.linearSubstRep` of the opposite matrix monoid on `homogeneousSubmodule σ R n`.
In two variables this is the action `P ↦ P(aX + bY, cX + dY)` of `2 × 2` matrices on binary
forms of degree `n`, through which the modular group acts on period polynomials.

## Main definitions

* `MvPolynomial.linearSubst`: the substitution `Xᵢ ↦ ∑ⱼ Mᵢⱼ Xⱼ`.
* `MvPolynomial.linearSubstRep`: its restriction to forms of degree `n`, as a representation of
  `(Matrix σ σ R)ᵐᵒᵖ`.

## Main results

* `MvPolynomial.aeval_linearSubst`: `linearSubst M p` evaluated at `x` is `p` evaluated at
  `M *ᵥ x`.
* `MvPolynomial.linearSubst_mul`: the substitution is a right action.
* `MvPolynomial.IsHomogeneous.linearSubst`: the substitution preserves homogeneity.
* `MvPolynomial.IsHomogeneous.linearSubst_smul`: rescaling the matrix by `c` rescales a form
  of degree `n` by `cⁿ`.
-/

public section

open Matrix MulOpposite

namespace MvPolynomial

variable {σ R : Type*} [Fintype σ] [CommSemiring R]

/-- The linear change of variables `Xᵢ ↦ ∑ⱼ Mᵢⱼ Xⱼ` given by a square matrix `M`. -/
noncomputable def linearSubst (M : Matrix σ σ R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun i ↦ ∑ j, C (M i j) * X j

theorem linearSubst_eq_aeval (M : Matrix σ σ R) :
    linearSubst M = aeval fun i ↦ ∑ j, C (M i j) * X j :=
  (rfl)

@[simp]
theorem linearSubst_X (M : Matrix σ σ R) (i : σ) :
    linearSubst M (X i) = ∑ j, C (M i j) * X j :=
  aeval_X _ _

/-- Evaluating `linearSubst M p` at `x` is evaluating `p` at `M *ᵥ x`. -/
theorem aeval_linearSubst {S : Type*} [CommSemiring S] [Algebra R S] (M : Matrix σ σ R)
    (x : σ → S) (p : MvPolynomial σ R) :
    aeval x (linearSubst M p) = aeval (M.map (algebraMap R S) *ᵥ x) p := by
  rw [← AlgHom.comp_apply]
  congr 1
  refine algHom_ext fun i ↦ ?_
  simp [mulVec, dotProduct]

/-- Evaluating `linearSubst M p` at `x` is evaluating `p` at `M *ᵥ x`. -/
theorem eval_linearSubst (M : Matrix σ σ R) (x : σ → R) (p : MvPolynomial σ R) :
    eval x (linearSubst M p) = eval (M *ᵥ x) p := by
  simpa using aeval_linearSubst M x p

@[simp]
theorem linearSubst_one [DecidableEq σ] : linearSubst (1 : Matrix σ σ R) = AlgHom.id R _ :=
  algHom_ext fun i ↦ by simp [one_apply]

/-- The substitution is a right action of the matrix monoid: substituting along `M * N` is
substituting along `M` and then along `N`. -/
theorem linearSubst_mul (M N : Matrix σ σ R) :
    linearSubst (M * N) = (linearSubst N).comp (linearSubst M) := by
  refine algHom_ext fun i ↦ ?_
  simp only [linearSubst_X, AlgHom.comp_apply, map_sum, map_mul, algHom_C, mul_apply,
    map_sum C, Finset.sum_mul, Finset.mul_sum, algebraMap_eq, mul_assoc]
  exact Finset.sum_comm

theorem linearSubst_mul_apply (M N : Matrix σ σ R) (p : MvPolynomial σ R) :
    linearSubst (M * N) p = linearSubst N (linearSubst M p) := by
  rw [linearSubst_mul, AlgHom.comp_apply]

/-- A linear change of variables preserves homogeneity. -/
theorem IsHomogeneous.linearSubst {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n)
    (M : Matrix σ σ R) : (MvPolynomial.linearSubst M p).IsHomogeneous n := by
  rw [linearSubst_eq_aeval, ← one_mul n]
  exact hp.aeval _ fun i ↦ IsHomogeneous.sum _ _ _ fun j _ ↦ isHomogeneous_C_mul_X (M i j) j

omit [Fintype σ] in
/-- Substituting `Xᵢ ↦ c Xᵢ` in a form of degree `n` multiplies it by `cⁿ`. -/
theorem IsHomogeneous.aeval_C_mul_X {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n)
    (c : R) : MvPolynomial.aeval (fun i ↦ C c * X i) p = c ^ n • p := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [aeval_monomial, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hp.degree_eq_sum_deg_support hd, ← map_pow, algebraMap_eq, smul_eq_C_mul, monomial_eq,
    Finsupp.prod]
  ring

/-- Rescaling the matrix by `c` rescales a form of degree `n` by `cⁿ`. -/
theorem IsHomogeneous.linearSubst_smul {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n)
    (c : R) (M : Matrix σ σ R) :
    MvPolynomial.linearSubst (c • M) p = c ^ n • MvPolynomial.linearSubst M p := by
  have hM : MvPolynomial.linearSubst (c • M) =
      (MvPolynomial.aeval fun i ↦ C c * X i).comp (MvPolynomial.linearSubst M) := by
    refine algHom_ext fun i ↦ ?_
    simp only [linearSubst_X, AlgHom.comp_apply, map_sum, map_mul, aeval_X, aeval_C,
      algebraMap_eq, smul_apply, smul_eq_mul, map_mul C]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [hM, AlgHom.comp_apply, (hp.linearSubst M).aeval_C_mul_X]

/-- On forms of degree `n`, negating the matrix multiplies by `(-1)ⁿ`. -/
theorem IsHomogeneous.linearSubst_neg {R : Type*} [CommRing R] {p : MvPolynomial σ R} {n : ℕ}
    (hp : p.IsHomogeneous n) (M : Matrix σ σ R) :
    MvPolynomial.linearSubst (-M) p = (-1 : R) ^ n • MvPolynomial.linearSubst M p := by
  rw [← neg_one_smul R M, hp.linearSubst_smul]

variable (σ R) in
/-- The linear changes of variables restricted to the forms of degree `n`, as a representation
of the opposite matrix monoid: `op M` acts by `p ↦ linearSubst M p`. -/
noncomputable def linearSubstRep [DecidableEq σ] (n : ℕ) :
    Representation R (Matrix σ σ R)ᵐᵒᵖ (homogeneousSubmodule σ R n) where
  toFun M := (linearSubst M.unop).toLinearMap.restrict fun _ hp ↦ IsHomogeneous.linearSubst hp _
  map_one' := LinearMap.ext fun p ↦ Subtype.ext <| by simp
  map_mul' M N := LinearMap.ext fun p ↦ Subtype.ext <| linearSubst_mul_apply _ _ _

@[simp]
theorem coe_linearSubstRep_apply [DecidableEq σ] {n : ℕ} (M : (Matrix σ σ R)ᵐᵒᵖ)
    (p : homogeneousSubmodule σ R n) :
    (linearSubstRep σ R n M p : MvPolynomial σ R) = linearSubst M.unop p :=
  (rfl)

end MvPolynomial
