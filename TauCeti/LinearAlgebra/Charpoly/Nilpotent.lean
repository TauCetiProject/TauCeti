/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import TauCeti.LinearAlgebra.Charpoly.Projective
public import TauCeti.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.Polynomial.Nilpotent

/-!
# Characteristic polynomials of scalar plus nilpotent endomorphisms

On a finite free module over a reduced commutative ring, an endomorphism whose difference from
`μ • 1` is nilpotent has characteristic polynomial `(X - μ) ^ finrank R M`.
Its reversed characteristic polynomial is `(1 - μ X) ^ finrank R M`, including `μ = 0`.
These formulas identify the determinant factor contributed by a generalised eigenspace.

The case `μ = 0`, `LinearMap.charpoly_eq_X_pow_finrank_of_isNilpotent`, generalizes Mathlib's
`IsNilpotent.charpoly_eq_X_pow_finrank` from integral domains to reduced rings. Reducedness is
needed: over `k[ε]` with `ε ^ 2 = 0`, the nilpotent scalar `ε` has characteristic polynomial
`X - ε` on `k[ε]`, not `X`.

The reversed formula fails similarly over a general commutative ring: on `R = K[ε]/(ε²)` the
endomorphism `μ + N` of `R²` with `N = [[0, 1], [ε, 0]]` has `N⁴ = 0` but
`det (1 - X (μ + N)) = (1 - μ X) ^ 2 - ε X ^ 2`. Suppose instead that `f` is an endomorphism of a
finite projective module with `f - μ • 1` nilpotent and `μ a = 1`, and that the Taylor coefficient
of order `h` at `a` of `Q = det (1 - X f)` is a unit. Then `M` has constant rank `h` on `Spec R`
(`LinearMap.rankAtStalk_eq_of_isNilpotent_sub_smul`): in every residue field `Q` becomes
`(1 - μ X) ^ r` with `r` the local rank, whose only nonzero Taylor coefficient at `a` has order
`r`. If moreover the Taylor coefficients of order less than `h` vanish, the degree bound by the
rank forces `Q = (1 - μ X) ^ h`
(`LinearMap.projectiveCharpolyRev_eq_pow_of_isNilpotent_sub_smul_of_isUnit`). These are the
rank and determinant of the spectral summand at a good zero of order `h` of a Fredholm
determinant, over coefficient rings with nilpotents.
-/

public section

namespace LinearMap

open Polynomial Module

section Reduced

variable {R M : Type*} [CommRing R] [IsReduced R] [AddCommGroup M] [Module R M]
  [Module.Free R M] [Module.Finite R M]

/-- Over a reduced commutative ring, a nilpotent endomorphism of a finite free module has
characteristic polynomial `X ^ finrank R M`. -/
theorem charpoly_eq_X_pow_finrank_of_isNilpotent {f : Module.End R M} (hf : IsNilpotent f) :
    f.charpoly = X ^ finrank R M := by
  -- This follows Mathlib's `IsNilpotent.charpoly_eq_X_pow_finrank`, replacing its final domain
  -- step by the coefficientwise criterion `Polynomial.isNilpotent_iff`.
  nontriviality R
  let b := Free.chooseBasis R M
  have hmat : toMatrixAlgEquiv b f = toMatrix b b f := by
    ext i j
    rw [toMatrixAlgEquiv_apply, toMatrix_apply]
  have hP :=
    Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent (hmat ▸ hf.map (toMatrixAlgEquiv b))
  rw [charpoly_toMatrix, ← finrank_eq_card_chooseBasisIndex] at hP
  rw [← sub_eq_zero]
  ext i
  simpa using (Polynomial.isNilpotent_iff.mp hP i).eq_zero

/-- A scalar plus a nilpotent endomorphism has only that scalar in its characteristic
polynomial, counted with the full rank of the module. -/
theorem charpoly_eq_pow_of_isNilpotent_sub_smul (f : Module.End R M) (μ : R)
    (hf : IsNilpotent (f - μ • 1)) :
    f.charpoly = (X - C μ) ^ finrank R M := by
  have h := congrArg (fun p : R[X] ↦ p.comp (X - C μ))
    (charpoly_eq_X_pow_finrank_of_isNilpotent hf)
  rw [charpoly_sub_smul] at h
  simpa [Polynomial.comp_assoc, sub_eq_add_neg] using h

/-- The determinant `det (1 - X f)` of a scalar plus a nilpotent endomorphism, including
the nilpotent case `μ = 0` and the zero module. -/
theorem projectiveCharpolyRev_eq_pow_of_isNilpotent_sub_smul (f : Module.End R M) (μ : R)
    (hf : IsNilpotent (f - μ • 1)) :
    f.projectiveCharpolyRev = (1 - C μ * X) ^ finrank R M := by
  nontriviality R
  rw [projectiveCharpolyRev_eq_reverse_charpoly, Polynomial.reverse, charpoly_natDegree,
    charpoly_eq_pow_of_isNilpotent_sub_smul f μ hf]
  have hlinear : (X - C μ : R[X]).reflect 1 = 1 - C μ * X := by
    rw [reflect_sub, reflect_one_X, reflect_C, pow_one]
  calc
    _ = (X - C μ : R[X]).reflect 1 ^ finrank R M := by
      simpa only [Nat.mul_one] using
        reflect_pow (X - C μ) (N := 1) (by simp) (finrank R M)
    _ = _ := congrArg (fun p : R[X] ↦ p ^ finrank R M) hlinear

end Reduced

section CommRing

open scoped TensorProduct

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
  [Module.Projective R M]

/-- **Constant rank from a unit Taylor coefficient.** Let `f - μ • 1` be nilpotent with
`μ a = 1`. If the Taylor coefficient of order `h` at `a` of `det (1 - X f)` is a unit, then `M`
has rank `h` at every point of `Spec R`. -/
theorem rankAtStalk_eq_of_isNilpotent_sub_smul (f : Module.End R M) {μ a : R} (hμa : μ * a = 1)
    (hf : IsNilpotent (f - μ • 1)) {h : ℕ}
    (hh : IsUnit ((taylor a (projectiveCharpolyRev f)).coeff h)) (p : PrimeSpectrum R) :
    rankAtStalk M p = h := by
  let k := p.asIdeal.ResidueField
  let φ := algebraMap R k
  have hg : IsNilpotent (f.baseChange k - φ μ • 1) := by
    obtain ⟨n, hn⟩ := hf
    refine ⟨n, ?_⟩
    rw [algebraMap_smul, ← baseChange_one R M, ← baseChange_smul, ← baseChange_sub,
      ← baseChange_pow, hn, baseChange_zero]
  -- in the residue field, `det (1 - X f)` is `(1 - μ X) ^ r` with `r` the rank at `p`
  have hQ : (projectiveCharpolyRev f).map φ = (1 - C (φ μ) * X) ^ finrank k (k ⊗[R] M) := by
    rw [← projectiveCharpolyRev_baseChange]
    exact projectiveCharpolyRev_eq_pow_of_isNilpotent_sub_smul _ _ hg
  have hlin : taylor (φ a) (1 - C (φ μ) * X) = C (-φ μ) * X := by
    have hC : C (φ μ) * C (φ a) = (1 : k[X]) := by rw [← C_mul, ← map_mul, hμa, map_one, C_1]
    rw [map_sub, taylor_one, taylor_mul, taylor_C, taylor_X, map_neg, C_1]
    linear_combination -hC
  have hc : φ ((taylor a (projectiveCharpolyRev f)).coeff h) =
      (taylor (φ a) ((projectiveCharpolyRev f).map φ)).coeff h := by
    rw [← coeff_map]
    simp [taylor_apply, map_comp]
  rw [hQ, taylor_pow, hlin, mul_pow, ← C_pow, coeff_C_mul_X_pow] at hc
  rw [rankAtStalk_eq]
  split_ifs at hc with hr
  · exact hr.symm
  · exact absurd hc (hh.map φ).ne_zero

/-- **The determinant at a good zero.** Let `f - μ • 1` be nilpotent with `μ a = 1`. If the
Taylor coefficients at `a` of `det (1 - X f)` vanish below order `h` and the one of order `h` is a
unit, then `det (1 - X f) = (1 - μ X) ^ h`. The vanishing hypothesis is needed: over
`R = K[ε]/(ε²)`, the scalar `f = μ + ε` on `R` has a unit Taylor coefficient of order one, but
`det (1 - X f) = 1 - (μ + ε) X`. -/
theorem projectiveCharpolyRev_eq_pow_of_isNilpotent_sub_smul_of_isUnit (f : Module.End R M)
    {μ a : R} (hμa : μ * a = 1) (hf : IsNilpotent (f - μ • 1)) {h : ℕ}
    (hlt : ∀ j < h, (taylor a (projectiveCharpolyRev f)).coeff j = 0)
    (hh : IsUnit ((taylor a (projectiveCharpolyRev f)).coeff h)) :
    projectiveCharpolyRev f = (1 - C μ * X) ^ h := by
  set Q := projectiveCharpolyRev f with hQdef
  set c := (taylor a Q).coeff h
  have hdeg : Q.natDegree ≤ h := natDegree_projectiveCharpolyRev_le
    (fun p ↦ (rankAtStalk_eq_of_isNilpotent_sub_smul f hμa hf hh p).le) f
  -- the Taylor expansion of `Q` at `a` has the single term `c (X - a) ^ h`
  have hT : taylor a Q = C c * X ^ h := by
    ext n
    rw [coeff_C_mul_X_pow]
    split_ifs with hn
    · rw [hn]
    · rcases lt_or_gt_of_ne hn with hn | hn
      · exact hlt n hn
      · exact coeff_eq_zero_of_natDegree_lt ((natDegree_taylor Q a).trans_le hdeg |>.trans_lt hn)
  have hQ : Q = C c * (X - C a) ^ h := by
    have := congrArg (taylor (-a)) hT
    rwa [taylor_taylor, neg_add_cancel, taylor_zero, taylor_mul, taylor_C, taylor_X_pow, map_neg,
      ← sub_eq_add_neg] at this
  -- the normalisation `Q(0) = 1` determines `c`
  have h0 : c * (-a) ^ h = 1 := by
    have := coeff_projectiveCharpolyRev_zero f
    rw [← hQdef, hQ, coeff_zero_eq_eval_zero] at this
    simpa using this
  have hc : c = (-μ) ^ h := by
    calc c = c * ((-a) * (-μ)) ^ h := by rw [neg_mul_neg, mul_comm a μ, hμa, one_pow, mul_one]
      _ = c * (-a) ^ h * (-μ) ^ h := by rw [mul_pow, mul_assoc]
      _ = (-μ) ^ h := by rw [h0, one_mul]
  have hC : C μ * C a = (1 : R[X]) := by rw [← C_mul, hμa, C_1]
  rw [hQ, hc, C_pow, ← mul_pow, map_neg]
  congr 1
  linear_combination hC

end CommRing

end LinearMap
