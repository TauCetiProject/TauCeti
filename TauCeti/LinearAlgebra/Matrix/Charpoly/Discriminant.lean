/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Disc
import TauCeti.Algebra.MvPolynomial.Eval
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# The discriminant of diagonal matrices and affine matrix families

The discriminant `Matrix.discr` of a matrix is the discriminant of its characteristic polynomial.
Over an integral domain, a diagonal matrix has nonzero discriminant exactly when its diagonal
entries are distinct (`Matrix.discr_diagonal_ne_zero_iff`).

Let `S` be a commutative `R`-algebra. The entries of an `R`-affine family `x ↦ M + L x` of
matrices over `S` are affine in the parameters, so the discriminant is a polynomial in them with
coefficients in `S`. Every `R`-linear functional `S → R` of it, such as the real part when `S` is
`ℂ` and `R` is `ℝ`, is therefore a polynomial over `R` (`Matrix.exists_eval_eq_linearMap_discr`).
Its zero locus contains the matrices with a repeated characteristic root.

This is the polynomial behind the null-set argument of Anderson, Guionnet and Zeitouni,
*An Introduction to Random Matrices* (2010), proof of Theorem 2.5.2.
-/

public section

namespace Matrix

variable {ι R S : Type*} [Fintype ι] [DecidableEq ι]

/-- Over an integral domain, a diagonal matrix has nonzero discriminant exactly when its diagonal
entries are distinct. -/
theorem discr_diagonal_ne_zero_iff [CommRing R] [IsDomain R] {d : ι → R} :
    (diagonal d).discr ≠ 0 ↔ Function.Injective d := by
  have h := Multiset.discr_prod_X_sub_C_ne_zero_iff (Finset.univ.val.map d)
  rw [Multiset.map_map, Multiset.nodup_map_iff_inj_on Finset.univ.nodup] at h
  rw [discr, charpoly_diagonal, Finset.prod_eq_multiset_prod]
  exact h.trans (by simp [Function.Injective])

variable [CommSemiring R] [CommRing S] [Algebra R S]

/-- Along an `R`-affine family `x ↦ M + L x` of matrices over an `R`-algebra `S`, every
`R`-linear functional of the discriminant is a polynomial over `R` in the parameters. -/
theorem exists_eval_eq_linearMap_discr {κ : Type*} [Finite κ] (M : Matrix ι ι S)
    (L : (κ → R) →ₗ[R] Matrix ι ι S) (f : S →ₗ[R] R) :
    ∃ q : MvPolynomial κ R, ∀ x : κ → R,
      MvPolynomial.eval x q = f (M + L x).discr := by
  classical
  let _ := Fintype.ofFinite κ
  let N : Matrix ι ι (MvPolynomial κ S) := of fun i j ↦ MvPolynomial.C (M i j) +
    ∑ k, MvPolynomial.C (L (fun l ↦ if k = l then 1 else 0) i j) * MvPolynomial.X k
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_eq_linearMap f N.charpoly.discr
  refine ⟨q, fun x ↦ ?_⟩
  have hN : N.map (MvPolynomial.eval (algebraMap R S ∘ x)) = M + L x := by
    rw [L.pi_apply_eq_sum_univ x]
    ext i j
    simp only [N, map_apply, of_apply, map_add, map_sum, map_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_X, Function.comp_apply, Matrix.add_apply, Matrix.sum_apply,
      Matrix.smul_apply]
    simp only [Algebra.smul_def, mul_comm]
  rw [← hN, discr, charpoly_map, N.charpoly_monic.discr_map]
  exact hq x

end Matrix
