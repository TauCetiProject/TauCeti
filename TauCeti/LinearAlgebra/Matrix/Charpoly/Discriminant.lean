/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import TauCeti.Algebra.MvPolynomial.Eval
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# The characteristic discriminant along a linear family of matrices

Let `S` be a commutative `R`-algebra. The entries of an `R`-linear family of matrices over `S`
are linear in the parameters, so the characteristic discriminant is a polynomial in them with
coefficients in `S`. Every `R`-linear functional `S → R` of it, such as the real part when `S` is
`ℂ` and `R` is `ℝ`, is therefore a polynomial over `R`
(`Matrix.exists_eval_eq_linearMap_charpoly_discr`). Its zero locus contains the matrices with a
repeated characteristic root.

This is the polynomial behind the null-set argument of Anderson, Guionnet and Zeitouni,
*An Introduction to Random Matrices* (2010), proof of Theorem 2.5.2.
-/

public section

namespace Matrix

variable {ι R S : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R] [CommRing S] [Algebra R S]

/-- Along an `R`-linear family of matrices over an `R`-algebra `S`, every `R`-linear functional of
the characteristic discriminant is a polynomial over `R` in the parameters. -/
theorem exists_eval_eq_linearMap_charpoly_discr {κ : Type*} [Finite κ]
    (L : (κ → R) →ₗ[R] Matrix ι ι S) (f : S →ₗ[R] R) :
    ∃ q : MvPolynomial κ R, ∀ x : κ → R,
      MvPolynomial.eval x q = f (L x).charpoly.discr := by
  classical
  let _ := Fintype.ofFinite κ
  let M : Matrix ι ι (MvPolynomial κ S) := of fun i j ↦
    ∑ k, MvPolynomial.C (L (fun l ↦ if k = l then 1 else 0) i j) * MvPolynomial.X k
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_eq_linearMap f M.charpoly.discr
  refine ⟨q, fun x ↦ ?_⟩
  have hM : M.map (MvPolynomial.eval (algebraMap R S ∘ x)) = L x := by
    rw [L.pi_apply_eq_sum_univ x]
    ext i j
    simp only [M, map_apply, of_apply, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      Function.comp_apply, Matrix.sum_apply, Matrix.smul_apply]
    simp only [Algebra.smul_def, mul_comm]
  rw [← hM, charpoly_map, M.charpoly_monic.discr_map]
  exact hq x

end Matrix
