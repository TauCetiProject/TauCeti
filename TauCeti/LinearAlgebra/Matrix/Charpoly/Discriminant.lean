/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import TauCeti.Algebra.MvPolynomial.Eval
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# The characteristic discriminant along a real-linear family of matrices

The entries of a real-linear family of real or complex matrices are linear in the parameters,
so the characteristic discriminant is a polynomial in them. Every real-linear functional of it,
such as its real part, is therefore a real polynomial
(`Matrix.exists_eval_eq_linearMap_charpoly_discr`). Its zero locus contains the matrices with a
repeated characteristic root.

This is the polynomial behind the null-set argument of Anderson, Guionnet and Zeitouni,
*An Introduction to Random Matrices* (2010), proof of Theorem 2.5.2.
-/

public section

namespace Matrix

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]

/-- Along a real-linear family of matrices, every real-linear functional of the characteristic
discriminant is a real polynomial in the parameters. -/
theorem exists_eval_eq_linearMap_charpoly_discr {κ : Type*} [Finite κ]
    (L : (κ → ℝ) →ₗ[ℝ] Matrix ι ι 𝕜) (f : 𝕜 →ₗ[ℝ] ℝ) :
    ∃ q : MvPolynomial κ ℝ, ∀ x : κ → ℝ,
      MvPolynomial.eval x q = f (L x).charpoly.discr := by
  classical
  let _ := Fintype.ofFinite κ
  let M : Matrix ι ι (MvPolynomial κ 𝕜) := of fun i j ↦
    ∑ k, MvPolynomial.C (L (fun l ↦ if k = l then 1 else 0) i j) * MvPolynomial.X k
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_eq_linearMap f M.charpoly.discr
  refine ⟨q, fun x ↦ ?_⟩
  have hM : M.map (MvPolynomial.eval (algebraMap ℝ 𝕜 ∘ x)) = L x := by
    rw [L.pi_apply_eq_sum_univ x]
    ext i j
    simp [M, RCLike.real_smul_eq_coe_mul, mul_comm]
  rw [← hM, charpoly_map, M.charpoly_monic.discr_map]
  exact hq x

end Matrix
