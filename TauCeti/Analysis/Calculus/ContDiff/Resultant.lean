/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import TauCeti.Analysis.Calculus.ContDiff.Matrix

/-!
# Smoothness of resultants

The resultant `Res_{m,k}(f, g)` of two polynomials (`Polynomial.resultant`) is the determinant of
their Sylvester matrix, whose entries are coefficients of `f` and `g` or zero. It is therefore a
polynomial in the coefficients, so a family of polynomials whose coefficients are `C^n` on a set
has `C^n` resultants there (`ContDiffOn.polynomial_resultant`).

For a family of monic polynomials `f_x` of degree `m` and their derivatives,
`Res_{m,m-1}(f_x, f_x')` is the product `∏ f_x'(r)` over the roots `r` of `f_x`
(`Polynomial.resultant_eq_prod_eval`), up to sign the discriminant. It vanishes exactly when `f_x`
has a repeated root, and it is `C^n` in `x` even across the collisions of roots, where the roots
themselves need not be differentiable.
-/

public section

open Polynomial

variable {𝕜 E 𝔸 : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedCommRing 𝔸] [NormedAlgebra 𝕜 𝔸] {n : WithTop ℕ∞}

/-- A family of polynomials whose coefficients are `C^n` on a set has `C^n` resultants on that
set, for any choice of the formal degrees `m` and `k`. -/
theorem ContDiffOn.polynomial_resultant {f g : E → 𝔸[X]} {s : Set E}
    (hf : ∀ i, ContDiffOn 𝕜 n (fun x ↦ (f x).coeff i) s)
    (hg : ∀ i, ContDiffOn 𝕜 n (fun x ↦ (g x).coeff i) s) (m k : ℕ) :
    ContDiffOn 𝕜 n (fun x ↦ (f x).resultant (g x) m k) s := by
  refine ContDiffOn.matrix_det fun i j ↦ ?_
  -- Each entry of the Sylvester matrix is a coefficient of `g` or of `f`, or zero.
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
  · simp only [sylvester, Matrix.of_apply, Fin.addCases_left]
    by_cases h : (i : ℕ) ∈ Set.Icc (j : ℕ) (j + k)
    · simpa only [h, ite_true] using hg _
    · simpa only [h, ite_false] using contDiffOn_const
  · simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
    by_cases h : (i : ℕ) ∈ Set.Icc (j : ℕ) (j + m)
    · simpa only [h, ite_true] using hf _
    · simpa only [h, ite_false] using contDiffOn_const
