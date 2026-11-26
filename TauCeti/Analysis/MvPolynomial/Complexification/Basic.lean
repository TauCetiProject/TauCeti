/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Basic.Complex.Basic

/-!
# Complexification of real multivariate polynomials

This file collects the basic algebra of the complexification `p.map Complex.ofRealHom` of a real
polynomial `p`. At real points it takes the real values of `p` (`MvPolynomial.eval_map_ofReal`),
also on a real line at a complex parameter with zero imaginary part
(`MvPolynomial.eval_map_ofReal_add_smul_of_im_eq_zero`), and it commutes with complex
conjugation (`MvPolynomial.eval_map_ofReal_conj`).
-/

public section

namespace MvPolynomial

variable {σ : Type*}

/-- Evaluating the complexification of a real polynomial at a real point gives the real value. -/
theorem eval_map_ofReal (p : MvPolynomial σ ℝ) (x : σ → ℝ) :
    eval (fun j ↦ (x j : ℂ)) (p.map Complex.ofRealHom) = (eval x p : ℂ) :=
  (map_eval Complex.ofRealHom x p).symm

/-- On the real line through `y` in the direction `v`, at a complex parameter `t` with zero
imaginary part, the complexification of a real polynomial takes the real value at `y + t.re • v`. -/
theorem eval_map_ofReal_add_smul_of_im_eq_zero (p : MvPolynomial σ ℝ) (y v : σ → ℝ) {t : ℂ}
    (ht : t.im = 0) :
    eval ((fun j ↦ (y j : ℂ)) + t • fun j ↦ (v j : ℂ)) (p.map Complex.ofRealHom) =
      (eval (y + t.re • v) p : ℂ) := by
  rw [← eval_map_ofReal]
  congr 2
  funext j
  simp [Complex.ext_iff, ht]

/-- The complexification of a real polynomial commutes with complex conjugation. -/
theorem eval_map_ofReal_conj (p : MvPolynomial σ ℝ) (v : σ → ℂ) :
    eval (fun j ↦ (starRingEnd ℂ) (v j)) (p.map Complex.ofRealHom) =
      (starRingEnd ℂ) (eval v (p.map Complex.ofRealHom)) := by
  rw [eval_map, eval_map, eval₂_comp_left]
  congr 1
  ext r
  simp

end MvPolynomial
