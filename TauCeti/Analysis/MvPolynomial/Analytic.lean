/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Polynomial

/-!
# Analytic coefficients of polynomials over multivariate polynomials

Mapping a polynomial over `MvPolynomial σ R` along a ring homomorphism `R →+* 𝕜` and
evaluating at a family of points gives coefficients depending analytically on the points, when
every coordinate of the family is analytic.

## Main results

* `Polynomial.analyticOnNhd_coeff_map_eval₂Hom`: the coefficients of such an evaluated
  polynomial are analytic in the family of points.
-/

public section

namespace Polynomial

/-- The coefficients of a polynomial over multivariate polynomials, mapped along a ring
homomorphism `g : R →+* 𝕜` and evaluated along a family of points, are analytic when every
coordinate of the family is analytic. -/
theorem analyticOnNhd_coeff_map_eval₂Hom {R σ E 𝕜 : Type*} [CommSemiring R]
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] (g : R →+* 𝕜)
    (p : Polynomial (MvPolynomial σ R)) {f : E → σ → 𝕜} {S : Set E}
    (hf : ∀ j, AnalyticOnNhd 𝕜 (fun z ↦ f z j) S) (i : ℕ) :
    AnalyticOnNhd 𝕜 (fun z ↦ (p.map (MvPolynomial.eval₂Hom g (f z))).coeff i) S := by
  intro z hz
  simp only [coeff_map, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq_eval_map]
  simpa only [MvPolynomial.aeval_eq_eval] using
    AnalyticAt.aeval_mvPolynomial (fun j ↦ hf j z hz) ((p.coeff i).map g)

end Polynomial
