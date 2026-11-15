/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Submanifold.Basic
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Analytic.Polynomial

/-!
# Polynomial coefficients on analytic submanifolds

Specializing a polynomial with multivariate polynomial coefficients along an analytic
submanifold gives intrinsically analytic coefficient functions. These supply the coefficient
regularity needed for analytic polynomial root sections.
-/

public section

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {n d : ℕ} {S : Set (Fin n → 𝕜)}

/-- The coefficients of a multivariate polynomial specialized along an analytic submanifold
are intrinsically analytic. -/
theorem IsAnalyticSubmanifold.analyticOnSubmanifold_coeff_map_eval
    (hS : IsAnalyticSubmanifold d S) (b : Polynomial (MvPolynomial (Fin n) 𝕜)) (j : ℕ) :
    AnalyticOnSubmanifold d (fun x ↦ (b.map (MvPolynomial.eval x)).coeff j) S := by
  simp only [Polynomial.coeff_map]
  exact ((AnalyticOnNhd.eval_continuousLinearMap
    (ContinuousLinearMap.id 𝕜 (Fin n → 𝕜)) (b.coeff j)).mono
      (Set.subset_univ S)).analyticOnSubmanifold hS

end TauCeti
