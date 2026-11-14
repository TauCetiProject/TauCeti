/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.PolynomialSpace
public import Mathlib.Analysis.Analytic.Polynomial

/-!
# Analyticity of polynomial functions

Bounded-degree polynomial functions are analytic on Euclidean space. In particular their
classical derivatives are continuous on compact sets, so they define Sobolev classes of every
order on bounded open sets.
-/

public section

noncomputable section

namespace TauCeti.polynomialsDegLE

variable {ι : Type*} {m : ℕ}

/-- A bounded-degree polynomial function is analytic on the whole Euclidean space. -/
theorem analyticOnNhd [Fintype ι] (q : polynomialsDegLE ι m) :
    AnalyticOnNhd ℝ (q : EuclideanSpace ℝ ι → ℝ) Set.univ := by
  obtain ⟨P, -, hP⟩ := (mem_polynomialsDegLE_iff ι).1 q.property
  rw [← hP]
  convert AnalyticOnNhd.eval_continuousLinearMap
    (EuclideanSpace.equiv ι ℝ).toContinuousLinearMap P using 1
  ext x
  exact polynomialEvalₗ_apply ι P x

end TauCeti.polynomialsDegLE
