/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Analytic logarithmic derivatives

The logarithmic derivative of an analytic function is analytic where the function is nonzero.
The variable and value fields may differ; the value field is complete.
-/

public section

/-- The logarithmic derivative is analytic wherever the function is analytic and nonzero. -/
@[fun_prop]
theorem AnalyticAt.logDeriv {𝕜 𝕝 : Type*} [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕝] [NormedAlgebra 𝕜 𝕝] [CompleteSpace 𝕝]
    {f : 𝕜 → 𝕝} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) (hx : f x ≠ 0) :
    AnalyticAt 𝕜 (logDeriv f) x :=
  hf.deriv.div hf hx
