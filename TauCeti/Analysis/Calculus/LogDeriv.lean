/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Logarithmic derivatives

The logarithmic derivative of an analytic function is analytic where the function is nonzero.
The variable and value fields may differ; the value field is complete.
Reflection of the argument negates the logarithmic derivative, even at points of
nondifferentiability or zeros of the function.
-/

public section

namespace TauCeti

/-- Reflection of the argument negates the logarithmic derivative, with no regularity or
nonvanishing assumption. -/
@[simp]
theorem logDeriv_comp_const_sub {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] (f : 𝕜 → 𝕜') (a x : 𝕜) :
    logDeriv (fun z ↦ f (a - z)) x = -logDeriv f (a - x) := by
  rw [logDeriv_apply, logDeriv_apply, deriv_comp_const_sub, neg_div]

end TauCeti

/-- The logarithmic derivative is analytic wherever the function is analytic and nonzero. -/
@[fun_prop]
protected theorem AnalyticAt.logDeriv {𝕜 𝕝 : Type*} [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕝] [NormedAlgebra 𝕜 𝕝] [CompleteSpace 𝕝]
    {f : 𝕜 → 𝕝} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) (hx : f x ≠ 0) :
    AnalyticAt 𝕜 (logDeriv f) x :=
  hf.deriv.div hf hx
