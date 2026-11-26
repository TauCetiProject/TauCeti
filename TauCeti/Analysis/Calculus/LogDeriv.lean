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

The logarithmic derivative of the derivative, `logDeriv (deriv f) = f'' / f'` (the pre-Schwarzian
derivative of `f`), is unchanged by an affine normalisation `w ↦ (w - c) / b` of the target:
`TauCeti.logDeriv_deriv_sub_div_const`.
-/

public section

/-- The logarithmic derivative is analytic wherever the function is analytic and nonzero. -/
@[fun_prop]
protected theorem AnalyticAt.logDeriv {𝕜 𝕝 : Type*} [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕝] [NormedAlgebra 𝕜 𝕝] [CompleteSpace 𝕝]
    {f : 𝕜 → 𝕝} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) (hx : f x ≠ 0) :
    AnalyticAt 𝕜 (logDeriv f) x :=
  hf.deriv.div hf hx

namespace TauCeti

/-- The logarithmic derivative of the derivative (the pre-Schwarzian derivative) is unchanged by
the affine normalisation `w ↦ (w - c) / b` of the target, for `b ≠ 0`. -/
theorem logDeriv_deriv_sub_div_const {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] (f : 𝕜 → 𝕜') (c : 𝕜') {b : 𝕜'} (hb : b ≠ 0)
    (z : 𝕜) :
    logDeriv (deriv fun z => (f z - c) / b) z = logDeriv (deriv f) z := by
  have hderiv : deriv (fun z => (f z - c) / b) = fun z => deriv f z / b := by
    ext z
    simp only [deriv_div_const, deriv_sub_const]
  rw [hderiv]
  simp only [div_eq_mul_inv, logDeriv_mul_const z b⁻¹ (inv_ne_zero hb)]

end TauCeti
