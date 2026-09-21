/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The logarithmic derivative of a principal complex power

Raising a holomorphic function to a fixed complex exponent multiplies its logarithmic derivative
by that exponent, exactly as for an integer exponent
(`logDeriv_fun_zpow`).  The principal power `f ^ c` is holomorphic where `f` avoids the branch
cut, so the statement asks for `f x ∈ Complex.slitPlane`; there the base is nonzero and the
quotient `f x ^ (c - 1) / f x ^ c` collapses to `(f x)⁻¹`.

This is the branch-free shape in which a power appears in a pre-Schwarzian computation: the
logarithmic derivative of `f ^ c` remembers only the exponent and the logarithmic derivative of
the base, never the branch used to define the power.

## Main result

* `TauCeti.logDeriv_fun_cpow`
-/

public section

namespace TauCeti

/-- The logarithmic derivative of a principal power `f ^ c` is `c` times that of `f`, at every
point where `f` is differentiable and misses the branch cut. -/
theorem logDeriv_fun_cpow {f : ℂ → ℂ} {x : ℂ} (hf : DifferentiableAt ℂ f x)
    (hx : f x ∈ Complex.slitPlane) (c : ℂ) :
    logDeriv (fun z => f z ^ c) x = c * logDeriv f x := by
  have hne : f x ≠ 0 := Complex.slitPlane_ne_zero hx
  have hpow : f x ^ c ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hne)
  rw [logDeriv_apply, deriv_cpow_const hf hx, logDeriv_apply, Complex.cpow_sub _ _ hne,
    Complex.cpow_one]
  field_simp

end TauCeti

end
