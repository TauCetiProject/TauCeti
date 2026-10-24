/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Time derivatives of rescaled profiles

For a profile `Ψ : E → F`, a fixed point `x : E`, and real exponents `a` and `b`, the expression
`s^(-a) Ψ(s^b x)` is differentiable at each `s > 0` where `Ψ` is differentiable at `y = s^b x`,
and its derivative is `s^(-(a + 1)) (-a Ψ(y) + b DΨ(y) y)`. The derivative is again of the same
form with a new profile, so iterated time derivatives of self-similar expressions, such as the
derivatives of the heat kernel under parabolic scaling, can be computed by induction.
-/

public section

namespace TauCeti

open Real

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The time derivative of a rescaled profile:
`∂ₛ (s^(-a) Ψ(s^b x)) = s^(-(a + 1)) (-a Ψ(y) + b DΨ(y) y)` with `y = s^b x`, provided `Ψ` is
differentiable at `y`. -/
theorem hasDerivAt_rpow_smul_comp_rpow_smul {Ψ : E → F} (a b : ℝ) (x : E) {s : ℝ} (hs : 0 < s)
    (hΨ : DifferentiableAt ℝ Ψ (s ^ b • x)) :
    HasDerivAt (fun s : ℝ => s ^ (-a) • Ψ (s ^ b • x))
      (s ^ (-(a + 1)) • (-a • Ψ (s ^ b • x) + b • fderiv ℝ Ψ (s ^ b • x) (s ^ b • x))) s := by
  have h1 : HasDerivAt (fun s : ℝ => s ^ (-a)) (-a * s ^ (-a - 1)) s :=
    hasDerivAt_rpow_const (Or.inl hs.ne')
  have h2 : HasDerivAt (fun s : ℝ => s ^ b • x) ((b * s ^ (b - 1)) • x) s :=
    (hasDerivAt_rpow_const (Or.inl hs.ne')).smul_const x
  have h3 : HasDerivAt (fun s : ℝ => Ψ (s ^ b • x))
      (fderiv ℝ Ψ (s ^ b • x) ((b * s ^ (b - 1)) • x)) s :=
    hΨ.hasFDerivAt.comp_hasDerivAt s h2
  convert h1.smul h3 using 1
  -- Collect the powers of `s`: `s^(-a) s^(b-1) = s^(-(a+1)) s^b`.
  have hpow : s ^ (-a) * s ^ (b - 1) = s ^ (-(a + 1)) * s ^ b := by
    rw [← rpow_add hs, ← rpow_add hs]
    ring_nf
  have hpow' : s ^ (-a - 1) = s ^ (-(a + 1)) := by ring_nf
  simp only [map_smul, smul_smul, smul_add, hpow']
  have hcoeff : s ^ (-a) * (b * s ^ (b - 1)) = s ^ (-(a + 1)) * b * s ^ b := by
    linear_combination b * hpow
  rw [hcoeff]
  module

end TauCeti
