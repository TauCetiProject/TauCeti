/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic

/-!
# Holomorphy and the conjugate Wirtinger derivative

For a real-differentiable map between complex normed spaces, vanishing of the conjugate
Wirtinger derivative characterizes complex differentiability. The real-differentiability
hypothesis is essential because the totalized real derivative vanishes at nondifferentiable
points. In one variable the real differential has coefficients `wirtingerDeriv f x 1` and
`conjWirtingerDeriv f x 1` in the basis `dz`, `dbar z`; testing the latter coefficient alone
detects its vanishing.

These statements connect the real differential and its type decomposition with holomorphy.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, Chapter II.
-/

public noncomputable section

open Complex
open scoped ComplexConjugate

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- In one variable the real differential is the sum of its `dz` and `dbar z` terms.
This identity also holds for the totalized derivative, without a differentiability assumption. -/
theorem fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv {f : ℂ → W} (x v : ℂ) :
    fderiv ℝ f x v =
      v • wirtingerDeriv f x 1 + conj v • conjWirtingerDeriv f x 1 := by
  rw [← wirtingerDeriv_add_conjWirtingerDeriv f x v]
  congr 1
  · simpa only [smul_eq_mul, mul_one] using (wirtingerDeriv f x).map_smul v (1 : ℂ)
  · simpa only [smul_eq_mul, mul_one] using (conjWirtingerDeriv f x).map_smulₛₗ v (1 : ℂ)

/-- A real-differentiable map between complex normed spaces is complex differentiable
exactly when its conjugate Wirtinger derivative vanishes. -/
theorem differentiableAt_iff_conjWirtingerDeriv_eq_zero {g : V → W} {x : V}
    (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℂ g x ↔ conjWirtingerDeriv g x = 0 := by
  constructor
  · exact fun h ↦ h.conjWirtingerDeriv_eq_zero
  · intro h
    apply (differentiableAt_iff_restrictScalars ℝ hg).mpr
    refine ⟨wirtingerDeriv g x, ?_⟩
    ext v
    simpa only [ContinuousLinearMap.coe_restrictScalars', h, zero_apply, add_zero] using
      wirtingerDeriv_add_conjWirtingerDeriv g x v

/-- In one variable the conjugate Wirtinger derivative vanishes exactly when its value
at `1` vanishes, since it is complex-antilinear. -/
theorem conjWirtingerDeriv_eq_zero_iff_apply_one_eq_zero {f : ℂ → W} {x : ℂ} :
    conjWirtingerDeriv f x = 0 ↔ conjWirtingerDeriv f x 1 = 0 := by
  constructor
  · intro h
    simp only [h, zero_apply]
  · intro h
    ext v
    simpa only [smul_eq_mul, mul_one, h, smul_zero, zero_apply] using
      (conjWirtingerDeriv f x).map_smulₛₗ v (1 : ℂ)

/-- For a real-differentiable function of one complex variable, the single equation
`conjWirtingerDeriv f x 1 = 0` characterizes complex differentiability. -/
theorem differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero {f : ℂ → W} {x : ℂ}
    (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℂ f x ↔ conjWirtingerDeriv f x 1 = 0 := by
  rw [differentiableAt_iff_conjWirtingerDeriv_eq_zero hf,
    conjWirtingerDeriv_eq_zero_iff_apply_one_eq_zero]

end TauCeti
