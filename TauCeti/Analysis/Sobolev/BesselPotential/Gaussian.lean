/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
public import TauCeti.Analysis.Distribution.SchwartzSpace.Gaussian
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.SpecialFunctions.Gaussian.DerivNorm

/-!
# The `H^{1,2}(ℝ)` norm of a Gaussian

A computation on Gaussians on the real line tests the identification of Mathlib's
Bessel-potential space `H^{1,2}(ℝ)` with the weak-derivative space `W^{1,2}(ℝ)`.

Mathlib's Bessel potential is the multiplier `(1 + ξ²)^{s/2}`, while the derivative has the symbol
`2πi ξ`, so by the Plancherel identity (`SchwartzMap.norm_toBesselPotentialSpaceCLM_one_sq`)

`‖u‖²_{H^{1,2}} = ‖u‖²_{L²} + (2π)⁻² ‖u'‖²_{L²}`.

For the Gaussian `g(x) = exp(-b x²)`, `0 < Re b`, the squared `L²` norms of `g` and `g'` are
`√(π / (2 Re b))` and `√(π / (2 Re b)) |b|² / Re b` (`TauCeti.norm_toLp_gaussian_sq`,
`TauCeti.norm_toLp_lineDerivOp_one_gaussian_sq`), so `‖g‖²_{H^{1,2}}` is
`√(π / (2 Re b)) (1 + |b|² / (4π² Re b))`
(`TauCeti.norm_toBesselPotentialSpaceCLM_one_gaussian_sq`), whereas the sum of the squared `L²`
norms of `g` and `g'` is `√(π / (2 Re b)) (1 + |b|² / Re b)`. The two norms are equivalent, with
constants `1` and `(2π)²` on the derivative term, but not equal.

## References

* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter V, §3.
* M. Taylor, *Partial Differential Equations I*, Chapter 4, Section 1.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal SchwartzMap BesselPotentialSpace LineDeriv Real

namespace TauCeti

/-- **The `H^{1,2}` norm of a Gaussian.** For `g(x) = exp(-b x²)` on `ℝ`, `0 < Re b`,
`‖g‖²_{H^{1,2}} = ‖g‖²_{L²} + (2π)⁻² ‖g'‖²_{L²} = √(π / (2 Re b)) (1 + |b|² / (4π² Re b))`.
Mathlib's Bessel potential has the symbol `(1 + ξ²)^{1/2}`, not `(1 + 4π² ξ²)^{1/2}`. -/
theorem norm_toBesselPotentialSpaceCLM_one_gaussian_sq {b : ℂ} (hb : 0 < b.re) :
    ‖SchwartzMap.toBesselPotentialSpaceCLM (1 : ℝ) 2 (SchwartzMap.gaussian (V := ℝ) hb)‖ ^ 2 =
      √(π / (2 * b.re)) * (1 + ‖b‖ ^ 2 / (4 * π ^ 2 * b.re)) := by
  simp only [SchwartzMap.norm_toBesselPotentialSpaceCLM_one_sq
      (OrthonormalBasis.singleton (Fin 1) ℝ), OrthonormalBasis.singleton_apply,
    Finset.univ_unique, Finset.sum_singleton, ← SchwartzMap.norm_toLp_sq, norm_toLp_gaussian_sq,
    Module.finrank_self, Nat.cast_one, ← Real.sqrt_eq_rpow, norm_toLp_lineDerivOp_one_gaussian_sq]
  field_simp
  ring

end TauCeti
