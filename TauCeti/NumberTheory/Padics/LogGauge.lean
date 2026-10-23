/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.LogGauge
public import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# The logarithmic gauge on `ℚ_[p]`

On the `p`-adic field the norm is multiplicative and ultrametric with `‖p‖ = p⁻¹`. For a
multiplicative pseudo-uniformiser `ϖ` of norm `p⁻¹`, for instance `p` itself through
`TauCeti.NormedRing.PseudoUniformizer.ofAlgebraMap` and `padicNormE.norm_p`, the logarithmic gauge
`v_ϖ(x) = log ‖x‖ / log ‖ϖ‖` is the `p`-adic valuation: it agrees with Mathlib's integer-valued
`Padic.addValuation` after viewing its integer values as reals. Thus the additive valuation
`ϖ.addValuation`, with values in `WithTop ℝ`, is the real form of the `p`-adic valuation
normalised by `v(p) = 1`.

## Main results

* `TauCeti.NormedRing.PseudoUniformizer.logGauge_eq_map_padicAddValuation`: the logarithmic gauge
  of a multiplicative pseudo-uniformiser of norm `p⁻¹` is `Padic.addValuation`.
-/

public section

namespace TauCeti.NormedRing.PseudoUniformizer

variable {p : ℕ} [Fact p.Prime]

/-- On `ℚ_[p]`, the logarithmic gauge of a multiplicative pseudo-uniformiser of norm `p⁻¹` is the
`p`-adic additive valuation `Padic.addValuation`, with its integer values viewed as reals. -/
theorem logGauge_eq_map_padicAddValuation (ϖ : PseudoUniformizer ℚ_[p])
    (hϖ : ‖(ϖ.unit : ℚ_[p])‖ = (p : ℝ)⁻¹) (x : ℚ_[p]) :
    ϖ.logGauge x = (Padic.addValuation x).map ((↑) : ℤ → ℝ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hp : (0 : ℝ) < p := Nat.cast_pos.2 (Fact.out : p.Prime).pos
  rw [Padic.addValuation.apply hx, WithTop.map_coe, logGauge_eq_coe_iff, hϖ,
    Padic.norm_eq_zpow_neg_valuation hx, Real.inv_rpow hp.le, ← Real.rpow_neg hp.le,
    ← Real.rpow_intCast, Int.cast_neg]

/-- On `ℚ_[p]`, the additive valuation attached to a multiplicative pseudo-uniformiser of norm
`p⁻¹` is `Padic.addValuation`, with its integer values viewed as reals. -/
theorem addValuation_eq_map_padicAddValuation (ϖ : PseudoUniformizer ℚ_[p])
    (hϖ : ‖(ϖ.unit : ℚ_[p])‖ = (p : ℝ)⁻¹) (x : ℚ_[p]) :
    ϖ.addValuation x = (Padic.addValuation x).map ((↑) : ℤ → ℝ) := by
  rw [addValuation_apply, logGauge_eq_map_padicAddValuation ϖ hϖ]

end TauCeti.NormedRing.PseudoUniformizer
