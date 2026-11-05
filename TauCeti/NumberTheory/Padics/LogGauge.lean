/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.Commensurable
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

Every nonzero norm on `ℚ_[p]` is an integer power of `p⁻¹`, so such a `ϖ` is commensurable, and
its rational valuation `ϖ.ratAddValuation` is again `Padic.addValuation`, with its integer values
viewed as rationals. For instance it takes the values `1` at `p` and `-2` at `p⁻²`.

## Main results

* `TauCeti.NormedRing.PseudoUniformizer.logGauge_eq_map_padicAddValuation`: the logarithmic gauge
  of a multiplicative pseudo-uniformiser of norm `p⁻¹` is `Padic.addValuation`.
* `TauCeti.NormedRing.PseudoUniformizer.isCommensurable_of_norm_eq_inv`: such a pseudo-uniformiser
  is commensurable.
* `TauCeti.NormedRing.PseudoUniformizer.ratAddValuation_eq_map_padicAddValuation`: its rational
  valuation is `Padic.addValuation`.
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

/-- On `ℚ_[p]`, a multiplicative pseudo-uniformiser of norm `p⁻¹` is commensurable: every nonzero
norm is an integer power of `p⁻¹`. -/
theorem isCommensurable_of_norm_eq_inv (ϖ : PseudoUniformizer ℚ_[p])
    (hϖ : ‖(ϖ.unit : ℚ_[p])‖ = (p : ℝ)⁻¹) : ϖ.IsCommensurable :=
  isCommensurable_of_forall_norm_eq_zpow fun x hx ↦ ⟨x.valuation, by
    rw [Padic.norm_eq_zpow_neg_valuation (norm_ne_zero_iff.1 hx), hϖ, inv_zpow']⟩

/-- On `ℚ_[p]`, the rational valuation of a multiplicative pseudo-uniformiser of norm `p⁻¹` is the
`p`-adic additive valuation `Padic.addValuation`, with its integer values viewed as rationals. -/
theorem ratAddValuation_eq_map_padicAddValuation (ϖ : PseudoUniformizer ℚ_[p])
    (hϖ : ‖(ϖ.unit : ℚ_[p])‖ = (p : ℝ)⁻¹) (hc : ϖ.IsCommensurable) (x : ℚ_[p]) :
    ϖ.ratAddValuation hc x = (Padic.addValuation x).map ((↑) : ℤ → ℚ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [Padic.addValuation.apply hx, WithTop.map_coe,
    ratAddValuation_eq_intCast hc (by rw [Padic.norm_eq_zpow_neg_valuation hx, hϖ, inv_zpow'])]

/-- On `ℚ_[p]`, normalised at `p`, the rational valuation of `p ^ n` is `n`, for `n ∈ ℤ`; for
instance `v_p(p⁻²) = -2`. -/
example (ϖ : PseudoUniformizer ℚ_[p]) (hϖ : (ϖ.unit : ℚ_[p]) = p) :
    ϖ.ratAddValuation (isCommensurable_of_norm_eq_inv ϖ (by rw [hϖ, Padic.norm_p]))
      ((p : ℚ_[p]) ^ (-2 : ℤ)) = ((-2 : ℚ) : WithTop ℚ) := by
  have h : (p : ℚ_[p]) ^ (-2 : ℤ) = ((ϖ.unit ^ (-2 : ℤ) : ℚ_[p]ˣ) : ℚ_[p]) := by
    rw [Units.val_zpow_eq_zpow_val, hϖ]
  rw [h, ratAddValuation_zpow]
  norm_num

end TauCeti.NormedRing.PseudoUniformizer
