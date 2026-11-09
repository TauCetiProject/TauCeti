/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.LogGauge.Rational
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import TauCeti.Analysis.Normed.Ring.UnitBall

/-!
# Order properties and discrete-ring comparison for rational valuations

The canonical rational valuation of a commensurable pseudo-uniformiser is defined in
`LogGauge.Rational`. This file characterizes its real refinement, proves its strict-order and
unit-power formulas, and compares it with the normalized valuation of a discrete valuation ring.
-/

public section

namespace TauCeti.NormedRing.PseudoUniformizer

variable {R : Type*} [SeminormedRing R] {ϖ : PseudoUniformizer R} {x y : R}
  [IsUltrametricDist R] [NormMulClass R] (hϖ : ϖ.IsCommensurable)

/-- **Uniqueness**: the rational valuation is the only additive valuation with values in
`WithTop ℚ` whose real values are the logarithmic gauge. -/
theorem eq_ratAddValuation_iff {v : AddValuation R (WithTop ℚ)} :
    v = ϖ.ratAddValuation hϖ ↔ ∀ x, (v x).map ((↑) : ℚ → ℝ) = ϖ.logGauge x := by
  refine ⟨fun h x ↦ h ▸ map_ratAddValuation hϖ x, fun h ↦ AddValuation.ext fun x ↦ ?_⟩
  exact (WithTop.map_injective (Rat.cast_injective (α := ℝ))) (by rw [h, map_ratAddValuation])

omit hϖ in
/-- A rational-valued additive valuation refining the logarithmic gauge exists exactly when `ϖ`
is commensurable. -/
theorem isCommensurable_iff_exists_addValuation :
    ϖ.IsCommensurable ↔
      ∃ v : AddValuation R (WithTop ℚ), ∀ x, (v x).map ((↑) : ℚ → ℝ) = ϖ.logGauge x := by
  refine ⟨fun hϖ ↦ ⟨_, map_ratAddValuation hϖ⟩, fun ⟨v, hv⟩ ↦ ?_⟩
  refine isCommensurable_iff_exists_rat.2 fun x hx ↦ ?_
  have hne : v x ≠ ⊤ := fun h ↦ hx (logGauge_eq_top_iff.1 (by rw [← hv, h, WithTop.map_top]))
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 hne
  exact ⟨q, by rw [← hv, ← hq, WithTop.map_coe]⟩

/-- The rational valuation strictly reverses the order of the norm. -/
theorem ratAddValuation_lt_ratAddValuation_iff :
    ϖ.ratAddValuation hϖ x < ϖ.ratAddValuation hϖ y ↔ ‖y‖ < ‖x‖ := by
  rw [lt_iff_not_ge, ratAddValuation_le_ratAddValuation_iff, not_le]

/-- The rational valuation is nonnegative exactly on the closed unit ball. -/
theorem ratAddValuation_nonneg_iff : 0 ≤ ϖ.ratAddValuation hϖ x ↔ ‖x‖ ≤ 1 := by
  rw [← (ϖ.ratAddValuation hϖ).map_one, ratAddValuation_le_ratAddValuation_iff, ϖ.norm_one]

/-- The rational valuation is positive exactly on the open unit ball. -/
theorem ratAddValuation_pos_iff : 0 < ϖ.ratAddValuation hϖ x ↔ ‖x‖ < 1 := by
  rw [← (ϖ.ratAddValuation hϖ).map_one, ratAddValuation_lt_ratAddValuation_iff, ϖ.norm_one]

/-- The rational valuation of `ϖ ^ n` is `n`, for `n ∈ ℤ`. -/
@[simp]
theorem ratAddValuation_zpow (n : ℤ) :
    ϖ.ratAddValuation hϖ ((ϖ.unit ^ n : Rˣ) : R) = ((n : ℚ) : WithTop ℚ) :=
  (WithTop.map_injective (Rat.cast_injective (α := ℝ))) (by
    rw [map_ratAddValuation, logGauge_zpow, WithTop.map_coe, Rat.cast_intCast])

/-- The rational valuation of `ϖ ^ n` is `n`, for `n ∈ ℕ`. -/
theorem ratAddValuation_unit_pow (n : ℕ) :
    ϖ.ratAddValuation hϖ ((ϖ.unit : R) ^ n) = ((n : ℚ) : WithTop ℚ) := by
  simp

/-- **The logarithmic form of norm recovery**: `-log ‖x‖ = (-log ‖ϖ‖) v_ϖ(x)` for an element of
nonzero norm. -/
theorem neg_log_norm_eq_mul_ratAddValuation (hx : ‖x‖ ≠ 0) :
    -Real.log ‖x‖ = -Real.log ‖(ϖ.unit : R)‖ *
      ((((ϖ.ratAddValuation hϖ x).untop ((ratAddValuation_eq_top_iff hϖ).not.2 hx)) : ℚ) : ℝ) := by
  conv_lhs => rw [norm_eq_rpow_ratAddValuation hϖ hx, Real.log_rpow ϖ.norm_pos]
  ring

/-- **Comparison with a discrete valuation ring.** Let `O` be a discrete valuation ring and
`φ : O →+* R` a ring homomorphism into the closed unit ball, mapping an irreducible `π` to an
element of norm `‖ϖ‖`, as for the valuation ring of a discretely valued field and a uniformiser
`ϖ = π`. Then the rational valuation restricts on `O` to the normalised valuation
`IsDiscreteValuationRing.addVal O`, with its values in `ℕ∞` read in `WithTop ℚ`. -/
theorem ratAddValuation_map_eq_addVal {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (φ : O →+* R) (hφ : ∀ a, ‖φ a‖ ≤ 1) {π : O} (hπ : Irreducible π)
    (hπϖ : ‖φ π‖ = ‖(ϖ.unit : R)‖) (a : O) :
    ϖ.ratAddValuation hϖ (φ a) =
      ENat.map ((↑) : ℕ → ℚ) (IsDiscreteValuationRing.addVal O a) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  have := ϖ.normOneClass
  have h : ‖φ (u * π ^ n)‖ = ‖(ϖ.unit : R)‖ ^ (n : ℤ) := by
    rw [map_mul, map_pow, _root_.norm_mul, _root_.norm_pow,
      norm_map_eq_one_of_isUnit hφ u.isUnit, hπϖ, one_mul, zpow_natCast]
  rw [ratAddValuation_eq_intCast hϖ h, IsDiscreteValuationRing.addVal_def' u hπ n,
    ENat.map_natCast, Int.cast_natCast]

end TauCeti.NormedRing.PseudoUniformizer
