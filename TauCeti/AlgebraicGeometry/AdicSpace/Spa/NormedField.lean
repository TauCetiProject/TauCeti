/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Basic
public import TauCeti.RingTheory.Huber.Normed
import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent

/-!
# The adic spectrum of a normed field

For a normed field `K` with an ultrametric norm, every point `v` of `Spa (K, K°)` compares
elements of `K` exactly as the norm does: `v(x) ≤ v(y)` if and only if `‖x‖ ≤ ‖y‖`. The plus ring
`K°` is the closed unit ball, which gives one direction, and continuity of `v` gives the other,
since an element of norm less than one is topologically nilpotent.

This is how points of `Spa (K, K°)` enter computations on spaces over `K`: whenever a point of
an adic spectrum over `K` pulls back to `Spa (K, K°)`, as every point of the closed polydisc does
along the constant embedding, it compares constants by their norms.

## Main results

* `TauCeti.ValuationSpectrum.vle_iff_norm_le_of_mem_spa`: every point of `Spa (K, K°)` compares
  elements of `K` by their norms.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 7.23 and
  Example 7.57.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- **Every point of `Spa (K, K°)` compares elements of `K` by their norms.** If `‖x‖ ≤ ‖y‖`
then `x / y` is power-bounded, so `v(x / y) ≤ 1`. If `‖y‖ < ‖x‖` then `y / x` is topologically
nilpotent, so `v(y / x) < 1` by continuity. -/
theorem vle_iff_norm_le_of_mem_spa {v : Spv K} (hv : v ∈ spa (powerBoundedSubring K))
    (x y : K) : v.toValuativeRel.vle x y ↔ ‖x‖ ≤ ‖y‖ := by
  rw [← valuation_le_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra! hlt
    have hx : x ≠ 0 := norm_pos_iff.mp ((norm_nonneg y).trans_lt hlt)
    have hnil : IsTopologicallyNilpotent (y / x) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by
        rwa [norm_div, div_lt_one (norm_pos_iff.mpr hx)])
    have hlt' := ((isContinuous_def v).mp ((mem_spa_iff _ v).mp hv).1
      ).lt_one_of_isTopologicallyNilpotent hnil
    have hvx : v.valuation x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
    rw [map_div₀, div_lt_one₀ (zero_lt_iff.mpr hvx)] at hlt'
    exact hlt'.not_ge h
  · rcases eq_or_ne y 0 with rfl | hy
    · rw [norm_zero, norm_le_zero_iff] at h
      rw [h]
    have hxy : x / y ∈ powerBoundedSubring K := by
      rw [mem_powerBoundedSubring, isPowerBounded_iff_norm_le_one, norm_div]
      exact div_le_one_of_le₀ h (norm_nonneg y)
    have hle := valuation_le_one_of_mem_spa hv hxy
    rwa [map_div₀, div_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hy))] at hle

end TauCeti.ValuationSpectrum
