/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import TauCeti.Analysis.Calculus.FDeriv.Antilipschitz

/-!
# Regression examples: inverse-Lipschitz bounds at a point and the squaring map

These examples check `TauCeti.AntilipschitzWithFrom`, the global lower bound
`dist x y ≤ K * dist (f x) (f y)` at a fixed point `x`, on two maps of `ℂ`:

* the identity is antilipschitz from every point with constant `1`, the ratio
  `dist (f x) (f y) / dist x y` being identically `1`;
* the squaring map `z ↦ z²` has the invertible derivative `2 x` at every `x ≠ 0`, so near `x` it
  satisfies the bound with some constant;
* but over the whole of `ℂ` it is antilipschitz from no point `x ≠ 0`, with any constant, since it
  identifies `x` with `-x`. A bound required only near the anchor point would not tell this double
  cover apart from an injective map.
-/

open Filter Topology TauCeti
open scoped NNReal

-- The identity is antilipschitz from every point with constant `1`.
example (x : ℂ) : AntilipschitzWithFrom 1 id x :=
  AntilipschitzWith.id.antilipschitzWithFrom x

-- Near a point `x ≠ 0`, the squaring map separates points from `x`, as its derivative `2 x` is
-- invertible.
example {x : ℂ} (hx : x ≠ 0) :
    ∃ K : ℝ≥0, ∀ᶠ y in 𝓝 x, dist x y ≤ K * dist (x ^ 2) (y ^ 2) := by
  have h2x : ‖(2 : ℂ) * x‖ ≠ 0 := norm_ne_zero_iff.2 (mul_ne_zero two_ne_zero hx)
  refine (hasDerivAt_pow 2 x).hasFDerivAt.exists_eventually_dist_le_mul_dist
    (C := ‖(2 : ℂ) * x‖₊⁻¹) (.of_le_mul_dist fun y z ↦ ?_)
  -- The derivative `2 x` multiplies distances by `‖2 x‖`.
  calc dist y z = ‖(2 : ℂ) * x‖⁻¹ * (‖y - z‖ * ‖(2 : ℂ) * x‖) := by
        rw [dist_eq_norm]; field_simp
    _ ≤ _ := by simp [dist_eq_norm, ← sub_mul]

-- Over all of `ℂ`, the squaring map is antilipschitz from no point `x ≠ 0`.
example {x : ℂ} (hx : x ≠ 0) (K : ℝ≥0) : ¬ AntilipschitzWithFrom K (fun z : ℂ ↦ z ^ 2) x :=
  fun h ↦ hx (CharZero.neg_eq_self_iff.1 (h.eq_of_apply_eq (y := -x) (by simp)))
