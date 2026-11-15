/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic

import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.Interval
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Bounds for linear forms over normed rings

This file records a Cramer's-rule bound for two linear forms in two variables and its uniform
consequence for a finite family of pairwise non-proportional linear forms. Both take coefficients
and variables in a commutative ring whose norm is multiplicative (`NormMulClass`), such as a
normed field or `ℤ`. It also records a lower bound for the single form `x - α y` in a seminormed
ring when `x` is large compared with `y`.

## Main results

* `TauCeti.norm_det_mul_max_norm_le`: a Cramer's-rule bound for two linear forms.
* `TauCeti.half_max_norm_le_norm_sub_of_mul_le`: if `x` is large compared with `y`, then
  `‖x - α y‖` is at least half of `max(‖x‖, ‖y‖)`.
* `TauCeti.exists_pos_mul_max_norm_le_norm_of_pairwise`: all but a smallest member of a finite
  family of pairwise non-proportional linear forms are uniformly bounded below.
-/

public section

open Filter Finset Topology

namespace TauCeti

/-- If `‖x‖ ≥ 2 (‖α‖ + 1) ‖y‖`, then `‖x - α y‖ ≥ max(‖x‖, ‖y‖) / 2`. -/
theorem half_max_norm_le_norm_sub_of_mul_le {R : Type*} [NonUnitalSeminormedRing R] (α x y : R)
    (hbig : 2 * (‖α‖ + 1) * ‖y‖ ≤ ‖x‖) : max ‖x‖ ‖y‖ / 2 ≤ ‖x - α * y‖ := by
  rw [max_eq_left (by nlinarith [norm_nonneg α, norm_nonneg y])]
  nlinarith [norm_sub_norm_le x (α * y), norm_mul_le α y, norm_nonneg α, norm_nonneg y]

/-- **Cramer's rule bound** for two linear forms `L = a x + b y` and `L' = a' x + b' y` in two
variables: the determinant `D = a b' - b a'` satisfies
`‖D‖ max(‖x‖, ‖y‖) ≤ (‖a‖ + ‖b‖ + ‖a'‖ + ‖b'‖) (‖L‖ + ‖L'‖)`. -/
theorem norm_det_mul_max_norm_le {R : Type*} [SeminormedCommRing R] [NormMulClass R]
    (a b a' b' x y : R) :
    ‖a * b' - b * a'‖ * max ‖x‖ ‖y‖ ≤
      (‖a‖ + ‖b‖ + ‖a'‖ + ‖b'‖) * (‖a * x + b * y‖ + ‖a' * x + b' * y‖) := by
  set L := a * x + b * y
  set L' := a' * x + b' * y
  have hx : (a * b' - b * a') * x = b' * L - b * L' := by ring
  have hy : (a * b' - b * a') * y = a * L' - a' * L := by ring
  rw [mul_max_of_nonneg _ _ (norm_nonneg _), ← norm_mul, ← norm_mul, hx, hy]
  refine max_le ((norm_sub_le _ _).trans ?_) ((norm_sub_le _ _).trans ?_) <;>
    simp only [norm_mul] <;> nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg a',
      norm_nonneg b', norm_nonneg L, norm_nonneg L']

/-- Among pairwise non-proportional linear forms `ℓ.1 x + ℓ.2 y`, `ℓ ∈ T`, in two variables, all
but one are large at every point: there is `c > 0` such that if `ℓ₀ ∈ T` minimizes
`‖ℓ.1 x + ℓ.2 y‖`, then every other `ℓ ∈ T` has `‖ℓ.1 x + ℓ.2 y‖ ≥ c max(‖x‖, ‖y‖)`. -/
theorem exists_pos_mul_max_norm_le_norm_of_pairwise {R : Type*} [NormedCommRing R]
    [NormMulClass R] {T : Finset (R × R)}
    (hT : (T : Set (R × R)).Pairwise fun ℓ ℓ' ↦ ℓ.1 * ℓ'.2 - ℓ.2 * ℓ'.1 ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x y : R, ∀ ℓ₀ ∈ T,
      (∀ ℓ ∈ T, ‖ℓ₀.1 * x + ℓ₀.2 * y‖ ≤ ‖ℓ.1 * x + ℓ.2 * y‖) →
        ∀ ℓ ∈ T, ℓ ≠ ℓ₀ → c * max ‖x‖ ‖y‖ ≤ ‖ℓ.1 * x + ℓ.2 * y‖ := by
  -- For each pair `ℓ ≠ ℓ₀`, every `c ≤ ‖D‖ / (2 N + 1)` works, by `norm_det_mul_max_norm_le`.
  have h : ∀ p ∈ T.offDiag, ∀ᶠ c in 𝓝[>] (0 : ℝ), ∀ x y : R,
      ‖p.2.1 * x + p.2.2 * y‖ ≤ ‖p.1.1 * x + p.1.2 * y‖ →
        c * max ‖x‖ ‖y‖ ≤ ‖p.1.1 * x + p.1.2 * y‖ := by
    rintro ⟨ℓ, ℓ₀⟩ hp
    obtain ⟨hℓ, hℓ₀, hne⟩ := Finset.mem_offDiag.1 hp
    set D := ℓ.1 * ℓ₀.2 - ℓ.2 * ℓ₀.1
    set N := ‖ℓ.1‖ + ‖ℓ.2‖ + ‖ℓ₀.1‖ + ‖ℓ₀.2‖
    have hD : 0 < ‖D‖ := norm_pos_iff.2 (hT hℓ hℓ₀ hne)
    have hN : 0 ≤ N := by positivity
    filter_upwards [Ioc_mem_nhdsGT (div_pos hD (by positivity : (0 : ℝ) < 2 * N + 1))]
      with c hc x y hle
    have key := norm_det_mul_max_norm_le ℓ.1 ℓ.2 ℓ₀.1 ℓ₀.2 x y
    have hM : 0 ≤ max ‖x‖ ‖y‖ := (norm_nonneg x).trans (le_max_left _ _)
    have hc' : c * (2 * N + 1) ≤ ‖D‖ := (le_div_iff₀ (by positivity)).1 hc.2
    nlinarith [norm_nonneg (ℓ.1 * x + ℓ.2 * y)]
  obtain ⟨c, hc, hc₀⟩ := ((eventually_all_finset _).2 h).and self_mem_nhdsWithin |>.exists
  exact ⟨c, hc₀, fun x y ℓ₀ hℓ₀ hmin ℓ hℓ hne ↦
    hc ⟨ℓ, ℓ₀⟩ (Finset.mem_offDiag.2 ⟨hℓ, hℓ₀, hne⟩) x y (hmin ℓ hℓ)⟩

end TauCeti
