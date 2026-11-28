/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exponential lower bounds for submultiplicative sequences

For a nonnegative submultiplicative sequence `c : ℕ → ℝ` (`Submultiplicative c`) and a positive
real base `b`, if `b ^ q ≤ c q` holds for arbitrarily large `q`, then `b ^ n ≤ c n` holds for
every `n : ℕ` (a direct consequence of Fekete's submultiplicative lemma).

## Main results

* `TauCeti.one_le_of_submultiplicative`: if `0 < c q` for some `q`, then `1 ≤ c 0`.
* `TauCeti.pow_le_of_submultiplicative`: if `b ^ q ≤ c q` for arbitrarily large `q`, then
  `b ^ n ≤ c n` for every `n : ℕ`.
* `TauCeti.pow_le_of_submultiplicative_frequently`: the same bound stated via `Filter.Frequently`.
* `TauCeti.le_rpow_inv_of_submultiplicative`: the `n`-th root form `b ≤ c n ^ (n : ℝ)⁻¹` for
  `0 < n`.

## Provenance

Adapted from `New.pow_le_of_submultiplicative` in `src/New/Derivatives/Sharpness/OneCurve.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean), commit
`72fead102f663d5c7a407964a13dc0cf9d977207` (Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

namespace TauCeti

/-- A submultiplicative sequence `c : ℕ → ℝ` with at least one positive value satisfies
`1 ≤ c 0`. -/
theorem one_le_of_submultiplicative {c : ℕ → ℝ} (hsub : Submultiplicative c)
    {q : ℕ} (hq : 0 < c q) : 1 ≤ c 0 := by
  simpa using one_le_of_le_mul_left₀ hq (by simpa using hsub q 0)

/-- If a nonnegative submultiplicative sequence `c : ℕ → ℝ` satisfies `b ^ q ≤ c q` for
arbitrarily large `q`, where `0 < b`, then `b ^ n ≤ c n` for every `n : ℕ`. -/
theorem pow_le_of_submultiplicative {c : ℕ → ℝ} {b : ℝ} (hb : 0 < b) (hc : ∀ n, 0 ≤ c n)
    (hsub : Submultiplicative c) (h_large : ∀ M : ℕ, ∃ q ≥ M, b ^ q ≤ c q) (n : ℕ) :
    b ^ n ≤ c n := by
  obtain rfl | hn := n.eq_zero_or_pos
  · obtain ⟨q, -, hq⟩ := h_large 0
    simpa using one_le_of_submultiplicative hsub ((pow_pos hb q).trans_le hq)
  have hroot {k : ℕ} (hk : 0 < k) : c k ^ (k : ℝ)⁻¹ < b ↔ c k < b ^ k := by
    simpa only [Real.rpow_natCast] using
      Real.rpow_inv_lt_iff_of_pos (hc k) hb.le (Nat.cast_pos.mpr hk : (0 : ℝ) < k)
  by_contra! h
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    (hsub.eventually_rpow_lt_of_rpow_lt hc hn.ne' ((hroot hn).mpr h))
  obtain ⟨q, hq, h_large_q⟩ := h_large (max M 1)
  exact h_large_q.not_gt ((hroot (by omega : 0 < q)).mp (hM q (by omega)))

/-- Filter-`Frequently` form of `TauCeti.pow_le_of_submultiplicative`. -/
theorem pow_le_of_submultiplicative_frequently {c : ℕ → ℝ} {b : ℝ} (hb : 0 < b)
    (hc : ∀ n, 0 ≤ c n) (hsub : Submultiplicative c)
    (h_freq : ∃ᶠ q : ℕ in Filter.atTop, b ^ q ≤ c q) (n : ℕ) :
    b ^ n ≤ c n :=
  pow_le_of_submultiplicative hb hc hsub (Filter.frequently_atTop.mp h_freq) n

/-- Root form of `TauCeti.pow_le_of_submultiplicative`: for `0 < n`, `b ≤ c n ^ (n : ℝ)⁻¹`. -/
theorem le_rpow_inv_of_submultiplicative {c : ℕ → ℝ} {b : ℝ} (hb : 0 < b) (hc : ∀ n, 0 ≤ c n)
    (hsub : Submultiplicative c) (h_large : ∀ M : ℕ, ∃ q ≥ M, b ^ q ≤ c q) {n : ℕ} (hn : 0 < n) :
    b ≤ c n ^ (n : ℝ)⁻¹ :=
  (Real.le_rpow_inv_iff_of_pos hb.le (hc n) (Nat.cast_pos.mpr hn)).mpr
    (by simpa [Real.rpow_natCast] using pow_le_of_submultiplicative hb hc hsub h_large n)

end TauCeti
