/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.RankOne

/-!
# A criterion for a valuative relation not to have rank at most one

A valuative relation has rank at most one (`ValuativeRel.IsRankLeOne`) exactly when its value
group is archimedean (`ValuativeRel.isRankLeOne_iff_mulArchimedean`). So it fails to have rank at
most one as soon as some value `γ > 1` has all its powers bounded. This file states that test in
terms of ring elements: if `g <ᵥ f` and `fⁿ ≤ᵥ gⁿ h` for every `n`, then `γ = v(f) / v(g)` is
larger than `1` and `γⁿ ≤ v(h)` for every `n`.

This is how one shows that an explicit valuation has rank at least two, for instance the points of
type (5) of the adic closed unit disc, which take values infinitesimally close to a real radius.

## Main results

* `ValuativeRel.not_isRankLeOne_of_forall_pow_vle`: if `g <ᵥ f` and `fⁿ ≤ᵥ gⁿ h` for every `n`,
  the valuative relation does not have rank at most one.
-/

public section

namespace ValuativeRel

variable {R : Type*} [Ring R] [ValuativeRel R]

/-- **A value above `1` with bounded powers rules out rank at most one.** If `g <ᵥ f` and
`fⁿ ≤ᵥ gⁿ h` for every `n`, then `v(f) / v(g) > 1` has all its powers bounded by `v(h)`, so the
value group is not archimedean. -/
theorem not_isRankLeOne_of_forall_pow_vle {f g h : R} (hgf : g <ᵥ f)
    (hpow : ∀ n : ℕ, f ^ n ≤ᵥ g ^ n * h) : ¬ IsRankLeOne R := by
  intro hR
  set v := valuation R
  have hlt : v g < v f := v.vlt_iff_lt.mp hgf
  have hle (n : ℕ) : v f ^ n ≤ v g ^ n * v h := by
    simpa only [map_pow, map_mul] using v.vle_iff_le.mp (hpow n)
  have hg : 0 < v g := pos_of_ne_zero fun h0 ↦ hlt.not_ge (by simpa [h0] using hle 1)
  -- `γ = v(f) / v(g)` exceeds `1`, and every power of it is at most `v(h)`
  have hγ : 1 < v f / v g := (one_lt_div₀ hg).mpr hlt
  have hγle (n : ℕ) : (v f / v g) ^ n ≤ v h := by
    rw [div_pow, div_le_iff₀ (pow_pos hg n), mul_comm]
    exact hle n
  obtain ⟨n, hn⟩ := MulArchimedean.arch (v h) hγ
  exact ((hγle (n + 1)).trans hn).not_gt (pow_lt_pow_right₀ hγ n.lt_succ_self)

end ValuativeRel
