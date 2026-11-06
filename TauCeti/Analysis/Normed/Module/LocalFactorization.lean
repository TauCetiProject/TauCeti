/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Field.Basic

/-!
# Uniqueness of the exponent of a local factorization

Near a point `z` of a nontrivially normed field `𝕜`, a function with values in a normed space
can be written as `(w - z) ^ n • v w` with `v` continuous and nonzero at `z` for at most one
`n` (`TauCeti.eq_of_eventually_sub_pow_smul_eq`). Punctured neighbourhoods of `z` are
nontrivial, and off `z` the power can be cancelled. This is the continuous-factor analogue of
Mathlib's `AnalyticAt.unique_eventuallyEq_pow_smul_ne_zero`, which requires analytic factors.
-/

public section

open Filter Topology

namespace TauCeti

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The exponent of a local factorization `(w - z) ^ m • v w`, with `v` continuous and nonzero at
`z`, is unique. -/
theorem eq_of_eventually_sub_pow_smul_eq {z : 𝕜} {m n : ℕ} {u v : 𝕜 → E}
    (hu : ContinuousAt u z) (hu₀ : u z ≠ 0) (hv : ContinuousAt v z) (hv₀ : v z ≠ 0)
    (h : ∀ᶠ w in 𝓝 z, (w - z) ^ m • u w = (w - z) ^ n • v w) : m = n := by
  wlog hmn : m < n generalizing m n u v
  · rcases (not_lt.mp hmn).eq_or_lt with h' | h'
    · exact h'.symm
    · exact (this hv hv₀ hu hu₀ (h.mono fun w hw ↦ hw.symm) h').symm
  exfalso
  -- Off `z`, cancelling `(w - z) ^ m` gives `u w = (w - z) ^ (n - m) • v w`, which tends to `0`.
  have hlim : Tendsto (fun w ↦ (w - z) ^ (n - m) • v w) (𝓝[≠] z) (𝓝 (u z)) := by
    refine (hu.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with w hw hwz
    apply smul_right_injective E (pow_ne_zero m (sub_ne_zero.mpr hwz))
    simp only [hw, smul_smul, ← pow_add, Nat.add_sub_cancel' hmn.le]
  have h0 : Tendsto (fun w ↦ (w - z) ^ (n - m) • v w) (𝓝[≠] z) (𝓝 0) := by
    have hc : ContinuousAt (fun w ↦ (w - z) ^ (n - m) • v w) z :=
      ((continuousAt_id.sub continuousAt_const).pow _).smul hv
    simpa [zero_pow (Nat.sub_ne_zero_of_lt hmn)] using hc.tendsto.mono_left nhdsWithin_le_nhds
  exact hu₀ (tendsto_nhds_unique hlim h0)

end TauCeti
