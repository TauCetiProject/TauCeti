/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Elementary asymptotic criteria

Two general criteria that supplement Mathlib's asymptotics API.

For functions into a normed division ring, `f` satisfies `f = a g + o(g)` exactly when `f / g`
tends to `a`, provided `g` is eventually nonzero. This criterion converts little-o error estimates
into limits of normalized functions, and conversely recovers error estimates from ratio limits.
The quotient is right division: multiplication need not be commutative. For ordered fields,
the ratio formulation also supports order arguments.

In a seminormed group the norm is at most one on a neighbourhood of the origin, so there a higher
power of the norm is dominated by any lower one. This is the comparison that lets a Taylor
remainder of one order be read as a remainder of a smaller order.

## Main results

* `Asymptotics.isLittleO_sub_mul_iff_tendsto_div`: `f - a g = o(g)` if and only if
  `f / g → a`, for an eventually nonzero `g`.
* `Asymptotics.isBigO_norm_pow_norm_pow_nhds_zero_of_le`: `‖x‖ ^ m = O(‖x‖ ^ n)` at the origin
  whenever `n ≤ m`.

## Related results

Mathlib's `Asymptotics.isLittleO_iff_tendsto'` is the underlying zero-limit ratio criterion, and
`Asymptotics.isBigO_pow_pow_cobounded_of_le` is the comparison of powers at infinity.
-/

public section

open Filter Topology

namespace Asymptotics

/-- **A linear asymptotic is a limit of ratios.** For an eventually nonzero `g`, `f = a g + o(g)`
if and only if `f / g` tends to `a`. -/
theorem isLittleO_sub_mul_iff_tendsto_div {α 𝕜 : Type*} [NormedDivisionRing 𝕜]
    {l : Filter α} {f g : α → 𝕜} {a : 𝕜} (hg : ∀ᶠ x in l, g x ≠ 0) :
    (fun x ↦ f x - a * g x) =o[l] g ↔ Tendsto (fun x ↦ f x / g x) l (𝓝 a) := by
  rw [isLittleO_iff_tendsto' (hg.mono fun x hx ↦ by simp [hx])]
  refine (tendsto_congr' (hg.mono fun x hx ↦ ?_)).trans tendsto_sub_nhds_zero_iff
  rw [sub_div, mul_div_cancel_right₀ _ hx]

/-- **At the origin a higher power of the norm is dominated by a lower one.** The norm is at most
one near `0`, so `‖x‖ ^ m = O(‖x‖ ^ n)` whenever `n ≤ m`. -/
theorem isBigO_norm_pow_norm_pow_nhds_zero_of_le {E : Type*} [SeminormedAddCommGroup E]
    {m n : ℕ} (h : n ≤ m) :
    (fun x : E ↦ ‖x‖ ^ m) =O[𝓝 (0 : E)] fun x ↦ ‖x‖ ^ n := by
  refine isBigO_iff.2 ⟨1, ?_⟩
  filter_upwards [Metric.closedBall_mem_nhds (0 : E) one_pos] with x hx
  simp only [one_mul, norm_pow, norm_norm]
  exact pow_le_pow_of_le_one (norm_nonneg x) (by simpa [Metric.mem_closedBall] using hx) h

end Asymptotics
