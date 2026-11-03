/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.RCLike.Lemmas

/-!
# The zero count of an analytic function on a disc

The zero count of `f` on an open disc is the finitely supported sum
`∑ᶠ z ∈ ball c R, analyticOrderNatAt f z`. It is what the argument principle produces — through
`TauCeti.Contour.argumentPrinciple_divisor` and the bridge
`MeromorphicOn.divisor_eq_analyticOrderNatAt` — and what Rouché's theorem
(`TauCeti.rouche_symm`) and Hurwitz's theorem (`TauCeti.hurwitz`) compare. This file collects the
three facts about that sum which those consumers need, none of which mentions either theorem.
They are stated for a function `f : 𝕜 → E` into a normed space; the detection criterion needs the
closed disc to be preconnected, so it is stated over `RCLike 𝕜`.

Care is needed about points of *infinite* order, where `f` vanishes identically nearby:
`analyticOrderNatAt` reads `0` there, exactly as it does where `f` does not vanish at all, so the
count does not see such a point. That is why detecting a zero from a vanishing count
(`AnalyticOnNhd.finsum_analyticOrderNatAt_ball_eq_zero_iff`) needs a hypothesis ruling infinite
order out. One point of the closed disc at which `f` is nonzero is enough: the disc is convex, hence
preconnected, so `AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected` propagates the finite
order there to every point.

## Main results

* `MeromorphicOn.analyticOrderNatAt_le_finsum_ball` — the order of vanishing at a single point of
  the open disc is at most the total count.
* `TauCeti.finsum_mem_analyticOrderNatAt_eq_zero_of_forall_ne_zero` — a function without zeros on
  a set has count `0` there.
* `AnalyticOnNhd.finsum_analyticOrderNatAt_ball_eq_zero_iff` — conversely, given a point of the
  closed disc where `f` does not vanish, a count of `0` means there is no zero in the open disc at
  all.

## References

* [Mathlib PR #33505](https://github.com/leanprover-community/mathlib4/pull/33505), the preceding
  human-curated Riemann-mapping development and its local analytic prerequisites.
-/

public section

open Metric

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {f : 𝕜 → E} {c : 𝕜} {R : ℝ}

/-- The order of vanishing at a single point of the open disc is at most the total zero count of a
function meromorphic on the closed disc. At a pole or a point of infinite order the left side reads
`0`, so the bound holds trivially there. -/
theorem MeromorphicOn.analyticOrderNatAt_le_finsum_ball [ProperSpace 𝕜]
    (hf : MeromorphicOn f (closedBall c R)) {z₀ : 𝕜} (hz₀ : z₀ ∈ ball c R) :
    analyticOrderNatAt f z₀ ≤ ∑ᶠ z ∈ ball c R, analyticOrderNatAt f z := by
  -- the count is supported in the support of `MeromorphicOn.divisor`, which is finite
  refine (single_le_finsum z₀ (hf.divisor_ball_support_finite.subset fun z hz => ?_)
    fun _ => Nat.zero_le _).trans_eq' (by simp [hz₀])
  classical
  rw [Function.mem_support, finsum_eq_if] at hz
  split_ifs at hz with hzb
  · have hA : AnalyticAt 𝕜 f z := by
      by_contra h
      exact hz (analyticOrderNatAt_of_not_analyticAt h)
    rw [Function.mem_support, (hf.mono_set ball_subset_closedBall).divisor_apply hzb,
      hA.meromorphicOrderAt_eq]
    cases h : analyticOrderAt f z <;> simp_all [analyticOrderNatAt]
  · exact absurd rfl hz

/-- A function without zeros on a set `s` has zero count `0` there. -/
theorem TauCeti.finsum_mem_analyticOrderNatAt_eq_zero_of_forall_ne_zero {s : Set 𝕜}
    (hne : ∀ z ∈ s, f z ≠ 0) : (∑ᶠ z ∈ s, analyticOrderNatAt f z) = 0 :=
  finsum_mem_of_eqOn_zero fun z hz => by
    simp [analyticOrderNatAt, analyticOrderAt_eq_zero.2 (.inr (hne z hz))]

end NontriviallyNormedField

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {c : 𝕜} {R : ℝ}

/-- **The zero count detects zeros.** For `f` analytic on `closedBall c R` and nonvanishing at
*some* point of that closed disc, the count `∑ᶠ z ∈ ball c R, analyticOrderNatAt f z` vanishes
precisely when `f` has no zero in the open disc.

The nonvanishing hypothesis cannot be dropped: `analyticOrderNatAt` sends a point of infinite order
to `0`, so the identically zero function has count `0` while vanishing everywhere. -/
theorem AnalyticOnNhd.finsum_analyticOrderNatAt_ball_eq_zero_iff
    (hf : AnalyticOnNhd 𝕜 f (closedBall c R)) (hne : ∃ z ∈ closedBall c R, f z ≠ 0) :
    (∑ᶠ z ∈ ball c R, analyticOrderNatAt f z) = 0 ↔ ∀ z ∈ ball c R, f z ≠ 0 := by
  refine ⟨fun hsum z₀ hz₀ h0 => ?_, TauCeti.finsum_mem_analyticOrderNatAt_eq_zero_of_forall_ne_zero⟩
  obtain ⟨w, hw, hwne⟩ := hne
  have htop : analyticOrderAt f z₀ ≠ ⊤ :=
    hf.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall c R).isPreconnected hw
      (ball_subset_closedBall hz₀) (by simp [(hf w hw).analyticOrderAt_eq_zero.2 hwne])
  have hle := hf.meromorphicOn.analyticOrderNatAt_le_finsum_ball hz₀
  rw [hsum] at hle
  simp [analyticOrderNatAt, ENat.toNat_eq_zero, htop,
    (hf z₀ (ball_subset_closedBall hz₀)).analyticOrderAt_eq_zero, h0] at hle

end RCLike
