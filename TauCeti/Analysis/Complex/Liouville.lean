/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Liouville

/-!
# Liouville's theorem under the inversion `t ↦ 1 / t`

An entire function `f` with `f(s) = -g(1 / s) / s²` for `s ≠ 0`, where `g` is continuous at `0`,
vanishes identically (`Differentiable.eq_zero_of_eq_neg_inv_sq_smul`): it tends to `0` at
infinity, so it is zero by Liouville's theorem. This is the transformation law of the coefficient
of a one-form `f(t) dt = g(s) ds` under the change of coordinate `s = 1 / t`, and it shows that a
holomorphic one-form on the Riemann sphere vanishes.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Section 2.6.
-/

public section

open Set Filter Topology

namespace Differentiable

/-- **Liouville's theorem for the transformation law of a one-form under `t ↦ 1 / t`.** If an entire
function `f` satisfies `f(s) = -g(1 / s) / s²` for `s ≠ 0`, with `g` continuous at `0`, then `f`
tends to `0` at infinity, so it vanishes. -/
theorem eq_zero_of_eq_neg_inv_sq_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f g : ℂ → F} (hf : Differentiable ℂ f) (hg : ContinuousAt g 0)
    (h : ∀ s ≠ 0, f s = -(s ^ 2)⁻¹ • g s⁻¹) (t : ℂ) : f t = 0 := by
  have hinv : Tendsto (fun s : ℂ ↦ s⁻¹) (cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded
  have hlim : Tendsto (fun s : ℂ ↦ -(s⁻¹ ^ 2) • g s⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa using (hinv.pow 2).neg.smul (hg.tendsto.comp hinv)
  refine hf.apply_eq_of_tendsto_cocompact t (hlim.congr' ?_)
  filter_upwards [(isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact] with s hs
  rw [h s (mem_compl_singleton_iff.1 hs), inv_pow]

end Differentiable
