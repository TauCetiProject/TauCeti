/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Boundedness near an endpoint from a bounded derivative

A function on the reals whose derivative is bounded just to the right of `a` stays bounded as the
variable tends to `a` from the right: the mean value inequality bounds it on a short interval
`(a, b)` on which the derivative bound holds.

## Main results

* `TauCeti.exists_norm_le_of_norm_hasDerivWithin_le`: if `f' = g` on a right neighbourhood of `a`
  and `‖g‖` is eventually bounded there, then `‖f t‖` is eventually bounded as `t → a⁺`.
-/

public section

open Filter
open scoped Topology

namespace TauCeti

/-- **Boundedness near `a⁺` from a bounded derivative.** If `f : ℝ → E` has derivative `g u`
within `(a, ∞)` at every `u` in a right neighbourhood of `a`, and `‖g u‖ ≤ C` there, then `‖f t‖`
is eventually bounded as `t` tends to `a` from the right. -/
theorem exists_norm_le_of_norm_hasDerivWithin_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : ℝ → E} {a C : ℝ}
    (hf : ∀ᶠ u in 𝓝[>] a, HasDerivWithinAt f (g u) (Set.Ioi a) u)
    (hg : ∀ᶠ u in 𝓝[>] a, ‖g u‖ ≤ C) :
    ∃ B, ∀ᶠ t in 𝓝[>] a, ‖f t‖ ≤ B := by
  obtain ⟨b, hab, hfg⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hf.and hg)
  obtain ⟨x₀, hx₀⟩ := Set.nonempty_Ioo.mpr hab
  have hC : 0 ≤ C := (norm_nonneg _).trans (hfg hx₀).2
  refine ⟨‖f x₀‖ + C * (b - a), eventually_of_mem (Ioo_mem_nhdsGT hab) fun t ht ↦ ?_⟩
  have hmvt := (convex_Ioo a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu ↦ (hfg hu).1.mono Set.Ioo_subset_Ioi_self) (fun u hu ↦ (hfg hu).2) hx₀ ht
  have hdist : ‖t - x₀‖ ≤ b - a := by
    rw [← dist_eq_norm]
    exact Real.dist_le_of_mem_Icc (Set.Ioo_subset_Icc_self ht) (Set.Ioo_subset_Icc_self hx₀)
  calc ‖f t‖ ≤ ‖f x₀‖ + ‖f t - f x₀‖ := norm_le_insert' _ _
    _ ≤ ‖f x₀‖ + C * (b - a) := by
      gcongr
      exact hmvt.trans (mul_le_mul_of_nonneg_left hdist hC)

end TauCeti
