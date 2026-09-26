/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Boundedness near an endpoint from a continuous derivative

A function on the reals whose right derivative just to the right of `a` is given by a function
right-continuous at `a` stays bounded as the variable tends to `a` from the right. The derivative
is bounded on a short interval `(a, a + ε)`, so the mean value inequality bounds the function
there.

## Main results

* `TauCeti.exists_norm_le_of_hasDerivWithinAt_of_continuousWithinAt`: if `f' = g` on a right
  neighbourhood of `a` and `g` is right-continuous at `a`, then `‖f t‖` is eventually bounded as
  `t → a⁺`.
-/

public section

open Filter
open scoped Topology

namespace TauCeti

/-- **Boundedness near `a⁺` from a derivative continuous at `a⁺`.** If `f : ℝ → E` has derivative
`g u` within `(a, ∞)` at every `u` in a right neighbourhood of `a`, and `g` is continuous at `a`
within `(a, ∞)`, then `‖f t‖` is eventually bounded as `t` tends to `a` from the right. -/
theorem exists_norm_le_of_hasDerivWithinAt_of_continuousWithinAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : ℝ → E} {a : ℝ}
    (hg : ContinuousWithinAt g (Set.Ioi a) a)
    (hf : ∀ᶠ u in 𝓝[>] a, HasDerivWithinAt f (g u) (Set.Ioi a) u) :
    ∃ B, ∀ᶠ t in 𝓝[>] a, ‖f t‖ ≤ B := by
  -- On some `(a, a + ε)`, `f' = g` and `‖g‖ < ‖g a‖ + 1`, so `f` is Lipschitz there.
  obtain ⟨b, hb, hfb⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp
    (hf.and (hg.norm.eventually_lt continuousWithinAt_const (lt_add_one ‖g a‖)))
  set ε := b - a
  have hε : 0 < ε := sub_pos.mpr hb
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, x₀ ∈ Set.Ioo a (a + ε) := ⟨a + ε / 2, by linarith, by linarith⟩
  refine ⟨‖f x₀‖ + (‖g a‖ + 1) * ε, ?_⟩
  have hab : a + ε = b := by simp [ε]
  filter_upwards [Ioo_mem_nhdsGT (lt_add_of_pos_right a hε)] with t ht
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f) (f' := g)
    (fun u hu ↦ ((hfb (hab ▸ hu)).1.mono Set.Ioo_subset_Ioi_self))
    (fun u hu ↦ (hfb (hab ▸ hu)).2.le) (convex_Ioo _ _) hx₀ ht
  have hdist : ‖t - x₀‖ ≤ ε := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [ht.1, ht.2, hx₀.1, hx₀.2]
  calc ‖f t‖ ≤ ‖f x₀‖ + ‖f t - f x₀‖ := norm_le_insert' _ _
    _ ≤ ‖f x₀‖ + (‖g a‖ + 1) * ε := by
        gcongr
        exact hmvt.trans (by gcongr)

end TauCeti
