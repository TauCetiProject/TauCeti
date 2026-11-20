/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Sign changes of functions growing at least linearly

Let `g : ℝ → ℝ` be differentiable at `a`, and suppose that `x - a = O(g x - g a)` as `x → a`,
that is, `g` moves away from `g a` at least linearly. Then the derivative of `g` at `a` is
nonzero, since otherwise `g x - g a = o(x - a)`. By Fermat's theorem `a` is then neither a local
minimum nor a local maximum, so `g` takes values both below and above `g a` arbitrarily close to
`a`.

## Main results

* `TauCeti.deriv_ne_zero_of_isBigO_sub`: the derivative at `a` is nonzero.
* `TauCeti.frequently_lt_and_frequently_gt_of_isBigO_sub`: `g` takes values on both sides of
  `g a` arbitrarily close to `a`.
-/

public section

open Asymptotics Filter Topology

namespace TauCeti

variable {g : ℝ → ℝ} {a : ℝ}

/-- **A function growing at least linearly has a nonzero derivative.** If `g` is differentiable
at `a` and `x - a = O(g x - g a)` as `x → a`, then `deriv g a ≠ 0`: a vanishing derivative would
make `g x - g a = o(x - a)`. -/
theorem deriv_ne_zero_of_isBigO_sub (hg : DifferentiableAt ℝ g a)
    (h : (fun x ↦ x - a) =O[𝓝 a] fun x ↦ g x - g a) : deriv g a ≠ 0 := by
  intro hd
  have ho := hasDerivAt_iff_isLittleO.1 (hd ▸ hg.hasDerivAt)
  simp only [smul_zero, sub_zero] at ho
  refine isLittleO_irrefl ?_ (h.trans_isLittleO ho)
  exact (eventually_mem_nhdsWithin (s := {a}ᶜ)).frequently.filter_mono nhdsWithin_le_nhds
    |>.mono fun _ hx ↦ sub_ne_zero.2 hx

/-- **A function growing at least linearly changes sign.** If `g` is differentiable at `a` and
`x - a = O(g x - g a)` as `x → a`, then `g` takes values below and above `g a` arbitrarily close
to `a`: its derivative at `a` is nonzero, so `a` is not a local extremum. -/
theorem frequently_lt_and_frequently_gt_of_isBigO_sub (hg : DifferentiableAt ℝ g a)
    (h : (fun x ↦ x - a) =O[𝓝 a] fun x ↦ g x - g a) :
    (∃ᶠ x in 𝓝 a, g x < g a) ∧ ∃ᶠ x in 𝓝 a, g a < g x := by
  have hd := deriv_ne_zero_of_isBigO_sub hg h
  exact ⟨fun h ↦ hd (IsLocalMin.deriv_eq_zero (h.mono fun _ hx ↦ not_lt.1 hx)),
    fun h ↦ hd (IsLocalMax.deriv_eq_zero (h.mono fun _ hx ↦ not_lt.1 hx))⟩

end TauCeti
