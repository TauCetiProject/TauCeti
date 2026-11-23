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

Let `g : 𝕜 → F` have derivative `g'` at `a`, and suppose that `x - a = O(g x - g a)` as `x → a`,
that is, `g` moves away from `g a` at least linearly. Then `g' ≠ 0`, since otherwise
`g x - g a = o(x - a)`. For `g : ℝ → ℝ`, Fermat's theorem then shows that `a` is neither a local
minimum nor a local maximum, so `g` takes values both below and above `g a` arbitrarily close to
`a`.

The hypothesis is the reverse of the bound `g x - g a = O(x - a)` of `HasDerivAt.isBigO_sub`,
hence the suffix `_rev` in the names.

## Main results

* `HasDerivAt.ne_zero_of_isBigO_sub_rev`: the derivative at `a` is nonzero.
* `TauCeti.deriv_ne_zero_of_isBigO_sub_rev`: the same for `deriv`.
* `TauCeti.frequently_lt_and_frequently_gt_of_isBigO_sub_rev`: a real function takes values on
  both sides of `g a` arbitrarily close to `a`.
-/

public section

open Asymptotics Filter Topology

/-- **A function growing at least linearly has a nonzero derivative.** If `g` has derivative `g'`
at `a` and `x - a = O(g x - g a)` as `x → a`, then `g' ≠ 0`: a vanishing derivative would make
`g x - g a = o(x - a)`. -/
theorem HasDerivAt.ne_zero_of_isBigO_sub_rev {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {g : 𝕜 → F} {g' : F} {a : 𝕜}
    (hg : HasDerivAt g g' a) (h : (fun x ↦ x - a) =O[𝓝 a] fun x ↦ g x - g a) : g' ≠ 0 := by
  rintro rfl
  have ho := hasDerivAt_iff_isLittleO.1 hg
  simp only [smul_zero, sub_zero] at ho
  refine isLittleO_irrefl ?_ (h.trans_isLittleO ho)
  exact (eventually_mem_nhdsWithin (s := {a}ᶜ)).frequently.filter_mono nhdsWithin_le_nhds
    |>.mono fun _ hx ↦ sub_ne_zero.2 hx

namespace TauCeti

/-- **A function growing at least linearly has a nonzero derivative.** If `g` is differentiable
at `a` and `x - a = O(g x - g a)` as `x → a`, then `deriv g a ≠ 0`
(`HasDerivAt.ne_zero_of_isBigO_sub_rev`). -/
theorem deriv_ne_zero_of_isBigO_sub_rev {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {g : 𝕜 → F} {a : 𝕜} (hg : DifferentiableAt 𝕜 g a)
    (h : (fun x ↦ x - a) =O[𝓝 a] fun x ↦ g x - g a) : deriv g a ≠ 0 :=
  hg.hasDerivAt.ne_zero_of_isBigO_sub_rev h

variable {g : ℝ → ℝ} {a : ℝ}

/-- **A function growing at least linearly changes sign.** If `g` is differentiable at `a` and
`x - a = O(g x - g a)` as `x → a`, then `g` takes values below and above `g a` arbitrarily close
to `a`: its derivative at `a` is nonzero, so `a` is not a local extremum. -/
theorem frequently_lt_and_frequently_gt_of_isBigO_sub_rev (hg : DifferentiableAt ℝ g a)
    (h : (fun x ↦ x - a) =O[𝓝 a] fun x ↦ g x - g a) :
    (∃ᶠ x in 𝓝 a, g x < g a) ∧ ∃ᶠ x in 𝓝 a, g a < g x := by
  have hd := deriv_ne_zero_of_isBigO_sub_rev hg h
  exact ⟨fun h ↦ hd (IsLocalMin.deriv_eq_zero (h.mono fun _ hx ↦ not_lt.1 hx)),
    fun h ↦ hd (IsLocalMax.deriv_eq_zero (h.mono fun _ hx ↦ not_lt.1 hx))⟩

end TauCeti
