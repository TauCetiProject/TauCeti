/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# A set containing a local line accumulates on both rays of the line

If a set `C ⊆ ℂ` contains, in a ball around `p`, the points of the line
`{z | (v * (z - p)).im = 0}` through `p`, then `p` lies in the closure of the part of `C` on each
open side of the perpendicular line through `p`, that is, `p` is approached by points of `C` along
both rays of the line issuing from `p`.

## Main results

* `TauCeti.mem_closure_inter_of_line_subset`: such a point `p` is in the closure of `C` on each
  open side of the perpendicular line through `p`, the sides being read off from the sign of
  `((q - p) / -(I / v)).im`.
-/

public section

open Complex Filter Metric Set Topology

namespace TauCeti

/-- If a set `C` contains the points of the line `{z | (v * (z - p)).im = 0}` lying in a ball
around `p`, then `p` lies in the closure of `C` on each open side of the perpendicular line through
`p`, the sides being measured in the coordinate `(q - p) / -(I / v)`; equivalently, `C`
accumulates at `p` along both rays of the line from `p`. -/
theorem mem_closure_inter_of_line_subset {C : Set ℂ} {p v : ℂ} {r : ℝ}
    (hv : v ≠ 0) (hr : 0 < r) (hline : ∀ z ∈ ball p r, (v * (z - p)).im = 0 → z ∈ C) :
    p ∈ closure (C ∩ {q | 0 < ((q - p) / -(I / v)).im}) ∧
      p ∈ closure (C ∩ {q | ((q - p) / -(I / v)).im < 0}) := by
  let d : ℂ := -(I / v)
  let φ : ℝ → ℂ := fun t => p + t / v
  have hφcont : Continuous φ := by fun_prop
  have hφ0 : Tendsto φ (𝓝 (0 : ℝ)) (𝓝 p) := by
    simpa [φ] using hφcont.tendsto 0
  have hφv (t : ℝ) : v * (φ t - p) = t := by
    dsimp [φ]
    field_simp [hv]
    ring
  have hφd (t : ℝ) : ((φ t - p) / d).im = t := by
    have heq : (φ t - p) / d = I * t := by
      dsimp [φ, d]
      field_simp [hv, I_ne_zero]
      simp [Complex.I_sq]
    rw [heq]
    simp
  have hφball : ∀ᶠ t in 𝓝 (0 : ℝ), φ t ∈ ball p r :=
    hφ0.eventually (ball_mem_nhds p hr)
  have hφC : ∀ᶠ t in 𝓝 (0 : ℝ), φ t ∈ C := by
    filter_upwards [hφball] with t ht
    exact hline _ ht (by rw [hφv]; simp)
  have hleft : p ∈ closure (C ∩ {q | 0 < ((q - p) / d).im}) := by
    apply mem_closure_of_tendsto (b := 𝓝[>] (0 : ℝ))
      (hφ0.mono_left nhdsWithin_le_nhds)
    filter_upwards [hφC.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with t htC (ht : 0 < t)
    exact ⟨htC, by simpa [hφd] using ht⟩
  have hright : p ∈ closure (C ∩ {q | ((q - p) / d).im < 0}) := by
    apply mem_closure_of_tendsto (b := 𝓝[<] (0 : ℝ))
      (hφ0.mono_left nhdsWithin_le_nhds)
    filter_upwards [hφC.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with t htC (ht : t < 0)
    exact ⟨htC, by simpa [hφd] using ht⟩
  exact ⟨hleft, hright⟩

end TauCeti
