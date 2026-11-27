/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.ReImTopology

/-!
# Maps on the closed strip

The closed strip `ℝ × [0, 1] = {z | 0 ≤ z.im ≤ 1}` is the closure of the open strip
`ℝ × (0, 1) = {z | 0 < z.im < 1}`, so an identity between maps continuous on the closed strip
extends from the open strip to the closed strip.

## Main results

* `TauCeti.eqOn_add_closedStrip_of_eqOn_strip`: two maps continuous on the closed strip which
  differ by a real translation on the open strip differ by that translation on the closed strip.
-/

public section

open Complex Set

namespace TauCeti

/-- Two maps `u` and `v`, continuous on the closed strip `0 ≤ z.im ≤ 1`, with `u z = v (z + c)` for
a real `c` on the open strip `0 < z.im < 1`, satisfy `u z = v (z + c)` on the closed strip. -/
theorem eqOn_add_closedStrip_of_eqOn_strip {u v : ℂ → ℂ} {c : ℝ}
    (huc : ContinuousOn u {z | z.im ∈ Icc 0 1}) (hvc : ContinuousOn v {z | z.im ∈ Icc 0 1})
    (h : EqOn u (fun z => v (z + c)) {z | z.im ∈ Ioo 0 1}) :
    EqOn u (fun z => v (z + c)) {z | z.im ∈ Icc 0 1} := by
  have hclosure : {z : ℂ | z.im ∈ Icc 0 1} ⊆ closure {z : ℂ | z.im ∈ Ioo 0 1} := by
    simp only [← mem_preimage, ofPred_mem_eq]
    rw [closure_preimage_im, closure_Ioo zero_ne_one]
  refine h.of_subset_closure huc ?_ (fun z hz => Ioo_subset_Icc_self hz) hclosure
  exact hvc.comp (continuous_id.add continuous_const).continuousOn fun z hz => by simpa using hz

end TauCeti
