/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import TauCeti.Analysis.Meromorphic.Order

/-!
# Meromorphy, pole order, and zeros of the Riemann zeta function

Mathlib's `riemannZeta` is analytic away from `s = 1` (`analyticOn_riemannZeta`) and
decomposes away from `1` as `(s - 1)⁻¹ + riemannZeta₀ s` with `riemannZeta₀` entire
(`riemannZeta_eq_inv_sub_add`, `differentiable_riemannZeta₀`). Consequently `riemannZeta` is
meromorphic on `ℂ`. Its residue at `s = 1` (`riemannZeta_residue_one`) reads off its simple pole
of order `-1` at `s = 1`, and analyticity away from `1` together with `riemannZeta_one_ne_zero`
characterizes positive meromorphic order by `riemannZeta s = 0`.

## Main results

* `TauCeti.meromorphic_riemannZeta`: `riemannZeta` is meromorphic on `ℂ`.
* `TauCeti.meromorphicOrderAt_riemannZeta_one`: `meromorphicOrderAt riemannZeta 1 = -1`.
* `TauCeti.meromorphicOrderAt_riemannZeta_pos_iff`:
  `0 < meromorphicOrderAt riemannZeta s ↔ riemannZeta s = 0`.
-/

public section

open Complex Filter
open scoped Topology

namespace TauCeti

/-- Mathlib's Riemann zeta function is meromorphic on `ℂ`. Away from `1` it is analytic
(`analyticOn_riemannZeta`), and near `1` it agrees on a punctured neighbourhood with
`(s - 1)⁻¹ + riemannZeta₀ s`. -/
@[fun_prop]
theorem meromorphic_riemannZeta : Meromorphic riemannZeta := by
  intro z
  rcases eq_or_ne z 1 with rfl | hz
  · have h₀ : AnalyticAt ℂ riemannZeta₀ 1 := differentiable_riemannZeta₀.analyticAt 1
    refine (by fun_prop : MeromorphicAt (fun s : ℂ ↦ (s - 1)⁻¹ + riemannZeta₀ s) 1).congr ?_
    filter_upwards [self_mem_nhdsWithin] with s (hs : s ≠ 1)
    exact (riemannZeta_eq_inv_sub_add hs).symm
  · exact (analyticOn_riemannZeta z hz).meromorphicAt

/-- The Riemann zeta function has a simple pole at `1`. -/
@[simp]
theorem meromorphicOrderAt_riemannZeta_one :
    meromorphicOrderAt riemannZeta 1 = -1 := by
  simpa using (meromorphic_riemannZeta 1).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    one_ne_zero riemannZeta_residue_one

/-- The Riemann zeta function has positive meromorphic order at `s` if and only if
`riemannZeta s = 0`. -/
@[simp]
theorem meromorphicOrderAt_riemannZeta_pos_iff {s : ℂ} :
    0 < meromorphicOrderAt riemannZeta s ↔ riemannZeta s = 0 := by
  rcases eq_or_ne s 1 with rfl | hs
  · simp [meromorphicOrderAt_riemannZeta_one, riemannZeta_one_ne_zero]
  · exact (analyticOn_riemannZeta s hs).meromorphicOrderAt_pos_iff_eq_zero

end TauCeti
