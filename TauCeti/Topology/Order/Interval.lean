/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Images of real half-intervals under monotone maps

The image of a half-infinite real interval under a continuous strictly monotone map is determined
by its value at the finite endpoint and its limit at infinity.  The endpoint at infinity is omitted
when the limit is finite.

## Main result

* `TauCeti.image_Ici_of_continuousOn_of_strictMonoOn_of_tendsto` — a continuous strictly
  increasing map
  on `Ici p` with a finite limit at `+∞` maps that interval to the half-open interval between its
  endpoint value and its limit.
* `TauCeti.interval_filter_sum_properties_of_forall_ne_zero_le` — if the nonzero terms of a
  finitely indexed real family occur at or to the left of `p`, the filtered sums at points of
  `Ici p` are either the sum at `p` or zero, and no such term occurs in the intervening interval.
-/

public section

open Filter Set Topology

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- If the nonzero terms of a finitely indexed real family occur at or to the left of `p`, then
the terms vanish strictly between `p` and any point of `Ici p`, and the filtered sum at that point
is either the filtered sum at `p` or zero. -/
theorem interval_filter_sum_properties_of_forall_ne_zero_le (a e : ι → ℝ) {p : ℝ}
    (hp : -1 < ∑ i with a i = p, e i) (ha : ∀ i, e i ≠ 0 → a i ≤ p) :
    (∀ {q : ℝ}, q ∈ Ici p → ∀ i, e i ≠ 0 → a i ∉ Ioo p q) ∧
      (∀ {q : ℝ}, q ∈ Ici p → -1 < ∑ i with a i = q, e i) := by
  constructor
  · intro q hq i hei hi
    exact (not_lt_of_ge (ha i hei)) hi.1
  · intro q hq
    have hq' : p ≤ q := hq
    rcases eq_or_lt_of_le hq' with hqp | hpq
    · subst q
      exact hp
    · have hz : ∀ i, i ∈ Finset.univ.filter (fun i => a i = q) → e i = 0 := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        by_contra hei
        have hai := ha i hei
        have hiq : p < a i := hi ▸ hpq
        linarith
      rw [Finset.sum_eq_zero hz]
      norm_num

/-- **A continuous strictly increasing map sends a half-line to a half-open interval.** The finite
limit at `+∞` is approached but is not attained. -/
theorem image_Ici_of_continuousOn_of_strictMonoOn_of_tendsto {d : ℝ → ℝ} {p D : ℝ}
    (hdcont : ContinuousOn d (Ici p))
    (hdmono : StrictMonoOn d (Ici p)) (hdl : Tendsto d atTop (𝓝 D)) :
    d '' Ici p = Ico (d p) D := by
  have hle : ∀ x ∈ Ici p, d x ≤ D := by
    intro x hx
    apply ge_of_tendsto hdl
    filter_upwards [eventually_ge_atTop x] with y hxy
    have hy : y ∈ Ici p := hx.trans hxy
    exact hdmono.monotoneOn hx hy hxy
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hxp : p ≤ x := hx
    have hx1 : x + 1 ∈ Ici p := by
      exact le_trans hxp (by linarith)
    have hlt : d x < D := lt_of_lt_of_le
      (hdmono hx hx1 (by linarith)) (hle (x + 1) hx1)
    exact ⟨hdmono.monotoneOn self_mem_Ici hx hxp, hlt⟩
  · exact isPreconnected_Ici.intermediate_value_Ico self_mem_Ici
      (le_principal_iff.mpr (Ici_mem_atTop p)) hdcont hdl

end TauCeti
