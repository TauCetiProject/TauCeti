/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.Dynamics.Flow.ExitTime
import TauCeti.Analysis.Calculus.Deriv.MeanValue
import TauCeti.Analysis.Calculus.Deriv.Slope
import TauCeti.Analysis.Calculus.MeanValue
import TauCeti.Dynamics.Flow.Deriv

/-!
# Exit tests by derivatives along a flow

Let `ϕ` be a flow of `ℝ` on a topological space `α` and let `P` be a set described near a point by
finitely many inequalities `g_i ≥ 0`, such as a compact block bounded by faces. A *derivative of
`g : α → ℝ` along the flow* at `y` is the derivative at time `0` of `t ↦ g (ϕ t y)`; for the flow of
a vector field `V` on a manifold and a differentiable function `g` it is `dg(V)`. This file gives
sufficient conditions, by the signs of such derivatives, for trajectories to leave `P` at once or
to stay in it for a common time. They serve the exit time `Flow.exitTime` from `P` in the
index-pair arguments of Conley index theory: its zeros are the points leaving `P` at once, and it
is continuous on a closed set `P` (`Flow.continuousOn_exitTime`) when every point of `P` of
positive exit time has a trajectory lying in `interior P` at every positive time before its exit,
and has neighbours staying in `P` for a common time. The two strict exit tests below give points
of exit time zero, and the inflow test supplies the common-initial-interval hypothesis `hin` of
`Flow.continuousOn_exitTime`; the interior-trajectory hypothesis `hint` is not addressed here and
must be proved separately.

* **Strict first-order exit.** If `g ≥ 0` on `P` near `x`, `g x ≤ 0` and the derivative of `g`
  along the flow at `x` is negative, then the trajectory of `x` leaves `P` at once: its exit time
  is zero (`Flow.exitTime_eq_zero_of_hasDerivAt_neg`).
* **Strict second-order exit.** If instead the derivative `g'` of `g` along the flow only satisfies
  `g' x ≤ 0`, but `g'` has a negative derivative along the flow at `x`, the exit time is still zero
  (`Flow.exitTime_eq_zero_of_hasDerivAt_of_hasDerivAt_neg`). This is the case of a trajectory
  touching a face of `P` from outside.
* **Inflow.** If near `x` the set `P` is `{y | ∀ i, 0 ≤ g i y}` for finitely many functions `g i`,
  each of which is either nonnegative near `x` or has a nonnegative derivative along the flow near
  `x`, then the points of `P` near `x` stay in `P` during a common time interval `[0, δ]`, `δ > 0`
  (`Flow.exists_pos_eventually_forall_apply_mem_of_hasDerivAt_nonneg`). This holds in particular
  when each `g i` is continuous at `x`, and its derivative along the flow is defined near `x`,
  continuous at `x` and positive at `x` whenever `g i x = 0`: every face through `x` is strictly
  entering.

Derivatives along the flow can be read at every point of a trajectory: the derivative of
`s ↦ g (ϕ s x)` at time `t` is the derivative along the flow at `ϕ t x`
(`Flow.hasDerivAt_apply_flow_iff` in `TauCeti/Dynamics/Flow/Deriv.lean`).

## Main results

* `Flow.exitTime_eq_zero_of_hasDerivAt_neg`,
  `Flow.exitTime_eq_zero_of_hasDerivAt_of_hasDerivAt_neg`: strict first- and second-order exit.
* `Flow.exists_pos_eventually_forall_apply_mem_of_hasDerivAt_nonneg`: a common initial interval in
  `P` for the points near an inflow point.

## References

* C. Conley and E. Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Inventiones Mathematicae 73 (1983), 33–49 (the exit set of the isolating block
  of a gradient flow, by the signs of first and second derivatives at its faces).
-/

public section

open Filter Set
open scoped Topology

namespace Flow

variable {α : Type*} [TopologicalSpace α] {ϕ : Flow ℝ α} {P : Set α} {x : α}

/-- **Strict first-order exit.** Let `g` be nonnegative on the points of `P` near `x`, with
`g x ≤ 0`. If the derivative of `g` along the flow at `x` is negative, the trajectory of `x` leaves
`P` at once: its exit time from `P` is zero. -/
theorem exitTime_eq_zero_of_hasDerivAt_neg {g : α → ℝ} {g' : ℝ}
    (hPg : ∀ᶠ y in 𝓝 x, y ∈ P → 0 ≤ g y) (hgx : g x ≤ 0)
    (hg : HasDerivAt (fun t ↦ g (ϕ t x)) g' 0) (hg' : g' < 0) : ϕ.exitTime P x = 0 := by
  have hx : Tendsto (fun t ↦ ϕ t x) (𝓝 0) (𝓝 x) :=
    (ϕ.continuous continuous_id continuous_const).tendsto' 0 x (ϕ.map_zero_apply x)
  -- just after time `0`, the function `g` is negative along the trajectory of `x`
  refine exitTime_eq_zero_of_eventually_notMem ?_
  filter_upwards [hg.hasDerivWithinAt.eventually_lt_of_neg hg',
    nhdsWithin_le_nhds (hx.eventually hPg)] with t ht hPt hP
  rw [ϕ.map_zero_apply] at ht
  linarith [hPt hP]

/-- **Strict second-order exit.** Let `g` be nonnegative on the points of `P` near `x`, with
`g x ≤ 0`, and let `g'` be a derivative of `g` along the flow near `x`, with `g' x ≤ 0`. If `g'`
has a negative derivative along the flow at `x`, the trajectory of `x` leaves `P` at once: its exit
time from `P` is zero. -/
theorem exitTime_eq_zero_of_hasDerivAt_of_hasDerivAt_neg {g g' : α → ℝ} {g'' : ℝ}
    (hPg : ∀ᶠ y in 𝓝 x, y ∈ P → 0 ≤ g y) (hgx : g x ≤ 0)
    (hg : ∀ᶠ y in 𝓝 x, HasDerivAt (fun t ↦ g (ϕ t y)) (g' y) 0) (hg'x : g' x ≤ 0)
    (hg' : HasDerivAt (fun t ↦ g' (ϕ t x)) g'' 0) (hg'' : g'' < 0) : ϕ.exitTime P x = 0 := by
  have hx : Tendsto (fun t ↦ ϕ t x) (𝓝 0) (𝓝 x) :=
    (ϕ.continuous continuous_id continuous_const).tendsto' 0 x (ϕ.map_zero_apply x)
  refine exitTime_eq_zero_of_eventually_notMem ?_
  -- just after time `0`, the function `t ↦ g (ϕ t x)` has a negative derivative `g' (ϕ t x)`
  have hneg : ∀ᶠ t in 𝓝[>] (0 : ℝ), g' (ϕ t x) < 0 :=
    (hg'.hasDerivWithinAt.eventually_lt_of_neg hg'').mono fun t ht ↦ by
      rw [ϕ.map_zero_apply] at ht
      exact ht.trans_le hg'x
  have hder : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (fun s ↦ g (ϕ s x)) (g' (ϕ t x)) t :=
    (hx.eventually hg).mono fun t ht ↦ hasDerivAt_apply_flow_iff.2 ht
  obtain ⟨ε, hε, hεsub⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.1 (hneg.and (nhdsWithin_le_nhds hder))
  have hg0 : HasDerivAt (fun s ↦ g (ϕ s x)) (g' x) 0 := by
    simpa [ϕ.map_zero_apply] using hder.self_of_nhds
  -- so `g` decreases along the trajectory of `x` during `[0, t]` for every `t ∈ (0, ε)`
  filter_upwards [Ioo_mem_nhdsGT hε,
    nhdsWithin_le_nhds (hx.eventually hPg)] with t ht hPt hP
  have hlt : g (ϕ t x) < g (ϕ 0 x) := by
    refine TauCeti.lt_of_hasDerivAt_neg (f' := fun s ↦ g' (ϕ s x)) ht.1 (fun s hs ↦ ?_)
      (fun s hs ↦ (hεsub ⟨hs.1, hs.2.trans ht.2⟩).2) fun s hs ↦ (hεsub ⟨hs.1, hs.2.trans ht.2⟩).1
    rcases hs.1.eq_or_lt with rfl | hs₀
    · exact hg0.continuousAt.continuousWithinAt
    · exact (hεsub ⟨hs₀, hs.2.trans_lt ht.2⟩).2.continuousAt.continuousWithinAt
  rw [ϕ.map_zero_apply] at hlt
  linarith [hPt hP]

/-- **Inflow.** Suppose that near `x` the set `P` is described by finitely many inequalities,
`y ∈ P ↔ ∀ i, 0 ≤ g i y`, and that each `g i` is either nonnegative near `x`, or has a
nonnegative derivative `g' i` along the flow at every point near `x`. Then the points of `P` near
`x` stay in `P` during a common time interval `[0, δ]` with `δ > 0`. -/
theorem exists_pos_eventually_forall_apply_mem_of_hasDerivAt_nonneg {ι : Type*} [Finite ι]
    {g g' : ι → α → ℝ} (hP : ∀ᶠ y in 𝓝 x, y ∈ P ↔ ∀ i, 0 ≤ g i y)
    (hg : ∀ i, (∀ᶠ y in 𝓝 x, 0 ≤ g i y) ∨
      ∀ᶠ y in 𝓝 x, HasDerivAt (fun t ↦ g i (ϕ t y)) (g' i y) 0 ∧ 0 ≤ g' i y) :
    ∃ δ > 0, ∀ᶠ y in 𝓝[P] x, ∀ s ∈ Icc (0 : ℝ) δ, ϕ s y ∈ P := by
  -- a neighbourhood of `x` on which `P` is described by the `g i`, and on which every `g i` is
  -- nonnegative or every `g i` has a nonnegative derivative along the flow, uniformly in the point
  set L : ι → Prop := fun i ↦ ∀ᶠ y in 𝓝 x, 0 ≤ g i y
  set Q : α → Prop := fun y ↦ (y ∈ P ↔ ∀ i, 0 ≤ g i y) ∧ ∀ i, (L i → 0 ≤ g i y) ∧
    (¬L i → HasDerivAt (fun t ↦ g i (ϕ t y)) (g' i y) 0 ∧ 0 ≤ g' i y)
  have hQ : ∀ᶠ y in 𝓝 x, Q y := by
    refine hP.and (eventually_all.2 fun i ↦ ?_)
    by_cases hL : L i
    · exact hL.mono fun y hy ↦ ⟨fun _ ↦ hy, fun h ↦ (h hL).elim⟩
    · exact ((hg i).resolve_left hL).mono fun y hy ↦ ⟨fun h ↦ (hL h).elim, fun _ ↦ hy⟩
  -- for times `|s| < ε` and points `y` near `x`, the point `ϕ s y` lies in this neighbourhood
  have hflow : ∀ᶠ p : ℝ × α in 𝓝 (0, x), Q (ϕ p.1 p.2) :=
    ((ϕ.continuous continuous_fst continuous_snd).tendsto' (0, x) x (ϕ.map_zero_apply x)).eventually
      hQ
  rw [nhds_prod_eq] at hflow
  obtain ⟨T, hT, W, hW, hTW⟩ := eventually_prod_iff.1 hflow
  obtain ⟨ε, hε, hεT⟩ := Metric.eventually_nhds_iff.1 hT
  have hQs : ∀ y, W y → ∀ s ∈ Icc (0 : ℝ) (ε / 2), Q (ϕ s y) := fun y hy s hs ↦
    hTW (hεT (by rw [Real.dist_0_eq_abs, abs_of_nonneg hs.1]; linarith [hs.2])) hy
  refine ⟨ε / 2, half_pos hε, ?_⟩
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hW] with y hyP hyW s hs
  have hy : Q y := by simpa [ϕ.map_zero_apply] using hQs y hyW 0 ⟨le_rfl, (half_pos hε).le⟩
  refine (hQs y hyW s hs).1.2 fun i ↦ ?_
  by_cases hL : L i
  · exact ((hQs y hyW s hs).2 i).1 hL
  · -- `t ↦ g i (ϕ t y)` has a nonnegative derivative during `[0, ε / 2]`, so it is monotone there
    have hd : ∀ u ∈ Icc (0 : ℝ) (ε / 2),
        HasDerivAt (fun t ↦ g i (ϕ t y)) (g' i (ϕ u y)) u ∧ 0 ≤ g' i (ϕ u y) := fun u hu ↦
      ⟨hasDerivAt_apply_flow_iff.2 (((hQs y hyW u hu).2 i).2 hL).1,
        (((hQs y hyW u hu).2 i).2 hL).2⟩
    have hmono : MonotoneOn (fun t ↦ g i (ϕ t y)) (Icc 0 (ε / 2)) :=
      TauCeti.monotoneOn_of_hasDerivAt_nonneg (convex_Icc 0 (ε / 2)) (fun u hu ↦ (hd u hu).1)
        fun u hu ↦ (hd u (interior_subset hu)).2
    have h0 : g i (ϕ 0 y) ≤ g i (ϕ s y) := hmono ⟨le_rfl, (half_pos hε).le⟩ hs hs.1
    rw [ϕ.map_zero_apply] at h0
    exact (hy.1.1 hyP i).trans h0

end Flow
