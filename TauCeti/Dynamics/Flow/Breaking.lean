/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.ProperSpace
public import TauCeti.Dynamics.Flow.Stable
-- Private: used only to send the exit times to infinity.
import Mathlib.Order.Filter.AtTopBot.Archimedean
-- Private: used only to extract a convergent subsequence of exit points.
import Mathlib.Topology.Sequences

/-!
# Breaking of orbits at an isolated rest point

Let `x` be a rest point of a real flow `φ` on a proper metric space, and let `r > 0` be an
*isolating radius*: every forward orbit trapped in the closed ball of radius `r` about `x` converges
to `x`, and so does every trapped backward orbit. Suppose that points `u n`, infinitely many of
which lie outside the stable set `W^s(x)`, converge to a point `y` of `W^s(x)`. Then the orbits of
these `u n` follow the orbit of `y` into the ball, linger near `x` for longer and longer, and must
eventually leave it again. Their exit points, reached at times tending to `+∞`, accumulate at a
point of the sphere of radius `r` lying in the unstable set `W^u(x)`.

This is the mechanism by which a sequence of trajectories converges to a *broken* trajectory: the
limit of the orbits of the `u n` runs along the orbit of `y` into `x` and leaves `x` along an orbit
of `W^u(x)`. Iterating it at the successive rest points is the core of the compactness theorem for
spaces of Morse trajectories. The isolating hypotheses are stated for an arbitrary flow; for a
negative gradient flow they follow from the absence of other critical points in the ball
(`TauCeti.Analysis.Calculus.Morse.Breaking`).

## Main declarations

* `Flow.exists_tendsto_mem_unstableSet_of_tendsto_mem_stableSet`: exit points of the orbits of
  the `u n`, taken at times tending to `+∞`, converge to a point of `W^u(x)` at distance `r`
  from `x`.
* `Flow.exists_tendsto_mem_stableSet_of_tendsto_mem_unstableSet`: the time-reversed statement.
* `Flow.exists_mem_closure_inter_unstableSet_of_mem_closure_inter_stableSet` and
  `Flow.exists_mem_closure_inter_stableSet_of_mem_closure_inter_unstableSet`: the closure of an
  invariant set disjoint from `W^s(x)` (respectively `W^u(x)`) that meets `W^s(x)` (respectively
  `W^u(x)`) also meets `W^u(x)` (respectively `W^s(x)`) on the sphere of radius `r`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (compactness of spaces of trajectories).
-/

public section

open Filter Metric Set Topology

namespace Flow

variable {α : Type*} [MetricSpace α] {φ : _root_.Flow ℝ α} {x : α} {r : ℝ}

/-- Points close enough to a rest point stay within any prescribed distance of it for any
prescribed compact stretch of time. -/
private theorem eventually_forall_Icc_dist_lt (hx : ∀ t, φ t x = x) (hr : 0 < r) (T : ℝ) :
    ∀ᶠ w in 𝓝 x, ∀ τ ∈ Icc 0 T, dist (φ τ w) x < r := by
  refine isCompact_Icc.eventually_forall_of_forall_eventually fun τ _ ↦ ?_
  have hcont : ContinuousAt (fun p : α × ℝ ↦ φ p.2 p.1) (x, τ) :=
    (φ.continuous continuous_snd continuous_fst).continuousAt
  have hlim := hcont.tendsto
  simp only [hx] at hlim
  exact hlim (ball_mem_nhds x hr)

/-- One step of the construction: for every `k`, some `u n` with `n ≥ k` enters the ball of radius
`r` about `x` at a time `s ≥ 0` and, at least `k` units of time later, reaches its boundary for the
first time. -/
private theorem exists_exit (hr : 0 < r)
    (hfwd : ∀ w, (∀ t, 0 ≤ t → φ t w ∈ closedBall x r) → w ∈ stableSet φ x)
    {y : α} (hy : y ∈ stableSet φ x) {u : ℕ → α} (hu : Tendsto u atTop (𝓝 y))
    (hux : ∃ᶠ n in atTop, u n ∉ stableSet φ x) (k : ℕ) :
    ∃ n, k ≤ n ∧ ∃ s t : ℝ, 0 ≤ s ∧ s + k ≤ t ∧ dist (φ t (u n)) x = r ∧
      ∀ τ ∈ Icc s t, dist (φ τ (u n)) x ≤ r := by
  -- An open neighbourhood `U` of `x` all of whose points stay in the open ball for time `k`.
  obtain ⟨U, hUV, hUo, hxU⟩ := _root_.mem_nhds_iff.1
    (eventually_forall_Icc_dist_lt (fixed_of_mem_stableSet hy) hr k)
  -- The orbit of `y` enters `U` at some time `s ≥ 0`, and so do the orbits of nearby `u n`.
  obtain ⟨s, hsU, hs0⟩ :=
    (((mem_stableSet.1 hy).eventually (hUo.mem_nhds hxU)).and (eventually_ge_atTop 0)).exists
  have hev : ∀ᶠ n in atTop, φ s (u n) ∈ U :=
    ((φ.continuous_toFun s).tendsto y).comp hu |>.eventually (hUo.mem_nhds hsU)
  obtain ⟨n, hkn, hns, hnU⟩ := (hux.and_eventually hev).forall_exists_of_atTop k
  set g : ℝ → ℝ := fun τ ↦ dist (φ τ (u n)) x with hgdef
  have hg : Continuous g := (φ.continuous continuous_id continuous_const).dist continuous_const
  have hshift (τ : ℝ) : g (τ + s) = dist (φ τ (φ s (u n))) x := by
    simp only [hgdef, φ.map_add]
  -- Between times `s` and `s + k` the orbit of `u n` stays in the open ball.
  have hin : ∀ τ ∈ Icc s (s + k), g τ < r := fun τ hτ ↦ by
    have := hUV hnU (τ - s) ⟨sub_nonneg.2 hτ.1, by linarith [hτ.2]⟩
    rwa [← hshift, sub_add_cancel] at this
  -- It is not trapped in the closed ball forever, since `u n` is not in the stable set.
  obtain ⟨τ₀, hτ₀, hτ₀r⟩ : ∃ τ₀, 0 ≤ τ₀ ∧ r < g (τ₀ + s) := by
    by_contra! htrap
    refine hns ?_
    have hmem := hfwd (φ s (u n)) fun τ hτ ↦ by
      rw [mem_closedBall, ← hshift]
      exact htrap τ hτ
    simpa only [← φ.map_add, neg_add_cancel, φ.map_zero_apply] using
      isInvariant_stableSet φ x (-s) hmem
  -- The exit time `t` is the first time after `s` at which the orbit reaches distance `r`.
  set A : Set ℝ := {τ ∈ Icc s (τ₀ + s) | r ≤ g τ}
  have hAne : A.Nonempty := ⟨τ₀ + s, ⟨by linarith, le_rfl⟩, hτ₀r.le⟩
  have hAbdd : BddBelow A := ⟨s, fun τ hτ ↦ hτ.1.1⟩
  have htA : sInf A ∈ A :=
    (isClosed_Icc.inter (isClosed_le continuous_const hg)).csInf_mem hAne hAbdd
  set t := sInf A
  have hbefore : ∀ τ ∈ Ico s t, g τ < r := fun τ hτ ↦ by
    by_contra! hle
    exact (not_le.2 hτ.2) (csInf_le hAbdd ⟨⟨hτ.1, hτ.2.le.trans htA.1.2⟩, hle⟩)
  have hst : s < t := lt_of_le_of_ne htA.1.1 fun hst ↦ by
    have := hin s ⟨le_rfl, by linarith [Nat.cast_nonneg (α := ℝ) k]⟩
    rw [hst] at this
    linarith [htA.2]
  have hgt : g t ≤ r := by
    have hcl : t ∈ closure (Ico s t) := by
      rw [closure_Ico hst.ne]
      exact right_mem_Icc.2 hst.le
    simpa only [closure_Iic, mem_Iic] using
      map_mem_closure hg hcl fun τ hτ ↦ mem_Iic.2 (hbefore τ hτ).le
  refine ⟨n, hkn, s, t, hs0, le_csInf hAne fun τ hτ ↦ ?_, le_antisymm hgt htA.2,
    fun τ hτ ↦ (eq_or_lt_of_le hτ.2).elim (fun h ↦ h ▸ hgt) fun h ↦ (hbefore τ ⟨hτ.1, h⟩).le⟩
  by_contra! hlt
  exact (not_le.2 (hin τ ⟨hτ.1.1, hlt.le⟩)) hτ.2

variable [ProperSpace α]

/-- **Orbits break at an isolated rest point.** Let `r > 0` be an isolating radius for the rest
point `x`: every forward orbit trapped in `closedBall x r` converges to `x` in forward time, and
every trapped backward orbit converges to `x` in backward time. If points `u n`, frequently outside
the stable set of `x`, converge to a point `y` of that stable set, then along a sequence of indices
`n k → ∞` and of times `t k → +∞` the points `φ (t k) (u (n k))` converge to a point `z` of the
unstable set of `x` at distance exactly `r` from `x`.

The trapping hypotheses are what makes `x` an isolated invariant set; without the backward one,
the limit `z` could lie on an orbit that lingers near `x` without converging to it. -/
theorem exists_tendsto_mem_unstableSet_of_tendsto_mem_stableSet (hr : 0 < r)
    (hfwd : ∀ w, (∀ t, 0 ≤ t → φ t w ∈ closedBall x r) → w ∈ stableSet φ x)
    (hbwd : ∀ w, (∀ t, t ≤ 0 → φ t w ∈ closedBall x r) → w ∈ unstableSet φ x)
    {y : α} (hy : y ∈ stableSet φ x) {u : ℕ → α} (hu : Tendsto u atTop (𝓝 y))
    (hux : ∃ᶠ n in atTop, u n ∉ stableSet φ x) :
    ∃ z ∈ unstableSet φ x, dist z x = r ∧ ∃ (n : ℕ → ℕ) (t : ℕ → ℝ),
      Tendsto n atTop atTop ∧ Tendsto t atTop atTop ∧
        Tendsto (fun k ↦ φ (t k) (u (n k))) atTop (𝓝 z) := by
  choose n hkn s t hs0 hst hdist hball using exists_exit hr hfwd hy hu hux
  -- The exit points lie on the compact sphere, so a subsequence of them converges.
  obtain ⟨z, hz, ψ, hψ, hlim⟩ :=
    (isCompact_sphere x r).tendsto_subseq (x := fun k ↦ φ (t k) (u (n k)))
      fun k ↦ mem_sphere.2 (hdist k)
  have htk (k : ℕ) : (k : ℝ) ≤ t k := by linarith [hs0 k, hst k]
  refine ⟨z, hbwd z fun τ hτ ↦ ?_, mem_sphere.1 hz, n ∘ ψ, t ∘ ψ,
    tendsto_atTop_mono (fun k ↦ (hψ.id_le k).trans (hkn _)) tendsto_id |>.comp tendsto_id,
    tendsto_atTop_mono (fun k ↦ (Nat.cast_le.2 (hψ.id_le k)).trans (htk _))
      tendsto_natCast_atTop_atTop, hlim⟩
  -- The backward orbit of `z` is a limit of pieces of orbits lying in the closed ball.
  have hτlim : Tendsto (fun k ↦ φ (τ + t (ψ k)) (u (n (ψ k)))) atTop (𝓝 (φ τ z)) := by
    simpa only [Function.comp_def, φ.map_add] using ((φ.continuous_toFun τ).tendsto z).comp hlim
  refine isClosed_closedBall.mem_of_tendsto hτlim ?_
  filter_upwards [eventually_ge_atTop ⌈-τ⌉₊] with k hk
  have hkτ : -τ ≤ ψ k := (Nat.le_ceil _).trans (Nat.cast_le.2 (hk.trans (hψ.id_le k)))
  exact mem_closedBall.2 (hball _ _ ⟨by linarith [hst (ψ k)], by linarith⟩)

/-- **Orbits break at an isolated rest point, in backward time.** The time reversal of
`Flow.exists_tendsto_mem_unstableSet_of_tendsto_mem_stableSet`: if points `u n`, frequently
outside the unstable set of `x`, converge to a point of it, then along indices `n k → ∞` and times
`t k → -∞` the points `φ (t k) (u (n k))` converge to a point of the stable set of `x` at distance
`r` from `x`. -/
theorem exists_tendsto_mem_stableSet_of_tendsto_mem_unstableSet (hr : 0 < r)
    (hfwd : ∀ w, (∀ t, 0 ≤ t → φ t w ∈ closedBall x r) → w ∈ stableSet φ x)
    (hbwd : ∀ w, (∀ t, t ≤ 0 → φ t w ∈ closedBall x r) → w ∈ unstableSet φ x)
    {y : α} (hy : y ∈ unstableSet φ x) {u : ℕ → α} (hu : Tendsto u atTop (𝓝 y))
    (hux : ∃ᶠ n in atTop, u n ∉ unstableSet φ x) :
    ∃ z ∈ stableSet φ x, dist z x = r ∧ ∃ (n : ℕ → ℕ) (t : ℕ → ℝ),
      Tendsto n atTop atTop ∧ Tendsto t atTop atBot ∧
        Tendsto (fun k ↦ φ (t k) (u (n k))) atTop (𝓝 z) := by
  obtain ⟨z, hz, hzr, n, t, hn, ht, hlim⟩ :=
    exists_tendsto_mem_unstableSet_of_tendsto_mem_stableSet (φ := φ.reverse) hr
      (fun w hw ↦ by
        rw [stableSet_reverse]
        exact hbwd w fun t ht ↦ by simpa using hw (-t) (neg_nonneg.2 ht))
      (fun w hw ↦ by
        rw [unstableSet_reverse]
        exact hfwd w fun t ht ↦ by simpa using hw (-t) (neg_nonpos.2 ht))
      (by rwa [stableSet_reverse]) hu (by simpa only [stableSet_reverse] using hux)
  rw [unstableSet_reverse] at hz
  exact ⟨z, hz, hzr, n, fun k ↦ -t k, hn, tendsto_neg_atTop_atBot.comp ht,
    by simpa only [_root_.Flow.reverse_apply] using hlim⟩

/-- **The closure of an invariant set continues through an isolated rest point.** If an invariant
set `S` is disjoint from the stable set of `x` but its closure meets that stable set, then its
closure also meets the unstable set of `x`, at distance exactly `r` from `x`, for every isolating
radius `r`. -/
theorem exists_mem_closure_inter_unstableSet_of_mem_closure_inter_stableSet (hr : 0 < r)
    (hfwd : ∀ w, (∀ t, 0 ≤ t → φ t w ∈ closedBall x r) → w ∈ stableSet φ x)
    (hbwd : ∀ w, (∀ t, t ≤ 0 → φ t w ∈ closedBall x r) → w ∈ unstableSet φ x)
    {S : Set α} (hS : IsInvariant φ S) (hSx : Disjoint S (stableSet φ x)) {y : α}
    (hy : y ∈ closure S ∩ stableSet φ x) :
    ∃ z ∈ closure S ∩ unstableSet φ x, dist z x = r := by
  obtain ⟨u, huS, hu⟩ := mem_closure_iff_seq_limit.1 hy.1
  obtain ⟨z, hz, hzr, n, t, -, -, hlim⟩ :=
    exists_tendsto_mem_unstableSet_of_tendsto_mem_stableSet hr hfwd hbwd hy.2 hu
      (Frequently.of_forall fun n ↦ hSx.notMem_of_mem_left (huS n))
  exact ⟨z, ⟨mem_closure_of_tendsto hlim (Eventually.of_forall fun k ↦ hS _ (huS _)), hz⟩, hzr⟩

/-- **The closure of an invariant set continues through an isolated rest point, in backward
time.** The time reversal of
`Flow.exists_mem_closure_inter_unstableSet_of_mem_closure_inter_stableSet`. -/
theorem exists_mem_closure_inter_stableSet_of_mem_closure_inter_unstableSet (hr : 0 < r)
    (hfwd : ∀ w, (∀ t, 0 ≤ t → φ t w ∈ closedBall x r) → w ∈ stableSet φ x)
    (hbwd : ∀ w, (∀ t, t ≤ 0 → φ t w ∈ closedBall x r) → w ∈ unstableSet φ x)
    {S : Set α} (hS : IsInvariant φ S) (hSx : Disjoint S (unstableSet φ x)) {y : α}
    (hy : y ∈ closure S ∩ unstableSet φ x) :
    ∃ z ∈ closure S ∩ stableSet φ x, dist z x = r := by
  obtain ⟨u, huS, hu⟩ := mem_closure_iff_seq_limit.1 hy.1
  obtain ⟨z, hz, hzr, n, t, -, -, hlim⟩ :=
    exists_tendsto_mem_stableSet_of_tendsto_mem_unstableSet hr hfwd hbwd hy.2 hu
      (Frequently.of_forall fun n ↦ hSx.notMem_of_mem_left (huS n))
  exact ⟨z, ⟨mem_closure_of_tendsto hlim (Eventually.of_forall fun k ↦ hS _ (huS _)), hz⟩, hzr⟩

end Flow

end
