/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import TauCeti.Analysis.InnerProductSpace.Harmonic.MeanValue.Basic
import TauCeti.Analysis.InnerProductSpace.Harmonic.MeanValue.Converse
import TauCeti.MeasureTheory.Integral.SubMeanValue

/-!
# Continuous subharmonic functions

Let `E` be a finite-dimensional real inner product space with its volume measure. This file
defines continuous subharmonic functions `u : E → ℝ` on a set `U` by the local sub-mean-value
inequality: `u` is continuous on `U`, and at every `x ∈ U` the value `u x` is at most the average
of `u` over `ball x r` for arbitrarily small radii `r > 0`. No differentiability is assumed, so
the class is closed under pointwise maxima, which is what Perron's method for the Dirichlet
problem needs.

The main result is the **comparison principle**: a subharmonic function on a bounded open set
`U` that lies below a harmonic function `h` on `frontier U`, both continuous on `closure U`, lies
below `h` on all of `closure U`. Applied to balls, it shows that the definition used here implies
the one of Gilbarg–Trudinger, Section 2.8: a subharmonic function lies below every harmonic
function that dominates it on the boundary sphere of a ball. The proof reduces to the maximum
principle for the sub-mean-value property on a compact superlevel set
(`TauCeti.exists_mem_frontier_isMaxOn_of_le_setAverage_ball`).

## Main declarations

* `TauCeti.SubharmonicOn`: continuous functions with the local sub-mean-value inequality.
* `InnerProductSpace.HarmonicOnNhd.subharmonicOn`: harmonic functions are subharmonic.
* `TauCeti.SubharmonicOn.frequently_le_setAverage_of_le`: a continuous function touching a
  subharmonic function from above satisfies the sub-mean-value inequality at the contact point.
* `TauCeti.SubharmonicOn.sup`: the pointwise maximum of two subharmonic functions is subharmonic.
* `TauCeti.SubharmonicOn.sub_harmonicOnNhd`: subtracting a harmonic function preserves
  subharmonicity.
* `TauCeti.SubharmonicOn.le_of_le_frontier`: the comparison principle on a bounded open set.
* `TauCeti.SubharmonicOn.le_of_le_sphere`: the comparison principle on a ball.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 2.8.
-/

public section

namespace TauCeti

open InnerProductSpace MeasureTheory Metric Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {u v w h : E → ℝ} {U V : Set E}

/-- A function `u` is **subharmonic** on `U` if it is continuous on `U` and satisfies the local
sub-mean-value inequality there: at every `x ∈ U`, the value `u x` is at most the average of `u`
over `ball x r` for arbitrarily small radii `r > 0`. -/
structure SubharmonicOn (u : E → ℝ) (U : Set E) : Prop where
  /-- A subharmonic function is continuous. -/
  continuousOn : ContinuousOn u U
  /-- The local sub-mean-value inequality. -/
  frequently_le_setAverage : ∀ x ∈ U, ∃ᶠ r in 𝓝[>] 0, u x ≤ ⨍ y in ball x r, u y

/-- A function subharmonic on a set is subharmonic on every subset. -/
theorem SubharmonicOn.mono (hu : SubharmonicOn u U) (hVU : V ⊆ U) : SubharmonicOn u V :=
  ⟨hu.continuousOn.mono hVU, fun x hx ↦ hu.frequently_le_setAverage x (hVU hx)⟩

/-- A harmonic function is subharmonic. -/
theorem _root_.InnerProductSpace.HarmonicOnNhd.subharmonicOn (hu : HarmonicOnNhd u U) :
    SubharmonicOn u U := by
  -- `u` is harmonic on the open set of points where it is harmonic, which contains `U`.
  obtain ⟨hc, hmean⟩ := (harmonicOnNhd_iff_continuousOn_setAverage_ball_eq (μ := volume)
    (isOpen_setOfPred_harmonicAt (f := u))).1 fun x hx ↦ hx
  exact ⟨hc.mono hu, fun x hx ↦ (hmean x (hu x hx)).mono fun _ h ↦ h.ge⟩

/-- A function `w`, continuous on the open set `U`, that lies above a subharmonic function `v` on
`U` and touches it at `x ∈ U` satisfies the sub-mean-value inequality at `x`. -/
theorem SubharmonicOn.frequently_le_setAverage_of_le (hv : SubharmonicOn v U) (hU : IsOpen U)
    (hw : ContinuousOn w U) (hvw : ∀ y ∈ U, v y ≤ w y) {x : E} (hx : x ∈ U) (hwx : w x = v x) :
    ∃ᶠ r in 𝓝[>] 0, w x ≤ ⨍ y in ball x r, w y := by
  obtain ⟨ε, hε, hεU⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx)
  refine ((hv.frequently_le_setAverage x hx).and_eventually (Ioo_mem_nhdsGT hε)).mono
    fun r ⟨hr, hrε⟩ ↦ ?_
  have hrU : closedBall x r ⊆ U := (closedBall_subset_closedBall hrε.2.le).trans hεU
  have hint : ∀ f : E → ℝ, ContinuousOn f U → IntegrableOn f (ball x r) := fun f hf ↦
    ((hf.mono hrU).integrableOn_compact (isCompact_closedBall x r)).mono_set ball_subset_closedBall
  -- The average of `w - v ≥ 0` over the ball is at least one of its values.
  obtain ⟨y, hy, hle⟩ := exists_le_setAverage (measure_ball_pos volume x hrε.1).ne'
    measure_ball_lt_top.ne ((hint w hw).sub (hint v hv.continuousOn))
  rw [setAverage_sub (hint w hw) (hint v hv.continuousOn), Pi.sub_apply] at hle
  linarith [hvw y (hrU (ball_subset_closedBall hy))]

/-- The pointwise maximum of two subharmonic functions on an open set is subharmonic. -/
theorem SubharmonicOn.sup (hu : SubharmonicOn u U) (hv : SubharmonicOn v U) (hU : IsOpen U) :
    SubharmonicOn (u ⊔ v) U := by
  have huv : ContinuousOn (u ⊔ v) U := hu.continuousOn.sup hv.continuousOn
  -- At `x` the maximum is attained by `u` or by `v`, which lies below `u ⊔ v`.
  refine ⟨huv, fun x hx ↦ ?_⟩
  rcases le_total (v x) (u x) with h | h
  · exact hu.frequently_le_setAverage_of_le hU huv (fun _ _ ↦ le_sup_left) hx (sup_eq_left.2 h)
  · exact hv.frequently_le_setAverage_of_le hU huv (fun _ _ ↦ le_sup_right) hx (sup_eq_right.2 h)

/-- Subtracting a harmonic function from a subharmonic function on an open set gives a
subharmonic function. -/
theorem SubharmonicOn.sub_harmonicOnNhd (hu : SubharmonicOn u U) (hh : HarmonicOnNhd h U)
    (hU : IsOpen U) : SubharmonicOn (u - h) U := by
  refine ⟨hu.continuousOn.sub hh.continuousOn, fun x hx ↦ ?_⟩
  obtain ⟨ε, hε, hεU⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx)
  refine ((hu.frequently_le_setAverage x hx).and_eventually (Ioo_mem_nhdsGT hε)).mono
    fun r ⟨hr, hrε⟩ ↦ ?_
  have hrU : closedBall x r ⊆ U := (closedBall_subset_closedBall hrε.2.le).trans hεU
  have hint : ∀ f : E → ℝ, ContinuousOn f U → IntegrableOn f (ball x r) := fun f hf ↦
    ((hf.mono hrU).integrableOn_compact (isCompact_closedBall x r)).mono_set ball_subset_closedBall
  rw [setAverage_sub (hint u hu.continuousOn) (hint h hh.continuousOn),
    (hh.mono hrU).setAverage_ball_eq hrε.1, Pi.sub_apply]
  linarith

variable [Nontrivial E]

/-- **The comparison principle for subharmonic functions.** Let `U` be a bounded open set, `u`
subharmonic and `h` harmonic on `U`, both continuous on `closure U`. If `u ≤ h` on `frontier U`,
then `u ≤ h` on `closure U`. -/
theorem SubharmonicOn.le_of_le_frontier (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hu : SubharmonicOn u U) (huc : ContinuousOn u (closure U)) (hh : HarmonicOnNhd h U)
    (hhc : ContinuousOn h (closure U)) (hle : ∀ x ∈ frontier U, u x ≤ h x) :
    ∀ x ∈ closure U, u x ≤ h x := by
  intro x hx
  by_contra! hlt
  set w := u - h
  have hwc : ContinuousOn w (closure U) := huc.sub hhc
  have hw := hu.sub_harmonicOnNhd hh hU
  -- The superlevel set `K = {w ≥ m}`, with `0 < m < w x`, is a compact subset of `U`.
  set m := w x / 2
  have hwx : 0 < w x := sub_pos.2 hlt
  have hm : 0 < m := half_pos hwx
  set K := closure U ∩ w ⁻¹' Ici m
  have hKc : IsCompact K := hUb.isCompact_closure.of_isClosed_subset
    (hwc.preimage_isClosed_of_isClosed isClosed_closure isClosed_Ici) inter_subset_left
  have hKU : K ⊆ U := fun y ⟨hyc, hym⟩ ↦ by
    by_contra hyU
    have : w y ≤ 0 := sub_nonpos.2 (hle y (hU.frontier_eq ▸ ⟨hyc, hyU⟩))
    simp only [mem_preimage, mem_Ici] at hym
    linarith
  have hxK : x ∈ K := ⟨hx, by simp only [mem_preimage, mem_Ici, m]; linarith⟩
  obtain ⟨z, hz, hzmax⟩ := exists_mem_frontier_isMaxOn_of_le_setAverage_ball (μ := volume) hKc
    ⟨x, hxK⟩ (hwc.mono inter_subset_left)
    fun y hy ↦ hw.frequently_le_setAverage y (hKU (interior_subset hy))
  -- A maximum point `z` of `w` on `K` has `w z ≥ w x > m`, so a neighbourhood of `z` lies in
  -- `K`, contradicting `z ∈ frontier K`.
  have hzK : z ∈ K := hKc.isClosed.frontier_subset hz
  have hzm : m < w z := by
    have : w x ≤ w z := hzmax hxK
    simp only [m]
    linarith
  have hzU := hKU hzK
  have hnhds : K ∈ 𝓝 z := by
    filter_upwards [hU.mem_nhds hzU,
      (hw.continuousOn.continuousAt (hU.mem_nhds hzU)).eventually (lt_mem_nhds hzm)] with y hyU hy
    exact ⟨subset_closure hyU, hy.le⟩
  exact (disjoint_left.1 disjoint_interior_frontier (mem_interior_iff_mem_nhds.2 hnhds)) hz

/-- **The comparison principle on a ball.** A function subharmonic on `ball c r` and continuous
on `closedBall c r` lies below every function harmonic on `ball c r` and continuous on
`closedBall c r` that dominates it on `sphere c r`. -/
theorem SubharmonicOn.le_of_le_sphere {c : E} {r : ℝ} (hu : SubharmonicOn u (ball c r))
    (huc : ContinuousOn u (closedBall c r)) (hh : HarmonicOnNhd h (ball c r))
    (hhc : ContinuousOn h (closedBall c r)) (hle : ∀ x ∈ sphere c r, u x ≤ h x) :
    ∀ x ∈ closedBall c r, u x ≤ h x := by
  rcases le_or_gt r 0 with hr | hr
  · -- For `r ≤ 0` the closed ball is contained in the sphere.
    intro x hx
    exact hle x (mem_sphere.2 (le_antisymm (mem_closedBall.1 hx) (hr.trans dist_nonneg)))
  rw [← closure_ball c hr.ne'] at huc hhc ⊢
  exact hu.le_of_le_frontier isOpen_ball isBounded_ball huc hh hhc
    (by rwa [frontier_ball c hr.ne'])

end TauCeti
