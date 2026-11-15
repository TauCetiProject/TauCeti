/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.InnerProductSpace.Harmonic.MeanValue.Basic
import TauCeti.Analysis.InnerProductSpace.Harmonic.MeanValue.Converse

/-!
# Locally uniform limits of harmonic functions

Let `E` be a finite-dimensional real inner product space. This file proves that a locally uniform
limit of harmonic functions `E → ℝ` on an open set `U` is harmonic. The limit is continuous and
inherits the mean-value property on small balls, so it is harmonic by the converse of the
mean-value property (`TauCeti.harmonicOnNhd_of_setAverage_ball_eq`).

## Main declarations

* `TauCeti.harmonicOnNhd_of_tendstoLocallyUniformlyOn`: a locally uniform limit of harmonic
  functions is harmonic.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 2.8.
* L. C. Evans, *Partial Differential Equations*, Section 2.2.3.
-/

public section

namespace TauCeti

open InnerProductSpace MeasureTheory Metric Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} {F : ι → E → ℝ} {f : E → ℝ} {U : Set E}

/-- **Locally uniform limits of harmonic functions are harmonic.** If eventually along a nontrivial
filter `p` the functions `F i` are harmonic on the open set `U`, and `F i` tends to `f` locally
uniformly on `U`, then `f` is harmonic on `U`. -/
theorem harmonicOnNhd_of_tendstoLocallyUniformlyOn {p : Filter ι} [p.NeBot] (hU : IsOpen U)
    (hF : ∀ᶠ i in p, HarmonicOnNhd (F i) U) (hlim : TendstoLocallyUniformlyOn F f p U) :
    HarmonicOnNhd f U := by
  borelize E
  let μ : Measure E := Measure.addHaar
  refine harmonicOnNhd_of_setAverage_ball_eq (μ := μ) hU
    (hlim.continuousOn (hF.mono fun i hi ↦ hi.continuousOn).frequently) fun x hx ↦ ?_
  obtain ⟨ε, hε, hεU⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx)
  refine (eventually_of_mem (Ioo_mem_nhdsGT hε) fun r hr ↦ ?_).frequently
  have hrU : closedBall x r ⊆ U := (closedBall_subset_closedBall hr.2.le).trans hεU
  have hunif : TendstoUniformlyOn F f p (closedBall x r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hlim _ hrU (isCompact_closedBall x r)
  have hfi : IntegrableOn f (ball x r) μ :=
    (((hlim.continuousOn (hF.mono fun i hi ↦ hi.continuousOn).frequently).mono
      hrU).integrableOn_compact (isCompact_closedBall x r)).mono_set ball_subset_closedBall
  have hμ : μ (ball x r) ≠ 0 := (measure_ball_pos μ x hr.1).ne'
  -- The averages of `F i` over `ball x r` converge to the average of `f`: wherever `F i` is
  -- uniformly `δ`-close to `f`, so are the averages.
  have havg : Tendsto (fun i ↦ ⨍ y in ball x r, F i y ∂μ) p (𝓝 (⨍ y in ball x r, f y ∂μ)) := by
    refine Metric.tendsto_nhds.2 fun δ hδ ↦ ?_
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunif δ hδ, hF] with i hi hFi
    have hFii : IntegrableOn (F i) (ball x r) μ :=
      (((hFi.mono hrU).continuousOn).integrableOn_compact
        (isCompact_closedBall x r)).mono_set ball_subset_closedBall
    have hsub := setAverage_sub hFii hfi
    obtain ⟨y, hy, hyle⟩ := exists_setAverage_le hμ measure_ball_lt_top.ne (hFii.sub hfi)
    obtain ⟨z, hz, hzle⟩ := exists_le_setAverage hμ measure_ball_lt_top.ne (hFii.sub hfi)
    have hy' := hi y (ball_subset_closedBall hy)
    have hz' := hi z (ball_subset_closedBall hz)
    rw [Real.dist_eq] at hy' hz' ⊢
    rw [abs_lt]
    simp only [Pi.sub_apply] at hsub hyle hzle
    constructor <;> linarith [abs_lt.1 hy', abs_lt.1 hz']
  -- Each `F i` equals its average at the centre, so the two limits agree.
  exact tendsto_nhds_unique
    (havg.congr' (hF.mono fun i hi ↦ HarmonicOnNhd.setAverage_ball_eq (hi.mono hrU) hr.1))
    (hunif.tendsto_at (mem_closedBall_self hr.1.le))

end TauCeti
