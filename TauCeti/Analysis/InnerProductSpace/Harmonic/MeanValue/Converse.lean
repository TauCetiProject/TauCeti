/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import TauCeti.Analysis.InnerProductSpace.Harmonic.MeanValue.Basic
import TauCeti.Analysis.PDE.PoissonIntegral.Ball
import TauCeti.MeasureTheory.Integral.SubMeanValue

/-!
# The converse of the mean-value property

Let `E` be a finite-dimensional real inner product space with an additive Haar measure `μ`. A
function harmonic near a closed ball equals its average over the ball at the centre
(`InnerProductSpace.HarmonicOnNhd.setAverage_ball_eq`). This file proves the converse: a function
continuous on an open set `U` that equals its average over `ball x r` at the centre `x`, for every
`x ∈ U` and for arbitrarily small radii `r > 0`, is harmonic on `U`. Thus harmonic functions are
exactly the continuous functions with the mean-value property, and harmonicity can be verified
without differentiating. This is how one shows that a limit or an envelope of harmonic functions
is harmonic, as in Perron's method for the Dirichlet problem.

## The argument

The first ingredient is the **maximum principle for the sub-mean-value property**
(`IsCompact.le_of_le_setAverage_ball_le_frontier`, in
`TauCeti.MeasureTheory.Integral.SubMeanValue`):
if `u` is continuous on a compact set `K` and `u x ≤ ⨍ y in ball x r, u y ∂μ` for arbitrarily
small `r` at every interior point `x`, then `u` is bounded on `K` by its bounds on `frontier K`.

For the converse, fix `x ∈ U` and a closed ball `closedBall x r ⊆ U`. The Dirichlet problem on the
ball has a solution `h`, harmonic in `ball x r`, continuous on `closedBall x r` and equal to `u` on
`sphere x r` (`TauCeti.exists_harmonicOnNhd_ball_continuousOn_closedBall_eqOn_sphere`). By the
mean-value property of `h`, the difference `u - h` has the mean-value property on small balls
inside `ball x r`, and it vanishes on the sphere. The maximum principle, applied to `u - h` and to
`h - u`, gives `u = h` on the closed ball, so `u` is harmonic near `x`.

## Main declarations

* `TauCeti.harmonicOnNhd_of_setAverage_ball_eq`: **the converse of the mean-value property**.
* `TauCeti.harmonicOnNhd_iff_continuousOn_setAverage_ball_eq`: the mean-value characterization of
  harmonic functions on an open set.

## References

* L. C. Evans, *Partial Differential Equations*, Section 2.2.3, Theorem 3, and Problem 2.5.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 2.7.
-/

public section

namespace TauCeti

open InnerProductSpace MeasureTheory Metric Set Filter Topology

section Converse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → ℝ}

/-- **The converse of the mean-value property.** Let `U` be open and let `u` be continuous on `U`.
If at every point `x ∈ U` the value `u x` equals the average of `u` over `ball x r` for
arbitrarily small radii `r > 0`, then `u` is harmonic on `U`. -/
theorem harmonicOnNhd_of_setAverage_ball_eq {U : Set E} (hU : IsOpen U) (hu : ContinuousOn u U)
    (hmean : ∀ x ∈ U, ∃ᶠ r in 𝓝[>] 0, ⨍ y in ball x r, u y ∂μ = u x) :
    HarmonicOnNhd u U := by
  intro x hx
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- In the trivial space `u` is constant.
    have hconst : u = fun _ ↦ u x := funext fun y ↦ congrArg u (Subsingleton.elim y x)
    rw [hconst]
    exact harmonicAt_const _
  obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx)
  have huK : ContinuousOn u (closedBall x r) := hu.mono hrU
  obtain ⟨h, hh, hhc, hhu⟩ := exists_harmonicOnNhd_ball_continuousOn_closedBall_eqOn_sphere
    (huK.mono sphere_subset_closedBall)
  -- The difference `u - h` has the mean-value property on small balls inside `ball x r`.
  have hmean' : ∀ y ∈ interior (closedBall x r),
      ∃ᶠ ρ in 𝓝[>] 0, ⨍ z in ball y ρ, (u - h) z ∂μ = (u - h) y := by
    intro y hy
    rw [interior_closedBall x hr.ne'] at hy
    have hyU : y ∈ U := hrU (ball_subset_closedBall hy)
    obtain ⟨ε, hε, hεx⟩ := Metric.isOpen_iff.1 isOpen_ball y hy
    refine ((hmean y hyU).and_eventually (Ioo_mem_nhdsGT hε)).mono fun ρ ⟨hρ, hρε⟩ ↦ ?_
    have hsub : closedBall y ρ ⊆ ball x r := (closedBall_subset_ball hρε.2).trans hεx
    have hhρ : HarmonicOnNhd h (closedBall y ρ) := hh.mono hsub
    have hui : Integrable u (μ.restrict (ball y ρ)) :=
      ((huK.mono (hsub.trans ball_subset_closedBall)).integrableOn_compact
        (isCompact_closedBall y ρ)).mono_set ball_subset_closedBall
    have hhi : Integrable h (μ.restrict (ball y ρ)) :=
      (hhρ.contDiffOn.continuousOn.integrableOn_compact
        (isCompact_closedBall y ρ)).mono_set ball_subset_closedBall
    rw [average_sub hui hhi, hρ, hhρ.setAverage_ball_eq hρε.1, Pi.sub_apply]
  have hK := isCompact_closedBall x r
  have hfr : frontier (closedBall x r) = sphere x r := frontier_closedBall x hr.ne'
  have hwc : ContinuousOn (u - h) (closedBall x r) := huK.sub hhc
  have hle := hK.le_of_le_setAverage_ball_le_frontier (μ := μ) (m := 0) hwc
    (fun y hy ↦ (hmean' y hy).mono fun _ h ↦ h.ge)
    (fun y hy ↦ by rw [hfr] at hy; simp [hhu hy])
  have hge := hK.ge_of_setAverage_ball_le_ge_frontier (μ := μ) (m := 0) hwc
    (fun y hy ↦ (hmean' y hy).mono fun _ h ↦ h.le)
    (fun y hy ↦ by rw [hfr] at hy; simp [hhu hy])
  have heq : u =ᶠ[𝓝 x] h := eventually_of_mem (ball_mem_nhds x hr) fun y hy ↦
    sub_eq_zero.1 (le_antisymm (hle (ball_subset_closedBall hy)) (hge (ball_subset_closedBall hy)))
  exact (harmonicAt_congr_nhds heq).2 (hh x (mem_ball_self hr))

/-- **The mean-value characterization of harmonic functions.** On an open set `U`, a function is
harmonic if and only if it is continuous and, at every point `x ∈ U`, equal to its average over
`ball x r` for arbitrarily small radii `r > 0`. A harmonic function in fact has this property for
every radius `r > 0` with `closedBall x r ⊆ U`
(`InnerProductSpace.HarmonicOnNhd.setAverage_ball_eq`). -/
theorem harmonicOnNhd_iff_continuousOn_setAverage_ball_eq {U : Set E} (hU : IsOpen U) :
    HarmonicOnNhd u U ↔
      ContinuousOn u U ∧ ∀ x ∈ U, ∃ᶠ r in 𝓝[>] 0, ⨍ y in ball x r, u y ∂μ = u x := by
  refine ⟨fun hu ↦ ⟨hu.contDiffOn.continuousOn, fun x hx ↦ ?_⟩,
    fun h ↦ harmonicOnNhd_of_setAverage_ball_eq hU h.1 h.2⟩
  obtain ⟨ε, hε, hεU⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx)
  exact (eventually_of_mem (Ioo_mem_nhdsGT hε) fun r hr ↦
    (hu.mono ((closedBall_subset_closedBall hr.2.le).trans hεU)).setAverage_ball_eq hr.1).frequently

end Converse

end TauCeti
