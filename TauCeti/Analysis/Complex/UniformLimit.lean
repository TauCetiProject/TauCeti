/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Normed.Group.FunctionSeries
import TauCeti.Analysis.Normed.Group.Basic

/-!
# Uniform limits of holomorphic maps on a complex normed space

Mathlib's `TendstoLocallyUniformlyOn.differentiableOn` shows that a locally uniform limit of
holomorphic functions on an open subset of `ℂ` is holomorphic; its proof uses the Cauchy integral
formula on circles. This file proves the corresponding statement for uniform limits on an open
subset of an arbitrary complex normed space `V`, with values in a complex Banach space `E`
(`TendstoUniformlyOn.differentiableOn`). It is the input needed to see that bounded holomorphic
functions form a closed subspace of the bounded continuous functions.

## Main results

* `TauCeti.norm_fderiv_le_of_forall_mem_ball_norm_le`: if `‖f‖ ≤ M` on `ball c r`, then
  `‖fderiv ℂ f c‖ ≤ 2 * M / r`.
* `TendstoUniformlyOn.differentiableOn`: a uniform limit of holomorphic maps on an open set is
  holomorphic.
* `TauCeti.exists_differentiableOn_eqOn_add_tsum`: the telescoping step in exhaustion proofs.
  Given approximations `P k` holomorphic on an open set `U` whose tail errors
  `‖(h (k + 1) - h k) z - P k z‖` on `U` (for `k ≥ m`) are dominated by a summable sequence and
  whose differences `h (k + 1) - h k` are holomorphic on `U`, the corrected series
  `h 0 + ∑' k, (h (k + 1) - h k - P k)` agrees on `U` with `h m` plus a holomorphic function.

## References

* J. Mujica, *Complex Analysis in Banach Spaces*, North-Holland Mathematics Studies **120**,
  North-Holland, 1986.
-/

public section

open Filter Metric Set Topology

variable {V E ι : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup E]
  [NormedSpace ℂ E]

namespace TauCeti

/-- **Cauchy's estimate on a ball in a complex normed space.** If `f` is holomorphic on
`ball c r` and bounded there by `M`, then `‖fderiv ℂ f c‖ ≤ 2 * M / r`. -/
theorem norm_fderiv_le_of_forall_mem_ball_norm_le {f : V → E} {c : V} {r M : ℝ}
    (hd : DifferentiableOn ℂ f (ball c r)) (hr : 0 < r) (hM : ∀ y ∈ ball c r, ‖f y‖ ≤ M) :
    ‖fderiv ℂ f c‖ ≤ 2 * M / r :=
  Complex.norm_fderiv_le_div_of_mapsTo_ball hd
    (mapsTo_closedBall_of_forall_norm_le hM (mem_ball_self hr)) hr

end TauCeti

/-- **A uniform limit of holomorphic maps is holomorphic.** If holomorphic maps `F n` on an open
subset `U` of a complex normed space converge uniformly on `U` to `f`, with values in a complex
Banach space, then `f` is holomorphic on `U`.

This is the analogue, for domains in an arbitrary complex normed space, of Mathlib's
`TendstoLocallyUniformlyOn.differentiableOn` for domains in `ℂ`. -/
theorem TendstoUniformlyOn.differentiableOn [CompleteSpace E] {l : Filter ι} [l.NeBot]
    {F : ι → V → E} {f : V → E} {U : Set V} (hf : TendstoUniformlyOn F f l U)
    (hF : ∀ᶠ n in l, DifferentiableOn ℂ (F n) U) (hU : IsOpen U) : DifferentiableOn ℂ f U := by
  -- The Cauchy estimate `TauCeti.norm_fderiv_le_of_forall_mem_ball_norm_le` makes the derivatives
  -- uniformly Cauchy on a smaller ball, so they converge uniformly there by completeness of
  -- `V →L[ℂ] E`, and `hasFDerivAt_of_tendstoUniformlyOnFilter` identifies the limit as the
  -- derivative of the limit function.
  intro x hx
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU x hx
  have hr : 0 < R / 2 := half_pos hR
  -- Around each point of `ball x (R / 2)`, the ball of radius `R / 2` stays inside `U`.
  have hsub : ∀ z ∈ ball x (R / 2), ball z (R / 2) ⊆ U := fun z hz =>
    (ball_subset_ball' (by linarith [mem_ball.mp hz])).trans hRU
  -- The derivatives are uniformly Cauchy on `ball x (R / 2)`, by the Cauchy estimate applied to
  -- the differences `F m - F n` on balls of radius `R / 2`.
  have hcauchy : UniformCauchySeqOn (fun n => fderiv ℂ (F n)) l (ball x (R / 2)) := by
    intro u hu
    obtain ⟨ε, hε, hεu⟩ := mem_uniformity_dist.mp hu
    have hδ : 0 < ε * (R / 2) / 4 := by positivity
    filter_upwards [hf.uniformCauchySeqOn _ (dist_mem_uniformity hδ), hF.prod_mk hF]
      with m hm hFm z hz
    have hd₁ := hFm.1.differentiableAt (hU.mem_nhds (hsub z hz (mem_ball_self hr)))
    have hd₂ := hFm.2.differentiableAt (hU.mem_nhds (hsub z hz (mem_ball_self hr)))
    have hest := TauCeti.norm_fderiv_le_of_forall_mem_ball_norm_le
      ((hFm.1.sub hFm.2).mono (hsub z hz)) hr fun y hy => by
        simpa [dist_eq_norm] using (hm y (hsub z hz hy)).le
    rw [fderiv_sub hd₁ hd₂] at hest
    refine hεu ?_
    rw [dist_eq_norm]
    calc ‖fderiv ℂ (F m.1) z - fderiv ℂ (F m.2) z‖ ≤ 2 * (ε * (R / 2) / 4) / (R / 2) := hest
      _ < ε := by field_simp; linarith
  -- By completeness, the derivatives converge pointwise, hence uniformly on the small ball.
  choose! g' hg' using fun z (hz : z ∈ ball x (R / 2)) =>
    cauchy_map_iff_exists_tendsto.mp (hcauchy.cauchy_map hz)
  have hT := hcauchy.tendstoUniformlyOn_of_tendsto hg'
  refine (hasFDerivAt_of_tendstoUniformlyOnFilter
    (hT.tendstoUniformlyOnFilter.mono_right (le_principal_iff.mpr (ball_mem_nhds x hr)))
    ((hF.prod_mk (hU.mem_nhds hx)).mono fun n hn =>
      (hn.1.differentiableAt (hU.mem_nhds hn.2)).hasFDerivAt)
    (eventually_of_mem (hU.mem_nhds hx) fun y hy => hf.tendsto_at hy)).differentiableAt
    |>.differentiableWithinAt

namespace TauCeti

/-- **Telescoping step.** Let `U` be an open subset of a complex normed space, let `P k` be
holomorphic on `U` for all `k`, and suppose that for `k ≥ m` the differences `h (k + 1) - h k` are
holomorphic on `U` and `‖(h (k + 1) - h k) z - P k z‖ ≤ M k` on `U` for a summable sequence `M`.
Then on `U` the corrected limit `h 0 + ∑' k, (h (k + 1) - h k - P k)` agrees with `h m` plus a
holomorphic function. -/
theorem exists_differentiableOn_eqOn_add_tsum [CompleteSpace E] {h P : ℕ → V → E}
    {U : Set V} {M : ℕ → ℝ} (hU : IsOpen U) (hP : ∀ k, DifferentiableOn ℂ (P k) U)
    (hM : Summable M) (m : ℕ)
    (hdiff : ∀ k, m ≤ k → DifferentiableOn ℂ (h (k + 1) - h k) U)
    (hP_le : ∀ k, m ≤ k → ∀ z ∈ U, ‖(h (k + 1) - h k) z - P k z‖ ≤ M k) :
    ∃ K : V → E, DifferentiableOn ℂ K U ∧
      EqOn (fun z ↦ h 0 z + ∑' k, (h (k + 1) - h k - P k) z) (h m + K) U := by
  set e : ℕ → V → E := fun k ↦ h (k + 1) - h k - P k
  have hsumm : Summable fun k ↦ M (k + m) := (summable_nat_add_iff m).2 hM
  refine ⟨fun z ↦ ∑' k, e (k + m) z - ∑ k ∈ Finset.range m, P k z, ?_, fun z hz ↦ ?_⟩
  · refine DifferentiableOn.sub ?_ (DifferentiableOn.fun_sum fun k _ ↦ hP k)
    exact (tendstoUniformlyOn_tsum hsumm fun k z hz ↦ hP_le (k + m) (Nat.le_add_left m k) z hz)
      |>.differentiableOn (Eventually.of_forall fun _ ↦ DifferentiableOn.fun_sum fun k _ ↦
        (hdiff (k + m) (Nat.le_add_left m k)).sub (hP (k + m))) hU
  · have hs : Summable fun k ↦ e k z := (summable_nat_add_iff m).1 <|
      .of_norm_bounded hsumm fun k ↦ hP_le (k + m) (Nat.le_add_left m k) z hz
    have htel : ∑ k ∈ Finset.range m, e k z = h m z - h 0 z - ∑ k ∈ Finset.range m, P k z := by
      simp only [e, Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_range_sub fun k ↦ h k z]
    simp only [Pi.add_apply]
    rw [← hs.sum_add_tsum_nat_add m, htel]
    abel

end TauCeti
