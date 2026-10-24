/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import TauCeti.Combinatorics.DenseGraphLimits.AEEqFun.Basic
import TauCeti.MeasureTheory.Function.Lp.Complete

/-!
# Limits of L¹-Cauchy graphon sequences

A sequence of graphons whose kernels have an `L¹` Cauchy modulus tending to zero converges in cut
distance to a graphon. The uncurried kernels converge in `L¹` by the general completeness result
`TauCeti.exists_tendsto_eLpNorm_of_tendsto_eLpNorm_bound`, and a subsequence converges almost
everywhere. The pointwise limit remains symmetric and `[0, 1]`-valued, so `exists_graphon_repr`
turns its almost-everywhere class back into a strict graphon. Finally, the cut norm is bounded by
the `L¹` norm.

This form is designed for graphon compactness arguments: after representatives of a Cauchy
subsequence have been realigned, this result supplies the limiting strict graphon.

## Main results

* `TauCeti.DenseGraphLimits.exists_graphon_tendsto_eLpNorm_of_tendsto_eLpNorm_bound` constructs a
  strict graphon `L¹` limit from an `L¹` Cauchy modulus tending to zero.
* `TauCeti.DenseGraphLimits.cutDist_le_eLpNorm_one_toReal` bounds cut distance by `L¹` distance.
* `TauCeti.DenseGraphLimits.exists_graphon_tendsto_cutDist_of_tendsto_eLpNorm_bound` is the
  resulting cut-distance convergence.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §9.3.
* L. Lovász and B. Szegedy, *Szemerédi's Lemma for the Analyst*, GAFA 17 (2007), §5.
-/

public section

noncomputable section

open Filter MeasureTheory

open scoped ENNReal Topology

namespace TauCeti.DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A graphon sequence with an `L¹` Cauchy modulus tending to zero has a strict graphon limit in
`L¹`.

The bound `B N` controls every pair of terms whose indices are at least `N`. This is the graphon
form of `TauCeti.exists_tendsto_eLpNorm_of_tendsto_eLpNorm_bound`: the limit is again symmetric and
`[0, 1]`-valued, and so is represented by a strict graphon. -/
theorem exists_graphon_tendsto_eLpNorm_of_tendsto_eLpNorm_bound
    (W : ℕ → Graphon Ω μ) {B : ℕ → ℝ≥0∞} (hB : Tendsto B atTop (𝓝 0))
    (hCauchy : ∀ N n m, N ≤ n → N ≤ m →
      eLpNorm
        ((fun z : Ω × Ω ↦ W n z.1 z.2) - fun z : Ω × Ω ↦ W m z.1 z.2)
        1 (μ.prod μ) ≤ B N) :
    ∃ Wlim : Graphon Ω μ,
      Tendsto
        (fun n ↦ eLpNorm
          ((fun z : Ω × Ω ↦ W n z.1 z.2) - fun z : Ω × Ω ↦ Wlim z.1 z.2)
          1 (μ.prod μ)) atTop (𝓝 0) := by
  let f : ℕ → Ω × Ω → ℝ := fun n z ↦ W n z.1 z.2
  obtain ⟨fLim, hfLimMeas, hLp⟩ := exists_tendsto_eLpNorm_of_tendsto_eLpNorm_bound le_rfl
    (fun n ↦ (W n).measurable.aestronglyMeasurable) hB (f := f) hCauchy
  -- A subsequence converges almost everywhere; along it, symmetry and the range `[0, 1]` pass to
  -- the limit.
  obtain ⟨φ, -, hfLim⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hLp).exists_seq_tendsto_ae
  have hfLimRange : ∀ᵐ z ∂(μ.prod μ), fLim z ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [hfLim] with z hz
    exact isClosed_Icc.mem_of_tendsto hz
      (Eventually.of_forall fun n ↦ (W (φ n)).mem_Icc z.1 z.2)
  have hfLimSwap : ∀ᵐ z ∂(μ.prod μ),
      Tendsto (fun n ↦ f (φ n) z.swap) atTop (𝓝 (fLim z.swap)) :=
    (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hfLim
  have hfLimSymm : ∀ᵐ z ∂(μ.prod μ), fLim z = fLim z.swap := by
    filter_upwards [hfLim, hfLimSwap] with z hz hzswap
    rcases z with ⟨x, y⟩
    have hzswap' : Tendsto (fun n ↦ f (φ n) (y, x)) atTop (𝓝 (fLim (y, x))) := by
      simpa only [Prod.swap_prod_mk] using hzswap
    have hz' : Tendsto (fun n ↦ f (φ n) (x, y)) atTop (𝓝 (fLim (y, x))) := by
      convert hzswap' using 1
      funext n
      simpa only [f, Prod.swap_prod_mk] using (W (φ n)).symm x y
    simpa only [Prod.swap_prod_mk] using tendsto_nhds_unique hz hz'
  let fLimAE : (Ω × Ω) →ₘ[μ.prod μ] ℝ := AEEqFun.mk fLim hfLimMeas.aestronglyMeasurable
  have hfLimAE_coe : ⇑fLimAE =ᵐ[μ.prod μ] fLim := AEEqFun.coeFn_mk _ _
  obtain ⟨Wlim, hWlim⟩ := exists_graphon_repr fLimAE
    (by
      filter_upwards [hfLimAE_coe, hfLimRange] with z hz hr
      exact hz.symm ▸ hr)
    (by
      filter_upwards [hfLimAE_coe,
        (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hfLimAE_coe,
        hfLimSymm] with z hz hzswap hsymm
      rw [hz, hzswap, hsymm])
  have hWlimAE : ∀ᵐ z ∂(μ.prod μ), Wlim z.1 z.2 = fLim z := by
    calc
      (fun z ↦ Wlim z.1 z.2) =ᵐ[μ.prod μ] ⇑(Graphon.toAEEqFun Wlim) :=
        (Graphon.coeFn_toAEEqFun Wlim).symm
      _ =ᵐ[μ.prod μ] ⇑fLimAE := by rw [hWlim]
      _ =ᵐ[μ.prod μ] fLim := hfLimAE_coe
  refine ⟨Wlim, hLp.congr' (Eventually.of_forall fun n ↦ ?_)⟩
  apply eLpNorm_congr_ae
  filter_upwards [hWlimAE] with z hz
  simp only [Pi.sub_apply, f, hz]

/-- The cut distance between two graphons on the same probability space is bounded by the real
`L¹` seminorm of the difference of their uncurried functions. -/
theorem cutDist_le_eLpNorm_one_toReal (U W : Graphon Ω μ) :
    cutDist U W ≤ (eLpNorm
      ((fun z : Ω × Ω ↦ U z.1 z.2) - fun z : Ω × Ω ↦ W z.1 z.2)
      1 (μ.prod μ)).toReal := by
  refine (cutDist_le_cutNorm_sub U W).trans ((cutNorm_le_toReal_eLpNorm μ _).trans_eq ?_)
  simp only [SymmKernel.coe_sub, Pi.sub_apply, Graphon.coe_toSymmKernel, Pi.sub_def]

/-- A graphon sequence with an `L¹` Cauchy modulus tending to zero converges in cut distance to a
strict graphon. This is the cut-distance consequence of
`exists_graphon_tendsto_eLpNorm_of_tendsto_eLpNorm_bound`. -/
theorem exists_graphon_tendsto_cutDist_of_tendsto_eLpNorm_bound
    (W : ℕ → Graphon Ω μ) {B : ℕ → ℝ≥0∞} (hB : Tendsto B atTop (𝓝 0))
    (hCauchy : ∀ N n m, N ≤ n → N ≤ m →
      eLpNorm
        ((fun z : Ω × Ω ↦ W n z.1 z.2) - fun z : Ω × Ω ↦ W m z.1 z.2)
        1 (μ.prod μ) ≤ B N) :
    ∃ Wlim : Graphon Ω μ, Tendsto (fun n ↦ cutDist (W n) Wlim) atTop (𝓝 0) := by
  obtain ⟨Wlim, hLp⟩ :=
    exists_graphon_tendsto_eLpNorm_of_tendsto_eLpNorm_bound W hB hCauchy
  refine ⟨Wlim, squeeze_zero
    (g := fun n ↦ (eLpNorm
      ((fun z : Ω × Ω ↦ W n z.1 z.2) - fun z : Ω × Ω ↦ Wlim z.1 z.2)
      1 (μ.prod μ)).toReal)
    (fun n ↦ cutDist_nonneg (W n) Wlim) ?_ ?_⟩
  · intro n
    exact cutDist_le_eLpNorm_one_toReal (W n) Wlim
  · exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hLp

end TauCeti.DenseGraphLimits
