/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import TauCeti.Combinatorics.DenseGraphLimits.AEEqFun

/-!
# Limits of L¹-Cauchy graphon sequences

A sequence of graphons whose kernels have an `L¹` Cauchy modulus tending to zero converges in cut
distance to a graphon. A summably fast subsequence and Mathlib's completeness machinery for
`eLpNorm` produce an almost-everywhere pointwise limit. The pointwise limit remains symmetric and
`[0, 1]`-valued, so `exists_graphon_repr` turns its almost-everywhere class back into a strict
graphon. Finally, the cut norm is bounded by the `L¹` norm.

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

The bound `B N` controls every pair of terms whose indices are at least `N`. A summably fast
subsequence gives an almost-everywhere pointwise limit through Mathlib's `Lp` completeness
machinery; the closed conditions of symmetry and range `[0, 1]` pass to that limit. -/
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
  have hf : ∀ n, AEStronglyMeasurable (f n) (μ.prod μ) :=
    fun n ↦ (W n).measurable.aestronglyMeasurable
  have hCauchy' : ∀ N n m, N ≤ n → N ≤ m →
      eLpNorm (f n - f m) 1 (μ.prod μ) ≤ B N := by
    simpa only [f] using hCauchy
  let Bfast : ℕ → ℝ≥0∞ := fun n ↦ 2⁻¹ ^ n
  have hBfast : ∑' n, Bfast n ≠ ∞ := by simp [Bfast]
  have hB_eventually : ∀ n, ∀ᶠ k in atTop, B k < Bfast n := by
    intro n
    exact (tendsto_order.1 hB).2 _
      (ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) n)
  obtain ⟨φ, hφ, hφB⟩ := Filter.extraction_forall_of_eventually hB_eventually
  let fSub : ℕ → Ω × Ω → ℝ := fun n ↦ f (φ n)
  have hfSub : ∀ n, AEStronglyMeasurable (fSub n) (μ.prod μ) := fun n ↦ hf (φ n)
  have hCauchySub : ∀ N n m, N ≤ n → N ≤ m →
      eLpNorm (fSub n - fSub m) 1 (μ.prod μ) < Bfast N := by
    intro N n m hn hm
    exact (hCauchy' (φ N) (φ n) (φ m) (hφ.monotone hn) (hφ.monotone hm)).trans_lt
      (hφB N)
  have haeLimit : ∀ᵐ z ∂(μ.prod μ), ∃ a : ℝ, Tendsto (fun n ↦ fSub n z) atTop (𝓝 a) :=
    Lp.ae_tendsto_of_cauchy_eLpNorm hfSub le_rfl hBfast hCauchySub
  obtain ⟨fLim, hfLimMeas, hfLim⟩ :=
    exists_stronglyMeasurable_limit_of_tendsto_ae hfSub haeLimit
  have hLp : Tendsto (fun n ↦ eLpNorm (f n - fLim) 1 (μ.prod μ)) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε
    obtain ⟨N, hN⟩ := (ENNReal.tendsto_atTop_zero.mp hB) ε hε
    refine ⟨N, fun n hn ↦ ?_⟩
    have hliminf : eLpNorm (f n - fLim) 1 (μ.prod μ) ≤
        atTop.liminf fun m ↦ eLpNorm (f n - fSub m) 1 (μ.prod μ) := by
      refine Lp.eLpNorm_lim_le_liminf_eLpNorm (fun m ↦ (hf n).sub (hfSub m)) (f n - fLim)
        ((hf n).sub hfLimMeas.aestronglyMeasurable) ?_
      refine hfLim.mono fun z hz ↦ ?_
      simpa only [Pi.sub_apply] using tendsto_const_nhds.sub hz
    refine hliminf.trans ((liminf_le_of_frequently_le' ?_).trans (hN N le_rfl))
    apply Eventually.frequently
    filter_upwards [hφ.tendsto_atTop (eventually_ge_atTop N)] with m hm
    exact hCauchy' N n (φ m) hn hm
  have hfLimRange : ∀ᵐ z ∂(μ.prod μ), fLim z ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [hfLim] with z hz
    exact isClosed_Icc.mem_of_tendsto hz
      (Eventually.of_forall fun n ↦ (W (φ n)).mem_Icc z.1 z.2)
  have hfLimSwap : ∀ᵐ z ∂(μ.prod μ),
      Tendsto (fun n ↦ fSub n z.swap) atTop (𝓝 (fLim z.swap)) :=
    (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hfLim
  have hfLimSymm : ∀ᵐ z ∂(μ.prod μ), fLim z = fLim z.swap := by
    filter_upwards [hfLim, hfLimSwap] with z hz hzswap
    rcases z with ⟨x, y⟩
    have hzswap' : Tendsto (fun n ↦ fSub n (y, x)) atTop (𝓝 (fLim (y, x))) := by
      simpa only [Prod.swap_prod_mk] using hzswap
    have hz' : Tendsto (fun n ↦ fSub n (x, y)) atTop (𝓝 (fLim (y, x))) := by
      convert hzswap' using 1
      funext n
      simpa only [fSub, f, Prod.swap_prod_mk] using (W (φ n)).symm x y
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
  refine (cutDist_le_cutNorm_sub U W).trans ?_
  refine (cutNorm_le_integral_abs μ (U.toSymmKernel - W.toSymmKernel)).trans ?_
  have hmeas : AEStronglyMeasurable
      ((fun z : Ω × Ω ↦ U z.1 z.2) - fun z : Ω × Ω ↦ W z.1 z.2) (μ.prod μ) :=
    U.measurable.aestronglyMeasurable.sub W.measurable.aestronglyMeasurable
  exact le_of_eq (calc
    ∫ z, |(U.toSymmKernel - W.toSymmKernel) z.1 z.2| ∂(μ.prod μ) =
        ∫ z, ‖U z.1 z.2 - W z.1 z.2‖ ∂(μ.prod μ) := by
      simp only [SymmKernel.coe_sub, Pi.sub_apply, Graphon.coe_toSymmKernel, Real.norm_eq_abs]
    _ = lpNorm
        ((fun z : Ω × Ω ↦ U z.1 z.2) - fun z : Ω × Ω ↦ W z.1 z.2)
        1 (μ.prod μ) := (lpNorm_one_eq_integral_norm hmeas).symm
    _ = (eLpNorm
        ((fun z : Ω × Ω ↦ U z.1 z.2) - fun z : Ω × Ω ↦ W z.1 z.2)
        1 (μ.prod μ)).toReal := toReal_eLpNorm.symm)

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
