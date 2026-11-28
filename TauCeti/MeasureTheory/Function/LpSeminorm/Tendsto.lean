/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import TauCeti.MeasureTheory.Integral.Prod
import TauCeti.Topology.UniformSpace.HeineCantor

/-!
# Convergence to zero of `Lᵖ` seminorms

If a family `f i` is eventually bounded almost everywhere by `δ ‖b‖ₑ` for every `δ > 0`, where `b`
has finite `Lᵖ` seminorm, then `eLpNorm (f i) p μ → 0`
(`TauCeti.tendsto_eLpNorm_zero_of_eventually_le_mul`). Taking `b = 1` on a finite measure space,
a family that eventually becomes uniformly small almost everywhere tends to `0` in every `Lᵖ`
(`TauCeti.tendsto_eLpNorm_zero_of_eventually_ae_le`). This is how uniform convergence on a set of
finite measure, or uniform convergence of a coefficient multiplying a fixed `Lᵖ` function, is
turned into convergence in `Lᵖ`. No lower bound on `p` is needed.

In a normed ring, `L²` convergence `eLpNorm (f i - g) 2 μ → 0` to a limit with finite `L²`
seminorm implies `L¹` convergence of the squares (`TauCeti.tendsto_eLpNorm_one_sq_sub_sq`). On a
product of s-finite measures, `L²` convergence of `MemLp` functions implies `L¹` convergence of
their first-factor squared section integrals (`TauCeti.tendsto_eLpNorm_one_integral_sq_sub`).

The case `p = ∞` needs no finiteness of the measure. A family of fields `M ν`, depending on a
parameter `ν` in a topological space `X`, which is jointly continuous at every point of `{ν₀} × K`
for a compact set `K` and, for `ν` near `ν₀`, agrees with `M ν₀` off `K`, converges uniformly on
`K` as `ν → ν₀`
(`IsCompact.tendstoUniformlyOn_of_continuousAt`), so `M ν → M ν₀` in `L^∞`
(`TauCeti.tendsto_eLpNorm_top_sub_of_continuousAt_of_eq`). This is how a family of coefficient
fields that is only modified on a compact part of a noncompact domain is seen to depend continuously
on its parameter in `L^∞`.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace TauCeti

variable {α ι ε ε' : Type*} [MeasurableSpace α] {μ : Measure α} [TopologicalSpace ε]
  [ContinuousENorm ε] [TopologicalSpace ε'] [ContinuousENorm ε'] {p : ℝ≥0∞} {l : Filter ι}
  {f : ι → α → ε}

/-- If `f i` is eventually bounded by `δ ‖b‖ₑ` for every `δ > 0`, and `b` has finite `Lᵖ` norm, then
the `Lᵖ` norm of `f i` tends to `0`. -/
theorem tendsto_eLpNorm_zero_of_eventually_le_mul {b : α → ε'} (hb : eLpNorm b p μ ≠ ∞)
    (hf : ∀ᶠ i in l, AEStronglyMeasurable (f i) μ)
    (h : ∀ δ : ℝ≥0, 0 < δ → ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖f i x‖ₑ ≤ δ * ‖b x‖ₑ) :
    Tendsto (fun i => eLpNorm (f i) p μ) l (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt hb hε.ne'
  filter_upwards [hf, h δ hδ] with i hfi hi
  exact (eLpNorm_le_mul_eLpNorm_of_ae_le_mul' hfi hi p).trans hδε.le

/-- On a finite measure space, if for every `δ > 0` eventually `‖f i‖ₑ ≤ δ` almost everywhere, then
the `Lᵖ` norm of `f i` tends to `0`. -/
theorem tendsto_eLpNorm_zero_of_eventually_ae_le [IsFiniteMeasure μ]
    (hf : ∀ᶠ i in l, AEStronglyMeasurable (f i) μ)
    (h : ∀ δ : ℝ≥0, 0 < δ → ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖f i x‖ₑ ≤ δ) :
    Tendsto (fun i => eLpNorm (f i) p μ) l (𝓝 0) := by
  refine tendsto_eLpNorm_zero_of_eventually_le_mul (b := fun _ => (1 : ℝ))
    (memLp_const 1).eLpNorm_ne_top hf fun δ hδ => ?_
  filter_upwards [h δ hδ] with i hi
  filter_upwards [hi] with x hx
  simpa using hx

/-- In a normed ring, `L²` convergence `eLpNorm (f i - g) 2 μ → 0` to a function with finite `L²`
seminorm implies `L¹` convergence of the squares `f i ^ 2 → g ^ 2`. No measurability assumption on
`f i` or `g` is needed. -/
theorem tendsto_eLpNorm_one_sq_sub_sq {R : Type*} [NormedRing R] {f : ι → α → R} {g : α → R}
    (hg : eLpNorm g 2 μ ≠ ∞)
    (hlim : Tendsto (fun i ↦ eLpNorm (f i - g) 2 μ) l (𝓝 0)) :
    Tendsto (fun i ↦ eLpNorm (fun x ↦ f i x ^ 2 - g x ^ 2) 1 μ) l (𝓝 0) := by
  let : ENNReal.HolderTriple 2 2 1 := ⟨by simp [ENNReal.inv_two_add_inv_two]⟩
  have hbound (i : ι) : eLpNorm (fun x ↦ f i x ^ 2 - g x ^ 2) 1 μ ≤
      eLpNorm (f i - g) 2 μ * eLpNorm (f i - g) 2 μ +
        (eLpNorm (f i - g) 2 μ * eLpNorm g 2 μ + eLpNorm g 2 μ * eLpNorm (f i - g) 2 μ) := by
    have hsplit : (fun x ↦ f i x ^ 2 - g x ^ 2) =
        ((f i - g) • (f i - g)) + (((f i - g) • g) + (g • (f i - g))) := by
      ext x
      simp only [smul_eq_mul, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, sq]
      noncomm_ring
    rw [hsplit]
    refine (eLpNorm_add_le le_rfl).trans (add_le_add
      (eLpNorm_smul_le_mul_eLpNorm_of_pos (p := 2) (q := 2) zero_lt_one)
      ((eLpNorm_add_le le_rfl).trans (add_le_add
        (eLpNorm_smul_le_mul_eLpNorm_of_pos (p := 2) (q := 2) zero_lt_one)
        (eLpNorm_smul_le_mul_eLpNorm_of_pos (p := 2) (q := 2) zero_lt_one))))
  have hrhs : Tendsto (fun i ↦ eLpNorm (f i - g) 2 μ * eLpNorm (f i - g) 2 μ +
      (eLpNorm (f i - g) 2 μ * eLpNorm g 2 μ + eLpNorm g 2 μ * eLpNorm (f i - g) 2 μ)) l (𝓝 0) := by
    have h1 : Tendsto (fun i ↦ eLpNorm (f i - g) 2 μ * eLpNorm (f i - g) 2 μ) l (𝓝 0) := by
      simpa only [zero_mul] using
        ENNReal.Tendsto.mul hlim (Or.inr ENNReal.zero_ne_top) hlim (Or.inr ENNReal.zero_ne_top)
    have h2 : Tendsto (fun i ↦ eLpNorm (f i - g) 2 μ * eLpNorm g 2 μ) l (𝓝 0) := by
      simpa only [zero_mul] using ENNReal.Tendsto.mul_const hlim (Or.inr hg)
    have h3 : Tendsto (fun i ↦ eLpNorm g 2 μ * eLpNorm (f i - g) 2 μ) l (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul hlim (Or.inr hg)
    simpa only [zero_add] using h1.add (h2.add h3)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrhs (fun _ ↦ bot_le) hbound

/-- On a product of s-finite measures, `L²` convergence `eLpNorm (f i - g) 2 (μ.prod ν) → 0` for
`MemLp` functions implies `L¹(ν)` convergence of the squared section integrals
`y ↦ ∫ x, f i (x, y) ^ 2 ∂μ` to `y ↦ ∫ x, g (x, y) ^ 2 ∂μ`. -/
theorem tendsto_eLpNorm_one_integral_sq_sub {β R : Type*} [MeasurableSpace β]
    {ν : Measure β} [SFinite μ] [SFinite ν] [NormedRing R] [NormedSpace ℝ R]
    {f : ι → α × β → R} {g : α × β → R}
    (hg : MemLp g 2 (μ.prod ν)) (hf : ∀ᶠ i in l, MemLp (f i) 2 (μ.prod ν))
    (hlim : Tendsto (fun i ↦ eLpNorm (f i - g) 2 (μ.prod ν)) l (𝓝 0)) :
    Tendsto (fun i ↦ eLpNorm (fun y ↦ (∫ x, f i (x, y) ^ 2 ∂μ) - ∫ x, g (x, y) ^ 2 ∂μ) 1 ν)
      l (𝓝 0) := by
  let : ENNReal.HolderTriple 2 2 1 := ⟨by simp [ENNReal.inv_two_add_inv_two]⟩
  have hg_sq : Integrable (fun p ↦ g p ^ 2) (μ.prod ν) := by
    simpa only [sq, Pi.mul_def] using hg.integrable_mul hg
  have hg_ae : ∀ᵐ y ∂ν, Integrable (fun x ↦ g (x, y) ^ 2) μ := hg_sq.prod_left_ae
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_eLpNorm_one_sq_sub_sq hg.eLpNorm_ne_top hlim)
    (.of_forall fun _ ↦ bot_le) (hf.mono fun i hfi ↦ ?_)
  have hfi_sq : Integrable (fun p ↦ f i p ^ 2) (μ.prod ν) := by
    simpa only [sq, Pi.mul_def] using hfi.integrable_mul hfi
  have hcongr : (fun y ↦ (∫ x, f i (x, y) ^ 2 ∂μ) - ∫ x, g (x, y) ^ 2 ∂μ) =ᵐ[ν]
      fun y ↦ ∫ x, (f i (x, y) ^ 2 - g (x, y) ^ 2) ∂μ := by
    filter_upwards [hfi_sq.prod_left_ae, hg_ae] with y hfy hgy
    exact (integral_sub hfy hgy).symm
  rw [eLpNorm_congr_ae hcongr]
  exact eLpNorm_one_integral_prod_left_le (fun p ↦ f i p ^ 2 - g p ^ 2)

/-- **`L^∞` continuity of a family modified on a compact set.** Let `M ν` be fields on a
measurable set `S`, depending on a parameter `ν` in a topological space `X`, which are jointly
continuous in `(ν, z)` at every point of `{ν₀} × K` for a compact set `K`. Suppose that for `ν`
near `ν₀` the field `M ν` is almost everywhere strongly measurable on `S` and agrees with `M ν₀` at
the points of `S` outside `K`. Then `M ν → M ν₀` in `L^∞(S)` as `ν → ν₀`. -/
theorem tendsto_eLpNorm_top_sub_of_continuousAt_of_eq {X α E : Type*} [TopologicalSpace X]
    [TopologicalSpace α] [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    {M : X → α → E} {S K : Set α} (hS : MeasurableSet S) (hK : IsCompact K)
    {ν₀ : X} (hmeas : ∀ᶠ ν in 𝓝 ν₀, AEStronglyMeasurable (M ν) (μ.restrict S))
    (hM : ∀ z ∈ K, ContinuousAt (Function.uncurry M) (ν₀, z))
    (heq : ∀ᶠ ν in 𝓝 ν₀, ∀ z ∈ S, z ∉ K → M ν z = M ν₀ z) :
    Tendsto (fun ν => eLpNorm (M ν - M ν₀) ∞ (μ.restrict S)) (𝓝 ν₀) (𝓝 0) := by
  refine tendsto_eLpNorm_zero_of_eventually_le_mul (b := fun _ => (1 : ℝ))
    (memLp_top_const 1).eLpNorm_ne_top (hmeas.mono fun ν hν => hν.sub hmeas.self_of_nhds)
    fun δ hδ => ?_
  -- On the compact set `K` the family converges uniformly.
  filter_upwards [hK.tendstoUniformlyOn_of_continuousAt hM _
    (Metric.dist_mem_uniformity (NNReal.coe_pos.2 hδ)), heq] with ν hν hνK
  filter_upwards [ae_restrict_mem hS] with z hz
  rw [eNorm_one, mul_one, Pi.sub_apply, ← eDist_eq_eNorm_sub]
  by_cases hzK : z ∈ K
  · exact (edist_lt_coe.2 (by simpa [nndist_comm] using hν z hzK)).le
  · rw [hνK z hz hzK, edist_self]
    exact zero_le

end TauCeti
