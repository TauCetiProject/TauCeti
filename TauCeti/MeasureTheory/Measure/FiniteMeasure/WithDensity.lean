/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import TauCeti.MeasureTheory.Integral.Scheffe
import TauCeti.Probability.Density

/-!
# Weak convergence of measures with converging densities

Let `μ` be a measure on a topological space and let `f i`, `g` be nonnegative integrable real
functions, the densities of the finite measures `μ.withDensity (ofReal ∘ f i)` and
`μ.withDensity (ofReal ∘ g)`. If `f i → g` in `L¹(μ)`, these measures converge weakly
(`MeasureTheory.FiniteMeasure.tendsto_of_tendsto_integral_norm_sub`): the integral of a bounded
continuous function `φ` changes by at most `‖φ‖ ∫ ‖f i - g‖`. In fact they converge in total
variation, but weak convergence is what is consumed by functionals continuous in the weak
topology.

Combined with Scheffé's lemma (`MeasureTheory.tendsto_integral_norm_sub_of_tendsto_integral`),
nonnegative densities converging almost everywhere give weakly converging measures as soon as the
total masses converge (`MeasureTheory.FiniteMeasure.tendsto_of_ae_tendsto_of_tendsto_integral`).
The convergence of the masses cannot be dropped: the densities `𝟙_[i, i + 1]` on `ℝ` tend to zero
pointwise while the measures keep mass one.
-/

public section

open BoundedContinuousFunction Filter Topology

namespace MeasureTheory

namespace FiniteMeasure

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
  {μ : Measure α} {ι : Type*} {l : Filter ι} {μs : ι → FiniteMeasure α} {ν : FiniteMeasure α}
  {f : ι → α → ℝ} {g : α → ℝ}

/-- **Weak convergence from `L¹` convergence of densities.** If `μs i` and `ν` are the measures
with nonnegative integrable densities `f i` and `g` with respect to `μ`, and `f i → g` in
`L¹(μ)`, then `μs i → ν` weakly. -/
theorem tendsto_of_tendsto_integral_norm_sub (hf : ∀ i, Integrable (f i) μ) (hg : Integrable g μ)
    (hf₀ : ∀ i, 0 ≤ᵐ[μ] f i) (hg₀ : 0 ≤ᵐ[μ] g)
    (hμs : ∀ i, (μs i : Measure α) = μ.withDensity fun a ↦ ENNReal.ofReal (f i a))
    (hν : (ν : Measure α) = μ.withDensity fun a ↦ ENNReal.ofReal (g a))
    (h : Tendsto (fun i ↦ ∫ a, ‖f i a - g a‖ ∂μ) l (𝓝 0)) :
    Tendsto μs l (𝓝 ν) := by
  rw [tendsto_iff_forall_integral_tendsto]
  intro φ
  have hφ : AEStronglyMeasurable φ μ := φ.continuous.measurable.aestronglyMeasurable
  have hφb : ∀ᵐ a ∂μ, ‖φ a‖ ≤ ‖φ‖ := Eventually.of_forall φ.norm_coe_le_norm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  -- The difference of the integrals is `∫ (f i - g) φ`, which is at most `‖φ‖ ∫ ‖f i - g‖` in
  -- absolute value.
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun i ↦ ?_) (by simpa using h.mul_const ‖φ‖)
  rw [hμs, hν, TauCeti.Probability.integral_withDensity_ofReal (hf i).aemeasurable (hf₀ i),
    TauCeti.Probability.integral_withDensity_ofReal hg.aemeasurable hg₀]
  simp only [smul_eq_mul]
  rw [← integral_sub ((hf i).mul_bdd hφ hφb) (hg.mul_bdd hφ hφb), ← integral_mul_const]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ ↦ norm_nonneg _) (((hf i).sub hg).norm.mul_const _)
    (Eventually.of_forall fun a ↦ ?_))
  dsimp only
  rw [← sub_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (φ.norm_coe_le_norm a) (norm_nonneg _)

/-- **Weak convergence from pointwise convergence of densities and of masses.** If `μs i` and `ν`
are the measures with densities the nonnegative integrable functions `f i` and the integrable
function `g`, with `f i → g` almost everywhere and `∫ f i → ∫ g`, then `μs i → ν` weakly. -/
theorem tendsto_of_ae_tendsto_of_tendsto_integral [l.IsCountablyGenerated]
    (hf : ∀ i, Integrable (f i) μ) (hg : Integrable g μ) (hf₀ : ∀ i, 0 ≤ᵐ[μ] f i)
    (hμs : ∀ i, (μs i : Measure α) = μ.withDensity fun a ↦ ENNReal.ofReal (f i a))
    (hν : (ν : Measure α) = μ.withDensity fun a ↦ ENNReal.ofReal (g a))
    (hlim : ∀ᵐ a ∂μ, Tendsto (fun i ↦ f i a) l (𝓝 (g a)))
    (hint : Tendsto (fun i ↦ ∫ a, f i a ∂μ) l (𝓝 (∫ a, g a ∂μ))) :
    Tendsto μs l (𝓝 ν) := by
  rcases l.eq_or_neBot with rfl | _
  · exact tendsto_bot
  -- The limit `g` is nonnegative almost everywhere: it is a limit along a sequence `i n` of
  -- functions which are all nonnegative off one null set.
  obtain ⟨i, hi⟩ := l.exists_seq_tendsto
  have hg₀ : 0 ≤ᵐ[μ] g := by
    filter_upwards [hlim, ae_all_iff.2 fun n ↦ hf₀ (i n)] with a ha hn
    exact ge_of_tendsto' (ha.comp hi) hn
  exact tendsto_of_tendsto_integral_norm_sub hf hg hf₀ hg₀ hμs hν
    (tendsto_integral_norm_sub_of_tendsto_integral hf hg hf₀ hlim hint)

end FiniteMeasure

end MeasureTheory
