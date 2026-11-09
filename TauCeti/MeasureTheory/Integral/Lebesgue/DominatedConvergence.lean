/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Consequences of dominated convergence for Lebesgue integrals

A function `f : α → ℝ≥0∞` of finite Lebesgue integral exceeds a large constant `M` only by an
amount of small integral: `∫⁻ x, f x - M ∂μ → 0` as `M → ∞`. This is dominated convergence with
the bound `f`, since `f x - M` vanishes for `M ≥ f x` and `f` is almost everywhere finite.

The file also records a squeeze principle: if `f n ≤ g n + h n` and the integrals of `g n` and
`h n` tend to `0`, so does the integral of `f n`.

Bounded real coefficients converging almost everywhere preserve `L¹` convergence of
vector-valued sequences. This lets products pass to the limit when the coefficient convergence
is pointwise and the vector-valued factor converges only in `L¹`.

## Main statements

* `TauCeti.tendsto_lintegral_tsub_atTop`: the integral of the excess of `f` over the constant `M`
  tends to `0` as `M → ∞`.
* `TauCeti.tendsto_lintegral_zero_of_le_add`: the integral of a function bounded by the sum of
  two functions with integrals tending to `0` tends to `0`.
* `TauCeti.tendsto_lintegral_enorm_smul_sub`: bounded, almost everywhere convergent real
  coefficients preserve `L¹` convergence in any real normed space.
-/

public section

namespace TauCeti

open Filter MeasureTheory Topology
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Uniformly small tails.** If `f : α → ℝ≥0∞` is almost everywhere measurable with finite
Lebesgue integral, then the integral of its excess `f x - M` over a finite level `M` tends to `0`
as `M → ∞`. -/
theorem tendsto_lintegral_tsub_atTop {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hfi : ∫⁻ x, f x ∂μ ≠ ∞) :
    Tendsto (fun M : ℝ≥0 ↦ ∫⁻ x, f x - M ∂μ) atTop (𝓝 0) := by
  have h := tendsto_lintegral_filter_of_dominated_convergence' (l := atTop)
    (F := fun (M : ℝ≥0) x ↦ f x - M) (f := fun _ ↦ 0) f
    (Eventually.of_forall fun M ↦ hf.sub aemeasurable_const)
    (Eventually.of_forall fun M ↦ ae_of_all _ fun x ↦ tsub_le_self) hfi ?_
  · simpa using h
  -- At a point where `f` is finite, the excess vanishes once `M ≥ f x`.
  filter_upwards [ae_lt_top' hf hfi] with x hx
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (f x).toNNReal] with M hM
  rw [eq_comm, tsub_eq_zero_iff_le]
  exact (ENNReal.coe_toNNReal hx.ne).symm.trans_le (ENNReal.coe_le_coe.2 hM)

/-- If `f n ≤ g n + h n` pointwise, `g n` is almost everywhere measurable, and the Lebesgue
integrals of `g n` and `h n` tend to `0`, then so do those of `f n`. -/
theorem tendsto_lintegral_zero_of_le_add {ι : Type*} {l : Filter ι} {f g h : ι → α → ℝ≥0∞}
    (hfgh : ∀ i x, f i x ≤ g i x + h i x) (hg : ∀ i, AEMeasurable (g i) μ)
    (hgt : Tendsto (fun i ↦ ∫⁻ x, g i x ∂μ) l (𝓝 0))
    (hht : Tendsto (fun i ↦ ∫⁻ x, h i x ∂μ) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫⁻ x, f i x ∂μ) l (𝓝 0) := by
  have hsum := hgt.add hht
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ ↦ zero_le) fun i ↦ ?_
  rw [← lintegral_add_left' (hg i)]
  exact lintegral_mono (hfgh i)

/-- If bounded coefficients `c i` converge almost everywhere to `c₀` and `g i → g₀` in `L¹`,
then `c i • g i → c₀ • g₀` in `L¹`. The functions take values in any real normed space. -/
theorem tendsto_lintegral_enorm_smul_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ν : Measure α} {M : ℝ≥0} {c : ℕ → α → ℝ} {c₀ : α → ℝ} {g : ℕ → α → E} {g₀ : α → E}
    (hc : ∀ i, AEStronglyMeasurable (c i) ν) (hg : ∀ i, AEStronglyMeasurable (g i) ν)
    (hg₀ : AEStronglyMeasurable g₀ ν) (hcM : ∀ i, ∀ᵐ x ∂ν, ‖c i x‖₊ ≤ M)
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun i => c i x) atTop (𝓝 (c₀ x)))
    (hg₀int : ∫⁻ x, ‖g₀ x‖ₑ ∂ν ≠ ∞)
    (hgg : Tendsto (fun i => ∫⁻ x, ‖g i x - g₀ x‖ₑ ∂ν) atTop (𝓝 0)) :
    Tendsto (fun i => ∫⁻ x, ‖c i x • g i x - c₀ x • g₀ x‖ₑ ∂ν)
      atTop (𝓝 0) := by
  have hc₀ : AEStronglyMeasurable c₀ ν := aestronglyMeasurable_of_tendsto_ae atTop hc hlim
  -- the bound passes to the almost everywhere limit
  have hc₀M : ∀ᵐ x ∂ν, ‖c₀ x‖₊ ≤ M := (ae_all_iff.2 hcM).and hlim |>.mono fun x ⟨hx, hx'⟩ =>
    le_of_tendsto' ((continuous_nnnorm.tendsto _).comp hx') hx
  have hC : Tendsto (fun i => ∫⁻ x, ‖c i x - c₀ x‖ₑ * ‖g₀ x‖ₑ ∂ν) atTop (𝓝 0) := by
    simpa using tendsto_lintegral_of_dominated_convergence' (fun x => (M + M) * ‖g₀ x‖ₑ)
      (F := fun i x => ‖c i x - c₀ x‖ₑ * ‖g₀ x‖ₑ) (f := 0)
      (fun i => ((hc i).sub hc₀).enorm.mul hg₀.enorm)
      (fun i => (hcM i).and hc₀M |>.mono fun x ⟨hx, hx'⟩ => by
        dsimp only
        gcongr
        exact enorm_sub_le.trans (add_le_add (enorm_le_coe.2 hx) (enorm_le_coe.2 hx')))
      (by rw [lintegral_const_mul' _ _ (by simp)]; exact ENNReal.mul_ne_top (by simp) hg₀int)
      (hlim.mono fun x hx => by
        simpa using ENNReal.Tendsto.mul_const (hx.sub_const (c₀ x)).enorm (Or.inr enorm_ne_top))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using (ENNReal.Tendsto.const_mul (a := M) hgg (Or.inr ENNReal.coe_ne_top)).add hC)
    (fun _ => zero_le) fun i => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top,
    ← lintegral_add_left' (f := fun x => M * ‖g i x - g₀ x‖ₑ) (((hg i).sub hg₀).enorm.const_mul _)]
  refine lintegral_mono_ae ((hcM i).mono fun x hx => ?_)
  calc
    ‖c i x • g i x - c₀ x • g₀ x‖ₑ
      = ‖c i x • (g i x - g₀ x) + (c i x - c₀ x) • g₀ x‖ₑ := by
          congr 1
          rw [smul_sub, sub_smul]
          abel
    _ ≤ M * ‖g i x - g₀ x‖ₑ + ‖c i x - c₀ x‖ₑ * ‖g₀ x‖ₑ := ?_
  refine (enorm_add_le _ _).trans (add_le_add ?_ (enorm_smul _ _).le)
  rw [enorm_smul]
  gcongr
  exact enorm_le_coe.2 hx

end TauCeti
