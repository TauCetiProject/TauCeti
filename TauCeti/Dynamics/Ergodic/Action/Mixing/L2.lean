/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.Action.Mixing
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import TauCeti.MeasureTheory.Function.L2Space
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# The `L²` correlation test for mixing along a filter

Let `M` act measurably on a probability space `(X, μ)` preserving `μ`, and let `l` be a
filter on `M`. The action is mixing along `l` exactly when the correlations of square-integrable
real functions converge: `∫ f · (g ∘ (m • ·)) dμ → (∫ f dμ) (∫ g dμ)` along `l` for all
`f, g ∈ L²(μ)`. Indicators of measurable sets give the converse; for the direct implication the
correlations are bilinear and, by the Cauchy–Schwarz inequality and invariance of `μ`, Lipschitz
in each argument uniformly in `m`, so convergence passes from indicators to all of `L²` by
`MeasureTheory.MemLp.induction`; the Lipschitz bound is
`MeasureTheory.MemLp.lipschitzWith_integral_mul`.

## Main results

* `TauCeti.MixingAlong.tendsto_integral_mul`: mixing along `l` gives convergence of `L²`
  correlations.
* `TauCeti.mixingAlong_iff_tendsto_integral_mul`: the `L²` correlation test.

Both results have additive versions (`TauCeti.AddMixingAlong.tendsto_integral_mul`,
`TauCeti.addMixingAlong_iff_tendsto_integral_mul`), for instance for flows.

## References

* M. Einsiedler and T. Ward, *Ergodic Theory with a view towards Number Theory*, Springer, 2011,
  §2.7 (mixing and weak mixing).
-/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace TauCeti

variable {M X : Type*} [MeasurableSpace X] {μ : Measure X} {l : Filter M}

section SMul

variable [SMul M X] [MeasurableConstSMul M X] [SMulInvariantMeasure M X μ]

omit [SMulInvariantMeasure M X μ] in
/-- The correlation of the constant-valued indicators `c • 1_s` and `d • 1_t ∘ (m • ·)` of
measurable sets is `c * d` times the measure of `s ∩ (m • ·)⁻¹' t`. -/
@[to_additive integral_indicator_mul_indicator_vadd /-- The correlation of the constant-valued
indicators `c • 1_s` and `d • 1_t ∘ (m +ᵥ ·)` of measurable sets is `c * d` times the measure of
`s ∩ (m +ᵥ ·)⁻¹' t`. -/]
theorem integral_indicator_mul_indicator_smul {s t : Set X} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (c d : ℝ) (m : M) :
    ∫ x, s.indicator (fun _ ↦ c) x * t.indicator (fun _ ↦ d) (m • x) ∂μ =
      c * d * μ.real (s ∩ (m • ·) ⁻¹' t) := by
  have hfun : (fun x ↦ s.indicator (fun _ ↦ c) x * t.indicator (fun _ ↦ d) (m • x)) =
      (s ∩ (m • ·) ⁻¹' t).indicator fun _ ↦ c * d := by
    funext x
    by_cases hx : x ∈ s <;> by_cases hx' : m • x ∈ t <;> simp [indicator, hx, hx']
  rw [hfun, integral_indicator_const _ (hs.inter (measurable_const_smul m ht)), smul_eq_mul,
    mul_comm]

variable [IsProbabilityMeasure μ]

/-- Convergence of the correlations against a fixed square-integrable `g` passes from indicators
of measurable sets to all of `L²(μ)`. -/
@[to_additive tendsto_integral_mul_vadd_of_indicator_left /-- Convergence of the correlations
against a fixed square-integrable `g` passes from indicators of measurable sets to all of `L²(μ)`.
-/]
theorem tendsto_integral_mul_of_indicator_left {g : X → ℝ} (hg : MemLp g 2 μ)
    (hind : ∀ (c : ℝ) ⦃s : Set X⦄, MeasurableSet s →
      Tendsto (fun m : M ↦ ∫ x, s.indicator (fun _ ↦ c) x * g (m • x) ∂μ) l
        (𝓝 ((∫ x, s.indicator (fun _ ↦ c) x ∂μ) * ∫ x, g x ∂μ)))
    {f : X → ℝ} (hf : MemLp f 2 μ) :
    Tendsto (fun m : M ↦ ∫ x, f x * g (m • x) ∂μ) l (𝓝 ((∫ x, f x ∂μ) * ∫ x, g x ∂μ)) := by
  have hgm (m : M) : MemLp (g ∘ (m • ·)) 2 μ :=
    hg.comp_measurePreserving (measurePreserving_smul m μ)
  refine MemLp.induction (p := 2) ENNReal.ofNat_ne_top
    (fun f ↦ Tendsto (fun m : M ↦ ∫ x, f x * g (m • x) ∂μ) l (𝓝 ((∫ x, f x ∂μ) * ∫ x, g x ∂μ)))
    (fun c s hs _ ↦ hind c hs) ?_ ?_ ?_ hf
  · intro f₁ f₂ _ hf₁ hf₂ h₁ h₂
    have heq (m : M) : ∫ x, (f₁ + f₂) x * g (m • x) ∂μ =
        ∫ x, f₁ x * g (m • x) ∂μ + ∫ x, f₂ x * g (m • x) ∂μ := by
      simp only [Pi.add_apply, add_mul]
      exact integral_add (hf₁.integrable_mul (hgm m)) (hf₂.integrable_mul (hgm m))
    rw [integral_add' (hf₁.integrable one_le_two) (hf₂.integrable one_le_two), add_mul]
    exact (h₁.add h₂).congr fun m ↦ (heq m).symm
  · -- Closedness: the correlations are uniformly Lipschitz in `f`.
    have hlip (m : M) : LipschitzWith (eLpNorm g 2 μ).toNNReal
        fun F : Lp ℝ 2 μ ↦ ∫ x, F x * g (m • x) ∂μ := by
      have := (hgm m).lipschitzWith_integral_mul
      rwa [eLpNorm_comp_measurePreserving hg.aestronglyMeasurable (measurePreserving_smul m μ)]
        at this
    have hcont : Continuous fun F : Lp ℝ 2 μ ↦ (∫ x, F x ∂μ) * ∫ x, g x ∂μ := by
      simpa using (memLp_const (1 : ℝ)).lipschitzWith_integral_mul.continuous.mul_const _
    exact ((LipschitzWith.uniformEquicontinuous _ _ hlip).equicontinuous).isClosed_setOfPred_tendsto
      hcont
  · intro f f' hff' _ hf
    have heq (m : M) : ∫ x, f x * g (m • x) ∂μ = ∫ x, f' x * g (m • x) ∂μ :=
      integral_congr_ae (hff'.mul EventuallyEq.rfl)
    simpa only [heq, integral_congr_ae hff'] using hf

/-- Convergence of the correlations of a fixed square-integrable `f` passes from indicators of
measurable sets to all of `L²(μ)`. -/
@[to_additive tendsto_integral_mul_vadd_of_indicator_right /-- Convergence of the correlations of a
fixed square-integrable `f` passes from indicators of measurable sets to all of `L²(μ)`. -/]
theorem tendsto_integral_mul_of_indicator_right {f : X → ℝ} (hf : MemLp f 2 μ)
    (hind : ∀ (d : ℝ) ⦃t : Set X⦄, MeasurableSet t →
      Tendsto (fun m : M ↦ ∫ x, f x * t.indicator (fun _ ↦ d) (m • x) ∂μ) l
        (𝓝 ((∫ x, f x ∂μ) * ∫ x, t.indicator (fun _ ↦ d) x ∂μ)))
    {g : X → ℝ} (hg : MemLp g 2 μ) :
    Tendsto (fun m : M ↦ ∫ x, f x * g (m • x) ∂μ) l (𝓝 ((∫ x, f x ∂μ) * ∫ x, g x ∂μ)) := by
  refine MemLp.induction (p := 2) ENNReal.ofNat_ne_top
    (fun g ↦ Tendsto (fun m : M ↦ ∫ x, f x * g (m • x) ∂μ) l (𝓝 ((∫ x, f x ∂μ) * ∫ x, g x ∂μ)))
    (fun d t ht _ ↦ hind d ht) ?_ ?_ ?_ hg
  · intro g₁ g₂ _ hg₁ hg₂ h₁ h₂
    have heq (m : M) : ∫ x, f x * (g₁ + g₂) (m • x) ∂μ =
        ∫ x, f x * g₁ (m • x) ∂μ + ∫ x, f x * g₂ (m • x) ∂μ := by
      have hmp := measurePreserving_smul m μ
      simp only [Pi.add_apply, mul_add]
      exact integral_add (hf.integrable_mul (hg₁.comp_measurePreserving hmp))
        (hf.integrable_mul (hg₂.comp_measurePreserving hmp))
    rw [integral_add' (hg₁.integrable one_le_two) (hg₂.integrable one_le_two), mul_add]
    exact (h₁.add h₂).congr fun m ↦ (heq m).symm
  · -- Closedness: the correlations are Lipschitz in `g`, composing with the isometric pullback.
    have hlip (m : M) : LipschitzWith ((eLpNorm f 2 μ).toNNReal * 1)
        fun G : Lp ℝ 2 μ ↦ ∫ x, f x * G (m • x) ∂μ := by
      have hmp := measurePreserving_smul m μ
      have := hf.lipschitzWith_integral_mul.comp
        (Lp.compMeasurePreservingₗᵢ ℝ (m • · : X → X) hmp).lipschitzWith
      convert this using 2 with G
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_compMeasurePreserving G hmp] with x hx
      rw [mul_comm]
      congr 1
      exact hx.symm
    have hcont : Continuous fun G : Lp ℝ 2 μ ↦ (∫ x, f x ∂μ) * ∫ x, G x ∂μ := by
      simpa using (memLp_const (1 : ℝ)).lipschitzWith_integral_mul.continuous.const_mul _
    exact ((LipschitzWith.uniformEquicontinuous _ _ hlip).equicontinuous).isClosed_setOfPred_tendsto
      hcont
  · intro g g' hgg' _ hg
    have heq (m : M) : ∫ x, f x * g (m • x) ∂μ = ∫ x, f x * g' (m • x) ∂μ :=
      integral_congr_ae (EventuallyEq.rfl.mul
        ((measurePreserving_smul m μ).quasiMeasurePreserving.ae_eq_comp hgg'))
    simpa only [heq, integral_congr_ae hgg'] using hg

/-- **Mixing and `L²` correlations.** If a measure-preserving action on a probability space is
mixing along `l`, then for all square-integrable real `f` and `g` the correlations
`∫ f · (g ∘ (m • ·)) dμ` tend to `(∫ f dμ) (∫ g dμ)` along `l`. -/
@[to_additive AddMixingAlong.tendsto_integral_mul /-- **Mixing and `L²` correlations.** If a
measure-preserving additive action on a probability space is mixing along `l`, then for all
square-integrable real `f` and `g` the correlations `∫ f · (g ∘ (m +ᵥ ·)) dμ` tend to
`(∫ f dμ) (∫ g dμ)` along `l`. -/]
theorem MixingAlong.tendsto_integral_mul (h : MixingAlong M X μ l) {f g : X → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Tendsto (fun m : M ↦ ∫ x, f x * g (m • x) ∂μ) l (𝓝 ((∫ x, f x ∂μ) * ∫ x, g x ∂μ)) := by
  refine tendsto_integral_mul_of_indicator_right hf (fun d t ht ↦ ?_) hg
  refine tendsto_integral_mul_of_indicator_left
    (memLp_indicator_const 2 ht.nullMeasurableSet d (Or.inr (measure_ne_top μ t)))
    (fun c s hs ↦ ?_) hf
  simp only [integral_indicator_mul_indicator_smul hs ht, integral_indicator_const _ hs,
    integral_indicator_const _ ht, smul_eq_mul]
  convert (h.tendsto hs ht).const_mul (c * d) using 2
  ring

/-- **The `L²` correlation test for mixing.** A measure-preserving action on a probability space is
mixing along `l` if and only if for all square-integrable real `f` and `g` the correlations
`∫ f · (g ∘ (m • ·)) dμ` tend to `(∫ f dμ) (∫ g dμ)` along `l`. -/
@[to_additive addMixingAlong_iff_tendsto_integral_mul /-- **The `L²` correlation test for mixing.**
A measure-preserving additive action on a probability space is mixing along `l` if and only if for
all square-integrable real `f` and `g` the correlations `∫ f · (g ∘ (m +ᵥ ·)) dμ` tend to
`(∫ f dμ) (∫ g dμ)` along `l`. -/]
theorem mixingAlong_iff_tendsto_integral_mul :
    MixingAlong M X μ l ↔ ∀ ⦃f g : X → ℝ⦄, MemLp f 2 μ → MemLp g 2 μ →
      Tendsto (fun m : M ↦ ∫ x, f x * g (m • x) ∂μ) l (𝓝 ((∫ x, f x ∂μ) * ∫ x, g x ∂μ)) := by
  refine ⟨fun h _ _ hf hg ↦ h.tendsto_integral_mul hf hg,
    fun h ↦ mixingAlong_iff.2 fun A B hA hB ↦ ?_⟩
  have := h (memLp_indicator_const 2 hA.nullMeasurableSet (1 : ℝ) (Or.inr (measure_ne_top μ A)))
    (memLp_indicator_const 2 hB.nullMeasurableSet (1 : ℝ) (Or.inr (measure_ne_top μ B)))
  simpa [integral_indicator_mul_indicator_smul hA hB, integral_indicator_const _ hA,
    integral_indicator_const _ hB] using this

end SMul

end TauCeti
