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

This file records a squeeze principle: if `f n ≤ g n + h n` and the integrals of `g n` and
`h n` tend to `0`, so does the integral of `f n`; and the reverse Fatou lemma for integrals over
sets: the integrals of a function of finite integral over measurable sets `s n` have limit
superior at most its integral over `limsup s n`, the set of points lying in infinitely many
`s n`.

Bounded scalar coefficients converging almost everywhere preserve `L¹` convergence of
vector-valued sequences. This lets products pass to the limit when the coefficient convergence
is pointwise and the vector-valued factor converges only in `L¹`.

## Main statements

* `TauCeti.tendsto_lintegral_zero_of_le_add`: the integral of a function bounded by the sum of
  two functions with integrals tending to `0` tends to `0`.
* `TauCeti.tendsto_setLIntegral_enorm_add_sub`: `L¹` convergence on a set is preserved by sums.
* `TauCeti.tendsto_lintegral_enorm_smul_sub`: bounded, almost everywhere convergent scalar
  coefficients preserve `L¹` convergence in any seminormed module.
* `TauCeti.limsup_setLIntegral_le`: `limsup ∫⁻_{s n} f ≤ ∫⁻_{limsup s n} f` when the `s n` lie
  in a set over which `f` has finite integral.
* `TauCeti.tendsto_lintegral_filter_limsup_of_dominated_convergence`: dominated convergence of
  `∫⁻ x, F j x ∂μ` to `∫⁻ x, limsup (fun j ↦ F j x) l ∂μ` under almost-everywhere convergence to
  some limit, without requiring a globally named limit function.
-/

public section

namespace TauCeti

open Filter MeasureTheory Topology
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- If eventually `f i ≤ g i + h i` almost everywhere and `g i` is almost everywhere measurable,
and the Lebesgue integrals of `g i` and `h i` tend to `0`, then so do those of `f i`. -/
theorem tendsto_lintegral_zero_of_le_add {ι : Type*} {l : Filter ι} {f g h : ι → α → ℝ≥0∞}
    (hfgh : ∀ᶠ i in l, f i ≤ᵐ[μ] g i + h i) (hg : ∀ᶠ i in l, AEMeasurable (g i) μ)
    (hgt : Tendsto (fun i ↦ ∫⁻ x, g i x ∂μ) l (𝓝 0))
    (hht : Tendsto (fun i ↦ ∫⁻ x, h i x ∂μ) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫⁻ x, f i x ∂μ) l (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using hgt.add hht) (.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [hfgh, hg] with i hi hgi
  rw [← lintegral_add_left' hgi]
  exact lintegral_mono_ae hi

/-- If two families converge in `L¹` on `W`, so does their sum. Only the errors of the first
family need to be almost everywhere strongly measurable. -/
theorem tendsto_setLIntegral_enorm_add_sub {H ι : Type*} [NormedAddCommGroup H] {W : Set α}
    {l : Filter ι} {a b : ι → α → H} {a₀ b₀ : α → H}
    (ha : ∀ n, AEStronglyMeasurable (fun x => a n x - a₀ x) (μ.restrict W))
    (h₁ : Tendsto (fun n => ∫⁻ x in W, ‖a n x - a₀ x‖ₑ ∂μ) l (𝓝 0))
    (h₂ : Tendsto (fun n => ∫⁻ x in W, ‖b n x - b₀ x‖ₑ ∂μ) l (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x in W, ‖a n x + b n x - (a₀ x + b₀ x)‖ₑ ∂μ) l (𝓝 0) :=
  tendsto_lintegral_zero_of_le_add (μ := μ.restrict W)
    (.of_forall fun n ↦ .of_forall fun x ↦ by
      simpa only [Pi.add_apply, add_sub_add_comm] using eNorm_add_le _ _)
    (.of_forall fun n ↦ (ha n).eNorm) h₁ h₂

/-- If bounded coefficients `c i` converge almost everywhere to `c₀` and `g i → g₀` in `L¹`,
then `c i • g i → c₀ • g₀` in `L¹`. The coefficients lie in any seminormed ring `𝕜` and the
functions take values in any seminormed `𝕜`-module with multiplicative norm of scalar
multiplication. -/
theorem tendsto_lintegral_enorm_smul_sub {𝕜 E : Type*} [SeminormedRing 𝕜]
    [SeminormedAddCommGroup E] [Module 𝕜 E] [NormSMulClass 𝕜 E]
    {ν : Measure α} {M : ℝ≥0} {c : ℕ → α → 𝕜} {c₀ : α → 𝕜} {g : ℕ → α → E} {g₀ : α → E}
    (hc : ∀ i, AEStronglyMeasurable (c i) ν)
    (hg₀ : AEStronglyMeasurable g₀ ν) (hcM : ∀ i, ∀ᵐ x ∂ν, ‖c i x‖₊ ≤ M)
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun i => c i x) atTop (𝓝 (c₀ x)))
    (hg₀int : ∫⁻ x, ‖g₀ x‖ₑ ∂ν ≠ ∞)
    (hgg : Tendsto (fun i => ∫⁻ x, ‖g i x - g₀ x‖ₑ ∂ν) atTop (𝓝 0)) :
    Tendsto (fun i => ∫⁻ x, ‖c i x • g i x - c₀ x • g₀ x‖ₑ ∂ν)
      atTop (𝓝 0) := by
  have hc₀ : AEStronglyMeasurable c₀ ν := aestronglyMeasurable_of_tendsto_ae atTop hc hlim
  -- the bound passes to the almost everywhere limit
  have hc₀M : ∀ᵐ x ∂ν, ‖c₀ x‖₊ ≤ M := (ae_all_iff.2 hcM).and hlim |>.mono fun x ⟨hx, hx'⟩ =>
    le_of_tendsto' ((continuous_nnNorm.tendsto _).comp hx') hx
  have hmeas (i : ℕ) : AEMeasurable (fun x => ‖c i x - c₀ x‖ₑ * ‖g₀ x‖ₑ) ν :=
    ((hc i).sub hc₀).eNorm.mul hg₀.eNorm
  have hC : Tendsto (fun i => ∫⁻ x, ‖c i x - c₀ x‖ₑ * ‖g₀ x‖ₑ ∂ν) atTop (𝓝 0) := by
    simpa using tendsto_lintegral_of_dominated_convergence' (fun x => (M + M) * ‖g₀ x‖ₑ)
      (F := fun i x => ‖c i x - c₀ x‖ₑ * ‖g₀ x‖ₑ) (f := 0) hmeas
      (fun i => (hcM i).and hc₀M |>.mono fun x ⟨hx, hx'⟩ => by
        dsimp only
        gcongr
        exact eNorm_sub_le.trans (add_le_add (eNorm_le_coe.2 hx) (eNorm_le_coe.2 hx')))
      (by rw [lintegral_const_mul' _ _ (by simp)]; exact ENNReal.mul_ne_top (by simp) hg₀int)
      (hlim.mono fun x hx => by
        simpa using ENNReal.Tendsto.mul_const (hx.sub_const (c₀ x)).eNorm (Or.inr eNorm_ne_top))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using (ENNReal.Tendsto.const_mul (a := M) hgg (Or.inr ENNReal.coe_ne_top)).add hC)
    (fun _ => zero_le) fun i => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← lintegral_add_right' _ (hmeas i)]
  refine lintegral_mono_ae ((hcM i).mono fun x hx => ?_)
  calc
    ‖c i x • g i x - c₀ x • g₀ x‖ₑ
      = ‖c i x • (g i x - g₀ x) + (c i x - c₀ x) • g₀ x‖ₑ := by
          congr 1
          rw [smul_sub, sub_smul]
          abel
    _ ≤ M * ‖g i x - g₀ x‖ₑ + ‖c i x - c₀ x‖ₑ * ‖g₀ x‖ₑ := ?_
  refine (eNorm_add_le _ _).trans (add_le_add ?_ (eNorm_smul _ _).le)
  rw [eNorm_smul]
  gcongr
  exact eNorm_le_coe.2 hx

/-- **The reverse Fatou lemma for integrals over sets.** Let the sets `s n` be measurable and
contained in a set `t` over which `f` is almost everywhere measurable with finite integral. Then
the limit superior of the integrals of `f` over `s n` is at most the integral of `f` over
`limsup s n`, the set of points that lie in `s n` for infinitely many `n`. -/
theorem limsup_setLIntegral_le {f : α → ℝ≥0∞} {s : ℕ → Set α} {t : Set α}
    (hf : AEMeasurable f (μ.restrict t)) (hs : ∀ n, MeasurableSet (s n)) (hst : ∀ n, s n ⊆ t)
    (ht : ∫⁻ x in t, f x ∂μ ≠ ∞) :
    limsup (fun n ↦ ∫⁻ x in s n, f x ∂μ) atTop ≤ ∫⁻ x in limsup s atTop, f x ∂μ := by
  -- Replace `f` by a measurable function equal to it almost everywhere on `t`.
  have hlim : limsup s atTop ⊆ t := fun x hx ↦
    (mem_limsup_iff_frequently_mem.1 hx).exists.elim fun n hn ↦ hst n hn
  have hmk {u : Set α} (hu : u ⊆ t) : ∫⁻ x in u, f x ∂μ = ∫⁻ x in u, hf.mk f x ∂μ :=
    lintegral_congr_ae (ae_restrict_of_ae_restrict_of_subset hu hf.ae_eq_mk)
  rw [hmk subset_rfl] at ht
  simp_rw [hmk (hst _), hmk hlim, ← lintegral_indicator (hs _)]
  refine (limsup_lintegral_le (t.indicator (hf.mk f))
    (fun n ↦ hf.measurable_mk.indicator (hs n))
    (fun n ↦ ae_of_all _ (Set.indicator_le_indicator_of_subset (hst n) fun _ ↦ zero_le))
    (ne_top_of_le_ne_top ht (lintegral_indicator_le _ t))).trans
    ((lintegral_mono fun x ↦ ?_).trans (lintegral_indicator_le _ _))
  -- Pointwise, the limit superior of the indicators is at most the indicator of `limsup s n`.
  by_cases hx : ∃ᶠ n in atTop, x ∈ s n
  · rw [Set.indicator_of_mem (mem_limsup_iff_frequently_mem.2 hx)]
    exact limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun n ↦
      Set.indicator_le_self (s n) _ x)
  · rw [not_frequently] at hx
    rw [limsup_congr (hx.mono fun n hn ↦ Set.indicator_of_notMem hn _)]
    simp

/-- **Dominated convergence to the pointwise `limsup`**, requiring only almost-everywhere
convergence to *some* limit rather than a globally named limit function. -/
theorem tendsto_lintegral_filter_limsup_of_dominated_convergence {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {F : ι → α → ℝ≥0∞} (bound : α → ℝ≥0∞)
    (hF_meas : ∀ᶠ j in l, AEMeasurable (F j) μ)
    (h_bound : ∀ᶠ j in l, ∀ᵐ x ∂μ, F j x ≤ bound x)
    (h_fin : ∫⁻ x, bound x ∂μ ≠ ∞)
    (h_lim : ∀ᵐ x ∂μ, ∃ c, Tendsto (fun j ↦ F j x) l (𝓝 c)) :
    Tendsto (fun j ↦ ∫⁻ x, F j x ∂μ) l (𝓝 (∫⁻ x, limsup (fun j ↦ F j x) l ∂μ)) := by
  rcases eq_or_neBot l with rfl | _
  · exact tendsto_bot
  · refine tendsto_lintegral_filter_of_dominated_convergence' bound hF_meas h_bound h_fin ?_
    exact h_lim.mono fun _ ⟨_, hc⟩ ↦ hc.limsup_eq ▸ hc

end TauCeti
