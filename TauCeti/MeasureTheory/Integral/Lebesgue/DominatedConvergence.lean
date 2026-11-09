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
import TauCeti.MeasureTheory.Integral.Lebesgue.Truncation

/-!
# Consequences of dominated convergence for Lebesgue integrals

A function `f : α → ℝ≥0∞` of finite Lebesgue integral exceeds a large constant `M` only by an
amount of small integral: `∫⁻ x, f x - M ∂μ → 0` as `M → ∞`. The excess and the truncation
`min f M` add up to `f`, so by superadditivity of the integral the integral of the excess is at
most `∫⁻ f - ∫⁻ min f M`, which tends to `0` by monotone convergence for the truncations.

The file also records a squeeze principle: if `f n ≤ g n + h n` and the integrals of `g n` and
`h n` tend to `0`, so does the integral of `f n`; and the reverse Fatou lemma for integrals over
sets: the integrals of a function of finite integral over measurable sets `s n` have limit
superior at most its integral over `limsup s n`, the set of points lying in infinitely many
`s n`.

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
* `TauCeti.limsup_setLIntegral_le`: `limsup ∫⁻_{s n} f ≤ ∫⁻_{limsup s n} f` when the `s n` lie
  in a set over which `f` has finite integral.
-/

public section

namespace TauCeti

open Filter MeasureTheory Topology
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Uniformly small tails.** If `f : α → ℝ≥0∞` has finite Lebesgue integral, then the integral
of its excess `f x - M` over a finite level `M` tends to `0` as `M → ∞`. -/
theorem tendsto_lintegral_tsub_atTop {f : α → ℝ≥0∞} (hfi : ∫⁻ x, f x ∂μ ≠ ∞) :
    Tendsto (fun M : ℝ≥0 ↦ ∫⁻ x, f x - M ∂μ) atTop (𝓝 0) := by
  -- The excess and the truncation at level `M` add up to `f`, and the integral is superadditive.
  have hle (M : ℝ≥0) : ∫⁻ x, f x - M ∂μ ≤ ∫⁻ x, f x ∂μ - ∫⁻ x, min (f x) M ∂μ :=
    ENNReal.le_sub_of_add_le_right
      (ne_top_of_le_ne_top hfi (lintegral_mono fun _ ↦ min_le_left _ _))
      ((le_lintegral_add _ _).trans (lintegral_mono fun x ↦ (tsub_add_min (a := f x)).le))
  have h := ENNReal.Tendsto.sub (tendsto_const_nhds (x := ∫⁻ x, f x ∂μ))
    (tendsto_lintegral_min_atTop (f := f) (μ := μ)) (.inl hfi)
  rw [tsub_self] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ ↦ zero_le) hle

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

/-- **The reverse Fatou lemma for integrals over sets.** Let `f` be measurable, let the sets `s n`
be measurable and contained in a set `t` over which `f` has finite integral. Then the limit
superior of the integrals of `f` over `s n` is at most the integral of `f` over `limsup s n`, the
set of points that lie in `s n` for infinitely many `n`. -/
theorem limsup_setLIntegral_le {f : α → ℝ≥0∞} {s : ℕ → Set α} {t : Set α} (hf : Measurable f)
    (hs : ∀ n, MeasurableSet (s n)) (hst : ∀ n, s n ⊆ t) (ht : ∫⁻ x in t, f x ∂μ ≠ ∞) :
    limsup (fun n ↦ ∫⁻ x in s n, f x ∂μ) atTop ≤ ∫⁻ x in limsup s atTop, f x ∂μ := by
  simp_rw [← lintegral_indicator (hs _)]
  refine (limsup_lintegral_le (t.indicator f) (fun n ↦ hf.indicator (hs n))
    (fun n ↦ ae_of_all _ (Set.indicator_le_indicator_of_subset (hst n) fun _ ↦ zero_le))
    (ne_top_of_le_ne_top ht (lintegral_indicator_le f t))).trans
    ((lintegral_mono fun x ↦ ?_).trans (lintegral_indicator_le f _))
  -- Pointwise, the limit superior of the indicators is at most the indicator of `limsup s n`.
  by_cases hx : ∃ᶠ n in atTop, x ∈ s n
  · rw [Set.indicator_of_mem (Filter.mem_limsup_iff_frequently_mem.2 hx)]
    exact limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun n ↦
      Set.indicator_le_self (s n) f x)
  · rw [not_frequently] at hx
    rw [limsup_congr (hx.mono fun n hn ↦ Set.indicator_of_notMem hn f)]
    simp

end TauCeti
