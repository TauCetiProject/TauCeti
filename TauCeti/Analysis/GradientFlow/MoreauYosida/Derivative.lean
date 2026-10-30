/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.GradientFlow.MoreauYosida.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Data.EReal.Operations

/-!
# The derivative of the Moreau–Yosida approximation in the time step

For an energy `φ : X → EReal` and a point `x`, the Moreau–Yosida approximation
`φ_τ(x) = inf_y (φ y + d(x, y)² / (2τ))` is nonincreasing in the time step `τ`. This file computes
its derivative: if `y_τ ∈ J_τ x` is a resolvent step for each `τ` in an interval, then

`d/dτ φ_τ(x) = -d(x, y_τ)² / (2τ²)`

at every time where `τ ↦ d(x, y_τ)` is continuous, hence at all but countably many times, and
integrating gives the energy identity of De Giorgi's variational interpolation

`φ_τ(x) + ∫₀^τ d(x, y_r)² / (2r²) dr = φ(x)`

for a lower semicontinuous energy and `φ(x)` finite. Combined with the slope estimate
`|∂φ|(y_r) ≤ d(x, y_r) / r` this gives the discrete energy–dissipation inequality
`φ_τ(x) + ∫₀^τ |∂φ|²(y_r) / 2 dr ≤ φ(x)` that drives the convergence of the minimizing movement
scheme.

The resolvent steps `y_τ` are an arbitrary selection, with no measurability assumed: the
monotonicity of `τ ↦ d(x, y_τ)` is what makes the integrals meaningful. The time step is a real
number `r`, entering the Moreau–Yosida approximation as `r.toNNReal`, so that the integrals are
ordinary interval integrals.

## Main results

* `TauCeti.moreauYosida_add_le_of_mem_moreauYosidaResolvent`: if `z ∈ J_τ x`, then
  `φ_σ(x) + d(x, z)² / (2τ) ≤ φ_τ(x) + d(x, z)² / (2σ)` for every time step `σ`.
* `TauCeti.hasDerivAt_toReal_moreauYosida`: the derivative `-d(x, y_r)² / (2r²)` of
  `r ↦ φ_r(x)` at a time `r > 0` where `r ↦ d(x, y_r)` is continuous.
* `TauCeti.countable_not_hasDerivAt_toReal_moreauYosida`: this derivative formula holds at all
  but countably many times of an interval.
* `TauCeti.moreauYosida_eq_add_integral`: `φ_τ(x) = φ_σ(x) + ∫_τ^σ d(x, y_r)² / (2r²) dr`.
* `TauCeti.tendsto_moreauYosida_nhdsGT_zero`: for `φ` lower semicontinuous at `x` with
  `φ_σ(x) ≠ ⊥` for some `σ > 0`, `φ_τ(x) → φ(x)` as `τ → 0⁺`.
* `TauCeti.moreauYosida_add_integral_eq`: the De Giorgi energy identity
  `φ_σ(x) + ∫₀^σ d(x, y_r)² / (2r²) dr = φ(x)`, with
  `TauCeti.intervalIntegrable_edist_sq_div_of_forall_mem_moreauYosidaResolvent` for the
  integrability of the integrand and `TauCeti.moreauYosida_add_integral_le` for the inequality
  without lower semicontinuity.
* `TauCeti.moreauYosida_add_lintegral_descendingSlope_le`: the discrete energy–dissipation
  inequality `φ_σ(x) + ∫₀^σ |∂φ|²(y_r) / 2 dr ≤ φ(x)`.
* `TauCeti.apply_add_add_lintegral_descendingSlope_le`: the same inequality for a resolvent step
  `z ∈ J_τ x`, as `φ z + d(x, z)² / (2τ) + ∫₀^τ |∂φ|²(y_r) / 2 dr ≤ φ(x)`, with no finiteness
  hypotheses.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapter 3, Sections 3.1 and 3.2, in particular
  Theorem 3.1.4.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace TauCeti

section PseudoEMetricSpace

variable {X : Type*} [PseudoEMetricSpace X] {φ : X → EReal} {x : X}

/-- **Comparison of Moreau–Yosida approximations at two time steps.** If `z ∈ J_τ x` is a resolvent
step, then `z` is a competitor for the Moreau–Yosida approximation at every other time step `σ`,
which gives `φ_σ(x) + d(x, z)² / (2τ) ≤ φ_τ(x) + d(x, z)² / (2σ)`. -/
theorem moreauYosida_add_le_of_mem_moreauYosidaResolvent {τ : ℝ≥0} {z : X}
    (hz : z ∈ moreauYosidaResolvent φ τ x) (σ : ℝ≥0) :
    moreauYosida φ σ x + (edist x z ^ 2 / (2 * τ) : ℝ≥0∞) ≤
      moreauYosida φ τ x + (edist x z ^ 2 / (2 * σ) : ℝ≥0∞) := by
  rw [← (mem_moreauYosidaResolvent_iff_eq_moreauYosida.1 hz).2, add_right_comm]
  exact add_le_add_left (moreauYosida_le φ σ (edist_ne_top_of_mem_moreauYosidaResolvent hz)) _

/-- If `J_τ x` contains a point and `φ_τ(x) < ⊤`, then `φ_σ(x) < ⊤` for every `σ > 0`. -/
private theorem moreauYosida_ne_top_of_mem {τ σ : ℝ≥0} {z : X}
    (hz : z ∈ moreauYosidaResolvent φ τ x) (hτ : moreauYosida φ τ x ≠ ⊤) (hσ : 0 < σ) :
    moreauYosida φ σ x ≠ ⊤ := by
  have h := moreauYosida_add_le_of_mem_moreauYosidaResolvent hz σ
  have hpen : edist x z ^ 2 / (2 * σ) ≠ ∞ :=
    ENNReal.div_ne_top (by simpa using edist_ne_top_of_mem_moreauYosidaResolvent hz)
      (by simp [hσ.ne'])
  intro htop
  rw [htop, EReal.top_add_of_ne_bot (EReal.coe_ennreal_ne_bot _), top_le_iff] at h
  exact (EReal.add_lt_top hτ (EReal.coe_ennreal_eq_top_iff.not.2 hpen)).ne h

/-- If `J_σ x` contains a point and `φ_τ(x) > ⊥`, then `φ_σ(x) > ⊥`. -/
private theorem moreauYosida_ne_bot_of_mem {τ σ : ℝ≥0} {z : X}
    (hz : z ∈ moreauYosidaResolvent φ σ x) (hτ : moreauYosida φ τ x ≠ ⊥) :
    moreauYosida φ σ x ≠ ⊥ := by
  have h := moreauYosida_add_le_of_mem_moreauYosidaResolvent hz τ
  intro hbot
  rw [hbot, EReal.bot_add, le_bot_iff, EReal.add_eq_bot_iff] at h
  exact h.elim hτ (EReal.coe_ennreal_ne_bot _)

/-- A resolvent step from a point where the Moreau–Yosida approximation is not `⊥` has energy
other than `⊥`. -/
private theorem apply_ne_bot_of_moreauYosida_ne_bot {τ : ℝ≥0} {z : X}
    (hz : z ∈ moreauYosidaResolvent φ τ x)
    (hτ : moreauYosida φ τ x ≠ ⊥) : φ z ≠ ⊥ := by
  intro h
  rw [← (mem_moreauYosidaResolvent_iff_eq_moreauYosida.1 hz).2, h, EReal.bot_add] at hτ
  exact hτ rfl

/-- `TauCeti.moreauYosida_add_le_of_mem_moreauYosidaResolvent` in real numbers, for positive real
time steps `s` and `t` at which the Moreau–Yosida approximation is finite. -/
private theorem toReal_moreauYosida_add_le {s t : ℝ} (hs : 0 < s) (ht : 0 < t) {z : X}
    (hz : z ∈ moreauYosidaResolvent φ s.toNNReal x) (hs₁ : moreauYosida φ s.toNNReal x ≠ ⊤)
    (hs₂ : moreauYosida φ s.toNNReal x ≠ ⊥) (ht₁ : moreauYosida φ t.toNNReal x ≠ ⊤)
    (ht₂ : moreauYosida φ t.toNNReal x ≠ ⊥) :
    (moreauYosida φ t.toNNReal x).toReal + (edist x z).toReal ^ 2 / (2 * s) ≤
      (moreauYosida φ s.toNNReal x).toReal + (edist x z).toReal ^ 2 / (2 * t) := by
  have h := moreauYosida_add_le_of_mem_moreauYosidaResolvent hz t.toNNReal
  have hd : edist x z ≠ ∞ := edist_ne_top_of_mem_moreauYosidaResolvent hz
  rw [← EReal.coe_toReal hs₁ hs₂, ← EReal.coe_toReal ht₁ ht₂,
    EReal.coe_add_coe_ennreal_le_coe_add_coe_ennreal_iff
      (ENNReal.div_ne_top (by finiteness) (by simp [hs])) (ENNReal.div_ne_top (by finiteness)
        (by simp [ht]))] at h
  simpa [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_mul, Real.coe_toNNReal _ hs.le,
    Real.coe_toNNReal _ ht.le] using h

/-- **The derivative of the Moreau–Yosida approximation in the time step.** Let `y s ∈ J_s x` be a
resolvent step for all times `s` near `r > 0`, with `φ_r(x)` finite. If `s ↦ d(x, y s)` is
continuous at `r`, then `s ↦ φ_s(x)` has derivative `-d(x, y r)² / (2r²)` at `r`. -/
theorem hasDerivAt_toReal_moreauYosida {y : ℝ → X} {r : ℝ} (hr : 0 < r)
    (hy : ∀ᶠ s in 𝓝 r, y s ∈ moreauYosidaResolvent φ s.toNNReal x)
    (hr₁ : moreauYosida φ r.toNNReal x ≠ ⊤) (hr₂ : moreauYosida φ r.toNNReal x ≠ ⊥)
    (hc : ContinuousAt (fun s ↦ (edist x (y s)).toReal) r) :
    HasDerivAt (fun s ↦ (moreauYosida φ s.toNNReal x).toReal)
      (-(edist x (y r)).toReal ^ 2 / (2 * r ^ 2)) r := by
  set M : ℝ → ℝ := fun s ↦ (moreauYosida φ s.toNNReal x).toReal
  set D : ℝ → ℝ := fun s ↦ (edist x (y s)).toReal
  -- The difference quotient at `s` lies between `u s` and `v s`, which both tend to the claimed
  -- derivative as `s → r`.
  set u : ℝ → ℝ := fun s ↦ -D r ^ 2 / (2 * r * s)
  set v : ℝ → ℝ := fun s ↦ -D s ^ 2 / (2 * r * s)
  have hlim (w : ℝ → ℝ) (hw : ContinuousAt w r) (hwr : w r = -D r ^ 2 / (2 * r * r)) :
      Tendsto w (𝓝[≠] r) (𝓝 (-D r ^ 2 / (2 * r ^ 2))) := by
    rw [sq r, ← mul_assoc, ← hwr]
    exact hw.tendsto.mono_left nhdsWithin_le_nhds
  have hu := hlim u (by fun_prop (disch := positivity)) rfl
  have hv := hlim v (((hc.pow 2).neg).div (by fun_prop) (by positivity)) rfl
  have hyr : y r ∈ moreauYosidaResolvent φ r.toNNReal x := hy.self_of_nhds
  have hbound : ∀ᶠ s in 𝓝[≠] r, min (u s) (v s) ≤ slope M r s ∧ slope M r s ≤ max (u s) (v s) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hy.and (Ioi_mem_nhds hr))]
      with s (hsr : s ≠ r) ⟨hys, hs⟩
    have hs₁ : moreauYosida φ s.toNNReal x ≠ ⊤ :=
      moreauYosida_ne_top_of_mem hyr hr₁ (Real.toNNReal_pos.2 hs)
    have hs₂ : moreauYosida φ s.toNNReal x ≠ ⊥ := moreauYosida_ne_bot_of_mem hys hr₂
    have hk (a : ℝ) : a / (2 * s) - a / (2 * r) = -a / (2 * r * s) * (s - r) := by
      field_simp
      ring
    -- The two comparisons, from `y r` against time `s` and from `y s` against time `r`.
    have h₁ : M s - M r ≤ u s * (s - r) := by
      have h := toReal_moreauYosida_add_le hr hs hyr hr₁ hr₂ hs₁ hs₂
      have k := hk (D r ^ 2)
      simp only [M, u] at h k ⊢
      linarith
    have h₂ : v s * (s - r) ≤ M s - M r := by
      have h := toReal_moreauYosida_add_le hs hr hys hs₁ hs₂ hr₁ hr₂
      have k := hk (D s ^ 2)
      simp only [M, v] at h k ⊢
      linarith
    rw [slope_def_field]
    rcases hsr.lt_or_gt with hsr | hsr
    · have hsr' : s - r < 0 := sub_neg.2 hsr
      exact ⟨(min_le_left _ _).trans ((le_div_iff_of_neg hsr').2 h₁),
        ((div_le_iff_of_neg hsr').2 h₂).trans (le_max_right _ _)⟩
    · have hsr' : 0 < s - r := sub_pos.2 hsr
      exact ⟨(min_le_right _ _).trans ((le_div_iff₀ hsr').2 h₂),
        ((div_le_iff₀ hsr').2 h₁).trans (le_max_left _ _)⟩
  rw [hasDerivAt_iff_tendsto_slope]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hu.min hv)
    (by simpa using hu.max hv) (hbound.mono fun _ h ↦ h.1) (hbound.mono fun _ h ↦ h.2)

/-- Along a selection `y r ∈ J_r x` of resolvent steps on an interval `s ⊆ (0, ∞)`, with the
Moreau–Yosida approximation finite on `s`, the distance `r ↦ d(x, y r)` is monotone. -/
private theorem monotoneOn_toReal_edist {y : ℝ → X} {s : Set ℝ} (hs : s ⊆ Ioi 0)
    (hy : ∀ r ∈ s, y r ∈ moreauYosidaResolvent φ r.toNNReal x)
    (hfin : ∀ r ∈ s, moreauYosida φ r.toNNReal x ≠ ⊤ ∧ moreauYosida φ r.toNNReal x ≠ ⊥) :
    MonotoneOn (fun r ↦ (edist x (y r)).toReal) s := by
  intro r hr t ht hrt
  rcases hrt.eq_or_lt with rfl | hrt
  · rfl
  refine ENNReal.toReal_mono (edist_ne_top_of_mem_moreauYosidaResolvent (hy t ht))
    (edist_le_edist_of_mem_moreauYosidaResolvent
    (Real.toNNReal_pos.2 (hs hr)) ?_ (hy r hr) (hy t ht)
    (apply_ne_bot_of_moreauYosida_ne_bot (hy r hr) (hfin r hr).2) (hfin r hr).1)
  exact Real.toNNReal_lt_toNNReal_iff'.2 ⟨hrt, hs ht⟩

/-- The Moreau–Yosida approximation is finite at every time of `[a, b]` if it is not `⊤` at `a`
and not `⊥` at `b`. -/
private theorem moreauYosida_ne_top_and_ne_bot {a b r : ℝ} (hr : r ∈ Icc a b)
    (ha : moreauYosida φ a.toNNReal x ≠ ⊤) (hb : moreauYosida φ b.toNNReal x ≠ ⊥) :
    moreauYosida φ r.toNNReal x ≠ ⊤ ∧ moreauYosida φ r.toNNReal x ≠ ⊥ :=
  ⟨ne_top_of_le_ne_top ha (antitone_moreauYosida φ x (Real.toNNReal_mono hr.1)),
    ne_bot_of_le_ne_bot hb (antitone_moreauYosida φ x (Real.toNNReal_mono hr.2))⟩

/-- **The derivative formula holds off a countable set.** Let `y r ∈ J_r x` be a resolvent step for
every time `r` in an interval `(a, b)` with `a ≥ 0`, and let `φ_a(x) ≠ ⊤` and `φ_b(x) ≠ ⊥`. Then
`r ↦ φ_r(x)` has derivative `-d(x, y r)² / (2r²)` at all but countably many `r ∈ (a, b)`. -/
theorem countable_not_hasDerivAt_toReal_moreauYosida {y : ℝ → X} {a b : ℝ} (ha : 0 ≤ a)
    (hy : ∀ r ∈ Ioo a b, y r ∈ moreauYosidaResolvent φ r.toNNReal x)
    (ha' : moreauYosida φ a.toNNReal x ≠ ⊤) (hb' : moreauYosida φ b.toNNReal x ≠ ⊥) :
    {r ∈ Ioo a b | ¬HasDerivAt (fun s ↦ (moreauYosida φ s.toNNReal x).toReal)
      (-(edist x (y r)).toReal ^ 2 / (2 * r ^ 2)) r}.Countable := by
  have hfin (r) (hr : r ∈ Ioo a b) :=
    moreauYosida_ne_top_and_ne_bot (Ioo_subset_Icc_self hr) ha' hb'
  refine ((monotoneOn_toReal_edist (fun r (hr : r ∈ Ioo a b) ↦ ha.trans_lt hr.1) hy
    hfin).countable_not_continuousWithinAt).mono fun r hr' ↦ ?_
  obtain ⟨hr, hd⟩ := hr'
  refine ⟨hr, fun hc ↦ hd ?_⟩
  exact hasDerivAt_toReal_moreauYosida (ha.trans_lt hr.1)
    (eventually_of_mem (isOpen_Ioo.mem_nhds hr) hy) (hfin r hr).1 (hfin r hr).2
    (hc.continuousAt (isOpen_Ioo.mem_nhds hr))

/-- The integrand `d(x, y r)² / (2r²)` is integrable on `[τ, σ]` when `y r ∈ J_r x` for every
`r ∈ [τ, σ]`, `0 < τ`, `φ_τ(x) ≠ ⊤` and `φ_σ(x) ≠ ⊥`: it is a monotone function times a continuous
one. -/
private theorem intervalIntegrable_edist_sq_div {y : ℝ → X} {τ σ : ℝ} (hτ : 0 < τ) (hτσ : τ ≤ σ)
    (hy : ∀ r ∈ Icc τ σ, y r ∈ moreauYosidaResolvent φ r.toNNReal x)
    (hτ' : moreauYosida φ τ.toNNReal x ≠ ⊤) (hσ' : moreauYosida φ σ.toNNReal x ≠ ⊥) :
    IntervalIntegrable (fun r ↦ (edist x (y r)).toReal ^ 2 / (2 * r ^ 2)) volume τ σ := by
  have hpos : Icc τ σ ⊆ Ioi 0 := fun r hr ↦ hτ.trans_le hr.1
  have hD := monotoneOn_toReal_edist hpos hy fun r hr ↦ moreauYosida_ne_top_and_ne_bot hr hτ' hσ'
  simp_rw [div_eq_mul_inv]
  refine MonotoneOn.intervalIntegrable ?_ |>.mul_continuousOn ?_
  · rw [uIcc_of_le hτσ]
    exact fun s hs t ht hst ↦ pow_le_pow_left₀ ENNReal.toReal_nonneg (hD hs ht hst) 2
  · rw [uIcc_of_le hτσ]
    exact ContinuousOn.inv₀ (by fun_prop) fun r hr ↦ by have : 0 < r := hpos hr; positivity

/-- **Integrated derivative formula.** Let `y r ∈ J_r x` be a resolvent step for every time
`r ∈ [τ, σ]`, with `0 < τ`, `φ_τ(x) ≠ ⊤` and `φ_σ(x) ≠ ⊥`. Then
`φ_τ(x) = φ_σ(x) + ∫_τ^σ d(x, y r)² / (2r²) dr`. -/
theorem moreauYosida_eq_add_integral {y : ℝ → X} {τ σ : ℝ} (hτ : 0 < τ) (hτσ : τ ≤ σ)
    (hy : ∀ r ∈ Icc τ σ, y r ∈ moreauYosidaResolvent φ r.toNNReal x)
    (hτ' : moreauYosida φ τ.toNNReal x ≠ ⊤) (hσ' : moreauYosida φ σ.toNNReal x ≠ ⊥) :
    moreauYosida φ τ.toNNReal x = moreauYosida φ σ.toNNReal x +
      ((∫ r in τ..σ, (edist x (y r)).toReal ^ 2 / (2 * r ^ 2) : ℝ) : EReal) := by
  set M : ℝ → ℝ := fun s ↦ (moreauYosida φ s.toNNReal x).toReal
  set D : ℝ → ℝ := fun s ↦ (edist x (y s)).toReal
  have hpos : Icc τ σ ⊆ Ioi 0 := fun r hr ↦ hτ.trans_le hr.1
  have hfin (r) (hr : r ∈ Icc τ σ) := moreauYosida_ne_top_and_ne_bot hr hτ' hσ'
  have hD : MonotoneOn D (Icc τ σ) := monotoneOn_toReal_edist hpos hy hfin
  -- `M` is Lipschitz on `[τ, σ]`, with constant `D σ² / (2τ²)`.
  have hM : ContinuousOn M (Icc τ σ) := by
    refine (LipschitzOnWith.of_dist_le_mul (K := (D σ ^ 2 / (2 * τ ^ 2)).toNNReal)
      fun s hs t ht ↦ ?_).continuousOn
    rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, Real.dist_eq]
    wlog hst : s ≤ t generalizing s t
    · rw [abs_sub_comm, abs_sub_comm s]
      exact this t ht s hs (le_of_not_ge hst)
    have hs0 : 0 < s := hpos hs
    have ht0 : 0 < t := hpos ht
    have h₁ := toReal_moreauYosida_add_le hs0 ht0 (hy s hs) (hfin s hs).1 (hfin s hs).2
      (hfin t ht).1 (hfin t ht).2
    have h₂ := toReal_moreauYosida_add_le ht0 hs0 (hy t ht) (hfin t ht).1 (hfin t ht).2
      (hfin s hs).1 (hfin s hs).2
    have hk (a : ℝ) : a / (2 * s) - a / (2 * t) = a * (t - s) / (2 * s * t) := by
      field_simp
    have hDt : D t ^ 2 ≤ D σ ^ 2 :=
      pow_le_pow_left₀ ENNReal.toReal_nonneg (hD ht ⟨hτσ, le_rfl⟩ ht.2) 2
    have hts : 0 ≤ t - s := sub_nonneg.2 hst
    have hlo : 0 ≤ M s - M t := by
      have k := hk (D s ^ 2)
      have : 0 ≤ D s ^ 2 * (t - s) / (2 * s * t) := by positivity
      simp only [M, D] at h₁ k this ⊢
      linarith
    have hhi : M s - M t ≤ D t ^ 2 * (t - s) / (2 * s * t) := by
      have k := hk (D t ^ 2)
      simp only [M, D] at h₂ k ⊢
      linarith
    rw [abs_of_nonneg hlo, abs_of_nonpos (sub_nonpos.2 hst), neg_sub, div_mul_eq_mul_div]
    refine hhi.trans (div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hDt hts)
      (by positivity) ?_)
    rw [sq, mul_assoc]
    gcongr
    exacts [hs.1, ht.1]
  have hint := intervalIntegrable_edist_sq_div hτ hτσ hy hτ' hσ'
  have hftc := integral_eq_of_hasDerivAt_off_countable_of_le M
    (fun r ↦ -D r ^ 2 / (2 * r ^ 2)) hτσ
    (countable_not_hasDerivAt_toReal_moreauYosida hτ.le (fun r hr ↦ hy r (Ioo_subset_Icc_self hr))
      hτ' hσ') hM (fun r hr ↦ not_not.1 fun h ↦ hr.2 ⟨hr.1, h⟩)
    (by convert hint.neg using 1; ext r; simp [D, neg_div])
  simp only [neg_div, intervalIntegral.integral_neg] at hftc
  rw [← EReal.coe_toReal hτ' (hfin τ ⟨le_rfl, hτσ⟩).2,
    ← EReal.coe_toReal (hfin σ ⟨hτσ, le_rfl⟩).1 hσ', ← EReal.coe_add, EReal.coe_eq_coe_iff]
  simp only [M, D] at hftc
  linarith

/-- **Continuity of the Moreau–Yosida approximation at time zero.** If `φ` is lower semicontinuous
at `x` and `φ_σ(x) ≠ ⊥` for some `σ > 0`, then `φ_τ(x) → φ(x)` as `τ → 0⁺`. This holds also when
`φ x = ⊤`, and needs no resolvent steps. -/
theorem tendsto_moreauYosida_nhdsGT_zero (hφ : LowerSemicontinuousAt φ x) {σ : ℝ≥0} (hσ : 0 < σ)
    (hσ' : moreauYosida φ σ x ≠ ⊥) :
    Tendsto (fun τ ↦ moreauYosida φ τ x) (𝓝[>] 0) (𝓝 (φ x)) := by
  refine tendsto_order.2 ⟨fun c hc ↦ ?_, fun c hc ↦
    Eventually.of_forall fun τ ↦ (moreauYosida_le_self φ τ x).trans_lt hc⟩
  obtain ⟨c', hcc', hc'⟩ := EReal.lt_iff_exists_real_btwn.1 hc
  obtain ⟨δ, hδ, hball⟩ := EMetric.mem_nhds_iff.1 (hφ c' hc')
  obtain ⟨δ₀, hδ₀, hδ₀δ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hδ
  set m := (moreauYosida φ σ x).toReal
  -- For small `τ`, the penalty at distance `δ₀` exceeds `c' - m` plus the penalty at time `σ`.
  have hinv : Tendsto (fun τ : ℝ≥0 ↦ ((τ : ℝ))⁻¹) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2
      ⟨(NNReal.continuous_coe.tendsto' 0 0 rfl).mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall fun τ hτ ↦ NNReal.coe_pos.2 hτ⟩)
  have hσ₀ : (0 : ℝ) < σ := NNReal.coe_pos.2 hσ
  have hδ₀' : (0 : ℝ) < δ₀ := NNReal.coe_pos.2 (ENNReal.coe_pos.1 hδ₀)
  filter_upwards [(hinv.const_mul_atTop (by positivity : (0 : ℝ) < δ₀ ^ 2 / 2)).eventually_ge_atTop
      (c' - m + δ₀ ^ 2 / (2 * σ)), nhdsWithin_le_nhds (Iio_mem_nhds hσ), self_mem_nhdsWithin]
    with τ hτK (hτσ : τ < σ) (hτ : 0 < τ)
  have hτ₀ : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ
  refine hcc'.trans_le (le_moreauYosida_iff.2 fun z hz ↦ ?_)
  rcases lt_or_ge (edist x z) δ₀ with hzδ | hzδ
  · refine (hball ?_ |>.le).trans (le_add_of_nonneg_right (EReal.coe_ennreal_nonneg _))
    rw [Metric.mem_eball, edist_comm]
    exact hzδ.trans hδ₀δ
  by_cases htop : φ z = ⊤
  · rw [htop, EReal.top_add_of_ne_bot (EReal.coe_ennreal_ne_bot _)]
    exact le_top
  -- Otherwise `φ z` and `φ_σ(x)` are real, and `φ_σ(x) ≤ φ z + d(x, z)² / (2σ)`.
  have h := moreauYosida_le φ σ hz
  have hzbot : φ z ≠ ⊥ := by
    rintro hbot
    rw [hbot, EReal.bot_add, le_bot_iff] at h
    exact hσ' h
  obtain ⟨b, hb⟩ : ∃ b : ℝ, φ z = b := ⟨_, (EReal.coe_toReal htop hzbot).symm⟩
  have hpen (ρ : ℝ≥0) (hρ : 0 < ρ) : edist x z ^ 2 / (2 * ρ) ≠ ∞ :=
    ENNReal.div_ne_top (by finiteness) (by simp [hρ.ne'])
  have hmtop : moreauYosida φ σ x ≠ ⊤ := by
    intro hm
    rw [hm, hb, top_le_iff] at h
    exact (EReal.add_lt_top (EReal.coe_ne_top b)
      (EReal.coe_ennreal_eq_top_iff.not.2 (hpen σ hσ))).ne h
  rw [← EReal.coe_toReal hmtop hσ', hb, EReal.coe_le_coe_add_coe_ennreal_iff (hpen σ hσ)] at h
  rw [hb, EReal.coe_le_coe_add_coe_ennreal_iff (hpen τ hτ)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.coe_toReal] at h ⊢
  set d := (edist x z).toReal
  have hdδ : (δ₀ : ℝ) ≤ d := by
    rw [← ENNReal.coe_toReal δ₀]
    exact ENNReal.toReal_mono hz hzδ
  have hw : 0 ≤ 1 / (2 * (τ : ℝ)) - 1 / (2 * σ) := by
    rw [sub_nonneg]
    gcongr
  have hsq : (δ₀ : ℝ) ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ δ₀.coe_nonneg hdδ 2
  have key : (δ₀ : ℝ) ^ 2 * (1 / (2 * τ) - 1 / (2 * σ)) ≤ d ^ 2 * (1 / (2 * τ) - 1 / (2 * σ)) :=
    mul_le_mul_of_nonneg_right hsq hw
  have e₁ : (δ₀ : ℝ) ^ 2 / 2 * (τ : ℝ)⁻¹ = δ₀ ^ 2 / (2 * τ) := by field_simp
  have e₂ : d ^ 2 * (1 / (2 * τ) - 1 / (2 * σ)) = d ^ 2 / (2 * τ) - d ^ 2 / (2 * σ) := by ring
  have e₃ : (δ₀ : ℝ) ^ 2 * (1 / (2 * τ) - 1 / (2 * σ)) = δ₀ ^ 2 / (2 * τ) - δ₀ ^ 2 / (2 * σ) := by
    ring
  linarith

variable {y : ℝ → X} {σ : ℝ}

/-- `TauCeti.moreauYosida_eq_add_integral` on `[τ, σ] ⊆ (0, σ]`, under the hypotheses of the De
Giorgi energy identity: `φ_τ(x) = φ_σ(x) + ∫_τ^σ d(x, y r)² / (2r²) dr` for `τ ∈ (0, σ]`. -/
private theorem moreauYosida_eq_add_integral_of_mem_Ioc (hy : ∀ r ∈ Ioc 0 σ,
      y r ∈ moreauYosidaResolvent φ r.toNNReal x) (hx : φ x ≠ ⊤)
    (hσ' : moreauYosida φ σ.toNNReal x ≠ ⊥) {τ : ℝ} (hτ : τ ∈ Ioc 0 σ) :
    moreauYosida φ τ.toNNReal x = moreauYosida φ σ.toNNReal x +
      ((∫ r in τ..σ, (edist x (y r)).toReal ^ 2 / (2 * r ^ 2) : ℝ) : EReal) :=
  moreauYosida_eq_add_integral hτ.1 hτ.2 (fun r hr ↦ hy r ⟨hτ.1.trans_le hr.1, hr.2⟩)
    (ne_top_of_le_ne_top hx (moreauYosida_le_self φ _ x)) hσ'

/-- The integrand `d(x, y r)² / (2r²)` of the De Giorgi energy identity is integrable on `(0, σ]`,
when `y r ∈ J_r x` for every `r ∈ (0, σ]`, `φ(x) ≠ ⊤` and `φ_σ(x) ≠ ⊥`. -/
theorem intervalIntegrable_edist_sq_div_of_forall_mem_moreauYosidaResolvent (hσ : 0 < σ)
    (hy : ∀ r ∈ Ioc 0 σ, y r ∈ moreauYosidaResolvent φ r.toNNReal x) (hx : φ x ≠ ⊤)
    (hσ' : moreauYosida φ σ.toNNReal x ≠ ⊥) :
    IntervalIntegrable (fun r ↦ (edist x (y r)).toReal ^ 2 / (2 * r ^ 2)) volume 0 σ := by
  set g : ℝ → ℝ := fun r ↦ (edist x (y r)).toReal ^ 2 / (2 * r ^ 2)
  have hxbot : φ x ≠ ⊥ := ne_bot_of_le_ne_bot hσ' (moreauYosida_le_self φ _ x)
  -- On `(a, σ]` with `a ∈ (0, σ]`, the integral of `g` is `φ_a(x) - φ_σ(x) ≤ φ(x) - φ_σ(x)`.
  have hbound {a : ℝ} (ha : a ∈ Ioc 0 σ) :
      ∫ r in a..σ, g r ≤ (φ x).toReal - (moreauYosida φ σ.toNNReal x).toReal := by
    have h := moreauYosida_eq_add_integral_of_mem_Ioc hy hx hσ' ha
    have hle := moreauYosida_le_self φ a.toNNReal x
    rw [h, ← EReal.coe_toReal (ne_top_of_le_ne_top hx (moreauYosida_le_self φ _ x)) hσ',
      ← EReal.coe_add, ← EReal.coe_toReal hx hxbot, EReal.coe_le_coe_iff] at hle
    linarith
  have hint {a : ℝ} (ha : a ∈ Ioc 0 σ) : IntervalIntegrable g volume a σ :=
    intervalIntegrable_edist_sq_div ha.1 ha.2 (fun r hr ↦ hy r ⟨ha.1.trans_le hr.1, hr.2⟩)
      (ne_top_of_le_ne_top hx (moreauYosida_le_self φ _ x)) hσ'
  -- Exhaust `(0, σ]` by the intervals `(σ / (n + 1), σ]`.
  set a : ℕ → ℝ := fun n ↦ σ / (n + 1)
  have ha (n : ℕ) : a n ∈ Ioc 0 σ :=
    ⟨by positivity, div_le_self hσ.le (by linarith [n.cast_nonneg (α := ℝ)])⟩
  have hlim : Tendsto a atTop (𝓝 0) := by
    simpa [a, div_eq_mul_inv] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul σ
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hσ.le]
  refine integrableOn_Ioc_of_intervalIntegral_norm_bounded_left
    (I := (φ x).toReal - (moreauYosida φ σ.toNNReal x).toReal)
    (fun n ↦ (hint (ha n)).1) hlim (Eventually.of_forall fun n ↦ ?_)
  have hg : ∀ r ∈ Ioc (a n) σ, ‖g r‖ = g r := fun r _ ↦ Real.norm_of_nonneg (by positivity)
  rw [setIntegral_congr_fun measurableSet_Ioc hg, ← intervalIntegral.integral_of_le (ha n).2]
  exact hbound (ha n)

/-- As `τ → 0⁺`, `φ_τ(x) = φ_σ(x) + ∫_τ^σ d(x, y r)² / (2r²) dr` tends to
`φ_σ(x) + ∫₀^σ d(x, y r)² / (2r²) dr`. -/
private theorem tendsto_moreauYosida_nhdsGT_zero_add_integral (hσ : 0 < σ)
    (hy : ∀ r ∈ Ioc 0 σ, y r ∈ moreauYosidaResolvent φ r.toNNReal x) (hx : φ x ≠ ⊤)
    (hσ' : moreauYosida φ σ.toNNReal x ≠ ⊥) :
    Tendsto (fun τ : ℝ ↦ moreauYosida φ τ.toNNReal x) (𝓝[>] 0)
      (𝓝 (moreauYosida φ σ.toNNReal x +
        ((∫ r in 0..σ, (edist x (y r)).toReal ^ 2 / (2 * r ^ 2) : ℝ) : EReal))) := by
  set g : ℝ → ℝ := fun r ↦ (edist x (y r)).toReal ^ 2 / (2 * r ^ 2)
  have hint := intervalIntegrable_edist_sq_div_of_forall_mem_moreauYosidaResolvent hσ hy hx hσ'
  have hI : IntegrableOn g (uIcc 0 σ) := by
    rw [uIcc_of_le hσ.le, integrableOn_Icc_iff_integrableOn_Ioc]
    exact hint.1
  have hF : Tendsto (fun τ ↦ ∫ r in τ..σ, g r) (𝓝[>] 0) (𝓝 (∫ r in 0..σ, g r)) :=
    (intervalIntegral.continuousOn_primitive_interval_left hI 0 left_mem_uIcc).tendsto.mono_left
      (nhdsWithin_le_of_mem (by rw [uIcc_of_le hσ.le]; exact Icc_mem_nhdsGT hσ))
  set m := (moreauYosida φ σ.toNNReal x).toReal
  have hm : moreauYosida φ σ.toNNReal x = m :=
    (EReal.coe_toReal (ne_top_of_le_ne_top hx (moreauYosida_le_self φ _ x)) hσ').symm
  rw [hm, ← EReal.coe_add]
  refine ((continuous_coe_real_ereal.tendsto _).comp (tendsto_const_nhds.add hF)).congr' ?_
  filter_upwards [Ioc_mem_nhdsGT hσ] with τ hτ
  rw [Function.comp_apply, moreauYosida_eq_add_integral_of_mem_Ioc hy hx hσ' hτ, hm, EReal.coe_add]

/-- **De Giorgi energy inequality.** Let `y r ∈ J_r x` be a resolvent step for every time
`r ∈ (0, σ]`, with `φ(x) ≠ ⊤` and `φ_σ(x) ≠ ⊥`. Then
`φ_σ(x) + ∫₀^σ d(x, y r)² / (2r²) dr ≤ φ(x)`. Equality holds when `φ` is lower semicontinuous at
`x` (`TauCeti.moreauYosida_add_integral_eq`). -/
theorem moreauYosida_add_integral_le (hσ : 0 < σ)
    (hy : ∀ r ∈ Ioc 0 σ, y r ∈ moreauYosidaResolvent φ r.toNNReal x) (hx : φ x ≠ ⊤)
    (hσ' : moreauYosida φ σ.toNNReal x ≠ ⊥) :
    moreauYosida φ σ.toNNReal x +
      ((∫ r in 0..σ, (edist x (y r)).toReal ^ 2 / (2 * r ^ 2) : ℝ) : EReal) ≤ φ x :=
  le_of_tendsto (tendsto_moreauYosida_nhdsGT_zero_add_integral hσ hy hx hσ')
    (Eventually.of_forall fun _ ↦ moreauYosida_le_self φ _ x)

/-- **De Giorgi energy identity.** Let `φ` be lower semicontinuous at `x` with `φ(x) ≠ ⊤`, and let
`y r ∈ J_r x` be a resolvent step for every time `r ∈ (0, σ]`, with `φ_σ(x) ≠ ⊥`. Then
`φ_σ(x) + ∫₀^σ d(x, y r)² / (2r²) dr = φ(x)`. -/
theorem moreauYosida_add_integral_eq (hφ : LowerSemicontinuousAt φ x) (hσ : 0 < σ)
    (hy : ∀ r ∈ Ioc 0 σ, y r ∈ moreauYosidaResolvent φ r.toNNReal x) (hx : φ x ≠ ⊤)
    (hσ' : moreauYosida φ σ.toNNReal x ≠ ⊥) :
    moreauYosida φ σ.toNNReal x +
      ((∫ r in 0..σ, (edist x (y r)).toReal ^ 2 / (2 * r ^ 2) : ℝ) : EReal) = φ x :=
  -- `Real.toNNReal` maps `𝓝[>] 0` to `𝓝[>] 0`.
  have h : Tendsto Real.toNNReal (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨(continuous_real_toNNReal.tendsto' 0 0 (by simp)).mono_left
      nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun _ hr ↦ Real.toNNReal_pos.2 hr⟩
  tendsto_nhds_unique (tendsto_moreauYosida_nhdsGT_zero_add_integral hσ hy hx hσ')
    ((tendsto_moreauYosida_nhdsGT_zero hφ (Real.toNNReal_pos.2 hσ) hσ').comp h)

end PseudoEMetricSpace

section EMetricSpace

variable {X : Type*} [EMetricSpace X] {φ : X → EReal} {x : X} {y : ℝ → X} {σ : ℝ}

/-- **Discrete energy–dissipation inequality.** Let `y r ∈ J_r x` be a resolvent step for every
time `r ∈ (0, σ]`, with `φ(x) ≠ ⊤` and `φ_σ(x) ≠ ⊥`. Then
`φ_σ(x) + ∫₀^σ |∂φ|²(y r) / 2 dr ≤ φ(x)`, where `|∂φ|` is the descending slope. -/
theorem moreauYosida_add_lintegral_descendingSlope_le (hσ : 0 < σ)
    (hy : ∀ r ∈ Ioc 0 σ, y r ∈ moreauYosidaResolvent φ r.toNNReal x) (hx : φ x ≠ ⊤)
    (hσ' : moreauYosida φ σ.toNNReal x ≠ ⊥) :
    moreauYosida φ σ.toNNReal x +
      ((∫⁻ r in Ioc 0 σ, descendingSlope φ (y r) ^ 2 / 2 : ℝ≥0∞) : EReal) ≤ φ x := by
  set g : ℝ → ℝ := fun r ↦ (edist x (y r)).toReal ^ 2 / (2 * r ^ 2)
  have hint := intervalIntegrable_edist_sq_div_of_forall_mem_moreauYosidaResolvent hσ hy hx hσ'
  refine le_trans (add_le_add_right ?_ _) (moreauYosida_add_integral_le hσ hy hx hσ')
  have hg : ∀ r ∈ Ioc 0 σ, 0 ≤ g r := fun r _ ↦ by positivity
  rw [intervalIntegral.integral_of_le hσ.le,
    ← max_eq_left (setIntegral_nonneg measurableSet_Ioc hg), ← EReal.coe_ennreal_ofReal,
    EReal.coe_ennreal_le_coe_ennreal_iff,
    ofReal_integral_eq_lintegral_ofReal hint.1 (ae_restrict_of_forall_mem measurableSet_Ioc hg)]
  refine setLIntegral_mono' measurableSet_Ioc fun r hr ↦ ?_
  -- At a resolvent step, `|∂φ|(y r) ≤ d(x, y r) / r`.
  have hr₀ : 0 < r.toNNReal := Real.toNNReal_pos.2 hr.1
  have hr₁ : moreauYosida φ r.toNNReal x ≠ ⊤ := ne_top_of_le_ne_top hx (moreauYosida_le_self φ _ x)
  have hr₂ : moreauYosida φ r.toNNReal x ≠ ⊥ :=
    ne_bot_of_le_ne_bot hσ' (antitone_moreauYosida φ x (Real.toNNReal_mono hr.2))
  have hd := edist_ne_top_of_mem_moreauYosidaResolvent (hy r hr)
  have hslope := descendingSlope_le_of_mem_moreauYosidaResolvent hr₀ (hy r hr)
    (apply_ne_bot_of_moreauYosida_ne_bot (hy r hr) hr₂) hr₁
  have hfin : (edist x (y r) / r.toNNReal) ^ 2 / 2 ≠ ∞ :=
    ENNReal.div_ne_top (ENNReal.pow_ne_top (ENNReal.div_ne_top hd (by simpa using hr₀.ne')))
      two_ne_zero
  refine (by gcongr : descendingSlope φ (y r) ^ 2 / 2 ≤ (edist x (y r) / r.toNNReal) ^ 2 / 2).trans
    ((ENNReal.le_ofReal_iff_toReal_le hfin (hg r hr)).2 (le_of_eq ?_))
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.coe_toReal,
    Real.coe_toNNReal _ hr.1.le, ENNReal.toReal_ofNat, g]
  ring

/-- **Discrete energy–dissipation inequality for one resolvent step.** Let `z ∈ J_τ x` be a
resolvent step with time step `τ > 0`, and let `y r ∈ J_r x` be a resolvent step for every time
`r ∈ (0, τ]`. Then `φ z + d(x, z)² / (2τ) + ∫₀^τ |∂φ|²(y r) / 2 dr ≤ φ(x)`, where `|∂φ|` is the
descending slope. Unlike `TauCeti.moreauYosida_add_lintegral_descendingSlope_le`, no finiteness
hypothesis is needed: the inequality is trivial when `φ x = ⊤` or `φ z = ⊥`. -/
theorem apply_add_add_lintegral_descendingSlope_le {τ : ℝ≥0} (hτ : 0 < τ) {z : X}
    (hz : z ∈ moreauYosidaResolvent φ τ x)
    (hy : ∀ r ∈ Ioc 0 (τ : ℝ), y r ∈ moreauYosidaResolvent φ r.toNNReal x) :
    φ z + (edist x z ^ 2 / (2 * τ) : ℝ≥0∞) +
      ((∫⁻ r in Ioc 0 (τ : ℝ), descendingSlope φ (y r) ^ 2 / 2 : ℝ≥0∞) : EReal) ≤ φ x := by
  by_cases hx : φ x = ⊤
  · exact hx ▸ le_top
  by_cases hz' : φ z = ⊥
  · simp [hz']
  have hφτ := (mem_moreauYosidaResolvent_iff_eq_moreauYosida.1 hz).2
  have hτ' : moreauYosida φ (τ : ℝ).toNNReal x ≠ ⊥ := by
    rw [Real.toNNReal_coe, ← hφτ]
    exact fun h ↦ (EReal.add_eq_bot_iff.1 h).elim hz' (EReal.coe_ennreal_ne_bot _)
  simpa only [Real.toNNReal_coe, ← hφτ] using
    moreauYosida_add_lintegral_descendingSlope_le (NNReal.coe_pos.2 hτ) hy hx hτ'

end EMetricSpace

end TauCeti
