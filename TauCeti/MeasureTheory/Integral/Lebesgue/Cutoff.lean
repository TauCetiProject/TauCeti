/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Topology.Order.WithTop
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Lebesgue integrals of cut-off functions

Multiplying a real function `u` by a cutoff `χ` with `|χ| ≤ 1` and support in a set `s` does not
increase the Lebesgue integral of its extended norm beyond that of `u` over `s`.

## Main statements

* `TauCeti.lintegral_enorm_mul_le_setLIntegral_of_support_subset`: `∫ |χ u| ≤ ∫_s |u|`.
* `TauCeti.tendsto_lintegral_enorm_mul_sub_of_eventually_eq_one`: cutoffs with values in `[0, 1]`
  that are eventually `1` at almost every point recover an integrable function in `L¹`.
* `TauCeti.tendsto_lintegral_ite_le_rpow_of_tendsto_of_le` / `..._pow_...`: `WithTop` cutoffs
  converging from above along a countably generated filter tend to zero in lower `p`-th power norm.
* `TauCeti.tendsto_measure_lintegral_ite_le_rpow_of_tendsto_measure_le` / `..._pow_...`: random
  `WithTop` cutoffs exceeding `T` in measure yield cutoff errors tending to zero in measure.
-/

public section

namespace TauCeti

open Filter MeasureTheory Function Set
open scoped ENNReal Topology

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α} {χ : α → ℝ}

/-- Multiplying by a cutoff `χ` with `|χ| ≤ 1` and `support χ ⊆ s` does not increase the `L¹`
norm on `s`: `∫ |χ u| ≤ ∫_s |u|`. Neither `s` nor the functions need be measurable. -/
theorem lintegral_enorm_mul_le_setLIntegral_of_support_subset (hχ1 : ∀ x, |χ x| ≤ 1)
    (hχs : support χ ⊆ s) (u : α → ℝ) :
    ∫⁻ x, ‖(χ * u) x‖ₑ ∂μ ≤ ∫⁻ x in s, ‖u x‖ₑ ∂μ := by
  refine (lintegral_mono fun x => ?_).trans (lintegral_indicator_le _ s)
  by_cases hx : x ∈ s
  · rw [indicator_of_mem hx, Pi.mul_apply, eNorm_mul]
    exact mul_le_of_le_one_left' (by simpa [← ofReal_norm] using hχ1 x)
  · simp [notMem_support.mp fun hmem => hx (hχs hmem)]

/-- **Cutoffs recover an integrable function in `L¹`.** If the cutoffs `χ n` take values in
`[0, 1]` almost everywhere and almost every point is eventually fixed by them, then
`‖χ n u - u‖₁ → 0` for integrable `u`, by dominated convergence. -/
theorem tendsto_lintegral_enorm_mul_sub_of_eventually_eq_one {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {χ : ι → α → ℝ} {u : α → ℝ} (hu : Integrable u μ)
    (hχ : ∀ n, ∀ᵐ x ∂μ, χ n x ∈ Icc 0 1) (hχm : ∀ n, AEStronglyMeasurable (χ n) μ)
    (hlim : ∀ᵐ x ∂μ, ∀ᶠ n in l, χ n x = 1) :
    Tendsto (fun n => ∫⁻ x, ‖χ n x * u x - u x‖ₑ ∂μ) l (𝓝 0) := by
  have hdom (n : ι) : ∀ᵐ x ∂μ, ‖χ n x * u x - u x‖ₑ ≤ ‖u x‖ₑ := (hχ n).mono fun x hx => by
    rw [← sub_one_mul, eNorm_mul]
    have hle : ‖χ n x - 1‖ₑ ≤ 1 := by
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonpos (by linarith [hx.1, hx.2])]
      exact ENNReal.ofReal_le_one.2 (by linarith [hx.1])
    simpa using mul_le_mul_left hle ‖u x‖ₑ
  simpa only [Pi.mul_apply, Pi.sub_apply, lintegral_zero] using
    tendsto_lintegral_filter_of_dominated_convergence' (f := fun _ => 0) (fun x => ‖u x‖ₑ)
      (.of_forall fun n => (((hχm n).mul hu.aestronglyMeasurable).sub
        hu.aestronglyMeasurable).eNorm)
      (.of_forall hdom) hu.hasFiniteIntegral.ne
      (hlim.mono fun x hx => tendsto_const_nhds.congr' (hx.mono fun n hn => by
        simp only [Pi.sub_apply, Pi.mul_apply, hn, one_mul, sub_self, eNorm_zero]))

section WithTopCutoff

variable {β ι E : Type*} [LinearOrder ι] [MeasurableSpace ι] [SeminormedAddCommGroup E]
  {l : Filter β} {μ : Measure ι}

/-- Along any countably generated filter `l` on which `v` converges to `u` eventually from above,
the lower `p`-th power norm error (`0 < p`) between the `[0, v a]` and `[0, u]` cutoffs of `f`
tends to zero whenever `s ↦ ‖f s‖ₑ ^ p` is `μ`-a.e. measurable with finite lower integral. -/
theorem tendsto_lintegral_ite_le_rpow_of_tendsto_of_le [TopologicalSpace ι] [OrderTopology ι]
    [OpensMeasurableSpace ι] [l.IsCountablyGenerated] {f : ι → E} {v : β → WithTop ι}
    {u : WithTop ι} {p : ℝ} (hp : 0 < p) (hv : Tendsto v l (𝓝 u)) (hle : ∀ᶠ a in l, u ≤ v a)
    (hf : AEMeasurable (fun s ↦ ‖f s‖ₑ ^ p) μ) (hfin : ∫⁻ s, ‖f s‖ₑ ^ p ∂μ ≠ ∞) :
    Tendsto (fun a ↦ ∫⁻ s, ‖(if (s : WithTop ι) ≤ v a then f s else 0) -
      (if (s : WithTop ι) ≤ u then f s else 0)‖ₑ ^ p ∂μ) l (𝓝 0) := by
  have hset (w : WithTop ι) : MeasurableSet {s : ι | (s : WithTop ι) ≤ w} := by
    cases w with | top => simp | coe r => simp only [WithTop.coe_le_coe]; exact measurableSet_Iic
  let S (a : β) : Set ι := {s | (s : WithTop ι) ≤ v a} \ {s | (s : WithTop ι) ≤ u}
  have hdom : Tendsto (fun a ↦ ∫⁻ s, (S a).indicator (fun r ↦ ‖f r‖ₑ ^ p) s ∂μ) l (𝓝 0) := by
    simpa only [lintegral_zero] using tendsto_lintegral_filter_of_dominated_convergence' (l := l)
      (F := fun a ↦ (S a).indicator (fun r ↦ ‖f r‖ₑ ^ p)) (f := fun _ ↦ 0) (fun s ↦ ‖f s‖ₑ ^ p)
      (.of_forall fun _ ↦ hf.indicator ((hset _).diff (hset _)))
      (.of_forall fun _ ↦ .of_forall fun s ↦ indicator_le_self' (fun _ _ ↦ zero_le) s) hfin <|
      .of_forall fun s ↦ by
        by_cases hs : (s : WithTop ι) ≤ u
        · exact tendsto_const_nhds.congr fun a ↦
            (indicator_of_notMem (fun (h : s ∈ S a) ↦ h.2 hs) _).symm
        · exact tendsto_const_nhds.congr' <| (hv.eventually (eventually_lt_nhds (not_le.1 hs))).mono
            fun a ha ↦ (indicator_of_notMem (fun (h : s ∈ S a) ↦ ha.not_ge h.1) _).symm
  exact hdom.congr' (hle.mono fun a ha ↦ lintegral_congr_ae (.of_forall fun s ↦ by
    by_cases hs : (s : WithTop ι) ≤ u
    · simp [S, hs, hs.trans ha, ENNReal.zero_rpow_of_pos hp]
    · by_cases hsv : (s : WithTop ι) ≤ v a <;>
        simp [S, hs, hsv, ENNReal.zero_rpow_of_pos hp]))

/-- Natural-power form of `tendsto_lintegral_ite_le_rpow_of_tendsto_of_le` for `n ≠ 0`. -/
theorem tendsto_lintegral_ite_le_pow_of_tendsto_of_le [TopologicalSpace ι] [OrderTopology ι]
    [OpensMeasurableSpace ι] [l.IsCountablyGenerated] {f : ι → E} {v : β → WithTop ι}
    {u : WithTop ι} {n : ℕ} (hn : n ≠ 0) (hv : Tendsto v l (𝓝 u)) (hle : ∀ᶠ a in l, u ≤ v a)
    (hf : AEMeasurable (fun s ↦ ‖f s‖ₑ ^ n) μ) (hfin : ∫⁻ s, ‖f s‖ₑ ^ n ∂μ ≠ ∞) :
    Tendsto (fun a ↦ ∫⁻ s, ‖(if (s : WithTop ι) ≤ v a then f s else 0) -
      (if (s : WithTop ι) ≤ u then f s else 0)‖ₑ ^ n ∂μ) l (𝓝 0) := by
  simpa only [ENNReal.rpow_natCast] using tendsto_lintegral_ite_le_rpow_of_tendsto_of_le
    (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)) hv hle (by simpa only [ENNReal.rpow_natCast] using hf)
    (by simpa only [ENNReal.rpow_natCast] using hfin)

/-- For a time measure `μ` supported a.e. in `(-∞, T]` and random `WithTop` cutoffs `τ` with
`P {ω | τ a ω ≤ T} → 0` along `l`, the positive tail measures of the lower `p`-th power cutoff
error (`0 < p`) of any `H` tend to zero along `l`. -/
theorem tendsto_measure_lintegral_ite_le_rpow_of_tendsto_measure_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {τ : β → Ω → WithTop ι} {T : ι}
    (hτ : Tendsto (fun a ↦ P {ω | τ a ω ≤ T}) l (𝓝 0)) (H : ι → Ω → E) (hμ : ∀ᵐ s ∂μ, s ≤ T)
    {p : ℝ} (hp : 0 < p) {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun a ↦ P {ω | ε ≤ ∫⁻ s,
      ‖(if (s : WithTop ι) ≤ τ a ω then H s ω else 0) - H s ω‖ₑ ^ p ∂μ}) l (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hτ (fun _ ↦ zero_le) fun a ↦
    measure_mono fun ω (hω : ε ≤ _) ↦ by_contra fun hnot ↦ hε.not_ge <| by
      rwa [lintegral_congr_ae (g := fun _ ↦ 0) (hμ.mono fun s hs ↦ by
        simp [(WithTop.coe_le_coe.2 hs).trans (not_le.1 hnot).le,
          ENNReal.zero_rpow_of_pos hp]), lintegral_zero] at hω

/-- Natural-power form of `tendsto_measure_lintegral_ite_le_rpow_of_tendsto_measure_le`. -/
theorem tendsto_measure_lintegral_ite_le_pow_of_tendsto_measure_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {τ : β → Ω → WithTop ι} {T : ι}
    (hτ : Tendsto (fun a ↦ P {ω | τ a ω ≤ T}) l (𝓝 0)) (H : ι → Ω → E) (hμ : ∀ᵐ s ∂μ, s ≤ T)
    {k : ℕ} (hk : k ≠ 0) {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun a ↦ P {ω | ε ≤ ∫⁻ s,
      ‖(if (s : WithTop ι) ≤ τ a ω then H s ω else 0) - H s ω‖ₑ ^ k ∂μ}) l (𝓝 0) := by
  simpa only [ENNReal.rpow_natCast] using
    tendsto_measure_lintegral_ite_le_rpow_of_tendsto_measure_le
      hτ H hμ (Nat.cast_pos.2 (Nat.pos_of_ne_zero hk)) hε

end WithTopCutoff

end TauCeti
