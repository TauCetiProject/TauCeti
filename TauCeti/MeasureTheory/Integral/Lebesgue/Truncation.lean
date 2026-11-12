/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
-- `Mathlib.Analysis.SpecialFunctions.Pow.Continuity` and
-- `Mathlib.MeasureTheory.Function.SpecialFunctions.Basic` are imported privately: they supply the
-- continuity and measurability of `x ↦ x ^ q` on `ℝ≥0∞` inside the proof of
-- `TauCeti.lintegral_rpow_le_of_forall_le`.
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Lebesgue integrals of truncations

The truncations `min f M` of a function `f : α → ℝ≥0∞` at finite levels `M` increase to `f`, so by
monotone convergence their Lebesgue integrals tend to that of `f` as `M → ∞`. Neither `f` nor its
integral needs to be finite.

A function `f : α → ℝ≥0∞` of finite Lebesgue integral exceeds a large constant `M` only by an
amount of small integral: `∫⁻ x, f x - M ∂μ → 0` as `M → ∞`. The excess and the truncation
`min f M` add up to `f`, so by superadditivity of the integral the integral of the excess is at
most `∫⁻ f - ∫⁻ min f M`, which tends to `0` by monotone convergence for the truncations.

Cutting the truncations off outside the sets spanning a σ-finite measure also makes every
power of them integrable, so a bound on `∫⁻ φ ^ q` proved for all `φ ≤ G` with `∫⁻ φ ^ q`
finite passes to `∫⁻ G ^ q`. This is the usual way to divide an inequality by a power of the
quantity being estimated.

## Main statements

* `TauCeti.tendsto_lintegral_min_atTop`: `∫⁻ x, min (f x) M ∂μ → ∫⁻ x, f x ∂μ` as `M → ∞`.
* `TauCeti.tendsto_lintegral_tsub_atTop`: the integral of the excess of `f` over the constant `M`
  tends to `0` as `M → ∞`.
* `TauCeti.lintegral_enorm_rpow_eq_setLIntegral`: the `q`-th power integral of a truncation to a
  measurable set is the truncated integral.
* `TauCeti.lintegral_rpow_le_of_forall_le`: a bound on `∫⁻ φ ^ q` for the measurable `φ ≤ G` with
  `∫⁻ φ ^ q` finite is a bound on `∫⁻ G ^ q`.
* `TauCeti.measurable_rpow_mul_setLIntegral_lt`, `TauCeti.measurable_rpow_mul_setLIntegral_le`:
  the weighted upper and lower truncated integrals of `f ^ q` are measurable in the height.
-/

public section

namespace TauCeti

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Integrals of truncations.** For `f : α → ℝ≥0∞`, the integrals of its truncations `min f M`
tend to the integral of `f` as the finite level `M` tends to `∞`, whether or not that integral is
finite. -/
theorem tendsto_lintegral_min_atTop {f : α → ℝ≥0∞} :
    Tendsto (fun M : ℝ≥0 ↦ ∫⁻ x, min (f x) M ∂μ) atTop (𝓝 (∫⁻ x, f x ∂μ)) := by
  -- Replace `f` by a measurable minorant with the same integral.
  obtain ⟨g, hgm, hgf, hint⟩ := exists_measurable_le_lintegral_eq μ f
  rw [hint]
  -- Monotone convergence along integer levels for `g`; the integral of `min f M` lies between
  -- the integral of `min g ⌊M⌋₊` and the integral of `f`.
  have hnat : Tendsto (fun n : ℕ ↦ ∫⁻ x, min (g x) n ∂μ) atTop (𝓝 (∫⁻ x, g x ∂μ)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun _ ↦ (hgm.min measurable_const).aemeasurable)
      (.of_forall fun _ _ _ hmn ↦ min_le_min_left _ (by exact_mod_cast hmn))
      (.of_forall fun x ↦ ?_)
    simpa using tendsto_const_nhds.min ENNReal.tendsto_nat_nhds_top
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (hnat.comp tendsto_nat_floor_atTop)
    tendsto_const_nhds (fun M ↦ lintegral_mono fun x ↦ min_le_min (hgf x) ?_)
    fun _ ↦ (lintegral_mono fun _ ↦ min_le_left _ _).trans_eq hint
  simpa using ENNReal.coe_le_coe.2 (Nat.floor_le (a := M) zero_le)

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

/-- The `q`-th power integral of a truncation of `f` is a truncated integral of `‖f‖ ^ q`. -/
theorem lintegral_enorm_rpow_eq_setLIntegral {E : Type*} [TopologicalSpace E]
    [ESeminormedAddMonoid E] {q : ℝ} {f g : α → E} {R : Set α} (hR : MeasurableSet R)
    (hg : g =ᵐ[μ] R.indicator f) (hq : 0 < q) :
    ∫⁻ x, ‖g x‖ₑ ^ q ∂μ = ∫⁻ x in R, ‖f x‖ₑ ^ q ∂μ := by
  rw [← lintegral_indicator hR]
  refine lintegral_congr_ae ?_
  filter_upwards [hg] with x hx
  by_cases hxR : x ∈ R <;> simp [hx, hxR, ENNReal.zero_rpow_of_pos hq]

/-- The case of `TauCeti.lintegral_rpow_le_of_forall_le` for a measurable `G`: the truncations
`min G N`, cut off outside the `N`-th spanning set of `μ`, have finite `∫⁻ φ ^ q` and increase to
`G`. -/
private theorem lintegral_rpow_le_of_forall_le_of_measurable [SigmaFinite μ] {G : α → ℝ≥0∞}
    (hG : Measurable G)
    {q : ℝ} (hq : 0 < q) {C : ℝ≥0∞} (h : ∀ φ : α → ℝ≥0∞, Measurable φ → (∀ x, φ x ≤ G x) →
      ∫⁻ x, φ x ^ q ∂μ ≠ ∞ → ∫⁻ x, φ x ^ q ∂μ ≤ C) :
    ∫⁻ x, G x ^ q ∂μ ≤ C := by
  let φ : ℕ → α → ℝ≥0∞ := fun N => (spanningSets μ N).indicator fun x => min (G x) N
  have hφm (N : ℕ) : Measurable (φ N) :=
    (hG.min measurable_const).indicator (measurableSet_spanningSets μ N)
  have hφG (N : ℕ) (x : α) : φ N x ≤ G x := indicator_le (fun x _ => min_le_left _ _) x
  have hφfin (N : ℕ) : ∫⁻ x, φ N x ^ q ∂μ ≠ ∞ := by
    refine ne_top_of_le_ne_top
      (b := ∫⁻ x, (spanningSets μ N).indicator (fun _ => (N : ℝ≥0∞) ^ q) x ∂μ) ?_
      (lintegral_mono fun x => ?_)
    · rw [lintegral_indicator_const (measurableSet_spanningSets μ N)]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hq.le (by simp))
        (measure_spanningSets_lt_top μ N).ne
    · by_cases hx : x ∈ spanningSets μ N
      · simp only [φ, indicator_of_mem hx]
        exact ENNReal.rpow_le_rpow (min_le_right _ _) hq.le
      · simp [φ, indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hq]
  have hφmono : Monotone φ := fun N N' h x => by
    by_cases hx : x ∈ spanningSets μ N
    · have hx' : x ∈ spanningSets μ N' := monotone_spanningSets μ h hx
      simp only [φ, indicator_of_mem hx, indicator_of_mem hx']
      exact min_le_min_left _ (by exact_mod_cast h)
    · simp [φ, indicator_of_notMem hx]
  -- The truncations increase to `G` pointwise, hence their `q`-th powers increase to `G ^ q`.
  have hsup (x : α) : G x ^ q = ⨆ N, φ N x ^ q := by
    have hGx : G x = ⨆ N, φ N x := by
      refine le_antisymm (le_of_forall_lt fun c hc => ?_) (iSup_le fun N => hφG N x)
      obtain ⟨N₁, hN₁⟩ := ENNReal.exists_nat_gt (hc.trans_le le_top).ne
      obtain ⟨N₂, hN₂⟩ := mem_iUnion.1 ((iUnion_spanningSets μ).symm ▸ mem_univ x)
      have hx : x ∈ spanningSets μ (max N₁ N₂) := monotone_spanningSets μ (le_max_right _ _) hN₂
      refine lt_iSup_iff.2 ⟨max N₁ N₂, ?_⟩
      simp only [φ, indicator_of_mem hx]
      exact lt_min hc (hN₁.trans_le (by exact_mod_cast le_max_left N₁ N₂))
    rw [hGx]
    exact Monotone.map_iSup_of_continuousAt ENNReal.continuous_rpow_const.continuousAt
      (ENNReal.monotone_rpow_of_nonneg hq.le) (by simp [hq])
  calc ∫⁻ x, G x ^ q ∂μ = ∫⁻ x, ⨆ N, φ N x ^ q ∂μ := by simp_rw [hsup]
    _ = ⨆ N, ∫⁻ x, φ N x ^ q ∂μ :=
        lintegral_iSup (fun N => (hφm N).pow_const q) fun N N' h x =>
          ENNReal.rpow_le_rpow (hφmono h x) hq.le
    _ ≤ C := iSup_le fun N => h (φ N) (hφm N) (hφG N) (hφfin N)

/-- **Monotone convergence through truncations.** For a σ-finite measure `μ` and `0 < q`, if
`∫⁻ φ ^ q ≤ C` for every measurable `φ ≤ G` with `∫⁻ φ ^ q` finite, then `∫⁻ G ^ q ≤ C`, with no
measurability assumption on `G`. -/
theorem lintegral_rpow_le_of_forall_le [SigmaFinite μ] {G : α → ℝ≥0∞} {q : ℝ} (hq : 0 < q)
    {C : ℝ≥0∞} (h : ∀ φ : α → ℝ≥0∞, Measurable φ → (∀ x, φ x ≤ G x) →
      ∫⁻ x, φ x ^ q ∂μ ≠ ∞ → ∫⁻ x, φ x ^ q ∂μ ≤ C) :
    ∫⁻ x, G x ^ q ∂μ ≤ C := by
  -- `G ^ q` has a measurable minorant `g` with the same integral, and `g ^ (1 / q)` is a
  -- measurable minorant of `G`.
  obtain ⟨g, hgm, hgG, hint⟩ := exists_measurable_le_lintegral_eq μ (fun x ↦ G x ^ q)
  have hgG' (x : α) : g x ^ q⁻¹ ≤ G x :=
    (ENNReal.rpow_le_rpow (hgG x) (inv_nonneg.2 hq.le)).trans_eq (ENNReal.rpow_rpow_inv hq.ne' _)
  rw [hint]
  calc ∫⁻ x, g x ∂μ = ∫⁻ x, (g x ^ q⁻¹) ^ q ∂μ := by
        simp_rw [ENNReal.rpow_inv_rpow hq.ne']
    _ ≤ C := lintegral_rpow_le_of_forall_le_of_measurable (hgm.pow_const _) hq
        (fun φ hφ hφg => h φ hφ fun x => (hφg x).trans (hgG' x))

/-- The weighted upper truncated integral of `f ^ q` is measurable in the height: it is the product
of a measurable function and a monotone or antitone one. -/
theorem measurable_rpow_mul_setLIntegral_lt {f : α → ℝ≥0∞} {c : ℝ} (q s : ℝ) :
    Measurable fun t : ℝ => ENNReal.ofReal (t ^ s) *
      ∫⁻ x in {x | ENNReal.ofReal (c * t) < f x}, f x ^ q ∂μ := by
  refine ((measurable_id.pow measurable_const).ennreal_ofReal).mul ?_
  rcases le_total 0 c with hc | hc
  · refine Antitone.measurable fun t₁ t₂ ht => lintegral_mono_set fun x hx => ?_
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by nlinarith)) hx
  · refine Monotone.measurable fun t₁ t₂ ht => lintegral_mono_set fun x hx => ?_
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by nlinarith)) hx

/-- The weighted lower truncated integral of `f ^ q` is measurable in the height: it is the product
of a measurable function and a monotone or antitone one. -/
theorem measurable_rpow_mul_setLIntegral_le {f : α → ℝ≥0∞} {c : ℝ} (q s : ℝ) :
    Measurable fun t : ℝ => ENNReal.ofReal (t ^ s) *
      ∫⁻ x in {x | f x ≤ ENNReal.ofReal (c * t)}, f x ^ q ∂μ := by
  refine ((measurable_id.pow measurable_const).ennreal_ofReal).mul ?_
  rcases le_total 0 c with hc | hc
  · refine Monotone.measurable fun t₁ t₂ ht => lintegral_mono_set fun x hx => ?_
    exact le_trans hx (ENNReal.ofReal_le_ofReal (by nlinarith))
  · refine Antitone.measurable fun t₁ t₂ ht => lintegral_mono_set fun x hx => ?_
    exact le_trans hx (ENNReal.ofReal_le_ofReal (by nlinarith))

end TauCeti
