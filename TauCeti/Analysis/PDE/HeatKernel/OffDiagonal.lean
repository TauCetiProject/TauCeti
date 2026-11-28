/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.Semigroup
import TauCeti.Analysis.Convolution.Young
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Off-diagonal estimates for the heat semigroup

The heat flow improves integrability from `Lᵖ` to every `Lᵠ` with `p ≤ q`, with the
scale-invariant bound `(4πt)^(-(d/2)(1/p - 1/q))`. Young's convolution inequality and
the Gaussian kernel bound give this estimate for Banach-space-valued functions, including
the endpoint `q = ∞`. These estimates supply the integrability gain used in derivative
smoothing bounds.

For a fixed `f ∈ Lᵖ` with `p < q`, the normalized norm `t^((d/2)(1/p - 1/q)) ‖e^{tΔ} f‖_q`
tends to `0` as `t → 0⁺` (`tendsto_rpow_mul_eLpNorm_heatSemigroup_nhdsGT_zero`). This little-o
refinement of the scale-invariant bound is the small-time input of Kato's `Lᵈ` theory for the
Navier–Stokes equations.

## References

* T. Kato, *Strong `Lᵖ`-solutions of the Navier–Stokes equation in `ℝᵐ`, with applications to
  weak solutions*, Math. Z. **187** (1984), 471–480.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Real
open scoped Topology
open scoped Convolution ENNReal NNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Off-diagonal heat estimate.** For `1 ≤ p ≤ q ≤ ∞`, convolution with `K_t`
maps `Lᵖ` to `Lᵠ` with constant `(4πt)^(-(d/2)(1/p - 1/q))`.
The extended norm formulation also applies when the input norm is infinite. -/
theorem eLpNorm_heatKernel_convolution_le {t : ℝ} (ht : 0 < t) {p q : ℝ≥0∞}
    (hp : 1 ≤ p) (hpq : p ≤ q) {f : E → F} (hf : AEStronglyMeasurable f volume) :
    eLpNorm (heatKernel t ⋆ f) q volume ≤
      ENNReal.ofReal ((4 * π * t) ^ (-(Module.finrank ℝ E : ℝ) / 2 *
        (1 / p.toReal - 1 / q.toReal))) * eLpNorm f p volume := by
  obtain ⟨r, hr, hrp, he⟩ := ENNReal.exists_inv_add_inv_eq_one_add_inv hp hpq
  have h := eLpNorm_convolution_le_of_inv_add_inv_eq (.lsmul ℝ ℝ) hr hp hrp
    ((contDiff_heatKernel (k := ⊤) t).continuous.aestronglyMeasurable) hf
  grw [ContinuousLinearMap.opENorm_lsmul_le, one_mul, eLpNorm_heatKernel_le ht hr] at h
  simpa only [he] using h

variable [CompleteSpace F]

/-- At positive times the `Lᵖ` heat semigroup satisfies the full `Lᵖ`–`Lᵠ` estimate,
including `q = ∞`. -/
theorem eLpNorm_heatSemigroup_le {p q : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hpq : p ≤ q) {t : ℝ≥0} (ht : t ≠ 0) (f : Lp F p (volume : Measure E)) :
    eLpNorm (heatSemigroup hp t f) q volume ≤
      ENNReal.ofReal ((4 * π * (t : ℝ)) ^ (-(Module.finrank ℝ E : ℝ) / 2 *
        (1 / p.toReal - 1 / q.toReal))) * eLpNorm f p volume := by
  rw [eLpNorm_congr_ae (heatSemigroup_ae_eq_convolution_coeFn hp ht f)]
  exact eLpNorm_heatKernel_convolution_le (by positivity) Fact.out hpq (Lp.aestronglyMeasurable f)

/-- Heat evolution sends finite-`p` data to every larger `Lᵠ` space at positive times. -/
theorem memLp_heatSemigroup {p q : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hpq : p ≤ q) {t : ℝ≥0} (ht : t ≠ 0) (f : Lp F p (volume : Measure E)) :
    MemLp (heatSemigroup hp t f : E → F) q volume :=
  (eLpNorm_heatSemigroup_le hp hpq ht f).trans_lt (by finiteness)

/-- For every `g ∈ Lᵖ`, the normalized `Lᵠ` norm `t^α ‖e^{tΔ} f‖_q` with
`α = (d/2)(1/p - 1/q)` is at most `t^α ‖g‖_q + (4π)^(-α) ‖f - g‖_p`. -/
private theorem rpow_mul_eLpNorm_heatSemigroup_le {p q : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hpq : p ≤ q) {t : ℝ≥0} (ht : t ≠ 0) (f g : Lp F p (volume : Measure E)) :
    ENNReal.ofReal ((t : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2 * (1 / p.toReal - 1 / q.toReal))) *
        eLpNorm (heatSemigroup hp t f) q volume ≤
      ENNReal.ofReal ((t : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2 *
          (1 / p.toReal - 1 / q.toReal))) * eLpNorm g q volume +
        ENNReal.ofReal ((4 * π) ^ (-((Module.finrank ℝ E : ℝ) / 2 *
          (1 / p.toReal - 1 / q.toReal)))) * eLpNorm (f - g) p volume := by
  set α : ℝ := (Module.finrank ℝ E : ℝ) / 2 * (1 / p.toReal - 1 / q.toReal)
  have hq : 1 ≤ q := (Fact.out : 1 ≤ p).trans hpq
  have ht' : (0 : ℝ) < t := by positivity
  -- The power `t^α` cancels the time dependence of the constant `(4πt)^(-α)`.
  have hc : ENNReal.ofReal ((t : ℝ) ^ α) * ENNReal.ofReal ((4 * π * t) ^ (-α)) =
      ENNReal.ofReal ((4 * π) ^ (-α)) := by
    rw [← ENNReal.ofReal_mul (by positivity), Real.mul_rpow (by positivity) ht'.le,
      mul_left_comm, Real.rpow_neg ht'.le, mul_inv_cancel₀ (by positivity), mul_one]
  have hsplit : heatSemigroup hp t f = heatSemigroup hp t g + heatSemigroup hp t (f - g) := by
    rw [← map_add, add_sub_cancel]
  have hg : eLpNorm (heatSemigroup hp t g) q volume ≤ eLpNorm g q volume := by
    rw [eLpNorm_congr_ae (heatSemigroup_ae_eq_convolution_coeFn hp ht g)]
    simpa using eLpNorm_heatKernel_convolution_le ht' hq le_rfl (Lp.aestronglyMeasurable g)
  have hfg := eLpNorm_heatSemigroup_le hp hpq ht (f - g)
  rw [neg_div, neg_mul] at hfg
  rw [hsplit, eLpNorm_congr_ae (Lp.coeFn_add _ _), ← hc, mul_assoc, ← mul_add]
  gcongr
  exact (eLpNorm_add_le hq).trans (add_le_add hg hfg)

/-- **Small-time vanishing of the off-diagonal heat estimate.** For `1 ≤ p < q ≤ ∞` with
`p < ∞` and a fixed `f ∈ Lᵖ`, the normalized norm `t^((d/2)(1/p - 1/q)) ‖e^{tΔ} f‖_q` tends
to `0` as `t → 0⁺`. The space must be nontrivial: in dimension `0` the normalizing power is `1`
and the heat flow is the identity. -/
theorem tendsto_rpow_mul_eLpNorm_heatSemigroup_nhdsGT_zero [Nontrivial E] {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p ≠ ∞) (hpq : p < q) (f : Lp F p (volume : Measure E)) :
    Tendsto (fun t : ℝ≥0 ↦ ENNReal.ofReal ((t : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2 *
        (1 / p.toReal - 1 / q.toReal))) * eLpNorm (heatSemigroup hp t f) q volume)
      (𝓝[>] 0) (𝓝 0) := by
  set α : ℝ := (Module.finrank ℝ E : ℝ) / 2 * (1 / p.toReal - 1 / q.toReal)
  have hp0 : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  have hα : 0 < α := by
    have hd : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast Module.finrank_pos
    have hpq' : 1 / q.toReal < 1 / p.toReal := by
      rcases eq_or_ne q ∞ with rfl | hq
      · simpa using hp0
      · exact one_div_lt_one_div_of_lt hp0 ((ENNReal.toReal_lt_toReal hp hq).2 hpq)
    exact mul_pos (half_pos hd) (sub_pos.2 hpq')
  set c : ℝ≥0∞ := ENNReal.ofReal ((4 * π) ^ (-α))
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε.ne').ne'
  obtain ⟨g, hgc, hfg, hg, hgp⟩ := (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le hp
    (ENNReal.div_pos_iff.2 ⟨hε2, ENNReal.ofReal_ne_top⟩).ne'
  -- On the compactly supported continuous approximant the normalized flow tends to zero.
  have hlim : Tendsto (fun t : ℝ≥0 ↦ ENNReal.ofReal ((t : ℝ) ^ α) * eLpNorm g q volume)
      (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous fun t : ℝ≥0 ↦ ENNReal.ofReal ((t : ℝ) ^ α) :=
      ENNReal.continuous_ofReal.comp
        ((Real.continuous_rpow_const hα.le).comp NNReal.continuous_coe)
    simpa [Real.zero_rpow hα.ne'] using
      (ENNReal.Tendsto.mul_const (hcont.tendsto 0)
        (.inr (hg.memLp_of_hasCompactSupport hgc).eLpNorm_ne_top)).mono_left nhdsWithin_le_nhds
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hlim _ (ENNReal.half_pos hε.ne'),
    self_mem_nhdsWithin] with t hgt (ht : 0 < t)
  have hrem : eLpNorm (⇑f - ⇑(hgp.toLp g)) p volume = eLpNorm (⇑f - g) p volume :=
    eLpNorm_congr_ae ((hgp.coeFn_toLp).mono fun x hx ↦ by simp [hx])
  calc _ ≤ ENNReal.ofReal ((t : ℝ) ^ α) * eLpNorm (hgp.toLp g) q volume +
        c * eLpNorm (f - hgp.toLp g) p volume :=
        rpow_mul_eLpNorm_heatSemigroup_le hp hpq.le ht.ne' f (hgp.toLp g)
    _ ≤ ε / 2 + ε / 2 := by
        rw [eLpNorm_congr_ae (hgp.coeFn_toLp), eLpNorm_congr_ae (Lp.coeFn_sub _ _), hrem]
        exact add_le_add hgt ((mul_le_mul_right hfg c).trans ENNReal.mul_div_le)
    _ = ε := ENNReal.add_halves ε

end TauCeti
