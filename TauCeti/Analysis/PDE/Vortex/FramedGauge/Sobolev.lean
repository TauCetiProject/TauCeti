/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Basic
public import TauCeti.Analysis.Sobolev.BesselPotential.RealFunction
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The Sobolev framed gauge group of the plane

The framed plane vortex fields of class `H^k` form the affine space
`A_m^k = (a_m, α_m) + H^k(ℂ; iT*ℂ ⊕ ℂ)` (`TauCeti.Vortex.framedFieldSpace`). The gauge group
completed at the matching regularity consists of the circle-valued maps that differ from the
constant `1` by a function of class `H^(k+1)`:

`G_s = {u = 1 + h : h ∈ H^s(ℂ; ℂ), |u| = 1}`,  `s = k + 1`.

This file constructs `G_s` for every real `s > 1` (`TauCeti.Vortex.sobolevGaugeGroup`). Its
elements are continuous maps `u : ℂ → S¹`, so `|u| = 1` holds pointwise for the continuous
representative, and `h = u - 1` is recorded through its real and imaginary parts, which lie in the
real Sobolev function space `TemperedDistribution.realSobolevFunctions ℂ s 2`. For `u = 1 + h` and
`v = 1 + h'`,

`uv - 1 = h + h' + h h'`,  `u⁻¹ - 1 = conj h`,

so the group laws follow from the algebra property of `H^s(ℂ)` for `s > 1 = dim ℂ / 2`
(`TemperedDistribution.mul_mem_realSobolevFunctions`); inversion is complex conjugation because
`|u| = 1`. By the Sobolev embedding every element tends to `1` at infinity
(`TauCeti.Vortex.tendsto_cocompact_of_mem_sobolevGaugeGroup`), which is the framing condition
of the smooth framed gauge group `TauCeti.Vortex.framedGaugeGroup`; hence the smooth elements of
`G_s` are smooth framed gauges (`TauCeti.Vortex.mem_framedGaugeGroup_of_mem_sobolevGaugeGroup`).
The smooth framed group is not used to define `G_s`: its end condition imposes no square
integrability on `u - 1`. Smooth gauges equal to `1` outside a compact set lie in every `G_s`
(`TauCeti.Vortex.mem_sobolevGaugeGroup_of_hasCompactSupport`).

The groups decrease as `s` increases (`TauCeti.Vortex.sobolevGaugeGroup_mono`). No topology,
chart, or action of `G_s` on `A_m^(s-1)` is constructed here.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Module TemperedDistribution
open scoped Topology ContDiff

/-- `dim ℂ / 2 < s` for `1 < s`: the order range in which `H^s(ℂ)` is an algebra. -/
private theorem finrank_lt_two_mul {s : ℝ} (hs : 1 < s) : (finrank ℝ ℂ : ℝ) < 2 * s := by
  rw [Complex.finrank_real_complex]
  push_cast
  linarith

/-- The real part of `uv - 1` in terms of `h = u - 1` and `h' = v - 1`:
`Re (uv) - 1 = Re h + Re h' + Re h Re h' - Im h Im h'`. -/
private theorem re_mul_sub_one (u v : ℂ → Circle) :
    (fun z ↦ ((u * v) z : ℂ).re - 1) =
      (fun z ↦ (u z : ℂ).re - 1) + (fun z ↦ (v z : ℂ).re - 1) +
        (fun z ↦ (u z : ℂ).re - 1) * (fun z ↦ (v z : ℂ).re - 1) -
          (fun z ↦ (u z : ℂ).im) * (fun z ↦ (v z : ℂ).im) := by
  ext z
  simp only [Pi.mul_apply, Circle.coe_mul, mul_re, Pi.add_apply, Pi.sub_apply]
  ring

/-- The imaginary part of `uv` in terms of `h = u - 1` and `h' = v - 1`:
`Im (uv) = Im h + Im h' + (Re h) Im h' + Im h Re h'`. -/
private theorem im_mul (u v : ℂ → Circle) :
    (fun z ↦ ((u * v) z : ℂ).im) =
      (fun z ↦ (u z : ℂ).im) + (fun z ↦ (v z : ℂ).im) +
        (fun z ↦ (u z : ℂ).re - 1) * (fun z ↦ (v z : ℂ).im) +
          (fun z ↦ (u z : ℂ).im) * (fun z ↦ (v z : ℂ).re - 1) := by
  ext z
  simp only [Pi.mul_apply, Circle.coe_mul, mul_im, Pi.add_apply]
  ring

/-- **The Sobolev framed gauge group** `G_s = {u = 1 + h : h ∈ H^s(ℂ; ℂ), |u| = 1}`, `s > 1`:
continuous circle-valued maps on the plane whose real part minus one and imaginary part lie in
the real Sobolev space `H^s(ℂ)`. -/
def sobolevGaugeGroup (s : ℝ) (hs : 1 < s) : Subgroup (ℂ → Circle) where
  carrier := {u | Continuous u ∧ (fun z ↦ (u z : ℂ).re - 1) ∈ realSobolevFunctions ℂ s 2 ∧
    (fun z ↦ (u z : ℂ).im) ∈ realSobolevFunctions ℂ s 2}
  one_mem' := by
    refine ⟨continuous_const, ?_, ?_⟩ <;>
      simp only [Pi.one_apply, Circle.coe_one, one_re, one_im, sub_self] <;> exact zero_mem _
  mul_mem' := by
    rintro u v ⟨hu, hu₁, hu₂⟩ ⟨hv, hv₁, hv₂⟩
    have hmul {f g : ℂ → ℝ} (hf : f ∈ realSobolevFunctions ℂ s 2)
        (hg : g ∈ realSobolevFunctions ℂ s 2) : f * g ∈ realSobolevFunctions ℂ s 2 :=
      mul_mem_realSobolevFunctions (finrank_lt_two_mul hs) hf hg
    refine ⟨hu.mul hv, ?_, ?_⟩
    · rw [re_mul_sub_one]
      exact sub_mem (add_mem (add_mem hu₁ hv₁) (hmul hu₁ hv₁)) (hmul hu₂ hv₂)
    · rw [im_mul]
      exact add_mem (add_mem (add_mem hu₂ hv₂) (hmul hu₁ hv₂)) (hmul hu₂ hv₁)
  inv_mem' := by
    rintro u ⟨hu, hu₁, hu₂⟩
    refine ⟨hu.inv, ?_, ?_⟩
    · simpa only [Pi.inv_apply, Circle.coe_inv_eq_conj, conj_re] using hu₁
    · simpa only [Pi.inv_apply, Circle.coe_inv_eq_conj, conj_im, Pi.neg_def] using neg_mem hu₂

/-- Membership in `G_s`: continuity, and `Re u - 1, Im u ∈ H^s`. -/
@[simp]
theorem mem_sobolevGaugeGroup {s : ℝ} (hs : 1 < s) (u : ℂ → Circle) :
    u ∈ sobolevGaugeGroup s hs ↔ Continuous u ∧
      (fun z ↦ (u z : ℂ).re - 1) ∈ realSobolevFunctions ℂ s 2 ∧
        (fun z ↦ (u z : ℂ).im) ∈ realSobolevFunctions ℂ s 2 :=
  Iff.rfl

/-- The Sobolev gauge groups decrease as the order increases. -/
theorem sobolevGaugeGroup_mono {s s' : ℝ} (hs : 1 < s) (hs' : 1 < s') (h : s' ≤ s) :
    sobolevGaugeGroup s hs ≤ sobolevGaugeGroup s' hs' :=
  fun _ ⟨hu, hu₁, hu₂⟩ ↦
    ⟨hu, realSobolevFunctions_mono h hu₁, realSobolevFunctions_mono h hu₂⟩

/-- **Elements of `G_s` are framed.** By the Sobolev embedding `H^s(ℂ) ⊆ C₀(ℂ)` for `s > 1`, an
element of the Sobolev gauge group tends to one at infinity. -/
theorem tendsto_cocompact_of_mem_sobolevGaugeGroup {s : ℝ} {hs : 1 < s} {u : ℂ → Circle}
    (hu : u ∈ sobolevGaugeGroup s hs) : Tendsto u (cocompact ℂ) (𝓝 1) := by
  obtain ⟨hc, hu₁, hu₂⟩ := hu
  have hcoe : Continuous fun z ↦ (u z : ℂ) := continuous_subtype_val.comp hc
  have hre := tendsto_cocompact_of_mem_realSobolevFunctions (finrank_lt_two_mul hs) hu₁
    (continuous_re.comp hcoe |>.sub continuous_const)
  have him := tendsto_cocompact_of_mem_realSobolevFunctions (finrank_lt_two_mul hs) hu₂
    (continuous_im.comp hcoe)
  have h : Tendsto (fun z ↦ (u z : ℂ)) (cocompact ℂ) (𝓝 1) := by
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun z ↦ norm_le_abs_re_add_abs_im ((u z : ℂ) - 1)) ?_)
    simpa only [sub_re, one_re, sub_im, one_im, sub_zero, abs_zero, add_zero] using
      hre.abs.add him.abs
  exact tendsto_subtype_rng.2 h

/-- **Smooth elements of `G_s` are smooth framed gauges.** -/
theorem mem_framedGaugeGroup_of_mem_sobolevGaugeGroup {s : ℝ} {hs : 1 < s} {u : ℂ → Circle}
    (hu : u ∈ sobolevGaugeGroup s hs) (hsmooth : ContDiff ℝ ∞ fun z ↦ (u z : ℂ)) :
    u ∈ framedGaugeGroup :=
  (mem_framedGaugeGroup u).2 ⟨hsmooth, tendsto_cocompact_of_mem_sobolevGaugeGroup hu⟩

/-- **Compactly supported smooth gauges.** A smooth circle-valued map equal to one outside a
compact set lies in every Sobolev gauge group. -/
theorem mem_sobolevGaugeGroup_of_hasCompactSupport {s : ℝ} (hs : 1 < s) {u : ℂ → Circle}
    (hsmooth : ContDiff ℝ ∞ fun z ↦ (u z : ℂ)) (hc : HasCompactSupport fun z ↦ (u z : ℂ) - 1) :
    u ∈ sobolevGaugeGroup s hs := by
  refine ⟨continuous_induced_rng.2 hsmooth.continuous, ?_, ?_⟩
  · have hre : ContDiff ℝ ∞ fun z ↦ ((u z : ℂ) - 1).re := reCLM.contDiff.comp (hsmooth.sub
      contDiff_const)
    simpa only [sub_re, one_re] using
      mem_realSobolevFunctions_of_hasCompactSupport hre (hc.comp_left zero_re) s 2
  · have him : ContDiff ℝ ∞ fun z ↦ ((u z : ℂ) - 1).im := imCLM.contDiff.comp (hsmooth.sub
      contDiff_const)
    simpa only [sub_im, one_im, sub_zero] using
      mem_realSobolevFunctions_of_hasCompactSupport him (hc.comp_left zero_im) s 2

end TauCeti.Vortex
