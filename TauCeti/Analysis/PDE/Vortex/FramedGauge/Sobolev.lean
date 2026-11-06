/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Basic
import TauCeti.Analysis.PDE.Vortex.FieldSpace
import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# The Sobolev framed gauge group of plane vortex fields

For `s > 1` the Sobolev framed gauge group is

  `G_s = {u = 1 + h : h ∈ H^s(ℂ; ℂ), |u| = 1}`,

the Banach gauge group paired with the affine Sobolev space `A_m^(s-1)` of framed plane vortex
fields (`TauCeti.Vortex.framedFieldSpace`). As for those fields, `h` is taken in real
coordinates: both real functions `Re u - 1` and `Im u` lie in `H^s`
(`TemperedDistribution.realSobolevFunctions`), so the pair `(Re u - 1, Im u)` lies in
`H^s(ℂ; ℝ²)`, identified with `H^s(ℂ; ℂ)` through `h = (Re u - 1) + i Im u`. For
`s > 1 = dim ℂ / 2` an `H^s` function has a continuous representative, and the elements of `G_s`
are taken to be continuous circle-valued maps.

The group laws come from the algebra property of `H^s` above half the dimension
(`TemperedDistribution.mul_mem_realSobolevFunctions`): writing `u = 1 + h` and `v = 1 + k`,
`uv = 1 + (h + k + hk)`, and `u⁻¹ = conj u = 1 + conj h`. So `sobolevGaugeGroup s` is a subgroup
of the circle-valued maps on the plane.

By the Sobolev embedding into `C₀`, every element tends to one at infinity
(`TauCeti.Vortex.tendsto_cocompact_of_mem_sobolevGaugeGroup`), so the smooth elements of `G_s` are
smooth framed gauges (`TauCeti.Vortex.mem_framedGaugeGroup_of_mem_sobolevGaugeGroup`). Conversely,
smooth gauges equal to one off a compact set, such as `exp (i f)` for a compactly supported smooth
phase `f`, lie in every `G_s`. A smooth framed gauge in `TauCeti.Vortex.framedGaugeGroup` need
not lie in `G_s`: it only tends to one, possibly too slowly for `u - 1` to be square integrable.

This file constructs the group and its algebraic and asymptotic properties. The Banach charts of
`G_s`, which need a quantitative product estimate in `H^s`, and its action on the affine field
space `A_m^(s-1)` are not constructed here.

## Main declarations

* `TauCeti.Vortex.sobolevGaugeGroup`: the Sobolev framed gauge group `G_s`, `s > 1`.
* `TauCeti.Vortex.exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup`: for `u ∈ G_s`, the complex
  function `u - 1` lies in `H^s(ℂ; ℂ)`.
* `TauCeti.Vortex.sobolevGaugeGroup_mono`: `G_s ≤ G_s'` for `s' ≤ s`.
* `TauCeti.Vortex.tendsto_cocompact_of_mem_sobolevGaugeGroup`: elements of `G_s` tend to one at
  infinity.
* `TauCeti.Vortex.mem_framedGaugeGroup_of_mem_sobolevGaugeGroup`: smooth elements of `G_s` are
  smooth framed gauges.
* `TauCeti.Vortex.mem_sobolevGaugeGroup_of_hasCompactSupport`,
  `TauCeti.Vortex.exp_mem_sobolevGaugeGroup`: smooth gauges equal to one off a compact set lie in
  every `G_s`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* M. E. Taylor, *Partial Differential Equations III: Nonlinear Equations*, 2nd ed., Applied
  Mathematical Sciences 117, Springer, 2011, Chapter 13, §3 (the algebra `H^s`, `s > n / 2`).
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex ComplexConjugate Filter MeasureTheory Module TemperedDistribution
open scoped Topology ContDiff SchwartzMap

/-- The **Sobolev framed gauge group** `G_s = {u = 1 + h : h ∈ H^s(ℂ; ℂ), |u| = 1}`, for `s > 1`.
Its elements are the continuous circle-valued maps `u` on the plane such that the real
functions `Re u - 1` and `Im u` lie in `H^s`. -/
def sobolevGaugeGroup (s : ℝ) [hs : Fact (1 < s)] : Subgroup (ℂ → Circle) where
  carrier := {u | Continuous (fun z ↦ (u z : ℂ)) ∧
    (fun z ↦ (u z : ℂ).re - 1) ∈ realSobolevFunctions ℂ s 2 ∧
    (fun z ↦ (u z : ℂ).im) ∈ realSobolevFunctions ℂ s 2}
  one_mem' := by
    refine ⟨continuous_const, ?_, ?_⟩ <;>
    · simp only [Pi.one_apply, Circle.coe_one, one_re, one_im, sub_self]
      exact zero_mem (realSobolevFunctions ℂ s 2)
  mul_mem' := by
    rintro u v ⟨hu, hu₁, hu₂⟩ ⟨hv, hv₁, hv₂⟩
    have hs' := finrank_lt_two_mul hs.out
    -- With `u = (1 + a) + i b` and `v = (1 + c) + i d`, the real and imaginary parts of `u v`
    -- are `1 + (a + c + a c - b d)` and `b + d + a d + b c`.
    refine ⟨hu.mul hv, ?_, ?_⟩
    · convert add_mem (add_mem hu₁ hv₁) (sub_mem (mul_mem_realSobolevFunctions hs' hu₁ hv₁)
        (mul_mem_realSobolevFunctions hs' hu₂ hv₂)) using 1
      ext z
      simp only [Pi.mul_apply, Circle.coe_mul, mul_re, Pi.add_apply, Pi.sub_apply]
      ring
    · convert add_mem (add_mem hu₂ hv₂) (add_mem (mul_mem_realSobolevFunctions hs' hu₁ hv₂)
        (mul_mem_realSobolevFunctions hs' hu₂ hv₁)) using 1
      ext z
      simp only [Pi.mul_apply, Circle.coe_mul, mul_im, Pi.add_apply]
      ring
  inv_mem' := by
    rintro u ⟨hu, hu₁, hu₂⟩
    -- The inverse of a circle-valued map is its complex conjugate.
    simp only [Set.mem_ofPred_eq, Pi.inv_apply, Circle.coe_inv_eq_conj, conj_re, conj_im]
    exact ⟨continuous_conj.comp hu, hu₁, neg_mem hu₂⟩

variable {s : ℝ} [Fact (1 < s)]

/-- Membership in `G_s`: continuity and `H^s` regularity of `Re u - 1` and `Im u`. -/
@[simp]
theorem mem_sobolevGaugeGroup (u : ℂ → Circle) :
    u ∈ sobolevGaugeGroup s ↔ Continuous (fun z ↦ (u z : ℂ)) ∧
      (fun z ↦ (u z : ℂ).re - 1) ∈ realSobolevFunctions ℂ s 2 ∧
      (fun z ↦ (u z : ℂ).im) ∈ realSobolevFunctions ℂ s 2 :=
  Iff.rfl

/-- **Elements of `G_s` are `1 + h` with `h ∈ H^s(ℂ; ℂ)`.** For `u ∈ G_s`, the complex function
`u - 1` agrees almost everywhere with an `L²` function in Mathlib's Bessel-potential space
`H^s(ℂ; ℂ)`. -/
theorem exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup {u : ℂ → Circle}
    (hu : u ∈ sobolevGaugeGroup s) :
    ∃ h : Lp ℂ 2 (volume : Measure ℂ), h =ᵐ[volume] (fun z ↦ (u z : ℂ) - 1) ∧
      MemSobolev s 2 (h : 𝓢'(ℂ, ℂ)) := by
  obtain ⟨-, h₁, h₂⟩ := hu
  obtain ⟨a, ha, hae⟩ := mem_realSobolevFunctions.1 h₁
  obtain ⟨b, hb, hbe⟩ := mem_realSobolevFunctions.1 h₂
  refine ⟨ofRealCLM.compLp a + I • ofRealCLM.compLp b, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_add (ofRealCLM.compLp a) (I • ofRealCLM.compLp b),
      Lp.coeFn_smul I (ofRealCLM.compLp b), ofRealCLM.coeFn_compLp (p := 2) (μ := volume) a,
      ofRealCLM.coeFn_compLp (p := 2) (μ := volume) b, hae, hbe] with z h h' ha' hb' ha'' hb''
    rw [h, Pi.add_apply, h', Pi.smul_apply, ha', hb']
    apply Complex.ext <;> simp [ha'', hb'']
  · have e := map_add (Lp.toTemperedDistributionCLM ℂ (volume : Measure ℂ) 2)
      (ofRealCLM.compLp a) (I • ofRealCLM.compLp b)
    rw [map_smul, Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistributionCLM_apply,
      Lp.toTemperedDistributionCLM_apply] at e
    rw [e]
    exact (mem_realSobolevSubmodule.1 ha).add ((mem_realSobolevSubmodule.1 hb).smul I)

/-- The Sobolev framed gauge groups decrease as the order increases. -/
theorem sobolevGaugeGroup_mono {s' : ℝ} [Fact (1 < s')] (h : s' ≤ s) :
    sobolevGaugeGroup s ≤ sobolevGaugeGroup s' :=
  fun _ ⟨hu, h₁, h₂⟩ ↦ ⟨hu, realSobolevFunctions_mono h h₁, realSobolevFunctions_mono h h₂⟩

/-- **Elements of `G_s` tend to one at infinity**, by the Sobolev embedding of `H^s` into the
continuous functions vanishing at infinity. -/
theorem tendsto_cocompact_of_mem_sobolevGaugeGroup {u : ℂ → Circle}
    (hu : u ∈ sobolevGaugeGroup s) : Tendsto u (cocompact ℂ) (𝓝 1) := by
  obtain ⟨hc, h₁, h₂⟩ := hu
  have hs := finrank_lt_two_mul (Fact.out : 1 < s)
  have hre := tendsto_cocompact_of_mem_realSobolevFunctions hs h₁
    ((continuous_re.comp hc).sub continuous_const)
  have him := tendsto_cocompact_of_mem_realSobolevFunctions hs h₂ (continuous_im.comp hc)
  -- Reassemble `u = 1 + (Re u - 1) + i Im u` and use that `Circle` carries the subspace topology.
  have hC : Tendsto (fun z ↦ (u z : ℂ)) (cocompact ℂ) (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (1 : ℂ))).add (continuous_ofReal.tendsto 0 |>.comp hre)).add
      ((continuous_ofReal.tendsto 0 |>.comp him).mul_const I)
    simp only [ofReal_zero, add_zero, zero_mul] at this
    refine this.congr fun z ↦ ?_
    simp only [Function.comp_apply, ofReal_sub, ofReal_one]
    conv_rhs => rw [← re_add_im (u z : ℂ)]
    ring
  exact Topology.IsInducing.subtypeVal.tendsto_nhds_iff.2 hC

/-- **Smooth elements of `G_s` are smooth framed gauges.** -/
theorem mem_framedGaugeGroup_of_mem_sobolevGaugeGroup {u : ℂ → Circle}
    (hu : u ∈ sobolevGaugeGroup s) (hsmooth : ContDiff ℝ ∞ (fun z ↦ (u z : ℂ))) :
    u ∈ framedGaugeGroup :=
  (mem_framedGaugeGroup u).2 ⟨hsmooth, tendsto_cocompact_of_mem_sobolevGaugeGroup hu⟩

/-- **Compactly supported gauges.** A smooth circle-valued map equal to one off a compact set lies
in every Sobolev framed gauge group. -/
theorem mem_sobolevGaugeGroup_of_hasCompactSupport {u : ℂ → Circle}
    (hsmooth : ContDiff ℝ ∞ (fun z ↦ (u z : ℂ)))
    (hc : HasCompactSupport (fun z ↦ (u z : ℂ) - 1)) : u ∈ sobolevGaugeGroup s := by
  have hre : ContDiff ℝ ∞ (fun z ↦ (u z : ℂ).re - 1) :=
    (reCLM.contDiff.comp hsmooth).sub contDiff_const
  have him : ContDiff ℝ ∞ (fun z ↦ (u z : ℂ).im) := imCLM.contDiff.comp hsmooth
  refine ⟨hsmooth.continuous, mem_realSobolevFunctions_of_hasCompactSupport hre ?_ s 2,
    mem_realSobolevFunctions_of_hasCompactSupport him ?_ s 2⟩
  · simpa only [Function.comp_def, sub_re, one_re] using hc.comp_left (g := re) zero_re
  · simpa only [Function.comp_def, sub_im, one_im, sub_zero] using hc.comp_left (g := im) zero_im

/-- A smooth compactly supported phase `f` gives the gauge `exp (i f)` in every Sobolev framed
gauge group. -/
theorem exp_mem_sobolevGaugeGroup {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (fun z ↦ Circle.exp (f z)) ∈ sobolevGaugeGroup s := by
  refine mem_sobolevGaugeGroup_of_hasCompactSupport ?_ ?_
  · simpa only [Circle.coe_exp, Function.comp_def, ofRealCLM_apply] using
      ((ofRealCLM.contDiff.comp hf).mul (contDiff_const (c := I))).cexp
  · refine hc.mono fun z hz h0 ↦ hz ?_
    simp [h0]

end TauCeti.Vortex
