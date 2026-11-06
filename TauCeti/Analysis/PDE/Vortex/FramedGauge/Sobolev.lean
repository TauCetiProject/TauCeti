/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Basic
import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# The Sobolev framed gauge group of plane vortices

For a real order `s > 1` the Sobolev framed gauge group `G_s` (`sobolevGaugeGroup`) consists of
the continuous circle-valued maps `u` on the plane with `u - 1 ∈ H^s(ℂ; ℂ)`: the real functions
`Re u - 1` and `Im u` lie in the Bessel-potential space `H^s`
(`TemperedDistribution.realSobolevFunctions`). Writing `u = 1 + h`, this is the group
`{1 + h : h ∈ H^s, |1 + h| = 1}`, with `u` the continuous representative. The gauge group of
the field space `A_m^k` of framed degree-`m` vortices (`TauCeti.Vortex.framedFieldSpace`) is
`G_(k+1)`.

Since `H^s(ℂ)` is an algebra for `s > 1`, the products `(1 + h)(1 + g) = 1 + (h + g + h g)` stay
in the group, and the inverse is the complex conjugate `1 + conj h`. The Sobolev embedding gives
the end condition `u → 1` at infinity, so the smooth elements of `G_s` are smooth framed gauges
(`TauCeti.Vortex.framedGaugeGroup`); they form the subgroup `G_s ⊓ framedGaugeGroup`. Conversely,
smooth gauges with `u - 1` compactly supported, such as `exp (i f)` for a smooth compactly
supported phase `f`, lie in every `G_s`. A smooth framed gauge need not lie in `G_s`: a phase
with a `1 / |z|` tail is not square integrable on the plane.

For a `C¹` gauge `u ∈ G_(s+1)`, the real one-form `Im (u⁻¹ du)` (`TauCeti.Vortex.gaugeForm`)
has coefficients in `H^s`. Its product with `i` is the connection increment `u⁻¹ du` of the
action `(a, α) ↦ (a - u⁻¹ du, u α)`, so the `C¹` elements of `G_(s+1)` preserve the connection
part of `A_m^s`.

No topology or Banach Lie group charts on `G_s` are constructed here, and the action on the
section part of `A_m^s`, which needs multiplication of `H^s` by the bounded reference section,
is not treated.

## Main definitions

* `TauCeti.Vortex.sobolevGaugeGroup hs`: the group `G_s`, `s > 1`, as a subgroup of `ℂ → Circle`.

## Main results

* `TauCeti.Vortex.exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup`: for `u ∈ G_s`, the complex
  function `u - 1` lies in `H^s(ℂ; ℂ)`.
* `TauCeti.Vortex.tendsto_cocompact_of_mem_sobolevGaugeGroup`: elements of `G_s` tend to one at
  infinity.
* `TauCeti.Vortex.mem_sobolevGaugeGroup_inf_framedGaugeGroup`: the smooth subgroup of `G_s` is
  `G_s ⊓ framedGaugeGroup`.
* `TauCeti.Vortex.mem_sobolevGaugeGroup_of_hasCompactSupport`,
  `TauCeti.Vortex.exp_mem_sobolevGaugeGroup`: compactly supported smooth gauges lie in `G_s`.
* `TauCeti.Vortex.gaugeForm_apply_mem_realSobolevFunctions`: for a `C¹` gauge in `G_(s+1)`,
  `Im (u⁻¹ du)` has coefficients in `H^s`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex ComplexConjugate Filter Module TemperedDistribution
open scoped ContDiff Topology

/-- **The Sobolev framed gauge group `G_s`**, `s > 1`: the continuous circle-valued maps `u` on
the plane with `u - 1 ∈ H^s(ℂ; ℂ)`, that is, with `Re u - 1` and `Im u` in `H^s`. -/
def sobolevGaugeGroup {s : ℝ} (hs : 1 < s) : Subgroup (ℂ → Circle) where
  carrier := {u | Continuous u ∧ (fun z ↦ (u z : ℂ).re - 1) ∈ realSobolevFunctions ℂ s 2 ∧
    (fun z ↦ (u z : ℂ).im) ∈ realSobolevFunctions ℂ s 2}
  one_mem' := by
    refine ⟨continuous_const, ?_, ?_⟩ <;>
    · convert zero_mem (realSobolevFunctions ℂ s 2) using 1
      ext z
      simp
  mul_mem' := by
    rintro u v ⟨hu, hu₁, hu₂⟩ ⟨hv, hv₁, hv₂⟩
    have hmul {f g : ℂ → ℝ} (hf : f ∈ realSobolevFunctions ℂ s 2)
        (hg : g ∈ realSobolevFunctions ℂ s 2) : f * g ∈ realSobolevFunctions ℂ s 2 :=
      mul_mem_realSobolevFunctions (finrank_real_complex_lt_two_mul hs) hf hg
    -- With `u = (1 + a) + i b` and `v = (1 + c) + i d`, the product is
    -- `(1 + (a c + a + c - b d)) + i (a d + d + b c + b)`.
    refine ⟨hu.mul hv, ?_, ?_⟩
    · convert add_mem (add_mem (add_mem (hmul hu₁ hv₁) hu₁) hv₁) (neg_mem (hmul hu₂ hv₂))
        using 1
      ext z
      simp only [Pi.mul_apply, Circle.coe_mul, mul_re, Pi.add_apply, Pi.neg_apply]
      ring
    · convert add_mem (add_mem (add_mem (hmul hu₁ hv₂) hv₂) (hmul hu₂ hv₁)) hu₂ using 1
      ext z
      simp only [Pi.mul_apply, Circle.coe_mul, mul_im, Pi.add_apply]
      ring
  inv_mem' := by
    rintro u ⟨hu, hu₁, hu₂⟩
    refine ⟨hu.inv, ?_, ?_⟩
    · simpa only [Pi.inv_apply, Circle.coe_inv_eq_conj, conj_re] using hu₁
    · convert neg_mem hu₂ using 1
      ext z
      simp

/-- Membership in `G_s`: continuity, and `Re u - 1`, `Im u` in `H^s`. -/
@[simp]
theorem mem_sobolevGaugeGroup {s : ℝ} (hs : 1 < s) (u : ℂ → Circle) :
    u ∈ sobolevGaugeGroup hs ↔ Continuous u ∧
      (fun z ↦ (u z : ℂ).re - 1) ∈ realSobolevFunctions ℂ s 2 ∧
      (fun z ↦ (u z : ℂ).im) ∈ realSobolevFunctions ℂ s 2 :=
  Iff.rfl

open MeasureTheory in
open scoped SchwartzMap in
/-- **Elements of `G_s` are `1 + h` with `h ∈ H^s(ℂ; ℂ)`.** For `u ∈ G_s`, the complex function
`u - 1` agrees almost everywhere with an `L²` function in Mathlib's Bessel-potential space
`H^s(ℂ; ℂ)`. -/
theorem exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup {s : ℝ} {hs : 1 < s} {u : ℂ → Circle}
    (hu : u ∈ sobolevGaugeGroup hs) :
    ∃ h : Lp ℂ 2 (volume : Measure ℂ), h =ᵐ[volume] (fun z ↦ (u z : ℂ) - 1) ∧
      MemSobolev s 2 (h : 𝓢'(ℂ, ℂ)) := by
  obtain ⟨-, h₁, h₂⟩ := (mem_sobolevGaugeGroup hs u).1 hu
  obtain ⟨a, hae, ha⟩ := mem_realSobolevFunctions.1 h₁
  obtain ⟨b, hbe, hb⟩ := mem_realSobolevFunctions.1 h₂
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
    exact ha.add (hb.smul I)

/-- The Sobolev gauge groups decrease as the order increases: `G_s ≤ G_s'` for `1 < s' ≤ s`. -/
theorem sobolevGaugeGroup_mono {s s' : ℝ} (hs' : 1 < s') (h : s' ≤ s) :
    sobolevGaugeGroup (hs'.trans_le h) ≤ sobolevGaugeGroup hs' := by
  intro u hu
  obtain ⟨hu, hu₁, hu₂⟩ := (mem_sobolevGaugeGroup _ u).1 hu
  have hmono := realSobolevFunctions_mono (E := ℂ) (p := 2) (by norm_num) (by norm_num) h
  exact (mem_sobolevGaugeGroup _ u).2 ⟨hu, hmono hu₁, hmono hu₂⟩

/-- **Elements of `G_s` tend to one at infinity**, by the Sobolev embedding of `H^s`, `s > 1`, into
the continuous functions vanishing at infinity. -/
theorem tendsto_cocompact_of_mem_sobolevGaugeGroup {s : ℝ} {hs : 1 < s} {u : ℂ → Circle}
    (hu : u ∈ sobolevGaugeGroup hs) : Tendsto u (cocompact ℂ) (𝓝 1) := by
  obtain ⟨hu, hu₁, hu₂⟩ := (mem_sobolevGaugeGroup hs u).1 hu
  have hs' := finrank_real_complex_lt_two_mul hs
  have hre := tendsto_cocompact_of_mem_realSobolevFunctions hs' hu₁
    ((continuous_re.comp (continuous_subtype_val.comp hu)).sub continuous_const)
  have him := tendsto_cocompact_of_mem_realSobolevFunctions hs' hu₂
    (continuous_im.comp (continuous_subtype_val.comp hu))
  have h := (((continuous_ofReal.tendsto 0).comp hre).add
    (((continuous_ofReal.tendsto 0).comp him).mul_const I)).const_add (1 : ℂ)
  have hfun : (fun z ↦ (u z : ℂ)) =
      fun z ↦ 1 + ((((u z : ℂ).re - 1 : ℝ) : ℂ) + ((u z : ℂ).im : ℂ) * I) := by
    ext1 z
    nth_rewrite 1 [← re_add_im (u z : ℂ)]
    push_cast
    ring
  have hc : Tendsto (fun z ↦ (u z : ℂ)) (cocompact ℂ) (𝓝 1) := by
    rw [hfun]
    simpa using h
  exact tendsto_subtype_rng.2 (by simpa using hc)

/-- **Smooth elements of `G_s` are smooth framed gauges.** -/
theorem mem_framedGaugeGroup_of_mem_sobolevGaugeGroup {s : ℝ} {hs : 1 < s} {u : ℂ → Circle}
    (hu : u ∈ sobolevGaugeGroup hs) (hsmooth : ContDiff ℝ ∞ (fun z ↦ (u z : ℂ))) :
    u ∈ framedGaugeGroup :=
  (mem_framedGaugeGroup u).2 ⟨hsmooth, tendsto_cocompact_of_mem_sobolevGaugeGroup hu⟩

/-- **The smooth subgroup of `G_s`** is its intersection with the smooth framed gauge group: it
consists of the elements of `G_s` that are smooth. -/
theorem mem_sobolevGaugeGroup_inf_framedGaugeGroup {s : ℝ} (hs : 1 < s) (u : ℂ → Circle) :
    u ∈ sobolevGaugeGroup hs ⊓ framedGaugeGroup ↔
      u ∈ sobolevGaugeGroup hs ∧ ContDiff ℝ ∞ (fun z ↦ (u z : ℂ)) :=
  ⟨fun h ↦ ⟨Subgroup.mem_inf.1 h |>.1, ((mem_framedGaugeGroup u).1 (Subgroup.mem_inf.1 h).2).1⟩,
    fun h ↦ Subgroup.mem_inf.2 ⟨h.1, mem_framedGaugeGroup_of_mem_sobolevGaugeGroup h.1 h.2⟩⟩

/-- **Compactly supported smooth gauges lie in `G_s`**: if `u` is smooth and `u - 1` has compact
support, then `u` lies in every `G_s`. -/
theorem mem_sobolevGaugeGroup_of_hasCompactSupport {s : ℝ} (hs : 1 < s) {u : ℂ → Circle}
    (hsmooth : ContDiff ℝ ∞ (fun z ↦ (u z : ℂ)))
    (hc : HasCompactSupport (fun z ↦ (u z : ℂ) - 1)) : u ∈ sobolevGaugeGroup hs := by
  have hd : ContDiff ℝ ∞ (fun z ↦ (u z : ℂ) - 1) := hsmooth.sub contDiff_const
  refine (mem_sobolevGaugeGroup hs u).2 ⟨continuous_induced_rng.2 hsmooth.continuous, ?_, ?_⟩
  · convert mem_realSobolevFunctions_of_hasCompactSupport (reCLM.contDiff.comp hd)
      (hc.comp_left (g := re) zero_re) s using 1
    ext z
    simp
  · convert mem_realSobolevFunctions_of_hasCompactSupport (imCLM.contDiff.comp hd)
      (hc.comp_left (g := im) zero_im) s using 1
    ext z
    simp

/-- A smooth compactly supported phase `f` gives the gauge `exp (i f)` in every `G_s`. -/
theorem exp_mem_sobolevGaugeGroup {s : ℝ} (hs : 1 < s) {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : (fun w ↦ Circle.exp (f w)) ∈ sobolevGaugeGroup hs := by
  refine mem_sobolevGaugeGroup_of_hasCompactSupport hs ?_ ?_
  · exact ((mem_framedGaugeGroup _).1 (exp_mem_framedGaugeGroup hf hc.is_zero_at_infty)).1
  · simpa only [Function.comp_def, Circle.coe_exp] using
      hc.comp_left (g := fun t : ℝ ↦ Complex.exp (t * I) - 1) (by simp)

/-- **The connection increment of a Sobolev gauge.** For `s > 1` and a `C¹` gauge `u ∈ G_(s+1)`,
the real one-form `Im (u⁻¹ du)` has coefficients in `H^s`: in each direction `v`,
`Im (u⁻¹ du) (v) = Re u · ∂_v Im u - Im u · ∂_v Re u`, a combination of products of `H^s`
functions. Hence the action `a ↦ a - u⁻¹ du` preserves connections whose coefficients differ from
a reference by `H^s` functions. -/
theorem gaugeForm_apply_mem_realSobolevFunctions {s : ℝ} (hs : 1 < s) {u : ℂ → Circle}
    (hu : u ∈ sobolevGaugeGroup (hs.trans (lt_add_one s)))
    (hC1 : ContDiff ℝ 1 (fun z ↦ (u z : ℂ))) (v : ℂ) :
    (fun z ↦ gaugeForm u z v) ∈ realSobolevFunctions ℂ s 2 := by
  obtain ⟨-, hu₁, hu₂⟩ := (mem_sobolevGaugeGroup _ u).1 hu
  have hmono := realSobolevFunctions_mono (E := ℂ) (p := 2) (by norm_num) (by norm_num)
    (lt_add_one s).le
  have hmul {f g : ℂ → ℝ} (hf : f ∈ realSobolevFunctions ℂ s 2)
      (hg : g ∈ realSobolevFunctions ℂ s 2) : f * g ∈ realSobolevFunctions ℂ s 2 :=
    mul_mem_realSobolevFunctions (finrank_real_complex_lt_two_mul hs) hf hg
  -- The directional derivatives of `Re u - 1` and `Im u` are those of `Re u` and `Im u`.
  have hre : ContDiff ℝ 1 (fun z ↦ (u z : ℂ).re - 1) :=
    (reCLM.contDiff.comp hC1).sub contDiff_const
  have him : ContDiff ℝ 1 (fun z ↦ (u z : ℂ).im) := imCLM.contDiff.comp hC1
  have hd (z : ℂ) := (hC1.differentiable one_ne_zero z).hasFDerivAt
  have hDre : (fun z ↦ fderiv ℝ (fun z ↦ (u z : ℂ).re - 1) z v) =
      fun z ↦ (fderiv ℝ (fun z ↦ (u z : ℂ)) z v).re := by
    ext z
    have h : HasFDerivAt (fun z ↦ (u z : ℂ).re - 1)
        (reCLM.comp (fderiv ℝ (fun z ↦ (u z : ℂ)) z)) z :=
      (reCLM.hasFDerivAt.comp z (hd z)).sub_const 1
    simp [h.fderiv]
  have hDim : (fun z ↦ fderiv ℝ (fun z ↦ (u z : ℂ).im) z v) =
      fun z ↦ (fderiv ℝ (fun z ↦ (u z : ℂ)) z v).im := by
    ext z
    have h : HasFDerivAt (fun z ↦ (u z : ℂ).im)
        (imCLM.comp (fderiv ℝ (fun z ↦ (u z : ℂ)) z)) z :=
      imCLM.hasFDerivAt.comp z (hd z)
    simp [h.fderiv]
  have hDre_mem := fderiv_apply_mem_realSobolevFunctions (by norm_num) (by norm_num)
    (by linarith) hre hu₁ v
  have hDim_mem := fderiv_apply_mem_realSobolevFunctions (by norm_num) (by norm_num)
    (by linarith) him hu₂ v
  rw [hDre] at hDre_mem
  rw [hDim] at hDim_mem
  -- `Im (conj u · du(v)) = (Re u - 1) ∂_v Im u + ∂_v Im u - Im u ∂_v Re u`.
  convert add_mem (add_mem (hmul (hmono hu₁) hDim_mem) hDim_mem)
    (neg_mem (hmul (hmono hu₂) hDre_mem)) using 1
  ext z
  simp only [gaugeForm_apply, mul_im, conj_re, conj_im, Pi.add_apply, Pi.neg_apply,
    Pi.mul_apply]
  ring

end TauCeti.Vortex
