/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Sobolev
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.Sobolev.BesselPotential.PowerSeries
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# The exponential map of the Sobolev framed gauge group

For a real order `s > 1`, the Sobolev framed gauge group `G_s` (`sobolevGaugeGroup`) consists of
the continuous circle-valued maps `u` on the plane with `u - 1 ∈ H^s(ℂ; ℂ)`. This file studies the
exponential `f ↦ exp (i f)` on continuous real phases `f ∈ H^s(ℂ; ℝ)`, and shows that it is a
chart of `G_s` at the identity modelled on `H^s(ℂ; ℝ)`, for the coordinate `u ↦ u - 1` of `G_s`
in `H^s(ℂ; ℂ)`. Functions are measured in `H^s` through `L²` representatives in `H^s(ℂ; ℂ)`; for a
real phase `f` this is an `L²` function equal almost everywhere to `f`.

* **The exponential lands in `G_s`.** For a continuous real `f ∈ H^s`, the gauge `exp (i f)` lies
  in `G_s` (`TauCeti.Vortex.exp_mem_sobolevGaugeGroup`), because `cos f - 1` and `sin f` lie in
  `H^s` (`TemperedDistribution.cos_sub_one_mem_realSobolevFunctions`,
  `TemperedDistribution.sin_mem_realSobolevFunctions`).
* **It is injective.** Two continuous real phases in `H^s` with the same exponential are equal
  (`TauCeti.Vortex.injOn_exp`): their difference takes values in `2πℤ`, so it is constant on the
  connected plane, and it tends to zero at infinity by the Sobolev embedding.
* **Its image contains an `H^s` neighbourhood of the identity.** There is `δ > 0` such that every
  `u ∈ G_s` with `‖u - 1‖_{H^s} < δ` is `exp (i f)` for a continuous real `f ∈ H^s` with
  `‖f‖_{H^s} ≤ 2 ‖u - 1‖_{H^s}`
  (`TauCeti.Vortex.exists_continuous_mem_realSobolevFunctions_eq_exp`). The proof takes
  `f = arg u`: here `log u = log (1 + (u - 1))` is the logarithm series in `u - 1`, which
  converges in `H^s` once `‖u - 1‖_{H^s}` is small
  (`TemperedDistribution.exists_memSobolev_ae_eq_log_one_add`), and `log u = i arg u` because
  `|u| = 1`.
* **It is bi-Lipschitz near `0`.** There is `ρ > 0` such that for phases `f, g` with
  `‖f‖_{H^s}, ‖g‖_{H^s} ≤ ρ`,
  `‖f - g‖_{H^s} ≤ 2 ‖exp (i f) - exp (i g)‖_{H^s} ≤ 4 ‖f - g‖_{H^s}`
  (`TauCeti.Vortex.exists_pos_forall_norm_toBesselPotentialSpace_sub_le_of_exp`). This is the
  case `U = i f` of the corresponding estimate for `U ↦ exp U - 1` on the Sobolev algebra
  (`TemperedDistribution.exists_pos_forall_norm_toBesselPotentialSpace_sub_le`).
* **Its inverse is Lipschitz.** Combining the last two points with injectivity, the phases of
  `u, v ∈ G_s` that are `δ`-close to `1` satisfy `‖f‖_{H^s} ≤ 2 ‖u - 1‖_{H^s}` and
  `‖f - g‖_{H^s} ≤ 2 ‖u - v‖_{H^s}`
  (`TauCeti.Vortex.exists_pos_forall_norm_toBesselPotentialSpace_sub_le_two_mul`).

So the exponential is a bi-Lipschitz bijection from a set of continuous real `H^s` phases
containing a ball about `0` onto the elements of `G_s` that are `H^s`-close to `1`. Since `G_s` is
abelian and `exp (i (f + g)) = exp (i f) exp (i g)`, it is moreover a homomorphism from the
additive group of continuous real `H^s` phases into `G_s`. These are estimates in the `H^s`
coordinates; no topology on `G_s` is constructed here.

## Main results

* `TauCeti.Vortex.exp_mem_sobolevGaugeGroup`: `exp (i f) ∈ G_s` for continuous real `f ∈ H^s`.
* `TauCeti.Vortex.injOn_exp`: the exponential is injective on continuous real `H^s` phases.
* `TauCeti.Vortex.exists_continuous_mem_realSobolevFunctions_eq_exp`: the elements of `G_s` close
  to `1` in `H^s` are exponentials of continuous real `H^s` phases, with `H^s` norm at most twice
  that of `u - 1`.
* `TauCeti.Vortex.exists_pos_forall_norm_toBesselPotentialSpace_sub_le_of_exp`: the exponential
  is bi-Lipschitz on a ball of phases.
* `TauCeti.Vortex.exists_pos_forall_norm_toBesselPotentialSpace_sub_le_two_mul`: the phase of an
  element of `G_s` close to `1` depends Lipschitz continuously on it.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* M. E. Taylor, *Partial Differential Equations III: Nonlinear Equations*, 2nd ed., Applied
  Mathematical Sciences 117, Springer, 2011, Chapter 13, Section 3.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Module TemperedDistribution
open scoped Real Topology SchwartzMap BesselPotentialSpace

/-- **The exponential of a Sobolev phase is a Sobolev gauge.** For `s > 1` and a continuous real
function `f ∈ H^s(ℂ)`, the gauge `exp (i f)` lies in `G_s`. In particular this holds for smooth
compactly supported `f`. -/
theorem exp_mem_sobolevGaugeGroup {s : ℝ} (hs : 1 < s) {f : ℂ → ℝ} (hf : Continuous f)
    (hfs : f ∈ realSobolevFunctions ℂ s 2) :
    (fun z ↦ Circle.exp (f z)) ∈ sobolevGaugeGroup hs := by
  have hs' := finrank_real_complex_lt_two_mul hs
  refine (mem_sobolevGaugeGroup hs _).2 ⟨Circle.exp.continuous.comp hf, ?_, ?_⟩
  · simpa only [Circle.coe_exp, exp_ofReal_mul_I_re] using
      cos_sub_one_mem_realSobolevFunctions hs' hfs
  · simpa only [Circle.coe_exp, exp_ofReal_mul_I_im] using sin_mem_realSobolevFunctions hs' hfs

/-- **The exponential is injective on continuous Sobolev phases.** For `s > 1`, two continuous
real functions in `H^s(ℂ)` with the same exponential `exp (i f)` are equal. -/
theorem injOn_exp {s : ℝ} (hs : 1 < s) :
    Set.InjOn (fun (f : ℂ → ℝ) (z : ℂ) ↦ Circle.exp (f z))
      {f | Continuous f ∧ f ∈ realSobolevFunctions ℂ s 2} := by
  rintro f ⟨hf, hfs⟩ g ⟨hg, hgs⟩ hfg
  have hD : Continuous (f - g) := hf.sub hg
  -- `f - g` takes values in `2πℤ`, so it is constant on the connected plane.
  have hmaps : Set.MapsTo (f - g) Set.univ (AddSubgroup.zmultiples (2 * π) : Set ℝ) := by
    intro z _
    have h : Circle.exp ((f - g) z) = 1 := by
      rw [Pi.sub_apply, Circle.exp_sub]
      exact div_eq_one.2 (congrFun hfg z)
    obtain ⟨n, hn⟩ := Circle.exp_eq_one.1 h
    exact ⟨n, by simp [hn, zsmul_eq_mul]⟩
  have hconst (z w : ℂ) : (f - g) z = (f - g) w :=
    isPreconnected_univ.constant_of_mapsTo
      (isDiscrete_iff_discreteTopology.2 (NormedSpace.discreteTopology_zmultiples (2 * π)))
      hD.continuousOn hmaps (Set.mem_univ z) (Set.mem_univ w)
  -- `f - g` tends to zero at infinity, so the constant is zero.
  have hlim := tendsto_cocompact_of_mem_realSobolevFunctions (finrank_real_complex_lt_two_mul hs)
    (sub_mem hfs hgs) hD
  funext z
  exact sub_eq_zero.1 (tendsto_nhds_unique (tendsto_const_nhds.congr fun w ↦ hconst z w) hlim)

/-- **Elements of `G_s` near the identity are exponentials of small phases.** For `s > 1` there is
`δ > 0` such that every `u ∈ G_s` with `‖u - 1‖_{H^s} < δ` is `exp (i f)` for a continuous real
function `f ∈ H^s(ℂ)` with `‖f‖_{H^s} ≤ 2 ‖u - 1‖_{H^s}`. Here `u - 1` is represented by an `L²`
function `h` in `H^s(ℂ; ℂ)`, as in `exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup`, and the
bound holds for every `L²` function in `H^s(ℂ; ℂ)` representing `f`. -/
theorem exists_continuous_mem_realSobolevFunctions_eq_exp {s : ℝ} (hs : 1 < s) :
    ∃ δ, 0 < δ ∧ ∀ u ∈ sobolevGaugeGroup hs, ∀ {h : Lp ℂ 2 (volume : Measure ℂ)},
      h =ᵐ[volume] (fun z ↦ (u z : ℂ) - 1) → ∀ hh : MemSobolev s 2 (h : 𝓢'(ℂ, ℂ)),
      ‖hh.toBesselPotentialSpace‖ < δ →
      ∃ f : ℂ → ℝ, Continuous f ∧ f ∈ realSobolevFunctions ℂ s 2 ∧
        (∀ {φ : Lp ℂ 2 (volume : Measure ℂ)} (hφ : MemSobolev s 2 (φ : 𝓢'(ℂ, ℂ))),
          φ =ᵐ[volume] (fun z ↦ (f z : ℂ)) →
          ‖hφ.toBesselPotentialSpace‖ ≤ 2 * ‖hh.toBesselPotentialSpace‖) ∧
        u = fun z ↦ Circle.exp (f z) := by
  obtain ⟨C, hC, hlog⟩ := exists_memSobolev_ae_eq_log_one_add (finrank_real_complex_lt_two_mul hs)
  refine ⟨(2 * C + 1)⁻¹, by positivity,
    fun u hu {h} hhu (hh : MemSobolev s 2 (h : 𝓢'(ℂ, ℂ))) hδ ↦ ?_⟩
  have hCR : C * ‖hh.toBesselPotentialSpace‖ ≤ 1 / 2 := by
    have h1 : (2 * C + 1) * ‖hh.toBesselPotentialSpace‖ < 1 := by
      calc (2 * C + 1) * ‖hh.toBesselPotentialSpace‖ < (2 * C + 1) * (2 * C + 1)⁻¹ := by gcongr
        _ = 1 := mul_inv_cancel₀ (by positivity)
    nlinarith [norm_nonneg hh.toBesselPotentialSpace]
  obtain ⟨hsmall, v, hv, hvs, hvn⟩ := hlog hh hCR
  have hu_cont : Continuous fun z ↦ (u z : ℂ) :=
    continuous_subtype_val.comp ((mem_sobolevGaugeGroup hs u).1 hu).1
  -- Pointwise, `‖u - 1‖ ≤ 1 / 2` everywhere: almost everywhere, then everywhere by continuity.
  have hsmall' : ∀ z, ‖(u z : ℂ) - 1‖ ≤ 1 / 2 :=
    (Continuous.ae_le_iff_le volume (f := fun z ↦ ‖(u z : ℂ) - 1‖)
      (hu_cont.sub continuous_const).norm continuous_const).1 <| by
      filter_upwards [hsmall, hhu] with z hz hz'
      rwa [← hz']
  have hslit (z : ℂ) : (u z : ℂ) ∈ slitPlane := by
    simpa using mem_slitPlane_of_norm_lt_one ((hsmall' z).trans_lt (by norm_num))
  -- `arg u = -i log u`, and `v` is `log (1 + (u - 1)) = log u`.
  have harg : ((-I) • v : Lp ℂ 2 (volume : Measure ℂ)) =ᵐ[volume]
      fun z ↦ ((arg (u z : ℂ) : ℝ) : ℂ) := by
    filter_upwards [Lp.coeFn_smul (-I) v, hv, hhu] with z hz hvz hhz
    rw [hz, Pi.smul_apply, smul_eq_mul, hvz, hhz, add_sub_cancel]
    apply Complex.ext <;> simp [log_re, log_im]
  have hargs : MemSobolev s 2 (((-I) • v : Lp ℂ 2 (volume : Measure ℂ)) : 𝓢'(ℂ, ℂ)) := by
    rw [Lp.toTemperedDistribution_smul]
    exact hvs.smul _
  refine ⟨fun z ↦ arg (u z : ℂ), ?_, mem_realSobolevFunctions_of_ae_eq_ofReal hargs harg,
    fun {φ} hφ hφf ↦ ?_, ?_⟩
  · exact continuous_iff_continuousAt.2 fun z ↦
      (continuousAt_arg (hslit z)).comp_of_eq hu_cont.continuousAt rfl
  · -- Every representative of `arg u` is `-i v`, of norm `‖v‖_{H^s} ≤ 2 ‖u - 1‖_{H^s}`.
    have hφv : φ = (-I) • v := Lp.ext (hφf.trans harg.symm)
    subst hφv
    have hn : hφ.toBesselPotentialSpace = (-I) • hvs.toBesselPotentialSpace :=
      BesselPotentialSpace.ext (by simp [Lp.toTemperedDistribution_smul])
    rw [hn, norm_smul, norm_neg, Complex.norm_I, one_mul]
    exact hvn
  · funext z
    exact (Circle.exp_arg (u z)).symm

/-- **The exponential chart of `G_s` is bi-Lipschitz.** For `s > 1` there is `ρ > 0` with the
following property. Let `f, g` be real phases represented in `H^s(ℂ; ℂ)` by `L²` functions `φ, ψ`
with `‖φ‖_{H^s}, ‖ψ‖_{H^s} ≤ ρ`, and let `h, k` be `L²` functions in `H^s(ℂ; ℂ)` representing
`exp (i f) - 1` and `exp (i g) - 1`. Then

`‖φ - ψ‖_{H^s} ≤ 2 ‖h - k‖_{H^s}`  and  `‖h - k‖_{H^s} ≤ 2 ‖φ - ψ‖_{H^s}`.

So in the coordinate `u ↦ u - 1` of `G_s`, the exponential is Lipschitz on the ball of radius `ρ`
of phases, with Lipschitz inverse on its image. -/
theorem exists_pos_forall_norm_toBesselPotentialSpace_sub_le_of_exp {s : ℝ} (hs : 1 < s) :
    ∃ ρ, 0 < ρ ∧ ∀ {f g : ℂ → ℝ} {φ ψ h k : Lp ℂ 2 (volume : Measure ℂ)}
      (hφ : MemSobolev s 2 (φ : 𝓢'(ℂ, ℂ))) (hψ : MemSobolev s 2 (ψ : 𝓢'(ℂ, ℂ)))
      (hh : MemSobolev s 2 (h : 𝓢'(ℂ, ℂ))) (hk : MemSobolev s 2 (k : 𝓢'(ℂ, ℂ))),
      φ =ᵐ[volume] (fun z ↦ (f z : ℂ)) → ψ =ᵐ[volume] (fun z ↦ (g z : ℂ)) →
      h =ᵐ[volume] (fun z ↦ (Circle.exp (f z) : ℂ) - 1) →
      k =ᵐ[volume] (fun z ↦ (Circle.exp (g z) : ℂ) - 1) →
      ‖hφ.toBesselPotentialSpace‖ ≤ ρ → ‖hψ.toBesselPotentialSpace‖ ≤ ρ →
      ‖hφ.toBesselPotentialSpace - hψ.toBesselPotentialSpace‖ ≤
          2 * ‖hh.toBesselPotentialSpace - hk.toBesselPotentialSpace‖ ∧
        ‖hh.toBesselPotentialSpace - hk.toBesselPotentialSpace‖ ≤
          2 * ‖hφ.toBesselPotentialSpace - hψ.toBesselPotentialSpace‖ := by
  obtain ⟨ρ, hρ, hexp⟩ :=
    exists_pos_forall_norm_toBesselPotentialSpace_sub_le (finrank_real_complex_lt_two_mul hs)
  refine ⟨ρ, hρ, fun {f g φ ψ h k} hφ hψ hh hk hφf hψg hhf hkg hφρ hψρ ↦ ?_⟩
  -- Apply the bi-Lipschitz estimate of the exponential to `U₁ = i φ` and `U₂ = i ψ`.
  have hIφ : MemSobolev s 2 ((I • φ : Lp ℂ 2 (volume : Measure ℂ)) : 𝓢'(ℂ, ℂ)) := by
    rw [Lp.toTemperedDistribution_smul]
    exact hφ.smul _
  have hIψ : MemSobolev s 2 ((I • ψ : Lp ℂ 2 (volume : Measure ℂ)) : 𝓢'(ℂ, ℂ)) := by
    rw [Lp.toTemperedDistribution_smul]
    exact hψ.smul _
  have hnφ : hIφ.toBesselPotentialSpace = I • hφ.toBesselPotentialSpace :=
    BesselPotentialSpace.ext (by simp [Lp.toTemperedDistribution_smul])
  have hnψ : hIψ.toBesselPotentialSpace = I • hψ.toBesselPotentialSpace :=
    BesselPotentialSpace.ext (by simp [Lp.toTemperedDistribution_smul])
  have hexpI {χ : Lp ℂ 2 (volume : Measure ℂ)} {F : ℂ → ℝ} {w : Lp ℂ 2 (volume : Measure ℂ)}
      (hχ : χ =ᵐ[volume] (fun z ↦ (F z : ℂ)))
      (hw : w =ᵐ[volume] (fun z ↦ (Circle.exp (F z) : ℂ) - 1)) :
      w =ᵐ[volume] (fun z ↦ Complex.exp ((I • χ : Lp ℂ 2 (volume : Measure ℂ)) z) - 1) := by
    filter_upwards [hw, hχ, Lp.coeFn_smul I χ] with z hwz hχz hIz
    rw [hwz, hIz, Pi.smul_apply, hχz, smul_eq_mul, Circle.coe_exp, mul_comm]
  have hnorm (x : H^{s}(ℂ, ℂ)) : ‖I • x‖ = ‖x‖ := by
    rw [norm_smul, Complex.norm_I, one_mul]
  have key := hexp hIφ hIψ hh hk (hexpI hφf hhf) (hexpI hψg hkg)
    (by rw [hnφ, hnorm]; exact hφρ) (by rw [hnψ, hnorm]; exact hψρ)
  rwa [hnφ, hnψ, ← smul_sub, hnorm] at key

/-- **The inverse of the exponential chart of `G_s` is Lipschitz.** For `s > 1` there is `δ > 0`
with the following property. Let `u, v ∈ G_s`, with `u - 1` and `v - 1` represented by `L²`
functions `h, k` in `H^s(ℂ; ℂ)` with `‖h‖_{H^s}, ‖k‖_{H^s} < δ`. Let `f, g` be continuous real
phases in `H^s(ℂ)` with `u = exp (i f)` and `v = exp (i g)`, represented by `L²` functions
`φ, ψ` in `H^s(ℂ; ℂ)`. Then

`‖φ‖_{H^s} ≤ 2 ‖h‖_{H^s}`  and  `‖φ - ψ‖_{H^s} ≤ 2 ‖h - k‖_{H^s}`.

Such phases exist by `exists_continuous_mem_realSobolevFunctions_eq_exp` and are unique by
`injOn_exp`. Together with `exists_pos_forall_norm_toBesselPotentialSpace_sub_le_of_exp`, the
exponential is a bi-Lipschitz bijection from a set of continuous real `H^s` phases onto the
elements of `G_s` that are `δ`-close to `1` in `H^s`: a chart of `G_s` at the identity, modelled
on `H^s(ℂ; ℝ)`. -/
theorem exists_pos_forall_norm_toBesselPotentialSpace_sub_le_two_mul {s : ℝ} (hs : 1 < s) :
    ∃ δ, 0 < δ ∧ ∀ {u v : ℂ → Circle}, u ∈ sobolevGaugeGroup hs → v ∈ sobolevGaugeGroup hs →
      ∀ {h k : Lp ℂ 2 (volume : Measure ℂ)} (hh : MemSobolev s 2 (h : 𝓢'(ℂ, ℂ)))
        (hk : MemSobolev s 2 (k : 𝓢'(ℂ, ℂ))),
      h =ᵐ[volume] (fun z ↦ (u z : ℂ) - 1) → k =ᵐ[volume] (fun z ↦ (v z : ℂ) - 1) →
      ‖hh.toBesselPotentialSpace‖ < δ → ‖hk.toBesselPotentialSpace‖ < δ →
      ∀ {f g : ℂ → ℝ}, Continuous f → f ∈ realSobolevFunctions ℂ s 2 →
        Continuous g → g ∈ realSobolevFunctions ℂ s 2 →
        u = (fun z ↦ Circle.exp (f z)) → v = (fun z ↦ Circle.exp (g z)) →
      ∀ {φ ψ : Lp ℂ 2 (volume : Measure ℂ)} (hφ : MemSobolev s 2 (φ : 𝓢'(ℂ, ℂ)))
        (hψ : MemSobolev s 2 (ψ : 𝓢'(ℂ, ℂ))),
      φ =ᵐ[volume] (fun z ↦ (f z : ℂ)) → ψ =ᵐ[volume] (fun z ↦ (g z : ℂ)) →
      ‖hφ.toBesselPotentialSpace‖ ≤ 2 * ‖hh.toBesselPotentialSpace‖ ∧
        ‖hφ.toBesselPotentialSpace - hψ.toBesselPotentialSpace‖ ≤
          2 * ‖hh.toBesselPotentialSpace - hk.toBesselPotentialSpace‖ := by
  obtain ⟨δ₁, hδ₁, hlog⟩ := exists_continuous_mem_realSobolevFunctions_eq_exp hs
  obtain ⟨ρ, hρ, hexp⟩ := exists_pos_forall_norm_toBesselPotentialSpace_sub_le_of_exp hs
  refine ⟨min δ₁ (ρ / 2), by positivity, fun {u v} hu hv {h k} hh hk hhu hkv hhδ hkδ {f g}
    hf hfs hg hgs hfu hgv {φ ψ} hφ hψ hφf hψg ↦ ?_⟩
  -- The phase of `u` given by the logarithm is `f`, by injectivity of the exponential; so `φ` is
  -- small, and likewise `ψ`.
  have hsmall {w : ℂ → Circle} (hw : w ∈ sobolevGaugeGroup hs) {l : Lp ℂ 2 (volume : Measure ℂ)}
      (hl : MemSobolev s 2 (l : 𝓢'(ℂ, ℂ))) (hlw : l =ᵐ[volume] (fun z ↦ (w z : ℂ) - 1))
      (hlδ : ‖hl.toBesselPotentialSpace‖ < min δ₁ (ρ / 2)) {F : ℂ → ℝ} (hF : Continuous F)
      (hFs : F ∈ realSobolevFunctions ℂ s 2) (hFw : w = fun z ↦ Circle.exp (F z))
      {χ : Lp ℂ 2 (volume : Measure ℂ)} (hχ : MemSobolev s 2 (χ : 𝓢'(ℂ, ℂ)))
      (hχF : χ =ᵐ[volume] (fun z ↦ (F z : ℂ))) :
      ‖hχ.toBesselPotentialSpace‖ ≤ 2 * ‖hl.toBesselPotentialSpace‖ := by
    obtain ⟨F', hF', hF's, hbound, hF'w⟩ :=
      hlog w hw hlw hl (hlδ.trans_le (min_le_left _ _))
    have hFF' : F = F' := injOn_exp hs ⟨hF, hFs⟩ ⟨hF', hF's⟩ (hFw.symm.trans hF'w)
    subst hFF'
    exact hbound hχ hχF
  have hφs := hsmall hu hh hhu hhδ hf hfs hfu hφ hφf
  have hψs := hsmall hv hk hkv hkδ hg hgs hgv hψ hψg
  have hρ₁ : 2 * ‖hh.toBesselPotentialSpace‖ ≤ ρ := by
    have := hhδ.trans_le (min_le_right _ _)
    linarith
  have hρ₂ : 2 * ‖hk.toBesselPotentialSpace‖ ≤ ρ := by
    have := hkδ.trans_le (min_le_right _ _)
    linarith
  have hhf : h =ᵐ[volume] (fun z ↦ (Circle.exp (f z) : ℂ) - 1) := by
    subst hfu
    exact hhu
  have hkg : k =ᵐ[volume] (fun z ↦ (Circle.exp (g z) : ℂ) - 1) := by
    subst hgv
    exact hkv
  exact ⟨hφs, (hexp hφ hψ hh hk hφf hψg hhf hkg (hφs.trans hρ₁) (hψs.trans hρ₂)).1⟩

end TauCeti.Vortex
