/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Homogeneous.Realization
public import TauCeti.Analysis.PDE.Strichartz.HomogeneousBesov
public import TauCeti.Analysis.PDE.Wave.Propagator
import TauCeti.Analysis.Fourier.Bernstein
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Homogeneous.Schwartz
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.MeasureTheory.Function.Holder
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Order.Filter.AtTopBot.Interval
import TauCeti.MeasureTheory.Function.Lp.Duality
import TauCeti.MeasureTheory.Function.Lp.Star
import TauCeti.Analysis.PDE.Wave.MixedNorm
import TauCeti.Analysis.PDE.Wave.TimeExponentTwo
import TauCeti.Analysis.PDE.Wave.WeakSolution

/-!
# Wave evolutions of data in homogeneous Besov spaces

On a real inner product space `E` of dimension `n`, let `D = √(-Δ)` and let `Pⱼ`, `j ∈ ℤ`, be the
homogeneous Littlewood–Paley blocks built from a bump function `φ`. The free wave equation
`∂ₜ²u = Δu` with data `u(0) = f` and `∂ₜu(0) = g` in `L²` is solved by
`u(t) = cos(tD) f + D⁻¹ sin(tD) g` (`TauCeti.waveCosPropagator`, `TauCeti.waveSinPropagator`), and
for a wave-admissible pair `(q, r)` with scaling-critical regularity `γ` it satisfies the
Strichartz estimate with the norms of the data in the homogeneous Besov spaces `\dot B^γ_{2,1}` and
`\dot B^{γ - 1}_{2,1}`
(`ContDiffBump.exists_eLpNorm_eLpNorm_waveCosPropagator_add_waveSinPropagator_le_tsum`).

This file treats data in these Besov spaces themselves (`TauCeti.HomogeneousBesovSpace`), which
are spaces of tempered distributions modulo those with spectrum at the origin, not of `L²`
functions, so `cos(tD)` and `D⁻¹ sin(tD)` have no a priori meaning on them. For
`f ∈ \dot B^γ_{2,1}` and `g ∈ \dot B^{γ - 1}_{2,1}` the file considers the dyadic series

`∑ⱼ cos(tD) Pⱼ f` and `∑ⱼ D⁻¹ sin(tD) Pⱼ g`,

whose pieces are the evolutions of the `L²` blocks of the data, and shows that these series
converge to some limit `U`, determined for almost every `t`, which serves as the evolution, with
the Strichartz bound. It builds no evolution operator on these Besov spaces; the attainment of the
position datum is shown at the pairs `(∞, r)`, and that of the velocity datum in the sense of
distributions (see below). For each
series there is `U : ℝ → L^r` such that the partial sums converge to `U(t)` in `L^r` for almost
every time `t` and to `U` in `L^q_t L^r_x`, with

`‖U‖_{L^q_t L^r_x} ≤ C ‖f‖_{\dot B^γ_{2,1}}`, respectively
`‖U‖_{L^q_t L^r_x} ≤ C ‖g‖_{\dot B^{γ - 1}_{2,1}}`,

and `C` independent of the data. This holds at the wave-admissible pairs with `2 < q < ∞`
(`ContDiffBump.exists_tendsto_eLpNorm_eLpNorm_sub_sum_waveCosPropagator_block`,
`ContDiffBump.exists_tendsto_eLpNorm_eLpNorm_sub_sum_waveSinPropagator_block`), at the pairs
`(∞, r)` with `2 ≤ r ≤ ∞` and `γ = n / 2 - n / r`, which include `(∞, ∞)` with `γ = n / 2`
(`ContDiffBump.exists_tendsto_eLpNorm_top_eLpNorm_sub_sum_waveCosPropagator_block` and its
`D⁻¹ sin(tD)` counterpart), and in dimension `n ≥ 4` at the pairs `(2, r)` from the endpoint on,
with `γ = n / 2 - n / r - 1 / 2`
(`ContDiffBump.exists_tendsto_eLpNorm_eLpNorm_sub_sum_waveCosPropagator_block_of_le_endpoint` and
its `D⁻¹ sin(tD)` counterpart). When the data are `L²` functions, any such limits agree with
`cos(tD) f` and `D⁻¹ sin(tD) g` for almost every `t`
(`ContDiffBump.ae_ae_eq_apply_of_tendsto_eLpNorm_sub_sum_apply_block`), so they are consistent
with the `L²` solution of the free wave equation.

Every such limit solves the wave equation `∂ₜ²U = ΔU` in the sense of distributions, tested against
products `θ(t) ψ(x)` of a compactly supported `C²` function of time and a Schwartz function:

`∫ θ''(t) ∫ conj (ψ(x)) U(t)(x) dx dt = ∫ θ(t) ∫ conj (Δψ(x)) U(t)(x) dx dt`

(`ContDiffBump.integral_deriv_deriv_mul_integral_inner_eq_of_tendsto_sum_waveCosPropagator_block`,
`ContDiffBump.integral_deriv_deriv_mul_integral_inner_eq_of_tendsto_sum_waveSinPropagator_block`).
The partial sums are free waves with `L²` data, which satisfy this identity
(`TauCeti.integral_deriv_deriv_mul_inner_waveDuhamelSolution`), and both sides pass to limits in
mixed norm (`TauCeti.integral_deriv_deriv_mul_integral_inner_eq_of_tendsto_waveDuhamelSolution`).

At the pairs `(∞, r)`, `2 ≤ r ≤ ∞`, the evolutions are continuous in time and attain the position
datum. For `f ∈ \dot B^γ_{2,1}` with `γ = n / 2 - n / r` the series `∑ⱼ cos(tD) Pⱼ f` converges
in `L^r` uniformly in `t`, to a continuous `U : ℝ → L^r` whose value `U(0)` is the sum `∑ⱼ Pⱼ f`
of the blocks of `f` in `L^r`, so that `U(t) → ∑ⱼ Pⱼ f` in `L^r` as `t → 0`
(`ContDiffBump.exists_continuous_tendsto_iSup_eLpNorm_sub_sum_waveCosPropagator_block`). For
`g ∈ \dot B^{γ - 1}_{2,1}` the series `∑ⱼ D⁻¹ sin(tD) Pⱼ g` converges in the same way, to a
continuous `U` with `U(0) = 0`
(`ContDiffBump.exists_continuous_tendsto_iSup_eLpNorm_sub_sum_waveSinPropagator_block`). These
follow from the
frequency-localized estimates at every time
(`ContDiffBump.exists_eLpNorm_waveCosPropagator_littlewoodPaley_le`) and the continuity of each
block in `L^r`, which is Bernstein's inequality
(`ContDiffBump.exists_eLpNorm_fourierMultiplierCLM_littlewoodPaley_le_of_two_le`) applied to the
continuous `L²` evolution.

The `D⁻¹ sin(tD)` evolution attains the velocity datum `g ∈ \dot B^σ_{2,1}`, `σ ≤ n / 2`, in the
sense of distributions. If the series `∑ⱼ D⁻¹ sin(tD) Pⱼ g` converges to `U(t)` in `L^r` at every
time, then for every Schwartz function `ψ` the pairing `t ↦ ∫ conj (ψ(x)) U(t)(x) dx` is
differentiable, with derivative `∑ⱼ ⟪ψ, cos(tD) Pⱼ g⟫`
(`ContDiffBump.hasDerivAt_integral_inner_of_tendsto_sum_waveSinPropagator_block`). At `t = 0`
this is `∂ₜU(0) = g`: the derivative of `∫ ψ(x) U(t)(x) dx` at `t = 0` is the value at `ψ` of the
realisation `∑ⱼ Pⱼ g` of `g` as a tempered distribution
(`ContDiffBump.hasDerivAt_integral_mul_of_tendsto_sum_waveSinPropagator_block`). The series of
derivatives converges absolutely and uniformly in `t` because the blocks of a Schwartz function
satisfy `‖Pₖ ψ‖₂ ≤ C 2^{kσ}` for `σ ≤ n / 2`
(`SchwartzMap.exists_two_rpow_mul_norm_fourierMultiplierCLM_littlewoodPaley_le`).

Each piece obeys the frequency-localized Strichartz estimate
`‖cos(tD) Pⱼ x‖_{L^q_t L^r_x} ≤ C 2^{jγ} ‖x‖₂`, and its `D⁻¹ sin(tD)` counterpart with
`2^{j(γ - 1)}`
(`TauCeti.Analysis.PDE.Wave.MixedNorm`, `TauCeti.Analysis.PDE.Wave.TimeExponentTwo`); the dyadic
series of the evolution of a datum in `\dot B^σ_{2,1}` converges under such estimates
(`ContDiffBump.exists_tendsto_eLpNorm_eLpNorm_sub_sum_apply_block`).

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Theorem 2.6 and its proof.
* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), Section 6.
-/

public section

open Filter MeasureTheory Topology TauCeti
open scoped ENNReal NNReal SchwartzMap Laplacian InnerProductSpace

namespace ContDiffBump

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (φ : ContDiffBump (0 : E)) {r : ℝ≥0∞} [Fact (1 ≤ r)]

/-! ### The pairs `(q, r)` with `2 < q < ∞` -/

section Admissible

variable {q : ℝ≥0}

/-- **`cos(tD)` on data in `\dot B^γ_{2,1}`.** Let `(q, r)` be wave-admissible,
`2 / q + (n - 1) / r ≤ (n - 1) / 2`, with `2 < q < ∞`, and let `γ = n / 2 - n / r - 1 / q`. There
is `C` such that for every `f ∈ \dot B^γ_{2,1}` the dyadic series `∑ⱼ cos(tD) Pⱼ f` converges: to
some `U : ℝ → L^r` in `L^r` for almost every `t` and in `L^q_t L^r_x`, with
`‖U‖_{L^q_t L^r_x} ≤ C ‖f‖_{\dot B^γ_{2,1}}`. -/
theorem exists_tendsto_eLpNorm_eLpNorm_sub_sum_waveCosPropagator_block (hq : 2 < q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ f : HomogeneousBesovSpace ℂ φ ((Module.finrank ℝ E : ℝ) / 2 -
        Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹) 2 1,
      ∃ U : ℝ → Lp ℂ r (volume : Measure E),
        (∀ᵐ t, Tendsto (fun s : Finset ℤ ↦
          eLpNorm (⇑(U t) - ⇑(∑ j ∈ s, waveCosPropagator ℂ t (f.block j))) r volume) atTop
            (𝓝 0)) ∧
        Tendsto (fun s : Finset ℤ ↦ eLpNorm (fun t ↦
          eLpNorm (⇑(U t) - ⇑(∑ j ∈ s, waveCosPropagator ℂ t (f.block j))) r volume) q volume)
            atTop (𝓝 0) ∧
        eLpNorm (fun t ↦ ‖U t‖ₑ) q volume ≤ C * ‖f‖ₑ :=
  φ.exists_tendsto_eLpNorm_eLpNorm_sub_sum_apply_block
    (by exact_mod_cast one_le_two.trans hq.le) _ _
    (fun x ↦ (continuous_waveCosPropagator_apply x).aestronglyMeasurable)
    (φ.exists_eLpNorm_eLpNorm_waveCosPropagator_littlewoodPaley_le hq
      (NNReal.HolderConjugate.conjExponent (one_lt_two.trans hq)).symm hqr)

/-- **`D⁻¹ sin(tD)` on data in `\dot B^{γ - 1}_{2,1}`.** Under the hypotheses of
`ContDiffBump.exists_tendsto_eLpNorm_eLpNorm_sub_sum_waveCosPropagator_block`, there is `C` such
that for every `g ∈ \dot B^{γ - 1}_{2,1}` the dyadic series `∑ⱼ D⁻¹ sin(tD) Pⱼ g` converges: to
some `U : ℝ → L^r` in `L^r` for almost every `t` and in `L^q_t L^r_x`, with
`‖U‖_{L^q_t L^r_x} ≤ C ‖g‖_{\dot B^{γ - 1}_{2,1}}`. -/
theorem exists_tendsto_eLpNorm_eLpNorm_sub_sum_waveSinPropagator_block (hq : 2 < q)
    (hqr : 2 / (q : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤
      ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ g : HomogeneousBesovSpace ℂ φ ((Module.finrank ℝ E : ℝ) / 2 -
        Module.finrank ℝ E * (r⁻¹).toReal - (q : ℝ)⁻¹ - 1) 2 1,
      ∃ U : ℝ → Lp ℂ r (volume : Measure E),
        (∀ᵐ t, Tendsto (fun s : Finset ℤ ↦
          eLpNorm (⇑(U t) - ⇑(∑ j ∈ s, waveSinPropagator ℂ t (g.block j))) r volume) atTop
            (𝓝 0)) ∧
        Tendsto (fun s : Finset ℤ ↦ eLpNorm (fun t ↦
          eLpNorm (⇑(U t) - ⇑(∑ j ∈ s, waveSinPropagator ℂ t (g.block j))) r volume) q volume)
            atTop (𝓝 0) ∧
        eLpNorm (fun t ↦ ‖U t‖ₑ) q volume ≤ C * ‖g‖ₑ :=
  φ.exists_tendsto_eLpNorm_eLpNorm_sub_sum_apply_block
    (by exact_mod_cast one_le_two.trans hq.le) _ _
    (fun x ↦ (continuous_waveSinPropagator_apply x).aestronglyMeasurable)
    (φ.exists_eLpNorm_eLpNorm_waveSinPropagator_littlewoodPaley_le hq
      (NNReal.HolderConjugate.conjExponent (one_lt_two.trans hq)).symm hqr)

end Admissible

/-! ### The pairs `(∞, r)` -/

/-- **`cos(tD)` on data in `\dot B^γ_{2,1}` at the pairs `(∞, r)`.** Let `2 ≤ r ≤ ∞` and
`γ = n / 2 - n / r`. There is `C` such that for every `f ∈ \dot B^γ_{2,1}` the dyadic series
`∑ⱼ cos(tD) Pⱼ f` converges: to some `U : ℝ → L^r` in `L^r` for almost every `t` and in
`L^∞_t L^r_x`, with `‖U‖_{L^∞_t L^r_x} ≤ C ‖f‖_{\dot B^γ_{2,1}}`. At `r = ∞` this bounds the
evolution uniformly in space and time for `f ∈ \dot B^{n/2}_{2,1}`. -/
theorem exists_tendsto_eLpNorm_top_eLpNorm_sub_sum_waveCosPropagator_block (hr : 2 ≤ r) :
    ∃ C : ℝ≥0, ∀ f : HomogeneousBesovSpace ℂ φ ((Module.finrank ℝ E : ℝ) / 2 -
        Module.finrank ℝ E * (r⁻¹).toReal) 2 1,
      ∃ U : ℝ → Lp ℂ r (volume : Measure E),
        (∀ᵐ t, Tendsto (fun s : Finset ℤ ↦
          eLpNorm (⇑(U t) - ⇑(∑ j ∈ s, waveCosPropagator ℂ t (f.block j))) r volume) atTop
            (𝓝 0)) ∧
        Tendsto (fun s : Finset ℤ ↦ eLpNorm (fun t ↦
          eLpNorm (⇑(U t) - ⇑(∑ j ∈ s, waveCosPropagator ℂ t (f.block j))) r volume) ∞ volume)
            atTop (𝓝 0) ∧
        eLpNorm (fun t ↦ ‖U t‖ₑ) ∞ volume ≤ C * ‖f‖ₑ :=
  φ.exists_tendsto_eLpNorm_eLpNorm_sub_sum_apply_block le_top _ _
    (fun x ↦ (continuous_waveCosPropagator_apply x).aestronglyMeasurable)
    (φ.exists_eLpNorm_top_eLpNorm_waveCosPropagator_littlewoodPaley_le hr)

/-- **`D⁻¹ sin(tD)` on data in `\dot B^{γ - 1}_{2,1}` at the pairs `(∞, r)`.** Let `2 ≤ r ≤ ∞` and
`γ = n / 2 - n / r`. There is `C` such that for every `g ∈ \dot B^{γ - 1}_{2,1}` the dyadic series
`∑ⱼ D⁻¹ sin(tD) Pⱼ g` converges: to some `U : ℝ → L^r` in `L^r` for almost every `t` and in
`L^∞_t L^r_x`, with `‖U‖_{L^∞_t L^r_x} ≤ C ‖g‖_{\dot B^{γ - 1}_{2,1}}`. -/
theorem exists_tendsto_eLpNorm_top_eLpNorm_sub_sum_waveSinPropagator_block (hr : 2 ≤ r) :
    ∃ C : ℝ≥0, ∀ g : HomogeneousBesovSpace ℂ φ ((Module.finrank ℝ E : ℝ) / 2 -
        Module.finrank ℝ E * (r⁻¹).toReal - 1) 2 1,
      ∃ U : ℝ → Lp ℂ r (volume : Measure E),
        (∀ᵐ t, Tendsto (fun s : Finset ℤ ↦
          eLpNorm (⇑(U t) - ⇑(∑ j ∈ s, waveSinPropagator ℂ t (g.block j))) r volume) atTop
            (𝓝 0)) ∧
        Tendsto (fun s : Finset ℤ ↦ eLpNorm (fun t ↦
          eLpNorm (⇑(U t) - ⇑(∑ j ∈ s, waveSinPropagator ℂ t (g.block j))) r volume) ∞ volume)
            atTop (𝓝 0) ∧
        eLpNorm (fun t ↦ ‖U t‖ₑ) ∞ volume ≤ C * ‖g‖ₑ :=
  φ.exists_tendsto_eLpNorm_eLpNorm_sub_sum_apply_block le_top _ _
    (fun x ↦ (continuous_waveSinPropagator_apply x).aestronglyMeasurable)
    (φ.exists_eLpNorm_top_eLpNorm_waveSinPropagator_littlewoodPaley_le hr)

/-! ### The pairs `(2, r)` -/

/-- **`cos(tD)` on data in `\dot B^γ_{2,1}` at the pairs `(2, r)`.** Let `E` have dimension
`n ≥ 4`, let `1 + (n - 1) / r ≤ (n - 1) / 2`, the endpoint exponent and `r = ∞` included, and let
`γ = n / 2 - n / r - 1 / 2`. There is `C` such that for every `f ∈ \dot B^γ_{2,1}` the dyadic
series `∑ⱼ cos(tD) Pⱼ f` converges: to some `U : ℝ → L^r` in `L^r` for almost every `t` and in
`L²_t L^r_x`, with `‖U‖_{L²_t L^r_x} ≤ C ‖f‖_{\dot B^γ_{2,1}}`. -/
theorem exists_tendsto_eLpNorm_eLpNorm_sub_sum_waveCosPropagator_block_of_le_endpoint
    (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤ ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ f : HomogeneousBesovSpace ℂ φ ((Module.finrank ℝ E : ℝ) / 2 -
        Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹) 2 1,
      ∃ U : ℝ → Lp ℂ r (volume : Measure E),
        (∀ᵐ t, Tendsto (fun s : Finset ℤ ↦
          eLpNorm (⇑(U t) - ⇑(∑ j ∈ s, waveCosPropagator ℂ t (f.block j))) r volume) atTop
            (𝓝 0)) ∧
        Tendsto (fun s : Finset ℤ ↦ eLpNorm (fun t ↦
          eLpNorm (⇑(U t) - ⇑(∑ j ∈ s, waveCosPropagator ℂ t (f.block j))) r volume) 2 volume)
            atTop (𝓝 0) ∧
        eLpNorm (fun t ↦ ‖U t‖ₑ) 2 volume ≤ C * ‖f‖ₑ :=
  φ.exists_tendsto_eLpNorm_eLpNorm_sub_sum_apply_block one_le_two _ _
    (fun x ↦ (continuous_waveCosPropagator_apply x).aestronglyMeasurable)
    (φ.exists_eLpNorm_eLpNorm_waveCosPropagator_littlewoodPaley_le_of_le_endpoint hn hr)

/-- **`D⁻¹ sin(tD)` on data in `\dot B^{γ - 1}_{2,1}` at the pairs `(2, r)`.** Under the hypotheses
of `ContDiffBump.exists_tendsto_eLpNorm_eLpNorm_sub_sum_waveCosPropagator_block_of_le_endpoint`,
there is `C` such that for every `g ∈ \dot B^{γ - 1}_{2,1}` the dyadic series
`∑ⱼ D⁻¹ sin(tD) Pⱼ g` converges: to some `U : ℝ → L^r` in `L^r` for almost every `t` and in
`L²_t L^r_x`, with `‖U‖_{L²_t L^r_x} ≤ C ‖g‖_{\dot B^{γ - 1}_{2,1}}`. -/
theorem exists_tendsto_eLpNorm_eLpNorm_sub_sum_waveSinPropagator_block_of_le_endpoint
    (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤ ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ g : HomogeneousBesovSpace ℂ φ ((Module.finrank ℝ E : ℝ) / 2 -
        Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹ - 1) 2 1,
      ∃ U : ℝ → Lp ℂ r (volume : Measure E),
        (∀ᵐ t, Tendsto (fun s : Finset ℤ ↦
          eLpNorm (⇑(U t) - ⇑(∑ j ∈ s, waveSinPropagator ℂ t (g.block j))) r volume) atTop
            (𝓝 0)) ∧
        Tendsto (fun s : Finset ℤ ↦ eLpNorm (fun t ↦
          eLpNorm (⇑(U t) - ⇑(∑ j ∈ s, waveSinPropagator ℂ t (g.block j))) r volume) 2 volume)
            atTop (𝓝 0) ∧
        eLpNorm (fun t ↦ ‖U t‖ₑ) 2 volume ≤ C * ‖g‖ₑ :=
  φ.exists_tendsto_eLpNorm_eLpNorm_sub_sum_apply_block one_le_two _ _
    (fun x ↦ (continuous_waveSinPropagator_apply x).aestronglyMeasurable)
    (φ.exists_eLpNorm_eLpNorm_waveSinPropagator_littlewoodPaley_le_of_le_endpoint hn hr)

/-! ### The limits solve the wave equation -/

section WaveEquation

variable {σ : ℝ} {b q : ℝ≥0∞}

/-- **The `cos(tD)` evolution of Besov data solves the wave equation.** Let
`f ∈ \dot B^σ_{2,b}` and let `U : ℝ → L^r` be a limit of the dyadic series `∑ⱼ cos(tD) Pⱼ f`, in
`L^r` for almost every `t` and in the mixed norm `L^q_t L^r_x` for some `1 ≤ q`, such as the limits
of `ContDiffBump.exists_tendsto_eLpNorm_eLpNorm_sub_sum_waveCosPropagator_block` and its
variants at the pairs `(∞, r)` and `(2, r)`. Then `∂ₜ²U = ΔU` in the sense of distributions,
tested against `θ(t) ψ(x)`: for every Schwartz function `ψ` and every compactly supported `C²`
function `θ` of time,

`∫ θ''(t) ∫ conj (ψ(x)) U(t)(x) dx dt = ∫ θ(t) ∫ conj (Δψ(x)) U(t)(x) dx dt`. -/
theorem integral_deriv_deriv_mul_integral_inner_eq_of_tendsto_sum_waveCosPropagator_block
    (hq : 1 ≤ q) {f : HomogeneousBesovSpace ℂ φ σ 2 b} {U : ℝ → Lp ℂ r (volume : Measure E)}
    (hae : ∀ᵐ t, Tendsto (fun s : Finset ℤ ↦
      eLpNorm (⇑(U t) - ⇑(∑ j ∈ s, waveCosPropagator ℂ t (f.block j))) r volume) atTop (𝓝 0))
    (hlim : Tendsto (fun s : Finset ℤ ↦ eLpNorm (fun t ↦
      eLpNorm (⇑(U t) - ⇑(∑ j ∈ s, waveCosPropagator ℂ t (f.block j))) r volume) q volume)
        atTop (𝓝 0))
    (ψ : 𝓢(E, ℂ)) {θ : ℝ → ℂ} (hθ : ContDiff ℝ 2 θ) (hθc : HasCompactSupport θ) :
    ∫ t, deriv (deriv θ) t * ∫ x, ⟪ψ x, U t x⟫_ℂ = ∫ t, θ t * ∫ x, ⟪(Δ ψ) x, U t x⟫_ℂ := by
  have h (s : Finset ℤ) (t : ℝ) : ∑ j ∈ s, waveCosPropagator ℂ t (f.block j) =
      waveDuhamelSolution ℂ (∑ j ∈ s, f.block j) 0 0 t := by
    simp [map_sum]
  simp_rw [h] at hae hlim
  exact integral_deriv_deriv_mul_integral_inner_eq_of_tendsto_waveDuhamelSolution hq hae hlim ψ hθ
    hθc

/-- **The `D⁻¹ sin(tD)` evolution of Besov data solves the wave equation.** Let
`g ∈ \dot B^σ_{2,b}` and let `U : ℝ → L^r` be a limit of the dyadic series `∑ⱼ D⁻¹ sin(tD) Pⱼ g`,
in `L^r` for almost every `t` and in the mixed norm `L^q_t L^r_x` for some `1 ≤ q`, such as the
limits of `ContDiffBump.exists_tendsto_eLpNorm_eLpNorm_sub_sum_waveSinPropagator_block` and its
variants at the pairs `(∞, r)` and `(2, r)`. Then `∂ₜ²U = ΔU` in the sense of distributions,
tested against `θ(t) ψ(x)`: for every Schwartz function `ψ` and every compactly supported `C²`
function `θ` of time,

`∫ θ''(t) ∫ conj (ψ(x)) U(t)(x) dx dt = ∫ θ(t) ∫ conj (Δψ(x)) U(t)(x) dx dt`. -/
theorem integral_deriv_deriv_mul_integral_inner_eq_of_tendsto_sum_waveSinPropagator_block
    (hq : 1 ≤ q) {g : HomogeneousBesovSpace ℂ φ σ 2 b} {U : ℝ → Lp ℂ r (volume : Measure E)}
    (hae : ∀ᵐ t, Tendsto (fun s : Finset ℤ ↦
      eLpNorm (⇑(U t) - ⇑(∑ j ∈ s, waveSinPropagator ℂ t (g.block j))) r volume) atTop (𝓝 0))
    (hlim : Tendsto (fun s : Finset ℤ ↦ eLpNorm (fun t ↦
      eLpNorm (⇑(U t) - ⇑(∑ j ∈ s, waveSinPropagator ℂ t (g.block j))) r volume) q volume)
        atTop (𝓝 0))
    (ψ : 𝓢(E, ℂ)) {θ : ℝ → ℂ} (hθ : ContDiff ℝ 2 θ) (hθc : HasCompactSupport θ) :
    ∫ t, deriv (deriv θ) t * ∫ x, ⟪ψ x, U t x⟫_ℂ = ∫ t, θ t * ∫ x, ⟪(Δ ψ) x, U t x⟫_ℂ := by
  have h (s : Finset ℤ) (t : ℝ) : ∑ j ∈ s, waveSinPropagator ℂ t (g.block j) =
      waveDuhamelSolution ℂ 0 (∑ j ∈ s, g.block j) 0 t := by
    simp [map_sum]
  simp_rw [h] at hae hlim
  exact integral_deriv_deriv_mul_integral_inner_eq_of_tendsto_waveDuhamelSolution hq hae hlim ψ hθ
    hθc

end WaveEquation

/-! ### Continuity in time and the initial data

At the pairs `(∞, r)` the frequency-localized estimates hold at every time, not only at almost
every time, and the evolutions are continuous in time for the `L^r` distance. -/

section Continuous

/-- **`cos(tD)` on data in `\dot B^γ_{2,1}`, continuously in time, attaining the datum.** Let
`2 ≤ r ≤ ∞` and `γ = n / 2 - n / r`. There is `C` such that for every `f ∈ \dot B^γ_{2,1}` the
dyadic series `∑ⱼ cos(tD) Pⱼ f` converges in `L^r`, uniformly in `t`, to a continuous
`U : ℝ → L^r` with `‖U(t)‖_r ≤ C ‖f‖_{\dot B^γ_{2,1}}` for every `t`, and `U(0)` is the sum
`∑ⱼ Pⱼ f` of the blocks of `f` in `L^r`. So `U(t) → ∑ⱼ Pⱼ f` in `L^r` as `t → 0`: the evolution
attains its initial datum. -/
theorem exists_continuous_tendsto_iSup_eLpNorm_sub_sum_waveCosPropagator_block (hr : 2 ≤ r) :
    ∃ C : ℝ≥0, ∀ f : HomogeneousBesovSpace ℂ φ ((Module.finrank ℝ E : ℝ) / 2 -
        Module.finrank ℝ E * (r⁻¹).toReal) 2 1,
      ∃ U : ℝ → Lp ℂ r (volume : Measure E), Continuous U ∧
        Tendsto (fun s : Finset ℤ ↦ ⨆ t,
          eLpNorm (⇑(U t) - ⇑(∑ j ∈ s, waveCosPropagator ℂ t (f.block j))) r volume) atTop
            (𝓝 0) ∧
        (∀ t, ‖U t‖ₑ ≤ C * ‖f‖ₑ) ∧
        Tendsto (fun s : Finset ℤ ↦ eLpNorm (⇑(U 0) - ⇑(∑ j ∈ s, f.block j)) r volume) atTop
          (𝓝 0) := by
  obtain ⟨C, hC⟩ := φ.exists_continuous_tendsto_iSup_eLpNorm_sub_sum_apply_block _
    (fun t ↦ waveCosPropagator ℂ t) (φ.exists_eLpNorm_waveCosPropagator_littlewoodPaley_le hr)
    fun j m hm x t₀ ↦ by
      simpa only [← fourierMultiplierCLM_waveCosPropagator_apply] using
        φ.tendsto_eLpNorm_fourierMultiplierCLM_littlewoodPaley_sub hr hm
          (continuous_waveCosPropagator_apply x) t₀
  refine ⟨C, fun f ↦ ?_⟩
  obtain ⟨U, hU, hunif, hle⟩ := hC f
  refine ⟨U, hU, hunif, hle, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hunif
    (fun _ ↦ zero_le) fun s ↦ le_iSup_of_le 0 (le_of_eq ?_)⟩
  simp [waveCosPropagator_zero]

/-- **`D⁻¹ sin(tD)` on data in `\dot B^{γ - 1}_{2,1}`, continuously in time.** Let `2 ≤ r ≤ ∞` and
`γ = n / 2 - n / r`. There is `C` such that for every `g ∈ \dot B^{γ - 1}_{2,1}` the dyadic series
`∑ⱼ D⁻¹ sin(tD) Pⱼ g` converges in `L^r`, uniformly in `t`, to a continuous `U : ℝ → L^r` with
`‖U(t)‖_r ≤ C ‖g‖_{\dot B^{γ - 1}_{2,1}}` for every `t`, and `U(0) = 0`. -/
theorem exists_continuous_tendsto_iSup_eLpNorm_sub_sum_waveSinPropagator_block (hr : 2 ≤ r) :
    ∃ C : ℝ≥0, ∀ g : HomogeneousBesovSpace ℂ φ ((Module.finrank ℝ E : ℝ) / 2 -
        Module.finrank ℝ E * (r⁻¹).toReal - 1) 2 1,
      ∃ U : ℝ → Lp ℂ r (volume : Measure E), Continuous U ∧
        Tendsto (fun s : Finset ℤ ↦ ⨆ t,
          eLpNorm (⇑(U t) - ⇑(∑ j ∈ s, waveSinPropagator ℂ t (g.block j))) r volume) atTop
            (𝓝 0) ∧
        (∀ t, ‖U t‖ₑ ≤ C * ‖g‖ₑ) ∧ U 0 = 0 := by
  obtain ⟨C, hC⟩ := φ.exists_continuous_tendsto_iSup_eLpNorm_sub_sum_apply_block _
    (fun t ↦ waveSinPropagator ℂ t) (φ.exists_eLpNorm_waveSinPropagator_littlewoodPaley_le hr)
    fun j m hm x t₀ ↦ by
      simpa only [← fourierMultiplierCLM_waveSinPropagator_apply] using
        φ.tendsto_eLpNorm_fourierMultiplierCLM_littlewoodPaley_sub hr hm
          (continuous_waveSinPropagator_apply x) t₀
  refine ⟨C, fun g ↦ ?_⟩
  obtain ⟨U, hU, hunif, hle⟩ := hC g
  refine ⟨U, hU, hunif, hle, ?_⟩
  -- At `t = 0` every partial sum vanishes, so the uniform convergence forces `‖U(0)‖_r = 0`.
  have h0 : Tendsto (fun _ : Finset ℤ ↦ ‖U 0‖ₑ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hunif (fun _ ↦ zero_le)
      fun s ↦ le_iSup_of_le 0 (le_of_eq ?_)
  · exact eNorm_eq_zero.1 (tendsto_nhds_unique tendsto_const_nhds h0)
  simp only [waveSinPropagator_zero, zero_apply, Finset.sum_const_zero, Lp.eNorm_def]
  refine eLpNorm_congr_ae ?_
  filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure E)] with x hx
  rw [Pi.sub_apply, hx, Pi.zero_apply, sub_zero]

end Continuous

/-! ### The initial velocity

The `D⁻¹ sin(tD)` evolution of `g ∈ \dot B^σ_{2,1}` has the initial velocity `g` in the sense of
distributions. Tested against a Schwartz function `ψ`, the pieces `⟪ψ, D⁻¹ sin(tD) Pⱼ g⟫` are
differentiable in `t` with derivatives `⟪ψ, cos(tD) Pⱼ g⟫`, and these are bounded uniformly in `t`
by a summable sequence: the block `Pⱼ g` is reproduced by the blocks `P_{j + d}`, `|d| ≤ L`, which
are self-adjoint and commute with `cos(tD)`, so

`|⟪ψ, cos(tD) Pⱼ g⟫| ≤ ∑_{|d| ≤ L} ‖P_{j + d} ψ‖₂ ‖Pⱼ g‖₂ ≤ C 2^{jσ} ‖Pⱼ g‖₂`

by the bounds `‖Pₖ ψ‖₂ ≤ C 2^{kσ}` of Schwartz functions for `σ ≤ n / 2`
(`SchwartzMap.exists_two_rpow_mul_norm_fourierMultiplierCLM_littlewoodPaley_le`). So the series of
pairings may be differentiated term by term (`hasDerivAt_tsum`). -/

section Velocity

variable {σ : ℝ}

/-- The pairings `⟪ψ, cos(tD) Pⱼ g⟫` are bounded by `K 2^{jσ} ‖Pⱼ g‖₂`, uniformly in `t` and in
`g ∈ \dot B^σ_{2,1}`, for `σ ≤ n / 2`. -/
private theorem exists_norm_inner_waveCosPropagator_block_le
    (hσ : σ ≤ (Module.finrank ℝ E : ℝ) / 2) (ψ : 𝓢(E, ℂ)) :
    ∃ K : ℝ, ∀ (g : HomogeneousBesovSpace ℂ φ σ 2 1) (j : ℤ) (t : ℝ),
      ‖⟪ψ.toLp 2, waveCosPropagator ℂ t (g.block j)⟫_ℂ‖ ≤ K * ‖g.weightedBlocks j‖ := by
  obtain ⟨C, hC⟩ := ψ.exists_two_rpow_mul_norm_fourierMultiplierCLM_littlewoodPaley_le φ
    (s := -σ) (by linarith)
  set m : ℤ → Lp ℂ ∞ (volume : Measure E) := fun j ↦ (φ.memLp_ofReal_littlewoodPaley j ∞).toLp _
  have hm (j : ℤ) : m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ) :=
    (φ.memLp_ofReal_littlewoodPaley j ∞).coeFn_toLp
  obtain ⟨L, hL⟩ := HomogeneousBesovSpace.exists_sum_fourierMultiplierCLM_block_eq
    (G := ℂ) (s := σ) (q := 1) φ
  -- `‖Pₖ ψ‖₂ ≤ C 2^{kσ}`.
  have hψ (k : ℤ) : ‖Lp.fourierMultiplierCLM ℂ (m k) (ψ.toLp 2)‖ ≤ C * (2 : ℝ) ^ (σ * k) := by
    have h := hC k (m k) (hm k)
    rw [neg_mul, Real.rpow_neg zero_le_two, inv_mul_le_iff₀ (by positivity)] at h
    linarith
  refine ⟨C * ∑ d ∈ Finset.Ico (-(L : ℤ)) L, (2 : ℝ) ^ (σ * d), fun g j t ↦ ?_⟩
  rw [← hL hm g j, map_sum, inner_sum, HomogeneousBesovSpace.norm_weightedBlocks_apply,
    Finset.mul_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ ↦ ?_)
  -- Move `P_{d + j}` onto `ψ`, then use `‖cos(tD)‖ ≤ 1`.
  have hsym (x y : Lp ℂ 2 (volume : Measure E)) :
      ⟪x, Lp.fourierMultiplierCLM ℂ (m (d + j)) y⟫_ℂ =
        ⟪Lp.fourierMultiplierCLM ℂ (m (d + j)) x, y⟫_ℂ :=
    ((Lp.isSelfAdjoint_fourierMultiplierCLM
      (Lp.star_eq_self_of_ae_eq_ofReal (hm (d + j)))).isSymmetric x y).symm
  rw [← fourierMultiplierCLM_waveCosPropagator_apply, hsym]
  refine (norm_inner_le_norm _ _).trans ?_
  have hcos : ‖waveCosPropagator ℂ t (g.block j)‖ ≤ ‖g.block j‖ :=
    ((waveCosPropagator ℂ t).le_opNorm _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (norm_waveCosPropagator_le t))
  have h2 : C * (2 : ℝ) ^ (σ * ((d + j : ℤ) : ℝ)) = C * 2 ^ (σ * d) * 2 ^ (σ * j) := by
    rw [Int.cast_add, mul_add, Real.rpow_add two_pos, mul_assoc]
  rw [← mul_assoc, ← h2]
  exact mul_le_mul (hψ (d + j)) hcos (norm_nonneg _) ((norm_nonneg _).trans (hψ (d + j)))

/-- **The velocity of the `D⁻¹ sin(tD)` evolution of Besov data.** Let `σ ≤ n / 2`, let
`g ∈ \dot B^σ_{2,1}`, and let `U : ℝ → L^r` be such that for every `t` the dyadic series
`∑ⱼ D⁻¹ sin(tD) Pⱼ g` converges to `U(t)` in `L^r`, as for the limits of
`ContDiffBump.exists_continuous_tendsto_iSup_eLpNorm_sub_sum_waveSinPropagator_block`. Then for
every Schwartz function `ψ` the pairing `t ↦ ∫ conj (ψ(x)) U(t)(x) dx` is differentiable, with
derivative the absolutely convergent series `∑ⱼ ⟪ψ, cos(tD) Pⱼ g⟫`: weakly,
`∂ₜU(t) = ∑ⱼ cos(tD) Pⱼ g`. -/
theorem hasDerivAt_integral_inner_of_tendsto_sum_waveSinPropagator_block
    (hσ : σ ≤ (Module.finrank ℝ E : ℝ) / 2) {g : HomogeneousBesovSpace ℂ φ σ 2 1}
    {U : ℝ → Lp ℂ r (volume : Measure E)}
    (hU : ∀ t, Tendsto (fun s : Finset ℤ ↦
      eLpNorm (⇑(U t) - ⇑(∑ j ∈ s, waveSinPropagator ℂ t (g.block j))) r volume) atTop (𝓝 0))
    (ψ : 𝓢(E, ℂ)) (t : ℝ) :
    HasDerivAt (fun t ↦ ∫ x, ⟪ψ x, U t x⟫_ℂ)
      (∑' j, ∫ x, ⟪ψ x, waveCosPropagator ℂ t (g.block j) x⟫_ℂ) t := by
  have := (ENNReal.HolderConjugate.conjExponent (Fact.out : (1 : ℝ≥0∞) ≤ r)).symm
  have hpair (h : Lp ℂ 2 (volume : Measure E)) : ∫ x, ⟪ψ x, h x⟫_ℂ = ⟪ψ.toLp 2, h⟫_ℂ := by
    rw [L2.inner_def]
    exact integral_congr_ae (by filter_upwards [ψ.coeFn_toLp 2] with x hx; rw [hx])
  -- At every time the pairing of `U(τ)` is the sum of the pairings of the pieces.
  have hsum (τ : ℝ) : HasSum (fun j ↦ ⟪ψ.toLp 2, waveSinPropagator ℂ τ (g.block j)⟫_ℂ)
      (∫ x, ⟪ψ x, U τ x⟫_ℂ) := by
    have hlim := ENNReal.Tendsto.const_mul (hU τ)
      (Or.inr (ψ.memLp (ENNReal.conjExponent r) volume).eLpNorm_ne_top)
    rw [mul_zero] at hlim
    rw [HasSum, tendsto_iff_edist_tendsto_0]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ ↦ zero_le)
      fun s ↦ ?_
    rw [← inner_sum, ← hpair, edist_comm, eDist_eq_eNorm_sub, ← integral_sub
      ((ψ.memLp (ENNReal.conjExponent r) volume).integrable_inner_of_holderConjugate
        (Lp.memLp (U τ)))
      ((ψ.memLp 2 volume).integrable_inner_of_holderConjugate (Lp.memLp _))]
    simp_rw [← inner_sub_right]
    exact enorm_integral_inner_le (u := ψ)
  obtain ⟨K, hK⟩ := φ.exists_norm_inner_waveCosPropagator_block_le hσ ψ
  have hsummable : Summable fun j ↦ K * ‖g.weightedBlocks j‖ := by
    have h := (memℓp_gen_iff (p := 1) (by simp)).1 (lp.memℓp g.weightedBlocks)
    simpa using h.mul_left K
  have hder (j : ℤ) (τ : ℝ) : HasDerivAt
      (fun τ ↦ ⟪ψ.toLp 2, waveSinPropagator ℂ τ (g.block j)⟫_ℂ)
      ⟪ψ.toLp 2, waveCosPropagator ℂ τ (g.block j)⟫_ℂ τ := by
    have h := (hasDerivAt_const τ (ψ.toLp 2)).inner ℂ (hasDerivAt_waveSinPropagator_apply
      (g.block j) τ)
    rwa [inner_zero_left, add_zero] at h
  have heq : (fun τ ↦ ∫ x, ⟪ψ x, U τ x⟫_ℂ) =
      fun τ ↦ ∑' j, ⟪ψ.toLp 2, waveSinPropagator ℂ τ (g.block j)⟫_ℂ :=
    funext fun τ ↦ (hsum τ).tsum_eq.symm
  rw [heq, tsum_congr fun j ↦ hpair (waveCosPropagator ℂ t (g.block j))]
  exact hasDerivAt_tsum hsummable hder (fun j τ ↦ hK g j τ) (hsum 0).summable t

/-- **The `D⁻¹ sin(tD)` evolution of Besov data attains its initial velocity.** Let `σ ≤ n / 2`, let
`g ∈ \dot B^σ_{2,1}`, and let `U : ℝ → L^r` be such that for every `t` the dyadic series
`∑ⱼ D⁻¹ sin(tD) Pⱼ g` converges to `U(t)` in `L^r`, as for the limits of
`ContDiffBump.exists_continuous_tendsto_iSup_eLpNorm_sub_sum_waveSinPropagator_block`. Then
`∂ₜU(0) = g` in the sense of distributions: for every Schwartz function `ψ`,

`d/dt|_{t = 0} ∫ ψ(x) U(t)(x) dx = ⟨g, ψ⟩`,

where `g` is realised as the tempered distribution `∑ⱼ Pⱼ g`
(`TauCeti.HomogeneousBesovSpace.realization`). -/
theorem hasDerivAt_integral_mul_of_tendsto_sum_waveSinPropagator_block
    (hσ : σ ≤ (Module.finrank ℝ E : ℝ) / 2) {g : HomogeneousBesovSpace ℂ φ σ 2 1}
    {U : ℝ → Lp ℂ r (volume : Measure E)}
    (hU : ∀ t, Tendsto (fun s : Finset ℤ ↦
      eLpNorm (⇑(U t) - ⇑(∑ j ∈ s, waveSinPropagator ℂ t (g.block j))) r volume) atTop (𝓝 0))
    (ψ : 𝓢(E, ℂ)) :
    HasDerivAt (fun t ↦ ∫ x, ψ x * U t x)
      (HomogeneousBesovSpace.realization (hσ.lt_or_eq.imp
        (fun h ↦ by simpa [div_eq_mul_inv] using h) fun h ↦ ⟨by simp [h, div_eq_mul_inv], le_rfl⟩)
        g ψ) 0 := by
  set χ := SchwartzMap.conjCLM ψ
  -- `ψ x * v = ⟪conj (ψ x), v⟫`.
  have hconj (v : E → ℂ) : (fun x ↦ ψ x * v x) = fun x ↦ ⟪χ x, v x⟫_ℂ := by
    ext x
    rw [SchwartzMap.conjCLM_apply, RCLike.inner_apply, RCLike.conj_conj, mul_comm]
  have h := φ.hasDerivAt_integral_inner_of_tendsto_sum_waveSinPropagator_block hσ hU χ 0
  simp only [waveCosPropagator_zero, ContinuousLinearMap.id_apply] at h
  convert h using 1
  · ext t
    rw [hconj]
  -- The realisation of `g` is the sum of its blocks, which converges absolutely against `ψ`.
  obtain ⟨K, hK⟩ := φ.exists_norm_inner_waveCosPropagator_block_le hσ χ
  have hsummable : Summable fun j ↦ ∫ x, ⟪χ x, g.block j x⟫_ℂ := by
    refine Summable.of_norm_bounded (g := fun j ↦ K * ‖g.weightedBlocks j‖) ?_ fun j ↦ ?_
    · have h := (memℓp_gen_iff (p := 1) (by simp)).1 (lp.memℓp g.weightedBlocks)
      simpa using h.mul_left K
    · have := hK g j 0
      rw [waveCosPropagator_zero, ContinuousLinearMap.id_apply, L2.inner_def] at this
      refine (le_of_eq ?_).trans this
      congr 1
      exact integral_congr_ae (by filter_upwards [χ.coeFn_toLp 2] with x hx; rw [hx])
  have htsum : Tendsto (fun s : Finset ℤ ↦ ∑ j ∈ s, ∫ x, ⟪χ x, g.block j x⟫_ℂ) atTop
      (𝓝 (∑' j, ∫ x, ⟪χ x, g.block j x⟫_ℂ)) :=
    hsummable.hasSum
  refine tendsto_nhds_unique (((continuous_eval_const ψ).tendsto _).comp
    (HomogeneousBesovSpace.tendsto_sum_realization _ g))
    ((htsum.comp Finset.tendsto_Ioc_atBot_prod_atTop).congr fun ab ↦ ?_)
  have heval (u : ℤ → 𝓢'(E, ℂ)) (s : Finset ℤ) : (∑ j ∈ s, u j) ψ = ∑ j ∈ s, u j ψ :=
    map_sum (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ ψ) u s
  simp only [Function.comp_apply, heval]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← HomogeneousBesovSpace.coe_block, Lp.toTemperedDistribution_apply]
  simp_rw [smul_eq_mul]
  rw [hconj]

end Velocity

end ContDiffBump
