/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Strichartz.HomogeneousBesov
public import TauCeti.Analysis.PDE.Wave.Propagator
import TauCeti.Analysis.PDE.Wave.MixedNorm
import TauCeti.Analysis.PDE.Wave.TimeExponentTwo

/-!
# The free wave equation with data in homogeneous Besov spaces

On a real inner product space `E` of dimension `n`, let `D = √(-Δ)` and let `Pⱼ`, `j ∈ ℤ`, be the
homogeneous Littlewood–Paley blocks built from a bump function `φ`. The free wave equation
`∂ₜ²u = Δu` with data `u(0) = f` and `∂ₜu(0) = g` in `L²` is solved by
`u(t) = cos(tD) f + D⁻¹ sin(tD) g` (`TauCeti.waveCosPropagator`, `TauCeti.waveSinPropagator`), and
for a wave-admissible pair `(q, r)` with scaling-critical regularity `γ` it satisfies the
Strichartz estimate with the norms of the data in the homogeneous Besov spaces `\dot B^γ_{2,1}` and
`\dot B^{γ - 1}_{2,1}`
(`ContDiffBump.exists_eLpNorm_eLpNorm_waveCosPropagator_add_waveSinPropagator_le_tsum`).

This file solves the equation for data in these Besov spaces themselves
(`TauCeti.HomogeneousBesovSpace`), which are spaces of tempered distributions modulo those with
spectrum at the origin, not of `L²` functions: the two terms of the solution are the dyadic series

`cos(tD) f = ∑ⱼ cos(tD) Pⱼ f` and `D⁻¹ sin(tD) g = ∑ⱼ D⁻¹ sin(tD) Pⱼ g`,

whose pieces are the evolutions of the `L²` blocks of the data. For each series there is
`U : ℝ → L^r` such that the partial sums converge to `U(t)` in `L^r` for almost every time `t` and
to `U` in `L^q_t L^r_x`, with

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
its `D⁻¹ sin(tD)` counterpart). When the data are `L²` functions, the sums are
`cos(tD) f` and `D⁻¹ sin(tD) g` for almost every `t`
(`ContDiffBump.ae_ae_eq_apply_of_tendsto_eLpNorm_sub_sum_apply_block`), so this extends the
solution of the free wave equation from `L²` data.

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
open scoped ENNReal NNReal

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
solution uniformly in space and time for `f ∈ \dot B^{n/2}_{2,1}`. -/
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

end ContDiffBump
