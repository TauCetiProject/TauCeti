/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Wave.Endpoint
public import TauCeti.Analysis.PDE.Wave.Energy
import TauCeti.Analysis.Fourier.Bernstein
import TauCeti.Analysis.PDE.Strichartz.LittlewoodPaley
import TauCeti.Analysis.PDE.Wave.MixedNorm
import TauCeti.Data.ENNReal.Holder
import TauCeti.MeasureTheory.Function.Lp.MixedNorm
import TauCeti.MeasureTheory.Function.Lp.Star

/-!
# Strichartz estimates for the wave equation at the pairs `(2, r)`

Let `E` have dimension `n ≥ 4`, let `W₊(t) = exp(itD)`, `D = √(-Δ)`, be the half-wave propagator,
and let `Pⱼ`, `j ∈ ℤ`, be the `L²` Fourier multipliers with the homogeneous Littlewood–Paley cutoffs
`ψⱼ` (`ContDiffBump.littlewoodPaley`). The wave-admissible pairs with time exponent `q = 2` are the
`(2, r)` with `1 + (n - 1) / r ≤ (n - 1) / 2`, that is `r₀ ≤ r ≤ ∞` for the endpoint exponent
`r₀ = 2 (n - 1) / (n - 3)`. At `r = r₀` the frequency-localized estimates are the Keel–Tao endpoint
estimates of `TauCeti.Analysis.PDE.Wave.Endpoint`. This file proves them at the **non-sharp pairs**
`(2, r)`, `r₀ < r ≤ ∞`, where `1 + (n - 1) / r < (n - 1) / 2`, with the scaling-critical regularity
`γ = n / 2 - n / r - 1 / 2`:

* `‖W₊(t) Pⱼ f‖_{L²_t L^r_x} ≤ C 2^{jγ} ‖f‖₂`, in mixed norm
  (`ContDiffBump.exists_eLpNorm_eLpNorm_halfWavePropagator_littlewoodPaley_le_of_lt_endpoint`), in
  weak form, and in the dual form `‖∫ W₊(-s) Pⱼ F(s) ds‖₂ ≤ C 2^{jγ} ‖F‖_{L²_t L^{r'}_x}`
  (`ContDiffBump.exists_enorm_integral_halfWavePropagator_neg_littlewoodPaley_le_of_lt_endpoint`).
  Joined with the endpoint case, the mixed-norm form holds at every pair `(2, r)`
  (`ContDiffBump.exists_eLpNorm_eLpNorm_halfWavePropagator_littlewoodPaley_le_of_le_endpoint`);
* on the whole time line, with data in the homogeneous Besov space `\dot B^γ_{2,1}`,
  `‖W₊(t) f‖_{L²_t L^r_x} ≤ C ∑ⱼ 2^{jγ} ‖Pⱼ f‖₂` and the same for `W₋(t) = W₊(-t)`, now at every
  pair `(2, r)`, the endpoint included
  (`ContDiffBump.exists_eLpNorm_eLpNorm_halfWavePropagator_le_tsum_of_le_endpoint`);
* for `r < ∞`, with data in the homogeneous Sobolev space `\dot H^γ` in its Littlewood–Paley form,
  `‖W₊(t) f‖_{L²_t L^r_x} ≤ C (∑ⱼ 2^{2jγ} ‖Pⱼ f‖₂²)^{1/2}` and the same for `W₋(t)`, again at every
  pair `(2, r)`, the endpoint included
  (`ContDiffBump.exists_eLpNorm_eLpNorm_halfWavePropagator_le_tsum_sq_rpow_of_le_endpoint`).

The same estimates hold for the propagators of the wave equation `∂ₜ²u = Δu`, at every pair
`(2, r)`, the endpoint included: for `cos(tD)` with the weight `2^{jγ}`, for `D⁻¹ sin(tD)` with the
weight `2^{j(γ - 1)}`, and for the free solution `u(t) = cos(tD) f + D⁻¹ sin(tD) g` with data
`u(0) = f` and `∂ₜu(0) = g`,

`‖u‖_{L²_t L^r_x} ≤ C (∑ⱼ 2^{jγ} ‖Pⱼ f‖₂ + ∑ⱼ 2^{j(γ - 1)} ‖Pⱼ g‖₂)`

(in the `ContDiffBump` namespace,
`exists_eLpNorm_eLpNorm_waveCosPropagator_add_waveSinPropagator_le_tsum_of_le_endpoint`), with the
square sums in place of the `ℓ¹` sums when `r < ∞`. Every strong solution of the free equation on an
interval of times containing `0` agrees there with the free solution for `f = u(0)` and
`g = ∂ₜu(0)`, so it satisfies these estimates on that interval
(`ContDiffBump.exists_eLpNorm_eLpNorm_le_tsum_of_isWaveSolutionOn_of_le_endpoint`). Together with
the pairs with `q > 2` of `TauCeti.Analysis.PDE.Wave.HomogeneousStrichartz` and
`TauCeti.Analysis.PDE.Wave.SobolevStrichartz`, which also treat `q = ∞`, this gives the
homogeneous estimates of Tao's Theorem 2.6 at every wave-admissible pair with finite `r` in
dimension `n ≥ 4`. At `r = ∞` only the forms with `\dot B^γ_{2,1}` and `\dot B^{γ - 1}_{2,1}` data
are proved, not the `\dot H^γ × \dot H^{γ - 1}` form of Tao's theorem.

At the pairs `(2, r)` with `r > r₀` the abstract endpoint theorem does not apply directly. Instead
the estimates come from the endpoint ones by **Bernstein's inequality**: some dyadic multiplier
`Qⱼ` reproduces the block, `Pⱼ Qⱼ = Pⱼ`
(`ContDiffBump.exists_fourierMultiplierCLM_dyadicMultiplier_eq`), and `Qⱼ` is bounded from
`L^{r₀}` to `L^r` with norm at most a constant times `2^{jn (1/r₀ - 1/r)}`
(`ContDiffBump.eLpNorm_dyadicMultiplier_le_of_le`). Since
`n / 2 - n / r₀ - 1 / 2 + n (1 / r₀ - 1 / r) = γ`, the powers of `2^j` match. In the dual form
Bernstein's inequality is applied to the forcing, from `L^{r'}` to `L^{r₀'}`.

Since `cos(τD) = (W₊(τ) + W₊(-τ)) / 2` and `D⁻¹ sin(τD) Pⱼ` is `2^{-j}` times a combination of
`W₊(±τ)` applied to a reproducing multiplier of `Pⱼ`, the block estimates for `cos(tD)` and
`D⁻¹ sin(tD)` follow from those for `W₊(t)`
(`ContDiffBump.exists_eLpNorm_eLpNorm_waveCosPropagator_littlewoodPaley_le_of_halfWavePropagator`,
`ContDiffBump.exists_eLpNorm_eLpNorm_waveSinPropagator_littlewoodPaley_le_of_halfWavePropagator`).
All block estimates are summed over `j` by Minkowski's inequality, in the `ℓ¹` form
`ContDiffBump.exists_eLpNorm_eLpNorm_le_mul_tsum` and, through the Littlewood–Paley inequality in
`L^r`, in the square-sum form `ContDiffBump.exists_eLpNorm_eLpNorm_le_mul_tsum_sq_rpow`.

## References

* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980,
  Corollary 1.3.
* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Theorem 2.6 and its proof.
-/

public section

open MeasureTheory TauCeti
open scoped ENNReal NNReal InnerProductSpace FourierTransform SchwartzMap

namespace ContDiffBump

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (φ : ContDiffBump (0 : E)) {r r' : ℝ≥0∞}

/-- The powers of `2^j` in the Bernstein step: the endpoint power `n / 2 - n / r₀ - 1 / 2` and the
cost `n (1 / r₀ - 1 / r)` of passing from `L^{r₀}` to `L^r` add up to `n / 2 - n / r - 1 / 2`. -/
private theorem ofReal_rpow_mul_ofReal_rpow (j : ℤ) (n a b : ℝ) :
    ENNReal.ofReal (((2 : ℝ) ^ j) ^ (n * (a - b))) *
        ENNReal.ofReal (((2 : ℝ) ^ j) ^ (n / 2 - n * a - 2⁻¹)) =
      ENNReal.ofReal (((2 : ℝ) ^ j) ^ (n / 2 - n * b - 2⁻¹)) := by
  rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add (zpow_pos two_pos j)]
  ring_nf

/-- **The Strichartz estimate for the frequency-localized wave equation at a non-sharp pair
`(2, r)`** in mixed norm, for the Littlewood–Paley blocks. Let `E` have dimension `n ≥ 4`, let
`Pⱼ` be the `L²` Fourier multiplier with the Littlewood–Paley symbol `ψⱼ` built from `φ`, and let
`1 + (n - 1) / r < (n - 1) / 2`, so that `r` lies beyond the endpoint exponent, `r = ∞` included.
Put `γ = n / 2 - n / r - 1 / 2`. There is `C` such that for every `j ∈ ℤ` and every `f ∈ L²(E)`,

`‖W₊(t) Pⱼ f‖_{L²_t L^r_x} ≤ C 2^{jγ} ‖f‖₂`. -/
theorem exists_eLpNorm_eLpNorm_halfWavePropagator_littlewoodPaley_le_of_lt_endpoint
    (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal < ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ f : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (halfWavePropagator ℂ t (Lp.fourierMultiplierCLM ℂ m f)) r
            volume) 2 volume ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹)) * ‖f‖ₑ := by
  rcases eq_or_ne r 0 with rfl | hr0
  · exact ⟨0, fun _ _ _ _ ↦ by simp [eLpNorm_exponent_zero, Lp.aestronglyMeasurable]⟩
  obtain ⟨r₀, hr₀, hr₀r⟩ := exists_waveEndpoint_le (by exact_mod_cast hn) hr0 hr
  have hr₀2 := (two_le_and_ne_top_of_waveEndpoint (by exact_mod_cast hn) hr₀).1
  obtain ⟨C, hC⟩ :=
    φ.exists_eLpNorm_eLpNorm_halfWavePropagator_littlewoodPaley_le_of_endpoint hn hr₀
  obtain ⟨σ, hσ⟩ := φ.exists_fourierMultiplierCLM_dyadicMultiplier_eq (F := ℂ)
  set B := eLpNorm (𝓕⁻ ⇑(φ.dyadicDilate σ 0)) (1 + r⁻¹ - r₀⁻¹)⁻¹ volume
  refine ⟨B.toNNReal * C, fun j m hm f ↦ ?_⟩
  -- `Qⱼ W₊(t) Pⱼ f = W₊(t) Pⱼ f`, since `Qⱼ` commutes with `Pⱼ` and `W₊(t)`, and `Pⱼ Qⱼ = Pⱼ`.
  have hQP : φ.dyadicMultiplier ℂ σ j (Lp.fourierMultiplierCLM ℂ m f) =
      Lp.fourierMultiplierCLM ℂ m f := by
    rw [dyadicMultiplier_def, Lp.fourierMultiplierCLM_fourierMultiplierCLM_comm,
      ← dyadicMultiplier_def, hσ j m hm]
  have hQ (t : ℝ) : φ.dyadicMultiplier ℂ σ j
      (halfWavePropagator ℂ t (Lp.fourierMultiplierCLM ℂ m f)) =
        halfWavePropagator ℂ t (Lp.fourierMultiplierCLM ℂ m f) := by
    rw [dyadicMultiplier_def, fourierMultiplierCLM_halfWavePropagator_apply,
      ← dyadicMultiplier_def, hQP]
  -- Bernstein's inequality from `L^{r₀}` to `L^r` at each time.
  have hB := eLpNorm_eLpNorm_apply_le (φ.dyadicMultiplier ℂ σ j).continuous
    (fun g ↦ φ.eLpNorm_dyadicMultiplier_le_of_le σ j g (one_le_two.trans hr₀2) hr₀r)
    (u := fun t ↦ halfWavePropagator ℂ t (Lp.fourierMultiplierCLM ℂ m f)) (ρ := volume)
    (continuous_phasePropagator_apply _ _).aestronglyMeasurable (q := 2)
  simp_rw [hQ] at hB
  refine hB.trans ?_
  calc _ ≤ ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) *
          (r₀.toReal⁻¹ - r.toReal⁻¹))) * B *
        (C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r₀⁻¹).toReal - 2⁻¹)) * ‖f‖ₑ) := by
        gcongr
        exact hC j m hm f
    _ = _ := by
        rw [ENNReal.coe_mul, ENNReal.coe_toNNReal
          (φ.memLp_fourierInv_dyadicDilate σ 0 _).eLpNorm_ne_top,
          ← ENNReal.toReal_inv, ← ENNReal.toReal_inv,
          ← ofReal_rpow_mul_ofReal_rpow j _ (r₀⁻¹).toReal (r⁻¹).toReal]
        ring

/-- **The dual Strichartz estimate for the frequency-localized wave equation at a non-sharp pair
`(2, r)`**, for the Littlewood–Paley blocks. Let `E` have dimension `n ≥ 4`, let `Pⱼ` be the `L²`
Fourier multiplier with the Littlewood–Paley symbol `ψⱼ` built from `φ`, and let
`1 + (n - 1) / r < (n - 1) / 2`, with Hölder conjugate `r'`. Put `γ = n / 2 - n / r - 1 / 2`. There
is `C` such that for every `j ∈ ℤ` and every almost everywhere strongly measurable
`F : ℝ → L²(E)`,

`‖∫ W₊(-s) Pⱼ F(s) ds‖₂ ≤ C 2^{jγ} ‖F‖_{L²_t L^{r'}_x}`. -/
theorem exists_enorm_integral_halfWavePropagator_neg_littlewoodPaley_le_of_lt_endpoint
    [r'.HolderConjugate r] (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal < ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
        ‖∫ s, halfWavePropagator ℂ (-s) (Lp.fourierMultiplierCLM ℂ m (F s))‖ₑ ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹)) *
            eLpNorm (fun s ↦ eLpNorm (F s) r' volume) 2 volume := by
  obtain ⟨r₀, hr₀, hr₀r⟩ := exists_waveEndpoint_le (by exact_mod_cast hn)
    (ENNReal.HolderConjugate.ne_zero r r') hr
  have hr₀2 := (two_le_and_ne_top_of_waveEndpoint (by exact_mod_cast hn) hr₀).1
  -- Bernstein's inequality is applied to the forcing, from `L^{r'}` to `L^{r₀'}`, where `r₀'` is
  -- the Hölder conjugate of the endpoint exponent.
  have := ENNReal.HolderConjugate.inv_one_sub_inv' (one_le_two.trans hr₀2)
  obtain ⟨C, hC⟩ := φ.exists_enorm_integral_halfWavePropagator_neg_littlewoodPaley_le_of_endpoint
    (r' := (1 - r₀⁻¹)⁻¹) hn hr₀
  obtain ⟨σ, hσ⟩ := φ.exists_fourierMultiplierCLM_dyadicMultiplier_eq (F := ℂ)
  set B := eLpNorm (𝓕⁻ ⇑(φ.dyadicDilate σ 0)) (1 + (1 - r₀⁻¹)⁻¹⁻¹ - r'⁻¹)⁻¹ volume
  refine ⟨C * B.toNNReal, fun j m hm F hF ↦ ?_⟩
  -- `Pⱼ F(s) = Pⱼ Qⱼ F(s)`, and the endpoint estimate applies to `Qⱼ F`.
  have h := hC j m hm _ ((φ.dyadicMultiplier ℂ σ j).continuous.comp_aestronglyMeasurable hF)
  simp only [hσ j m hm] at h
  have hB := eLpNorm_eLpNorm_apply_le (φ.dyadicMultiplier ℂ σ j).continuous
    (fun g ↦ φ.eLpNorm_dyadicMultiplier_le_of_le σ j g (ENNReal.HolderConjugate.one_le r' r)
      (ENNReal.HolderConjugate.le_inv_one_sub_inv (q' := r') hr₀r)) hF (q := 2)
  refine h.trans ?_
  calc _ ≤ C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r₀⁻¹).toReal - 2⁻¹)) *
        (ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) *
          (r'.toReal⁻¹ - ((1 - r₀⁻¹)⁻¹).toReal⁻¹))) * B *
          eLpNorm (fun s ↦ eLpNorm (F s) r' volume) 2 volume) := by
        gcongr
    _ = _ := by
        rw [ENNReal.HolderConjugate.inv_toReal_sub_inv_toReal_inv_one_sub_inv (q := r) (q' := r')
            (one_le_two.trans hr₀2), ENNReal.coe_mul, ENNReal.coe_toNNReal
          (φ.memLp_fourierInv_dyadicDilate σ 0 _).eLpNorm_ne_top,
          ← ofReal_rpow_mul_ofReal_rpow j _ (r₀⁻¹).toReal (r⁻¹).toReal]
        ring

/-- **The Strichartz estimate for the frequency-localized wave equation at a non-sharp pair
`(2, r)`**, in weak form, for the Littlewood–Paley blocks. Let `E` have dimension `n ≥ 4`, let `Pⱼ`
be the `L²` Fourier multiplier with the Littlewood–Paley symbol `ψⱼ` built from `φ`, and let
`1 + (n - 1) / r < (n - 1) / 2`, with Hölder conjugate `r'`. Put `γ = n / 2 - n / r - 1 / 2`. There
is `C` such that for every `j ∈ ℤ`, every `f ∈ L²(E)` and every integrable `G : ℝ → L²(E)`,

`|∫ ⟪W₊(t) Pⱼ f, G(t)⟫ dt| ≤ C 2^{jγ} ‖f‖₂ ‖G‖_{L²_t L^{r'}_x}`. -/
theorem exists_enorm_integral_inner_halfWavePropagator_littlewoodPaley_le_of_lt_endpoint
    [r'.HolderConjugate r] (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal < ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ (f : Lp ℂ 2 (volume : Measure E)) (G : ℝ → Lp ℂ 2 (volume : Measure E)), Integrable G →
        ‖∫ t, ⟪halfWavePropagator ℂ t (Lp.fourierMultiplierCLM ℂ m f), G t⟫_ℂ‖ₑ ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹)) * ‖f‖ₑ *
            eLpNorm (fun t ↦ eLpNorm (G t) r' volume) 2 volume := by
  obtain ⟨C, hC⟩ :=
    φ.exists_enorm_integral_halfWavePropagator_neg_littlewoodPaley_le_of_lt_endpoint (r' := r')
      hn hr
  refine ⟨C, fun j m hm f G hG ↦ ?_⟩
  have hPG : Integrable fun t ↦
      halfWavePropagator ℂ (-t) (Lp.fourierMultiplierCLM ℂ m (G t)) :=
    integrable_phasePropagator_apply _ continuous_neg.aestronglyMeasurable
      ((Lp.fourierMultiplierCLM ℂ m).integrable_comp hG)
  -- `(W₊(t) Pⱼ)* = W₊(-t) Pⱼ`, since the symbol of `Pⱼ` is real.
  have hadj (t : ℝ) : ⟪halfWavePropagator ℂ t (Lp.fourierMultiplierCLM ℂ m f), G t⟫_ℂ =
      ⟪f, halfWavePropagator ℂ (-t) (Lp.fourierMultiplierCLM ℂ m (G t))⟫_ℂ := by
    rw [← ContinuousLinearMap.comp_apply (halfWavePropagator ℂ t),
      ← ContinuousLinearMap.adjoint_inner_right,
      adjoint_halfWavePropagator_comp_fourierMultiplierCLM_apply,
      Lp.star_eq_self_of_ae_eq_ofReal hm, fourierMultiplierCLM_halfWavePropagator_apply]
  simp_rw [hadj]
  rw [integral_inner hPG]
  calc _ ≤ ‖f‖ₑ * ‖∫ t, halfWavePropagator ℂ (-t) (Lp.fourierMultiplierCLM ℂ m (G t))‖ₑ :=
        eNorm_inner_le_eNorm _ _
    _ ≤ ‖f‖ₑ * (C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
          Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹)) *
          eLpNorm (fun t ↦ eLpNorm (G t) r' volume) 2 volume) := by
        gcongr
        exact hC j m hm G hG.aestronglyMeasurable
    _ = _ := by ring

/-- **The Strichartz estimate for the frequency-localized wave equation at the pairs `(2, r)`** in
mixed norm, for the Littlewood–Paley blocks. Let `E` have dimension `n ≥ 4`, let `Pⱼ` be the `L²`
Fourier multiplier with the Littlewood–Paley symbol `ψⱼ` built from `φ`, and let
`1 + (n - 1) / r ≤ (n - 1) / 2`, the endpoint exponent and `r = ∞` included. Put
`γ = n / 2 - n / r - 1 / 2`. There is `C` such that for every `j ∈ ℤ` and every `f ∈ L²(E)`,

`‖W₊(t) Pⱼ f‖_{L²_t L^r_x} ≤ C 2^{jγ} ‖f‖₂`.

This is the Keel–Tao endpoint estimate at `r = r₀` and Bernstein's inequality beyond it. -/
theorem exists_eLpNorm_eLpNorm_halfWavePropagator_littlewoodPaley_le_of_le_endpoint
    (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤ ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ f : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (halfWavePropagator ℂ t (Lp.fourierMultiplierCLM ℂ m f)) r
            volume) 2 volume ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹)) * ‖f‖ₑ :=
  hr.lt_or_eq.elim
    (φ.exists_eLpNorm_eLpNorm_halfWavePropagator_littlewoodPaley_le_of_lt_endpoint hn)
    (φ.exists_eLpNorm_eLpNorm_halfWavePropagator_littlewoodPaley_le_of_endpoint hn)

/-! ### Data in homogeneous Besov and Sobolev spaces -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- At the pairs `(2, r)` with `r ≠ 0`, the spatial exponent is at least `2`. -/
private theorem two_le_of_le_endpoint (hn : 3 < Module.finrank ℝ E) (hr0 : r ≠ 0)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤ ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    2 ≤ r :=
  two_le_of_waveAdmissible (E := E) (q := 2) hr0 (by simpa using hr) (by omega)

/-- `ContDiffBump.exists_eLpNorm_eLpNorm_le_tsum_of_littlewoodPaley_le_of_one_le` at a pair `(2, r)`
for a strongly continuous family `T(t)` of operators on `L²(E)`. At `r = 0` every mixed norm
vanishes; otherwise `2 ≤ r`. -/
private theorem exists_eLpNorm_eLpNorm_le_tsum_of_le_endpoint (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤ ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (σ : ℝ) (T : ℝ → Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (hT : ∀ x, Continuous fun t ↦ T t x)
    (hloc : ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ f : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (T t (Lp.fourierMultiplierCLM ℂ m f)) r volume) 2 volume ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) * ‖f‖ₑ) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (T t f) r volume) 2 volume ≤
          C * ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) *
            ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ := by
  rcases eq_or_ne r 0 with rfl | hr0
  · exact ⟨0, fun _ _ _ ↦ by simp [eLpNorm_exponent_zero, Lp.aestronglyMeasurable]⟩
  have := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
  exact φ.exists_eLpNorm_eLpNorm_le_tsum_of_littlewoodPaley_le_of_one_le one_le_two
    (one_le_two.trans (two_le_of_le_endpoint hn hr0 hr)) σ T
    (fun x ↦ (hT x).aestronglyMeasurable) hloc

/-- `ContDiffBump.exists_eLpNorm_eLpNorm_le_tsum_sq_rpow_of_littlewoodPaley_le` at a pair `(2, r)`
with `r < ∞`, for a strongly continuous family `T(t)` of operators on `L²(E)` commuting with the
Fourier multipliers. At `r = 0` every mixed norm vanishes; otherwise `2 ≤ r`. -/
private theorem exists_eLpNorm_eLpNorm_le_tsum_sq_rpow_of_le_endpoint
    (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤ ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hr_top : r ≠ ∞) (σ : ℝ)
    (T : ℝ → Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (hT : ∀ x, Continuous fun t ↦ T t x)
    (hcomm : ∀ t (n : Lp ℂ ∞ (volume : Measure E)) x,
      T t (Lp.fourierMultiplierCLM ℂ n x) = Lp.fourierMultiplierCLM ℂ n (T t x))
    (hloc : ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ f : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (T t (Lp.fourierMultiplierCLM ℂ m f)) r volume) 2 volume ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) * ‖f‖ₑ) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (T t f) r volume) 2 volume ≤
          C * (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ σ) *
            ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ) ^ 2) ^ (2⁻¹ : ℝ) := by
  rcases eq_or_ne r 0 with rfl | hr0
  · exact ⟨0, fun _ _ _ ↦ by simp [eLpNorm_exponent_zero, Lp.aestronglyMeasurable]⟩
  have := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
  exact φ.exists_eLpNorm_eLpNorm_le_tsum_sq_rpow_of_littlewoodPaley_le le_rfl
    (two_le_of_le_endpoint hn hr0 hr) hr_top σ T (fun x ↦ (hT x).aestronglyMeasurable) hcomm hloc

/-- **The Strichartz estimate for the half-wave propagator at the pairs `(2, r)` with data in
`\dot B^γ_{2,1}`.** Let `E` have dimension `n ≥ 4`, let `ψⱼ` be the Littlewood–Paley cutoffs built
from `φ`, and let `Pⱼ` be the `L²` Fourier multiplier with symbol `ψⱼ`. Let
`1 + (n - 1) / r ≤ (n - 1) / 2`, the endpoint exponent and `r = ∞` included, and let
`γ = n / 2 - n / r - 1 / 2`. There is `C` such that for every `f ∈ L²(E)`,

`‖W₊(t) f‖_{L²_t L^r_x} ≤ C ∑ⱼ 2^{jγ} ‖Pⱼ f‖₂`. -/
theorem exists_eLpNorm_eLpNorm_halfWavePropagator_le_tsum_of_le_endpoint
    (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤ ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (halfWavePropagator ℂ t f) r volume) 2 volume ≤
          C * ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹)) * ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ :=
  φ.exists_eLpNorm_eLpNorm_le_tsum_of_le_endpoint hn hr _ _ (continuous_phasePropagator_apply _)
    (φ.exists_eLpNorm_eLpNorm_halfWavePropagator_littlewoodPaley_le_of_le_endpoint hn hr)

/-- **The Strichartz estimate for the backward half-wave propagator at the pairs `(2, r)` with data
in `\dot B^γ_{2,1}`.** Under the hypotheses of
`ContDiffBump.exists_eLpNorm_eLpNorm_halfWavePropagator_le_tsum_of_le_endpoint`, for
`W₋(t) = W₊(-t)` there is `C` such that for every `f ∈ L²(E)`,

`‖W₊(-t) f‖_{L²_t L^r_x} ≤ C ∑ⱼ 2^{jγ} ‖Pⱼ f‖₂`. -/
theorem exists_eLpNorm_eLpNorm_halfWavePropagator_neg_le_tsum_of_le_endpoint
    (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤ ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (halfWavePropagator ℂ (-t) f) r volume) 2 volume ≤
          C * ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹)) * ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ := by
  obtain ⟨C, hC⟩ := φ.exists_eLpNorm_eLpNorm_halfWavePropagator_le_tsum_of_le_endpoint hn hr
  exact ⟨C, fun m hm f ↦ ((continuous_phasePropagator_apply _ f).aestronglyMeasurable
    |>.eLpNorm_eLpNorm_comp_neg).trans_le (hC m hm f)⟩

/-- **The Strichartz estimate for the half-wave propagator at the pairs `(2, r)` with data in
`\dot H^γ`.** Let `E` have dimension `n ≥ 4`, let `ψⱼ` be the Littlewood–Paley cutoffs built from
`φ`, and let `Pⱼ` be the `L²` Fourier multiplier with symbol `ψⱼ`. Let
`1 + (n - 1) / r ≤ (n - 1) / 2` with `r < ∞`, the endpoint exponent included, and let
`γ = n / 2 - n / r - 1 / 2`. There is `C` such that for every `f ∈ L²(E)`,

`‖W₊(t) f‖_{L²_t L^r_x} ≤ C (∑ⱼ 2^{2jγ} ‖Pⱼ f‖₂²)^{1/2}`. -/
theorem exists_eLpNorm_eLpNorm_halfWavePropagator_le_tsum_sq_rpow_of_le_endpoint
    (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤ ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hr_top : r ≠ ∞) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (halfWavePropagator ℂ t f) r volume) 2 volume ≤
          C * (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹)) *
              ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ) ^ 2) ^ (2⁻¹ : ℝ) :=
  φ.exists_eLpNorm_eLpNorm_le_tsum_sq_rpow_of_le_endpoint hn hr hr_top _ _
    (continuous_phasePropagator_apply _)
    (fun t n x ↦ (fourierMultiplierCLM_halfWavePropagator_apply t n x).symm)
    (φ.exists_eLpNorm_eLpNorm_halfWavePropagator_littlewoodPaley_le_of_le_endpoint hn hr)

/-- **The Strichartz estimate for the backward half-wave propagator at the pairs `(2, r)` with data
in `\dot H^γ`.** Under the hypotheses of
`ContDiffBump.exists_eLpNorm_eLpNorm_halfWavePropagator_le_tsum_sq_rpow_of_le_endpoint`, for
`W₋(t) = W₊(-t)` there is `C` such that for every `f ∈ L²(E)`,

`‖W₊(-t) f‖_{L²_t L^r_x} ≤ C (∑ⱼ 2^{2jγ} ‖Pⱼ f‖₂²)^{1/2}`. -/
theorem exists_eLpNorm_eLpNorm_halfWavePropagator_neg_le_tsum_sq_rpow_of_le_endpoint
    (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤ ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hr_top : r ≠ ∞) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (halfWavePropagator ℂ (-t) f) r volume) 2 volume ≤
          C * (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹)) *
              ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ) ^ 2) ^ (2⁻¹ : ℝ) := by
  obtain ⟨C, hC⟩ :=
    φ.exists_eLpNorm_eLpNorm_halfWavePropagator_le_tsum_sq_rpow_of_le_endpoint hn hr hr_top
  exact ⟨C, fun m hm f ↦ ((continuous_phasePropagator_apply _ f).aestronglyMeasurable
    |>.eLpNorm_eLpNorm_comp_neg).trans_le (hC m hm f)⟩

/-! ### `cos(tD)`, `D⁻¹ sin(tD)` and the free wave equation -/

/-- **The Strichartz estimate for the frequency-localized `cos(tD)` at the pairs `(2, r)`** in
mixed norm. Let `E` have dimension `n ≥ 4`, let `Pⱼ` be the `L²` Fourier multiplier with the
Littlewood–Paley symbol `ψⱼ` built from `φ`, and let `1 + (n - 1) / r ≤ (n - 1) / 2`, the endpoint
exponent and `r = ∞` included. Put `γ = n / 2 - n / r - 1 / 2`. There is `C` such that for every
`j ∈ ℤ` and every `f ∈ L²(E)`,

`‖cos(tD) Pⱼ f‖_{L²_t L^r_x} ≤ C 2^{jγ} ‖f‖₂`. -/
theorem exists_eLpNorm_eLpNorm_waveCosPropagator_littlewoodPaley_le_of_le_endpoint
    (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤ ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ f : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (waveCosPropagator ℂ t (Lp.fourierMultiplierCLM ℂ m f)) r
            volume) 2 volume ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹)) * ‖f‖ₑ :=
  φ.exists_eLpNorm_eLpNorm_waveCosPropagator_littlewoodPaley_le_of_halfWavePropagator one_le_two
    (φ.exists_eLpNorm_eLpNorm_halfWavePropagator_littlewoodPaley_le_of_le_endpoint hn hr)

/-- **The Strichartz estimate for the frequency-localized `D⁻¹ sin(tD)` at the pairs `(2, r)`** in
mixed norm. Under the hypotheses of
`ContDiffBump.exists_eLpNorm_eLpNorm_waveCosPropagator_littlewoodPaley_le_of_le_endpoint`, there is
`C` such that for every `j ∈ ℤ` and every `g ∈ L²(E)`,

`‖D⁻¹ sin(tD) Pⱼ g‖_{L²_t L^r_x} ≤ C 2^{j(γ - 1)} ‖g‖₂`.

The extra factor `2^{-j}` is the size of `D⁻¹` at frequencies `‖ξ‖ ≈ 2^j`. -/
theorem exists_eLpNorm_eLpNorm_waveSinPropagator_littlewoodPaley_le_of_le_endpoint
    (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤ ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ g : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (waveSinPropagator ℂ t (Lp.fourierMultiplierCLM ℂ m g)) r
            volume) 2 volume ≤
          C * ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹ - 1)) * ‖g‖ₑ :=
  φ.exists_eLpNorm_eLpNorm_waveSinPropagator_littlewoodPaley_le_of_halfWavePropagator one_le_two
    (φ.exists_eLpNorm_eLpNorm_halfWavePropagator_littlewoodPaley_le_of_le_endpoint hn hr)

/-- **The Strichartz estimate for `cos(tD)` at the pairs `(2, r)` with data in
`\dot B^γ_{2,1}`.** Let `E` have dimension `n ≥ 4`, let `ψⱼ` be the Littlewood–Paley cutoffs built
from `φ`, and let `Pⱼ` be the `L²` Fourier multiplier with symbol `ψⱼ`. Let
`1 + (n - 1) / r ≤ (n - 1) / 2`, the endpoint exponent and `r = ∞` included, and let
`γ = n / 2 - n / r - 1 / 2`. There is `C` such that for every `f ∈ L²(E)`,

`‖cos(tD) f‖_{L²_t L^r_x} ≤ C ∑ⱼ 2^{jγ} ‖Pⱼ f‖₂`. -/
theorem exists_eLpNorm_eLpNorm_waveCosPropagator_le_tsum_of_le_endpoint
    (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤ ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (waveCosPropagator ℂ t f) r volume) 2 volume ≤
          C * ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹)) * ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ :=
  φ.exists_eLpNorm_eLpNorm_le_tsum_of_le_endpoint hn hr _ _ continuous_waveCosPropagator_apply
    (φ.exists_eLpNorm_eLpNorm_waveCosPropagator_littlewoodPaley_le_of_le_endpoint hn hr)

/-- **The Strichartz estimate for `D⁻¹ sin(tD)` at the pairs `(2, r)` with data in
`\dot B^{γ - 1}_{2,1}`.** Under the hypotheses of
`ContDiffBump.exists_eLpNorm_eLpNorm_waveCosPropagator_le_tsum_of_le_endpoint`, there is `C` such
that for every `g ∈ L²(E)`,

`‖D⁻¹ sin(tD) g‖_{L²_t L^r_x} ≤ C ∑ⱼ 2^{j(γ - 1)} ‖Pⱼ g‖₂`. -/
theorem exists_eLpNorm_eLpNorm_waveSinPropagator_le_tsum_of_le_endpoint
    (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤ ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ g : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (waveSinPropagator ℂ t g) r volume) 2 volume ≤
          C * ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹ - 1)) *
              ‖Lp.fourierMultiplierCLM ℂ (m j) g‖ₑ :=
  φ.exists_eLpNorm_eLpNorm_le_tsum_of_le_endpoint hn hr _ _ continuous_waveSinPropagator_apply
    (φ.exists_eLpNorm_eLpNorm_waveSinPropagator_littlewoodPaley_le_of_le_endpoint hn hr)

/-- **The Strichartz estimate for the free wave equation at the pairs `(2, r)` with data in
`\dot B^γ_{2,1} × \dot B^{γ - 1}_{2,1}`.** Under the hypotheses of
`ContDiffBump.exists_eLpNorm_eLpNorm_waveCosPropagator_le_tsum_of_le_endpoint`, there is `C` such
that for all `f, g ∈ L²(E)`, the solution `u(t) = cos(tD) f + D⁻¹ sin(tD) g` of `∂ₜ²u = Δu` with
`u(0) = f` and `∂ₜu(0) = g` satisfies

`‖u‖_{L²_t L^r_x} ≤ C (∑ⱼ 2^{jγ} ‖Pⱼ f‖₂ + ∑ⱼ 2^{j(γ - 1)} ‖Pⱼ g‖₂)`. -/
theorem exists_eLpNorm_eLpNorm_waveCosPropagator_add_waveSinPropagator_le_tsum_of_le_endpoint
    (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤ ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ f g : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (waveCosPropagator ℂ t f + waveSinPropagator ℂ t g) r volume) 2
            volume ≤
          C * (∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹)) *
                ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ +
            ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹ - 1)) *
                ‖Lp.fourierMultiplierCLM ℂ (m j) g‖ₑ) := by
  rcases eq_or_ne r 0 with rfl | hr0
  · exact ⟨0, fun _ _ _ _ ↦ by simp [eLpNorm_exponent_zero, AEEqFun.aestronglyMeasurable]⟩
  obtain ⟨C₁, h₁⟩ := φ.exists_eLpNorm_eLpNorm_waveCosPropagator_le_tsum_of_le_endpoint hn hr
  obtain ⟨C₂, h₂⟩ := φ.exists_eLpNorm_eLpNorm_waveSinPropagator_le_tsum_of_le_endpoint hn hr
  exact ⟨C₁ + C₂, fun m hm f g ↦
    eLpNorm_eLpNorm_waveCosPropagator_add_waveSinPropagator_le_of_one_le one_le_two
      (one_le_two.trans (two_le_of_le_endpoint hn hr0 hr)) (h₁ m hm f) (h₂ m hm g)⟩

/-- **The Strichartz estimate at the pairs `(2, r)` for strong solutions of the free wave
equation.** Under the hypotheses of
`ContDiffBump.exists_eLpNorm_eLpNorm_waveCosPropagator_le_tsum_of_le_endpoint`, there is `C` such
that for every interval `I` containing `0`, every strong solution `u` of `∂ₜ²u = Δu` on `I`, with
velocity `u'`, satisfies

`‖u‖_{L²(I; L^r_x)} ≤ C (∑ⱼ 2^{jγ} ‖Pⱼ u(0)‖₂ + ∑ⱼ 2^{j(γ - 1)} ‖Pⱼ u'(0)‖₂)`. -/
theorem exists_eLpNorm_eLpNorm_le_tsum_of_isWaveSolutionOn_of_le_endpoint
    (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤ ((Module.finrank ℝ E : ℝ) - 1) / 2) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ (s : Set ℝ) [s.OrdConnected], 0 ∈ s →
      ∀ u u' u'' : ℝ → Lp ℂ 2 (volume : Measure E), IsWaveSolutionOn u u' u'' 0 s →
        eLpNorm (fun t ↦ eLpNorm (u t) r volume) 2 (volume.restrict s) ≤
          C * (∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹)) *
                ‖Lp.fourierMultiplierCLM ℂ (m j) (u 0)‖ₑ +
            ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹ - 1)) *
                ‖Lp.fourierMultiplierCLM ℂ (m j) (u' 0)‖ₑ) := by
  obtain ⟨C, hC⟩ :=
    φ.exists_eLpNorm_eLpNorm_waveCosPropagator_add_waveSinPropagator_le_tsum_of_le_endpoint hn hr
  exact ⟨C, fun m hm s _ h0 u u' u'' hu ↦
    (hu.eLpNorm_eLpNorm_restrict_le h0).trans (hC m hm _ _)⟩

/-- **The Strichartz estimate for `cos(tD)` at the pairs `(2, r)` with data in `\dot H^γ`.** Let
`E` have dimension `n ≥ 4`, let `ψⱼ` be the Littlewood–Paley cutoffs built from `φ`, and let `Pⱼ`
be the `L²` Fourier multiplier with symbol `ψⱼ`. Let `1 + (n - 1) / r ≤ (n - 1) / 2` with
`r < ∞`, the endpoint exponent included, and let `γ = n / 2 - n / r - 1 / 2`. There is `C` such
that for every `f ∈ L²(E)`,

`‖cos(tD) f‖_{L²_t L^r_x} ≤ C (∑ⱼ 2^{2jγ} ‖Pⱼ f‖₂²)^{1/2}`. -/
theorem exists_eLpNorm_eLpNorm_waveCosPropagator_le_tsum_sq_rpow_of_le_endpoint
    (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤ ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hr_top : r ≠ ∞) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ f : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (waveCosPropagator ℂ t f) r volume) 2 volume ≤
          C * (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹)) *
              ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ) ^ 2) ^ (2⁻¹ : ℝ) :=
  φ.exists_eLpNorm_eLpNorm_le_tsum_sq_rpow_of_le_endpoint hn hr hr_top _ _
    continuous_waveCosPropagator_apply
    (fun t n x ↦ (fourierMultiplierCLM_waveCosPropagator_apply t n x).symm)
    (φ.exists_eLpNorm_eLpNorm_waveCosPropagator_littlewoodPaley_le_of_le_endpoint hn hr)

/-- **The Strichartz estimate for `D⁻¹ sin(tD)` at the pairs `(2, r)` with data in
`\dot H^{γ - 1}`.** Under the hypotheses of
`ContDiffBump.exists_eLpNorm_eLpNorm_waveCosPropagator_le_tsum_sq_rpow_of_le_endpoint`, there is
`C` such that for every `g ∈ L²(E)`,

`‖D⁻¹ sin(tD) g‖_{L²_t L^r_x} ≤ C (∑ⱼ 2^{2j(γ - 1)} ‖Pⱼ g‖₂²)^{1/2}`. -/
theorem exists_eLpNorm_eLpNorm_waveSinPropagator_le_tsum_sq_rpow_of_le_endpoint
    (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤ ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hr_top : r ≠ ∞) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ g : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (waveSinPropagator ℂ t g) r volume) 2 volume ≤
          C * (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
            Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹ - 1)) *
              ‖Lp.fourierMultiplierCLM ℂ (m j) g‖ₑ) ^ 2) ^ (2⁻¹ : ℝ) :=
  φ.exists_eLpNorm_eLpNorm_le_tsum_sq_rpow_of_le_endpoint hn hr hr_top _ _
    continuous_waveSinPropagator_apply
    (fun t n x ↦ (fourierMultiplierCLM_waveSinPropagator_apply t n x).symm)
    (φ.exists_eLpNorm_eLpNorm_waveSinPropagator_littlewoodPaley_le_of_le_endpoint hn hr)

/-- **The Strichartz estimate for the free wave equation at the pairs `(2, r)` with data in
`\dot H^γ × \dot H^{γ - 1}`.** Under the hypotheses of
`ContDiffBump.exists_eLpNorm_eLpNorm_waveCosPropagator_le_tsum_sq_rpow_of_le_endpoint`, there is
`C` such that for all `f, g ∈ L²(E)`, the solution `u(t) = cos(tD) f + D⁻¹ sin(tD) g` of
`∂ₜ²u = Δu` with `u(0) = f` and `∂ₜu(0) = g` satisfies

`‖u‖_{L²_t L^r_x} ≤ C ((∑ⱼ 2^{2jγ} ‖Pⱼ f‖₂²)^{1/2} + (∑ⱼ 2^{2j(γ - 1)} ‖Pⱼ g‖₂²)^{1/2})`. -/
theorem
    exists_eLpNorm_eLpNorm_waveCosPropagator_add_waveSinPropagator_le_tsum_sq_rpow_of_le_endpoint
    (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤ ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hr_top : r ≠ ∞) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ f g : Lp ℂ 2 (volume : Measure E),
        eLpNorm (fun t ↦ eLpNorm (waveCosPropagator ℂ t f + waveSinPropagator ℂ t g) r volume) 2
            volume ≤
          C * ((∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹)) *
                ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ) ^ 2) ^ (2⁻¹ : ℝ) +
            (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹ - 1)) *
                ‖Lp.fourierMultiplierCLM ℂ (m j) g‖ₑ) ^ 2) ^ (2⁻¹ : ℝ)) := by
  rcases eq_or_ne r 0 with rfl | hr0
  · exact ⟨0, fun _ _ _ _ ↦ by simp [eLpNorm_exponent_zero, AEEqFun.aestronglyMeasurable]⟩
  obtain ⟨C₁, h₁⟩ :=
    φ.exists_eLpNorm_eLpNorm_waveCosPropagator_le_tsum_sq_rpow_of_le_endpoint hn hr hr_top
  obtain ⟨C₂, h₂⟩ :=
    φ.exists_eLpNorm_eLpNorm_waveSinPropagator_le_tsum_sq_rpow_of_le_endpoint hn hr hr_top
  exact ⟨C₁ + C₂, fun m hm f g ↦
    eLpNorm_eLpNorm_waveCosPropagator_add_waveSinPropagator_le_of_one_le one_le_two
      (one_le_two.trans (two_le_of_le_endpoint hn hr0 hr)) (h₁ m hm f) (h₂ m hm g)⟩

/-- **The Strichartz estimate at the pairs `(2, r)` for strong solutions of the free wave equation
with homogeneous Sobolev data.** Under the hypotheses of
`ContDiffBump.exists_eLpNorm_eLpNorm_waveCosPropagator_le_tsum_sq_rpow_of_le_endpoint`, there is
`C` such that for every interval `I` containing `0`, every strong solution `u` of `∂ₜ²u = Δu` on
`I`, with velocity `u'`, satisfies

`‖u‖_{L²(I; L^r_x)} ≤ C ((∑ⱼ 2^{2jγ} ‖Pⱼ u(0)‖₂²)^{1/2} + (∑ⱼ 2^{2j(γ - 1)} ‖Pⱼ u'(0)‖₂²)^{1/2})`.
-/
theorem exists_eLpNorm_eLpNorm_le_tsum_sq_rpow_of_isWaveSolutionOn_of_le_endpoint
    (hn : 3 < Module.finrank ℝ E)
    (hr : 1 + ((Module.finrank ℝ E : ℝ) - 1) * (r⁻¹).toReal ≤ ((Module.finrank ℝ E : ℝ) - 1) / 2)
    (hr_top : r ≠ ∞) :
    ∃ C : ℝ≥0, ∀ m : ℤ → Lp ℂ ∞ (volume : Measure E),
      (∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) →
      ∀ (s : Set ℝ) [s.OrdConnected], 0 ∈ s →
      ∀ u u' u'' : ℝ → Lp ℂ 2 (volume : Measure E), IsWaveSolutionOn u u' u'' 0 s →
        eLpNorm (fun t ↦ eLpNorm (u t) r volume) 2 (volume.restrict s) ≤
          C * ((∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹)) *
                ‖Lp.fourierMultiplierCLM ℂ (m j) (u 0)‖ₑ) ^ 2) ^ (2⁻¹ : ℝ) +
            (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ ((Module.finrank ℝ E : ℝ) / 2 -
              Module.finrank ℝ E * (r⁻¹).toReal - 2⁻¹ - 1)) *
                ‖Lp.fourierMultiplierCLM ℂ (m j) (u' 0)‖ₑ) ^ 2) ^ (2⁻¹ : ℝ)) := by
  obtain ⟨C, hC⟩ :=
    φ.exists_eLpNorm_eLpNorm_waveCosPropagator_add_waveSinPropagator_le_tsum_sq_rpow_of_le_endpoint
      hn hr hr_top
  exact ⟨C, fun m hm s _ h0 u u' u'' hu ↦
    (hu.eLpNorm_eLpNorm_restrict_le h0).trans (hC m hm _ _)⟩

end ContDiffBump
