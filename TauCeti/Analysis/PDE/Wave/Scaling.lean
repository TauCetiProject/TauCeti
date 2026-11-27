/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.LittlewoodPaley.Dilation
public import TauCeti.Analysis.PDE.Wave.Propagator

/-!
# Scaling of the wave equation and the scaling-critical regularity

If `u(x, t)` solves the wave equation `∂ₜ²u = Δu` on a real inner product space `E` of dimension
`n`, then so does `u(x / λ, t / λ)` for every `λ > 0`: unlike the Schrödinger equation, time and
space scale alike. For the normalized dilation `D_λ f = λ ^ (-n/2) • f (λ⁻¹ • ·)` of `L²`
(`MeasureTheory.Measure.dilateLp`) and `D = √(-Δ)`, this is the family of identities

* `W₊(t) (D_λ f) = D_λ (W₊(t / λ) f)` for the half-wave propagator `W₊(t) = exp(itD)`
  (`TauCeti.halfWavePropagator_dilateLp`), the case `k = 1` of the scaling law of a phase propagator
  whose phase is positively homogeneous of degree `k` (`TauCeti.phasePropagator_dilateLp`);
* `cos(tD) (D_λ f) = D_λ (cos((t / λ)D) f)` (`TauCeti.waveCosPropagator_dilateLp`) and
  `D⁻¹ sin(tD) (D_λ g) = λ • D_λ (D⁻¹ sin((t / λ)D) g)` (`TauCeti.waveSinPropagator_dilateLp`), so
  that the free solution `u(t) = cos(tD) f + D⁻¹ sin(tD) g` with data `(D_λ f, λ⁻¹ • D_λ g)` is
  `D_λ (u(t / λ))` (`TauCeti.waveCosPropagator_add_waveSinPropagator_dilateLp`).

Taking `Lʳ` norms in space and then `L^q` norms in time, the dilation multiplies the Strichartz
norm `‖W₊(t) f‖_{L^q_t L^r_x}` by `λ ^ (n/r - n/2 + 1/q)`
(`TauCeti.eLpNorm_eLpNorm_halfWavePropagator_dilateLp`), while it multiplies the norms of the
homogeneous Besov space `\dot B^s_{2,1}` and of the homogeneous Sobolev space `\dot H^s`, written
through the Littlewood–Paley blocks, by `λ ^ (-s)` when `λ` is a power of `2`
(`ContDiffBump.tsum_enorm_fourierMultiplierCLM_littlewoodPaley_dilateLp_two_zpow`,
`ContDiffBump.tsum_sq_rpow_enorm_fourierMultiplierCLM_littlewoodPaley_dilateLp_two_zpow`). The two
powers agree exactly when `s` is the **scaling-critical regularity**

`s(q, r) = n / 2 - n / r - 1 / q`.

So a homogeneous Strichartz estimate `‖W₊(t) f‖_{L^q_t L^r_x} ≤ C ‖f‖_{\dot B^s_{2,1}}` or
`‖W₊(t) f‖_{L^q_t L^r_x} ≤ C ‖f‖_{\dot H^s}` on the whole time line can only hold for
`s = s(q, r)` (`ContDiffBump.eq_of_eLpNorm_eLpNorm_halfWavePropagator_le_tsum`,
`ContDiffBump.eq_of_eLpNorm_eLpNorm_halfWavePropagator_le_tsum_sq_rpow`). The general form, for
the dyadic dilates of one nonzero datum, is
`TauCeti.eq_of_eLpNorm_eLpNorm_halfWavePropagator_dilateLp_le`, the case `k = 1` of
`TauCeti.eq_of_eLpNorm_eLpNorm_phasePropagator_dilateLp_le` for phases homogeneous of degree `k`.
This is the regularity at which the estimates of `TauCeti.Analysis.PDE.Wave.HomogeneousStrichartz`
and `TauCeti.Analysis.PDE.Wave.SobolevStrichartz` are stated. No admissibility condition on
`(q, r)` is assumed or derived here: scaling fixes the regularity, not the pair.

## The argument

Test the estimate on the dilates `D_{2^k} f₀`, `k ∈ ℤ`, of one nonzero datum `f₀` whose data norm
is finite. The left side is `2^{k(n/r - n/2 + 1/q)}` times a positive number, since `W₊(t)` is
unitary, and the right side is `2^{-ks}` times a finite number, so `2^{k(n/r - n/2 + 1/q + s)}` is
bounded over all `k ∈ ℤ` and the exponent vanishes (`Real.eq_zero_of_forall_zpow_rpow_le`).
For the Littlewood–Paley norms, a single block `f₀ = P_{j₀} g ≠ 0` has only finitely many nonzero
blocks (`ContDiffBump.exists_ne_zero_forall_notMem_fourierMultiplierCLM_eq_zero`): cutoffs whose
indices differ by at least a fixed `L` have disjoint supports, so `Pⱼ P_{j₀} = 0` for
`|j - j₀| ≥ L` (`ContDiffBump.fourierMultiplierCLM_fourierMultiplierCLM_littlewoodPaley_eq_zero`).

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.3 (the scaling heuristic, and Theorem 2.6 with the
  regularity `s = d/2 - d/r - 1/q`).
-/

public section

noncomputable section

open scoped ENNReal NNReal
open MeasureTheory MeasureTheory.Measure Module Filter

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The phase `2π ‖ξ‖` of the half-wave propagator is positively homogeneous of degree `1`. -/
private theorem sqrtNegLaplacianSymbol_smul_of_pos (c : ℝ) (hc : 0 < c) (ξ : E) :
    sqrtNegLaplacianSymbol (c • ξ) = c ^ 1 * sqrtNegLaplacianSymbol ξ := by
  rw [sqrtNegLaplacianSymbol_smul, abs_of_pos hc, pow_one]

/-- **The scaling law of the half-wave equation.** If `u(x, t)` solves `∂ₜu = iDu`, so does
`u(x / r, t / r)`. For the propagator `W₊(t) = exp(itD)` and the normalized dilation
`D_r f = r ^ (-n/2) • f (r⁻¹ • ·)` of `L²`, this reads `W₊(t) (D_r f) = D_r (W₊(t / r) f)`. -/
theorem halfWavePropagator_dilateLp {r : ℝ} (hr : 0 < r) (t : ℝ)
    (f : Lp F 2 (volume : Measure E)) :
    halfWavePropagator F t (dilateLp volume ℝ 2 r hr f) =
      dilateLp volume ℝ 2 r hr (halfWavePropagator F (t / r) f) := by
  rw [halfWavePropagator_def, halfWavePropagator_def,
    phasePropagator_dilateLp sqrtNegLaplacianSymbol_smul_of_pos hr, pow_one]

/-- **Scaling of the Strichartz norms of the half-wave propagator.** For `q ≠ 0`, dilating the
datum by `l` multiplies the mixed norm `‖W₊(t) f‖_{L^q_t L^r_x}`, `t ∈ ℝ`, by
`l ^ (n/r - n/2 + 1/q)`, where `n / r` and `1 / q` are `n / r.toReal` and `1 / q.toReal`, which are
`0` for an infinite exponent. This is the case `k = 1` of
`TauCeti.eLpNorm_eLpNorm_phasePropagator_dilateLp`. -/
theorem eLpNorm_eLpNorm_halfWavePropagator_dilateLp {l : ℝ} (hl : 0 < l)
    (f : Lp F 2 (volume : Measure E)) {q : ℝ≥0∞} (hq : q ≠ 0) (r : ℝ≥0∞) :
    eLpNorm (fun t ↦ eLpNorm (halfWavePropagator F t (dilateLp volume ℝ 2 l hl f)) r volume) q
        volume =
      ENNReal.ofReal (l ^ ((finrank ℝ E : ℝ) / r.toReal - finrank ℝ E / 2 + 1 / q.toReal)) *
        eLpNorm (fun t ↦ eLpNorm (halfWavePropagator F t f) r volume) q volume := by
  simpa only [halfWavePropagator_def, Nat.cast_one] using
    eLpNorm_eLpNorm_phasePropagator_dilateLp sqrtNegLaplacianSymbol_smul_of_pos hl f hq r

/-- **The scaling law of `cos(tD)`.** For the normalized dilation `D_r` of `L²`, `r > 0`,
`cos(tD) (D_r f) = D_r (cos((t / r)D) f)`: the symbol `cos(2π t ‖ξ‖)` dilated by `r` is
`cos(2π (t / r) ‖ξ‖)`. -/
theorem waveCosPropagator_dilateLp {r : ℝ} (hr : 0 < r) (t : ℝ)
    (f : Lp F 2 (volume : Measure E)) :
    waveCosPropagator F t (dilateLp volume ℝ 2 r hr f) =
      dilateLp volume ℝ 2 r hr (waveCosPropagator F (t / r) f) := by
  have hsym : dilateLp volume ℝ ∞ r hr ((memLp_waveCosSymbol (E := E) t).toLp _) =
      (memLp_waveCosSymbol (t / r)).toLp _ := by
    refine Lp.ext ?_
    filter_upwards [coeFn_dilateLp_top_of_ae_eq (𝕜 := ℝ) hr (memLp_waveCosSymbol t).coeFn_toLp,
      (memLp_waveCosSymbol (t / r)).coeFn_toLp] with ξ h₁ h₂
    rw [h₁, h₂, waveCosSymbol_apply, waveCosSymbol_apply, sqrtNegLaplacianSymbol_smul,
      abs_of_pos (inv_pos.2 hr), ← mul_assoc, ← div_eq_mul_inv]
  rw [waveCosPropagator_def, waveCosPropagator_def, Lp.fourierMultiplierCLM_dilateLp, hsym]

/-- **The scaling law of `D⁻¹ sin(tD)`.** For the normalized dilation `D_r` of `L²`, `r > 0`,
`D⁻¹ sin(tD) (D_r g) = r • D_r (D⁻¹ sin((t / r)D) g)`: the symbol `sin(2π t ‖ξ‖) / (2π ‖ξ‖)`
dilated by `r` is `r` times `sin(2π (t / r) ‖ξ‖) / (2π ‖ξ‖)`, since `D⁻¹` has degree `-1`. -/
theorem waveSinPropagator_dilateLp {r : ℝ} (hr : 0 < r) (t : ℝ)
    (g : Lp F 2 (volume : Measure E)) :
    waveSinPropagator F t (dilateLp volume ℝ 2 r hr g) =
      r • dilateLp volume ℝ 2 r hr (waveSinPropagator F (t / r) g) := by
  have hsym : dilateLp volume ℝ ∞ r hr ((memLp_waveSinSymbol (E := E) t).toLp _) =
      (r : ℂ) • (memLp_waveSinSymbol (t / r)).toLp _ := by
    refine Lp.ext ?_
    filter_upwards [coeFn_dilateLp_top_of_ae_eq (𝕜 := ℝ) hr (memLp_waveSinSymbol t).coeFn_toLp,
      Lp.coeFn_smul (r : ℂ) ((memLp_waveSinSymbol (E := E) (t / r)).toLp _),
      (memLp_waveSinSymbol (t / r)).coeFn_toLp] with ξ h₁ h₂ h₃
    rw [h₁, h₂, Pi.smul_apply, h₃, waveSinSymbol_apply, waveSinSymbol_apply,
      sqrtNegLaplacianSymbol_smul, abs_of_pos (inv_pos.2 hr), smul_eq_mul]
    push_cast
    field_simp [Complex.ofReal_ne_zero.2 hr.ne']
  rw [waveSinPropagator_def, waveSinPropagator_def, Lp.fourierMultiplierCLM_dilateLp, hsym,
    Lp.fourierMultiplierCLM_smul, _root_.smul_apply, Complex.coe_smul, map_smul]

/-- **The scaling law of the wave equation.** If `u(x, t)` solves `∂ₜ²u = Δu`, so does
`u(x / r, t / r)`. For the free solution `u(t) = cos(tD) f + D⁻¹ sin(tD) g` with data
`u(0) = f`, `∂ₜu(0) = g` and the normalized dilation `D_r` of `L²`, `r > 0`: the solution with the
dilated data `(D_r f, r⁻¹ • D_r g)` is `D_r (u(t / r))`. -/
theorem waveCosPropagator_add_waveSinPropagator_dilateLp {r : ℝ} (hr : 0 < r) (t : ℝ)
    (f g : Lp F 2 (volume : Measure E)) :
    waveCosPropagator F t (dilateLp volume ℝ 2 r hr f) +
        waveSinPropagator F t (r⁻¹ • dilateLp volume ℝ 2 r hr g) =
      dilateLp volume ℝ 2 r hr (waveCosPropagator F (t / r) f + waveSinPropagator F (t / r) g) := by
  rw [ContinuousLinearMap.map_smul_of_tower, waveCosPropagator_dilateLp, waveSinPropagator_dilateLp,
    smul_smul, inv_mul_cancel₀ hr.ne', one_smul, map_add]

/-- **Scaling fixes the regularity of a homogeneous Strichartz estimate.** Let `q, r ≠ 0`, let
`f₀ ∈ L²` be nonzero and let `B < ∞`. If the dyadic dilates `D_{2^k} f₀` satisfy

`‖W₊(t) (D_{2^k} f₀)‖_{L^q_t L^r_x} ≤ C 2^{-ks} B`

on the whole time line for every `k ∈ ℤ`, then `s` is the scaling-critical regularity
`n / 2 - n / r - 1 / q`, where `1 / r` and `1 / q` are `0` for an infinite exponent. This is how a
homogeneous estimate `‖W₊(t) f‖_{L^q_t L^r_x} ≤ C N f` constrains `s` when `N` is homogeneous of
degree `-s` under the dyadic dilations, `N (D_{2^k} f) = 2^{-ks} N f`, and `N f₀ = B`: the left side
scales like `2^{k(n/r - n/2 + 1/q)}` and is positive, since `W₊(t)` is unitary, so the two powers
must agree. This is the case of a phase homogeneous of degree `1` in
`TauCeti.eq_of_eLpNorm_eLpNorm_phasePropagator_dilateLp_le`. -/
theorem eq_of_eLpNorm_eLpNorm_halfWavePropagator_dilateLp_le {q r : ℝ≥0∞} (hq : q ≠ 0)
    (hr : r ≠ 0) {s : ℝ} {f₀ : Lp F 2 (volume : Measure E)} (hf₀ : f₀ ≠ 0) {B : ℝ≥0∞}
    (hB : B ≠ ∞) {C : ℝ≥0}
    (h : ∀ k : ℤ, eLpNorm (fun t ↦ eLpNorm (halfWavePropagator F t
        (dilateLp volume ℝ 2 _ (zpow_pos two_pos k) f₀)) r volume) q volume ≤
      C * (ENNReal.ofReal (((2 : ℝ) ^ k) ^ (-s)) * B)) :
    s = finrank ℝ E / 2 - finrank ℝ E * (r⁻¹).toReal - (q⁻¹).toReal := by
  simpa only [Nat.cast_one, one_mul] using eq_of_eLpNorm_eLpNorm_phasePropagator_dilateLp_le
    sqrtNegLaplacianSymbol_smul_of_pos hq hr hf₀ hB h

end TauCeti

namespace ContDiffBump

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (φ : ContDiffBump (0 : E))

/-- **The regularity of a Strichartz estimate with `\dot B^s_{2,1}` data is scaling-critical.**
Let `E` be nontrivial of dimension `n`, let `ψⱼ` be the Littlewood–Paley cutoffs built from `φ`,
let `Pⱼ` be the `L²` Fourier multiplier with symbol `ψⱼ`, and let `q, r ≠ 0`. If

`‖W₊(t) f‖_{L^q_t L^r_x} ≤ C ∑ⱼ 2^{js} ‖Pⱼ f‖₂`

holds on the whole time line for every `f ∈ L²(E)`, then `s = n / 2 - n / r - 1 / q`, where `1 / r`
and `1 / q` are `0` for an infinite exponent. This is the regularity of the estimates
`ContDiffBump.exists_eLpNorm_eLpNorm_halfWavePropagator_le_tsum_of_le_endpoint`, at the pairs
`(2, r)`, and `ContDiffBump.exists_eLpNorm_top_eLpNorm_halfWavePropagator_le_tsum`, at the pairs
`(∞, r)`, `r = ∞` included. -/
theorem eq_of_eLpNorm_eLpNorm_halfWavePropagator_le_tsum [Nontrivial E]
    {m : ℤ → Lp ℂ ∞ (volume : Measure E)}
    (hm : ∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) {q r : ℝ≥0∞} (hq : q ≠ 0)
    (hr : r ≠ 0) {s : ℝ} {C : ℝ≥0}
    (h : ∀ f : Lp ℂ 2 (volume : Measure E),
      eLpNorm (fun t ↦ eLpNorm (halfWavePropagator ℂ t f) r volume) q volume ≤
        C * ∑' j : ℤ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ s) * ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ) :
    s = finrank ℝ E / 2 - finrank ℝ E * (r⁻¹).toReal - (q⁻¹).toReal := by
  obtain ⟨f₀, hf₀, S, hS⟩ := φ.exists_ne_zero_forall_notMem_fourierMultiplierCLM_eq_zero (F := ℂ) hm
  refine eq_of_eLpNorm_eLpNorm_halfWavePropagator_dilateLp_le hq hr hf₀ ?_ fun k ↦ (h _).trans_eq
    (by rw [φ.tsum_enorm_fourierMultiplierCLM_littlewoodPaley_dilateLp_two_zpow hm s k f₀])
  rw [tsum_eq_sum (s := S) fun j hj ↦ by rw [hS j hj, eNorm_zero, mul_zero]]
  exact ENNReal.sum_ne_top.2 fun j _ ↦ ENNReal.mul_ne_top ENNReal.ofReal_ne_top eNorm_ne_top

/-- **The regularity of a Strichartz estimate with `\dot H^s` data is scaling-critical.**
Let `E` be nontrivial of dimension `n`, let `ψⱼ` be the Littlewood–Paley cutoffs built from `φ`,
let `Pⱼ` be the `L²` Fourier multiplier with symbol `ψⱼ`, and let `q, r ≠ 0`. If

`‖W₊(t) f‖_{L^q_t L^r_x} ≤ C (∑ⱼ 2^{2js} ‖Pⱼ f‖₂²)^{1/2}`

holds on the whole time line for every `f ∈ L²(E)`, then `s = n / 2 - n / r - 1 / q`, where `1 / r`
and `1 / q` are `0` for an infinite exponent. This is the regularity of
`ContDiffBump.exists_eLpNorm_eLpNorm_halfWavePropagator_le_tsum_sq_rpow`. -/
theorem eq_of_eLpNorm_eLpNorm_halfWavePropagator_le_tsum_sq_rpow [Nontrivial E]
    {m : ℤ → Lp ℂ ∞ (volume : Measure E)}
    (hm : ∀ j, m j =ᵐ[volume] fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) {q r : ℝ≥0∞} (hq : q ≠ 0)
    (hr : r ≠ 0) {s : ℝ} {C : ℝ≥0}
    (h : ∀ f : Lp ℂ 2 (volume : Measure E),
      eLpNorm (fun t ↦ eLpNorm (halfWavePropagator ℂ t f) r volume) q volume ≤
        C * (∑' j : ℤ, (ENNReal.ofReal (((2 : ℝ) ^ j) ^ s) *
          ‖Lp.fourierMultiplierCLM ℂ (m j) f‖ₑ) ^ 2) ^ (2⁻¹ : ℝ)) :
    s = finrank ℝ E / 2 - finrank ℝ E * (r⁻¹).toReal - (q⁻¹).toReal := by
  obtain ⟨f₀, hf₀, S, hS⟩ := φ.exists_ne_zero_forall_notMem_fourierMultiplierCLM_eq_zero (F := ℂ) hm
  refine eq_of_eLpNorm_eLpNorm_halfWavePropagator_dilateLp_le hq hr hf₀ ?_ fun k ↦ (h _).trans_eq
    (by rw [φ.tsum_sq_rpow_enorm_fourierMultiplierCLM_littlewoodPaley_dilateLp_two_zpow hm s k f₀])
  rw [tsum_eq_sum (s := S) fun j hj ↦ by rw [hS j hj, eNorm_zero, mul_zero, zero_pow two_ne_zero]]
  exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.sum_ne_top.2 fun j _ ↦
    ENNReal.pow_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top eNorm_ne_top))

end ContDiffBump
