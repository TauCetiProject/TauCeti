/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.BumpFunction.LittlewoodPaley
public import TauCeti.Analysis.PDE.Wave.HalfWave
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.SchwartzSpace.LittlewoodPaley
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.Analysis.Fourier.NonstationaryPhase
import TauCeti.Analysis.PDE.Schrodinger.Dispersive
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# The dispersive estimate for frequency-localized half-wave propagators

On a finite-dimensional real inner product space `E` of dimension `n`, the half-wave
propagator `W₊(t) = exp(itD)`, `D = √(-Δ)`, is the Fourier multiplier with symbol
`exp(2πit‖ξ‖)` (`TauCeti.halfWavePropagator`). It is not bounded from `L¹` to `L^∞`, but on
functions whose frequencies lie in an annulus it disperses at the rate `(n - 1)/2`: for `ψ`
smooth, compactly supported and vanishing near the origin,

`|𝓕⁻ (exp(2πit‖·‖) ψ) (x)| ≤ C (1 + |t|)^(-(n - 1)/2)`

(`TauCeti.exists_norm_fourierInv_phaseSymbol_sqrtNegLaplacianSymbol_mul_le`). Rescaling to the
Littlewood–Paley cutoffs `ψⱼ`, supported where `‖ξ‖ ≈ 2^j`, gives the kernel bound
`C 2^{jn} (1 + 2^j |t|)^(-(n - 1)/2)` uniformly in `j ∈ ℤ`, and with it the dispersive estimate

`‖W₊(t) Pⱼ f‖_∞ ≤ C 2^{jn} (1 + 2^j |t|)^(-(n - 1)/2) ‖f‖₁`

for the frequency-localized propagators, the decay that drives the wave Strichartz estimates. No
bound for the unlocalized propagator is claimed: its kernel is not a function.

## The argument

Rather than applying stationary phase on the sphere, we subordinate the wave phase to the
Schrödinger phases. Let `ρ` be a smooth cutoff, supported in `(0, ∞)` and equal to `1` at
`‖ξ‖²` for every `ξ` in the support of `ψ`. Then `G_t(u) = exp(2πit√u) ρ(u)` is a Schwartz
function of `u`, and Fourier inversion gives, on the support of `ψ`,

`exp(2πit‖ξ‖) = ∫ 𝓕 G_t (s) exp(2πis‖ξ‖²) ds`.

So the kernel is `∫ 𝓕 G_t (s) S_s(x) ds`, where `S_s(x) = ∫ exp(2πi (⟪ξ, x⟫ + s‖ξ‖²)) ψ(ξ) dξ` is
the Schrödinger evolution of `𝓕⁻ ψ` at time `-s/2π`. It is bounded by `‖ψ‖₁` and, by the
Schrödinger dispersive estimate, by `(2|s|)^(-n/2) ‖𝓕⁻ ψ‖₁`. After the substitution `u = r²`,
`𝓕 G_t (s) = ∫ exp(2πi (t r - s r²)) a(r) dr`, where `a(r) = 2r ρ(r²)` for `r > 0` and
`a(r) = 0` for `r ≤ 0`. This is a one-dimensional
Schrödinger evolution, so `|𝓕 G_t (s)| ≤ (2|s|)^(-1/2) ‖𝓕⁻ a‖₁`. When `|s| ≪ |t|` its phase
is non-stationary on the support of `a`, so `𝓕 G_t (s) = O(|t|^(-N))`
(`TauCeti.exists_norm_integral_cexp_mul_le_of_mul_abs_le`). The region `|s| ≳ |t|` contributes
`∫_{|s| ≳ |t|} |s|^(-(n+1)/2) ds ≈ |t|^(-(n-1)/2)`; the region `|s| ≲ |t|` contributes
`O(|t|^(1-N))`.

## Main declarations

* `TauCeti.exists_norm_fourierInv_phaseSymbol_sqrtNegLaplacianSymbol_mul_le`: the dispersive
  kernel bound for one frequency cutoff vanishing near the origin.
* `ContDiffBump.exists_norm_fourierInv_phaseSymbol_sqrtNegLaplacianSymbol_mul_littlewoodPaley_le`:
  the kernel bound for the dyadic cutoffs, `C 2^{jn} (1 + 2^j |t|)^(-(n - 1)/2)`.
* `ContDiffBump.exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_littlewoodPaley_le`: the
  `L¹ → L^∞` dispersive estimate for `W₊(t) Pⱼ`.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.2.
-/
public section

noncomputable section

open scoped FourierTransform ContDiff SchwartzMap ENNReal RealInnerProductSpace
open MeasureTheory Filter Complex Set Metric
open Real hiding exp

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### The subordination of `exp(2πit‖ξ‖)` to `exp(2πis‖ξ‖²)` -/

section Subordination

variable {ρ : ℝ → ℝ} {α β : ℝ}

/-- The radial profile `u ↦ exp(2πi t √u) ρ(u)`, a smooth compactly supported function of
`u = ‖ξ‖²` when `ρ` is supported in `[α, β]`, `α > 0`. -/
private def subordinator (ρ : ℝ → ℝ) (t u : ℝ) : ℂ :=
  cexp (((2 * π * t * √u : ℝ) : ℂ) * I) * ρ u

/-- The amplitude `r ↦ 2r ρ(r²)` on `r > 0`, extended by zero: the Fourier transform of the
subordinator is the oscillatory integral of this amplitude against `exp(2πi (t r - s r²))`. -/
private def subordinatorAmplitude (ρ : ℝ → ℝ) (r : ℝ) : ℂ :=
  if 0 < r then ((2 * r * ρ (r ^ 2) : ℝ) : ℂ) else 0

private theorem contDiff_subordinator (hα : 0 < α) (hρ : ContDiff ℝ ∞ ρ)
    (hρs : tsupport ρ ⊆ Icc α β) (t : ℝ) : ContDiff ℝ ∞ (subordinator ρ t) := by
  refine contDiff_iff_contDiffAt.2 fun u ↦ ?_
  rcases lt_or_ge u α with hu | hu
  · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hu] with v hv
    simp [subordinator, image_eq_zero_of_notMem_tsupport fun h ↦ (not_le.2 hv) (hρs h).1]
  · have hu0 : u ≠ 0 := (hα.trans_le hu).ne'
    unfold subordinator
    have hs : ContDiffAt ℝ ∞ (fun v : ℝ ↦ √v) u := contDiffAt_sqrt hu0
    have h1 : ContDiffAt ℝ ∞ (fun v : ℝ ↦ ((2 * π * t * √v : ℝ) : ℂ) * I) u :=
      (ofRealCLM.contDiff.contDiffAt.comp u (contDiffAt_const.mul hs)).mul contDiffAt_const
    exact h1.cexp.mul (ofRealCLM.contDiff.contDiffAt.comp u hρ.contDiffAt)

private theorem hasCompactSupport_subordinator (hρs : tsupport ρ ⊆ Icc α β) (t : ℝ) :
    HasCompactSupport (subordinator ρ t) :=
  HasCompactSupport.intro (isCompact_Icc (a := α) (b := β)) fun u hu ↦ by
    simp [subordinator, image_eq_zero_of_notMem_tsupport fun h ↦ hu (hρs h)]

private theorem contDiff_subordinatorAmplitude (hα : 0 < α) (hρ : ContDiff ℝ ∞ ρ)
    (hρs : tsupport ρ ⊆ Icc α β) : ContDiff ℝ ∞ (subordinatorAmplitude ρ) := by
  refine contDiff_iff_contDiffAt.2 fun r ↦ ?_
  rcases lt_or_ge r √α with hr | hr
  · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hr] with v hv
    by_cases hv0 : 0 < v
    · have : v ^ 2 < α := by
        have := pow_lt_pow_left₀ hv hv0.le two_ne_zero
        rwa [sq_sqrt hα.le] at this
      simp [subordinatorAmplitude, hv0,
        image_eq_zero_of_notMem_tsupport fun h ↦ (not_le.2 this) (hρs h).1]
    · simp [subordinatorAmplitude, hv0]
  · have hr0 : 0 < r := (sqrt_pos.2 hα).trans_le hr
    have hsm : ContDiff ℝ ∞ (fun v : ℝ ↦ ((2 * v * ρ (v ^ 2) : ℝ) : ℂ)) :=
      ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).mul (hρ.comp (contDiff_id.pow 2)))
    refine hsm.contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hr0] with v hv
    simp [subordinatorAmplitude, mem_Ioi.1 hv]

private theorem tsupport_subordinatorAmplitude_subset (hρs : tsupport ρ ⊆ Icc α β) :
    tsupport (subordinatorAmplitude ρ) ⊆ Icc (-(β + 1)) (β + 1) := by
  refine closure_minimal (fun r hr ↦ ?_) isClosed_Icc
  have hr0 : 0 < r := by
    by_contra h
    exact hr (by simp [subordinatorAmplitude, h])
  have hρr : ρ (r ^ 2) ≠ 0 := fun h ↦ hr (by simp [subordinatorAmplitude, hr0, h])
  have hβ := (hρs (subset_tsupport ρ hρr)).2
  have hβ0 : 0 ≤ β := (sq_nonneg r).trans hβ
  refine ⟨by linarith, ?_⟩
  rcases le_or_gt r 1 with h1 | h1
  · nlinarith [(sq_nonneg r).trans hβ]
  · nlinarith

/-- The Fourier transform of the subordinator, after the substitution `u = r²`. -/
private theorem fourier_subordinator_eq (hα : 0 < α) (hρs : tsupport ρ ⊆ Icc α β) (t s : ℝ) :
    𝓕 (subordinator ρ t) s =
      ∫ r, cexp (((2 * π * (t * r - s * r ^ 2) : ℝ) : ℂ) * I) * subordinatorAmplitude ρ r := by
  set g : ℝ → ℂ := fun u ↦ cexp (((-2 * π * u * s) : ℝ) * I) • subordinator ρ t u
  have hg0 : ∀ u ∉ Ioi (0 : ℝ), g u = 0 := fun u hu ↦ by
    simp [g, subordinator, image_eq_zero_of_notMem_tsupport fun h ↦
      (not_le.2 ((not_lt.1 hu).trans_lt hα)) (hρs h).1]
  have ha0 : ∀ r ∉ Ioi (0 : ℝ), cexp (((2 * π * (t * r - s * r ^ 2) : ℝ) : ℂ) * I) *
      subordinatorAmplitude ρ r = 0 := fun r hr ↦ by
    simp [subordinatorAmplitude, not_lt.1 hr]
  rw [fourier_real_eq_integral_exp_smul, ← setIntegral_eq_integral_of_forall_compl_eq_zero hg0,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero ha0,
    ← integral_comp_rpow_Ioi g two_ne_zero]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
  have hr : 0 < r := hr
  have h2 : r ^ (2 : ℝ) = r ^ 2 := rpow_two r
  simp only [g, subordinator, subordinatorAmplitude, hr, ite_true, h2, sqrt_sq hr.le, abs_two,
    show (2 : ℝ) - 1 = 1 by norm_num, rpow_one, smul_eq_mul, Complex.real_smul]
  rw [show cexp (((2 * π * (t * r - s * r ^ 2) : ℝ) : ℂ) * I) =
      cexp (((-2 * π * r ^ 2 * s : ℝ) : ℂ) * I) * cexp (((2 * π * t * r : ℝ) : ℂ) * I) by
    rw [← Complex.exp_add]; congr 1; push_cast; ring]
  push_cast
  ring

/-- Fourier inversion for the subordinator. -/
private theorem subordinator_eq_integral (hα : 0 < α) (hρ : ContDiff ℝ ∞ ρ)
    (hρs : tsupport ρ ⊆ Icc α β) (t u : ℝ) :
    subordinator ρ t u =
      ∫ s, cexp (((2 * π * (s * u)) : ℝ) * I) * 𝓕 (subordinator ρ t) s := by
  set G : 𝓢(ℝ, ℂ) := (hasCompactSupport_subordinator hρs t).toSchwartzMap
    (contDiff_subordinator hα hρ hρs t)
  have hG : ⇑G = subordinator ρ t := funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  have h := congrArg (fun F : 𝓢(ℝ, ℂ) ↦ F u)
    (FourierTransform.fourierInv_fourier_eq (F := 𝓢(ℝ, ℂ)) G)
  simp only [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe, hG] at h
  rw [← h, fourierInv_eq']
  congr 1
  ext s
  rw [smul_eq_mul, real_inner_eq_re_inner ℝ, RCLike.inner_apply, conj_trivial, RCLike.re_to_real,
    mul_comm u s]

/-- The subordination identity: on the support of `ψ`, `exp(2πit‖ξ‖)` is the superposition
`∫ 𝓕 G_t (s) exp(2πis‖ξ‖²) ds` of Schrödinger phases, so the half-wave kernel is the
superposition of the Schrödinger kernels with the weights `𝓕 G_t (s)`. -/
private theorem fourierInv_phaseSymbol_mul_eq_integral {ψ : E → ℂ} (hα : 0 < α)
    (hρ : ContDiff ℝ ∞ ρ) (hρs : tsupport ρ ⊆ Icc α β)
    (hψρ : ∀ ξ ∈ tsupport ψ, ρ (‖ξ‖ ^ 2) = 1) (hψ : Continuous ψ) (hψi : Integrable ψ)
    (t : ℝ) (x : E) :
    𝓕⁻ (fun ξ ↦ phaseSymbol sqrtNegLaplacianSymbol t ξ * ψ ξ) x =
      ∫ s, 𝓕 (subordinator ρ t) s *
        ∫ ξ, cexp (((2 * π * (⟪ξ, x⟫ + s * ‖ξ‖ ^ 2) : ℝ) : ℂ) * I) * ψ ξ := by
  set G : 𝓢(ℝ, ℂ) := (hasCompactSupport_subordinator hρs t).toSchwartzMap
    (contDiff_subordinator hα hρ hρs t)
  have hG : 𝓕 (subordinator ρ t) = ⇑(𝓕 G : 𝓢(ℝ, ℂ)) := by
    rw [SchwartzMap.fourier_coe]
    congr 1
  set h := 𝓕 (subordinator ρ t)
  have hpt : ∀ ξ, phaseSymbol sqrtNegLaplacianSymbol t ξ * ψ ξ =
      ∫ s, cexp (((2 * π * (s * ‖ξ‖ ^ 2)) : ℝ) * I) * h s * ψ ξ := fun ξ ↦ by
    rw [integral_mul_const]
    by_cases hξ : ξ ∈ tsupport ψ
    · rw [← subordinator_eq_integral hα hρ hρs, subordinator, hψρ ξ hξ, sqrt_sq (norm_nonneg ξ),
        phaseSymbol_apply, sqrtNegLaplacianSymbol_apply]
      push_cast
      ring_nf
    · simp [image_eq_zero_of_notMem_tsupport hξ]
  have hint : Integrable (Function.uncurry fun (ξ : E) (s : ℝ) ↦
      cexp (((2 * π * ⟪ξ, x⟫ : ℝ) : ℂ) * I) * (cexp (((2 * π * (s * ‖ξ‖ ^ 2)) : ℝ) * I) * h s *
        ψ ξ)) (volume.prod volume) := by
    refine (hψi.norm.mul_prod (hG ▸ (𝓕 G).integrable).norm).mono' ?_
      (Eventually.of_forall fun p ↦ ?_)
    · refine Continuous.aestronglyMeasurable ?_
      rw [hG]
      fun_prop
    · simp only [Function.uncurry, norm_mul, norm_exp_ofReal_mul_I, one_mul]
      exact (mul_comm _ _).le
  rw [fourierInv_eq']
  simp_rw [hpt, smul_eq_mul, ← integral_const_mul]
  rw [integral_integral_swap hint]
  congr 1
  ext s
  congr 1
  ext ξ
  rw [show ∀ a b c d : ℂ, a * (b * c * d) = c * (a * b * d) by intros; ring, ← Complex.exp_add]
  congr 3
  push_cast
  ring

/-- The weights `𝓕 G_t (s)` obey the one-dimensional Schrödinger dispersive bound
`|𝓕 G_t (s)| ≤ (2|s|)^(-1/2) ‖𝓕⁻ a‖₁`, uniformly in `t`. -/
private theorem norm_fourier_subordinator_le (hα : 0 < α) (hρ : ContDiff ℝ ∞ ρ)
    (hρs : tsupport ρ ⊆ Icc α β) (t : ℝ) {s : ℝ} (hs : s ≠ 0) :
    ‖𝓕 (subordinator ρ t) s‖ ≤
      (2 * |s|) ^ (-(1 / 2 : ℝ)) * ∫ y, ‖𝓕⁻ (subordinatorAmplitude ρ) y‖ := by
  set a : 𝓢(ℝ, ℂ) := (HasCompactSupport.intro (isCompact_Icc (a := -(β + 1)) (b := β + 1))
      fun r hr ↦ image_eq_zero_of_notMem_tsupport fun h ↦
        hr (tsupport_subordinatorAmplitude_subset hρs h)).toSchwartzMap
    (contDiff_subordinatorAmplitude hα hρ hρs)
  have ha : ⇑a = subordinatorAmplitude ρ := funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  have h := a.norm_integral_cexp_quadratic_smul_le (neg_ne_zero.2 hs) t
  simp only [smul_eq_mul] at h
  rw [ha, abs_neg, Module.finrank_self, Nat.cast_one] at h
  rw [fourier_subordinator_eq hα hρs]
  refine le_of_eq_of_le ?_ (h.trans_eq (by rw [neg_div]))
  congr 2
  ext r
  rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply, conj_trivial, RCLike.re_to_real,
    Real.norm_eq_abs, sq_abs]
  congr 4
  ring

end Subordination

/-! ### The kernel bound -/

/-- The kernel of the localized half-wave propagator is bounded by `‖ψ‖₁` at all times. -/
private theorem norm_fourierInv_phaseSymbol_mul_le_integral_norm (ψ : E → ℂ) (t : ℝ) (x : E) :
    ‖𝓕⁻ (fun ξ ↦ phaseSymbol sqrtNegLaplacianSymbol t ξ * ψ ξ) x‖ ≤ ∫ ξ, ‖ψ ξ‖ := by
  rw [fourierInv_eq_fourier_neg]
  refine (norm_fourier_le_integral_norm _ _).trans_eq ?_
  simp

/-- The large-time decay `|t|^(-(n - 1)/2)` of the localized half-wave kernel, `n ≥ 2`. The
kernel is the superposition `∫ 𝓕 G_t (s) S_s(x) ds` of
`fourierInv_phaseSymbol_mul_eq_integral`; `norm_integral_le_max_mul_rpow_sub_mul_integral`
integrates the bounds on its integrand: `|S_s| ≤ ‖ψ‖₁` times non-stationary phase for `𝓕 G_t (s)`
when `4R|s| ≤ |t|`, and the product of the two dispersive bounds otherwise. -/
private theorem exists_norm_fourierInv_phaseSymbol_mul_le_rpow {ψ : E → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψ0 : (0 : E) ∉ tsupport ψ)
    (hE : 2 ≤ Module.finrank ℝ E) :
    ∃ K, 0 ≤ K ∧ ∀ t : ℝ, 1 ≤ |t| → ∀ x : E,
      ‖𝓕⁻ (fun ξ ↦ phaseSymbol sqrtNegLaplacianSymbol t ξ * ψ ξ) x‖ ≤
        K * |t| ^ (-((Module.finrank ℝ E : ℝ) - 1) / 2) := by
  -- `ψ` is supported in an annulus `r₁ ≤ ‖ξ‖ ≤ r₂`, and `ρ` is a cutoff equal to `1` on
  -- `[r₁², r₂²]` and supported in `[r₁²/2, r₂² + 2r₁²]`.
  obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.1 (isClosed_tsupport ψ).isOpen_compl 0 hψ0
  obtain ⟨r₂, -, hsub⟩ := hψc.isCompact.isBounded.subset_closedBall_lt 0 (0 : E)
  have hψr : ∀ ξ ∈ tsupport ψ, r₁ ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ r₂ := fun ξ hξ ↦
    ⟨not_lt.1 fun h ↦ hball (mem_ball_zero_iff.2 h) hξ, mem_closedBall_zero_iff.1 (hsub hξ)⟩
  obtain ⟨ρ, hρ, -, hρ1, -, hρs⟩ :=
    (isCompact_Icc (a := r₁ ^ 2) (b := r₂ ^ 2)).exists_contDiff_cutoff
      (isOpen_Ioo (a := r₁ ^ 2 / 2) (b := r₂ ^ 2 + 2 * r₁ ^ 2))
      (Icc_subset_Ioo (by linarith [pow_pos hr₁ 2]) (by linarith [pow_pos hr₁ 2]))
  replace hρs := hρs.trans Ioo_subset_Icc_self
  have hα : 0 < r₁ ^ 2 / 2 := by positivity
  have hψρ : ∀ ξ ∈ tsupport ψ, ρ (‖ξ‖ ^ 2) = 1 := fun ξ hξ ↦ interior_subset (hρ1
    ⟨pow_le_pow_left₀ hr₁.le (hψr ξ hξ).1 2, pow_le_pow_left₀ (norm_nonneg _) (hψr ξ hξ).2 2⟩)
  set ψs : 𝓢(E, ℂ) := hψc.toSchwartzMap hψ
  have hψs : ⇑ψs = ψ := funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  set R : ℝ := r₂ ^ 2 + 2 * r₁ ^ 2 + 1
  have hR : 0 < R := by positivity
  set n : ℝ := ((Module.finrank ℝ E : ℕ) : ℝ)
  have hn : 2 ≤ n := by simp only [n]; exact_mod_cast hE
  set q : ℝ := (n + 1) / 2
  have hq : 1 < q := by simp only [q]; linarith
  have hqN : q ≤ (Module.finrank ℝ E : ℕ) := by simp only [q, n]; linarith
  obtain ⟨C₃, hC₃0, hC₃⟩ := exists_norm_integral_cexp_mul_le_of_mul_abs_le
    (contDiff_infty.1 (contDiff_subordinatorAmplitude hα hρ hρs) (Module.finrank ℝ E)) hR
    (tsupport_subordinatorAmplitude_subset hρs)
  set A : ℝ := ∫ ξ, ‖ψ ξ‖
  set D : ℝ := (∫ y, ‖𝓕⁻ (subordinatorAmplitude ρ) y‖) * ∫ y, ‖𝓕⁻ ψ y‖
  refine ⟨max (C₃ * A * (1 + 1 / (4 * R)) ^ q) (D * (4 * R + 1) ^ q) *
    ∫ σ : ℝ, (1 + |σ|) ^ (-q), mul_nonneg (le_max_of_le_right (by positivity))
      (integral_nonneg fun _ ↦ by positivity), fun t ht x ↦ ?_⟩
  have ht0 : t ≠ 0 := fun h ↦ by rw [h, abs_zero] at ht; linarith
  rw [fourierInv_phaseSymbol_mul_eq_integral hα hρ hρs hψρ hψ.continuous
    (hψ.continuous.integrable_of_hasCompactSupport hψc)]
  refine (norm_integral_le_max_mul_rpow_sub_mul_integral volume (T := |t|) (C := C₃ * A) (D := D)
    (f := fun s ↦ 𝓕 (subordinator ρ t) s *
      ∫ ξ, cexp (((2 * π * (⟪ξ, x⟫ + s * ‖ξ‖ ^ 2) : ℝ) : ℂ) * I) * ψ ξ)
    (abs_pos.2 ht0) (by positivity : (0 : ℝ) < 4 * R) (by simpa using hq) (fun s hs ↦ ?_)
    (fun s hs ↦ ?_)).trans_eq ?_
  · -- Non-stationary phase for the weights near `s = 0`, times `|S_s| ≤ ‖ψ‖₁`.
    rw [Real.norm_eq_abs] at hs
    have hTN : (|t| ^ Module.finrank ℝ E)⁻¹ ≤ |t| ^ (-q) := by
      rw [← rpow_natCast, ← rpow_neg (abs_nonneg t)]
      exact rpow_le_rpow_of_exponent_le ht (by linarith)
    have hh : ‖𝓕 (subordinator ρ t) s‖ ≤ C₃ * |t| ^ (-q) := by
      rw [fourier_subordinator_eq hα hρs]
      exact (hC₃ t s ht0 hs).trans (by gcongr)
    have hS : ‖∫ ξ, cexp (((2 * π * (⟪ξ, x⟫ + s * ‖ξ‖ ^ 2) : ℝ) : ℂ) * I) * ψ ξ‖ ≤ A := by
      refine (norm_integral_le_integral_norm _).trans_eq ?_
      simp only [norm_mul, norm_exp_ofReal_mul_I, one_mul, A]
    rw [norm_mul]
    calc _ ≤ C₃ * |t| ^ (-q) * A := mul_le_mul hh hS (norm_nonneg _) (by positivity)
      _ = C₃ * A * |t| ^ (-q) := by ring
  · -- The product of the two dispersive bounds away from `s = 0`.
    simp only [Real.norm_eq_abs] at hs ⊢
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [abs_zero, mul_zero] at hs
      linarith
    have h₁ := norm_fourier_subordinator_le hα hρ hρs t hs0
    have h₂ := ψs.norm_integral_cexp_quadratic_smul_le hs0 x
    simp only [smul_eq_mul] at h₂
    rw [hψs] at h₂
    have h2s : 0 < 2 * |s| := by positivity
    rw [norm_mul]
    calc _ ≤ (2 * |s|) ^ (-(1 / 2 : ℝ)) * (∫ y, ‖𝓕⁻ (subordinatorAmplitude ρ) y‖) *
          ((2 * |s|) ^ (-n / 2) * ∫ y, ‖𝓕⁻ ψ y‖) :=
        mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)
      _ = D * ((2 * |s|) ^ (-(1 / 2 : ℝ)) * (2 * |s|) ^ (-n / 2)) := by ring
      _ = D * (2 * |s|) ^ (-q) := by
        rw [← rpow_add h2s]
        congr 2
        simp only [q]
        ring
      _ ≤ D * |s| ^ (-q) := mul_le_mul_of_nonneg_left (rpow_le_rpow_of_nonpos (abs_pos.2 hs0)
          (by linarith [abs_nonneg s]) (by linarith)) (by positivity)
  · simp only [Module.finrank_self, Nat.cast_one, Real.norm_eq_abs]
    rw [show 1 - q = -(n - 1) / 2 by simp only [q]; ring]
    ring

/-- **The dispersive bound for a frequency-localized half-wave kernel.** Let `E` have dimension
`n` and let `ψ` be smooth, compactly supported and vanish near the origin. Then the kernel
`𝓕⁻ (exp(2πit‖·‖) ψ)` of `W₊(t) = exp(itD)` localized by `ψ` satisfies

`|𝓕⁻ (exp(2πit‖·‖) ψ) (x)| ≤ C (1 + |t|)^(-(n - 1)/2)`

for every time `t` and every point `x`, with `C ≥ 0` depending only on `ψ`. For `n = 1` the
exponent is `0` and the bound only records that the kernel is bounded; for `n = 0` the space is a
point, so `ψ`, which vanishes near the origin, is zero and so is the kernel. -/
theorem exists_norm_fourierInv_phaseSymbol_sqrtNegLaplacianSymbol_mul_le {ψ : E → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψ0 : (0 : E) ∉ tsupport ψ) :
    ∃ C, 0 ≤ C ∧ ∀ (t : ℝ) (x : E),
      ‖𝓕⁻ (fun ξ ↦ phaseSymbol sqrtNegLaplacianSymbol t ξ * ψ ξ) x‖ ≤
        C * (1 + |t|) ^ (-((Module.finrank ℝ E : ℝ) - 1) / 2) := by
  set n : ℝ := ((Module.finrank ℝ E : ℕ) : ℝ)
  obtain ⟨K, hK0, hK⟩ : ∃ K, 0 ≤ K ∧ (2 ≤ Module.finrank ℝ E → ∀ t : ℝ, 1 ≤ |t| → ∀ x : E,
      ‖𝓕⁻ (fun ξ ↦ phaseSymbol sqrtNegLaplacianSymbol t ξ * ψ ξ) x‖ ≤
        K * |t| ^ (-(n - 1) / 2)) := by
    by_cases hE : 2 ≤ Module.finrank ℝ E
    · obtain ⟨K, hK0, hK⟩ := exists_norm_fourierInv_phaseSymbol_mul_le_rpow hψ hψc hψ0 hE
      exact ⟨K, hK0, fun _ ↦ hK⟩
    · exact ⟨0, le_rfl, fun h ↦ absurd h hE⟩
  set A : ℝ := ∫ ξ, ‖ψ ξ‖
  have hA : 0 ≤ A := integral_nonneg fun _ ↦ norm_nonneg _
  refine ⟨max A K * max 1 (2 ^ ((n - 1) / 2)),
    mul_nonneg (le_max_of_le_left hA) (le_max_of_le_left zero_le_one), fun t x ↦ ?_⟩
  by_cases h : |t| < 1 ∨ n ≤ 1
  · -- Small times and low dimensions: the trivial bound `‖ψ‖₁`.
    calc _ ≤ A := norm_fourierInv_phaseSymbol_mul_le_integral_norm ψ t x
      _ ≤ A * (max 1 (2 ^ ((n - 1) / 2)) * (1 + |t|) ^ (-(n - 1) / 2)) := by
          refine le_mul_of_one_le_right hA ?_
          rcases le_or_gt n 1 with hn | hn
          · exact one_le_mul_of_one_le_of_one_le (le_max_left _ _)
              (one_le_rpow (by linarith [abs_nonneg t]) (by linarith))
          · have ht : |t| < 1 := h.resolve_right (not_le.2 hn)
            calc (1 : ℝ) = 1 ^ (-((n - 1) / 2)) := (one_rpow _).symm
              _ ≤ 2 ^ ((n - 1) / 2) * (1 + |t|) ^ (-((n - 1) / 2)) :=
                  rpow_neg_le_mul_rpow_neg (by positivity) (by norm_num) (by linarith)
                    (by linarith)
              _ ≤ max 1 (2 ^ ((n - 1) / 2)) * (1 + |t|) ^ (-(n - 1) / 2) := by
                  rw [neg_div]; gcongr; exact le_max_right _ _
      _ ≤ max A K * max 1 (2 ^ ((n - 1) / 2)) * (1 + |t|) ^ (-(n - 1) / 2) := by
          rw [← mul_assoc]; gcongr; exact le_max_left _ _
  · -- Large times in dimension `n ≥ 2`: the decay `|t|^(-(n-1)/2)`.
    push Not at h
    have hE : 2 ≤ Module.finrank ℝ E := by
      have : (1 : ℝ) < Module.finrank ℝ E := h.2
      exact_mod_cast this
    have h2 : |t| ^ (-(n - 1) / 2) ≤ 2 ^ ((n - 1) / 2) * (1 + |t|) ^ (-(n - 1) / 2) := by
      rw [neg_div]
      exact rpow_neg_le_mul_rpow_neg (by positivity) (by norm_num) (by linarith) (by linarith)
    calc _ ≤ K * |t| ^ (-(n - 1) / 2) := hK hE t h.1 x
      _ ≤ K * (max 1 (2 ^ ((n - 1) / 2)) * (1 + |t|) ^ (-(n - 1) / 2)) := by
          gcongr
          exact h2.trans (by gcongr; exact le_max_right _ _)
      _ ≤ max A K * max 1 (2 ^ ((n - 1) / 2)) * (1 + |t|) ^ (-(n - 1) / 2) := by
          rw [← mul_assoc]; gcongr; exact le_max_right _ _

end TauCeti

/-! ### Dyadic blocks -/

namespace ContDiffBump

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (φ : ContDiffBump (0 : E))

/-- **The dispersive estimate for the dyadic half-wave kernels.** Let `E` have dimension
`n` and let `ψⱼ` be the Littlewood–Paley cutoffs built from `φ`, supported in the annuli
`‖ξ‖ ≈ 2^j`. There is `C` such that for every `j ∈ ℤ`, every time `t` and every point `x`,

`|𝓕⁻ (exp(2πit‖·‖) ψⱼ) (x)| ≤ C 2^{jn} (1 + 2^j |t|)^(-(n - 1)/2)`, and `C ≥ 0`. -/
theorem exists_norm_fourierInv_phaseSymbol_sqrtNegLaplacianSymbol_mul_littlewoodPaley_le :
    ∃ C, 0 ≤ C ∧ ∀ (j : ℤ) (t : ℝ) (x : E),
      ‖𝓕⁻ (fun ξ ↦ phaseSymbol sqrtNegLaplacianSymbol t ξ * φ.littlewoodPaley j ξ) x‖ ≤
        C * ((2 : ℝ) ^ j) ^ Module.finrank ℝ E *
          (1 + 2 ^ j * |t|) ^ (-((Module.finrank ℝ E : ℝ) - 1) / 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_fourierInv_phaseSymbol_sqrtNegLaplacianSymbol_mul_le
    (ofRealCLM.contDiff.comp (φ.contDiff_littlewoodPaley 0))
    ((φ.hasCompactSupport_littlewoodPaley 0).comp_left ofReal_zero)
    (fun h ↦ φ.zero_notMem_tsupport_littlewoodPaley 0 (tsupport_comp_subset ofReal_zero _ h))
  refine ⟨C, hC0, fun j t x ↦ ?_⟩
  have h2 : (0 : ℝ) < 2 ^ j := zpow_pos two_pos j
  have heq : (fun ξ ↦ phaseSymbol sqrtNegLaplacianSymbol t ξ * φ.littlewoodPaley j ξ) =
      fun ξ ↦ (fun η ↦ phaseSymbol sqrtNegLaplacianSymbol (2 ^ j * t) η *
        φ.littlewoodPaley 0 η) (((2 : ℝ) ^ j)⁻¹ • ξ) := by
    ext ξ
    dsimp only
    rw [littlewoodPaley_apply_eq_littlewoodPaley_zero_apply, phaseSymbol_apply, phaseSymbol_apply,
      sqrtNegLaplacianSymbol_apply, sqrtNegLaplacianSymbol_apply, norm_smul, norm_inv,
      Real.norm_of_nonneg h2.le]
    congr 4
    field_simp
  rw [heq, fourierInv_comp_smul (fun η ↦ phaseSymbol sqrtNegLaplacianSymbol (2 ^ j * t) η *
    (φ.littlewoodPaley 0 η : ℂ)), inv_inv, norm_smul]
  simp only [Real.norm_eq_abs, inv_pow, abs_inv, inv_inv, abs_of_pos (pow_pos h2 _)]
  calc _ ≤ ((2 : ℝ) ^ j) ^ Module.finrank ℝ E *
        (C * (1 + |2 ^ j * t|) ^ (-((Module.finrank ℝ E : ℝ) - 1) / 2)) := by
        gcongr
        exact hC _ _
    _ = _ := by
        rw [abs_mul, abs_of_pos h2]
        ring

/-! ### The operator form -/

/-- **The dispersive estimate for the frequency-localized half-wave propagator.** Let `E` have
dimension `n`, let `ψⱼ` be the Littlewood–Paley cutoffs built from `φ`, and let `Pⱼ` be the
`L²` Fourier multiplier with symbol `ψⱼ`. There is `C ≥ 0` such that for every `j ∈ ℤ`, every time
`t` and every integrable `f ∈ L²`,

`‖W₊(t) Pⱼ f‖_∞ ≤ C 2^{jn} (1 + 2^j |t|)^(-(n - 1)/2) ‖f‖₁`.

Since `W₋(t) = W₊(-t)`, the same bound holds for `W₋`. -/
theorem exists_eLpNorm_halfWavePropagator_fourierMultiplierCLM_littlewoodPaley_le
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] :
    ∃ C, 0 ≤ C ∧ ∀ (j : ℤ) (m : Lp ℂ ∞ (volume : Measure E)),
      m =ᵐ[volume] (fun ξ ↦ (φ.littlewoodPaley j ξ : ℂ)) → ∀ (t : ℝ)
      (f : Lp F 2 (volume : Measure E)), Integrable f →
      eLpNorm (halfWavePropagator F t (Lp.fourierMultiplierCLM F m f)) ∞ volume ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ Module.finrank ℝ E *
          (1 + 2 ^ j * |t|) ^ (-((Module.finrank ℝ E : ℝ) - 1) / 2)) * eLpNorm f 1 volume := by
  obtain ⟨C, hC0, hC⟩ :=
    φ.exists_norm_fourierInv_phaseSymbol_sqrtNegLaplacianSymbol_mul_littlewoodPaley_le
  refine ⟨C, hC0, fun j m hm t f hf ↦ ?_⟩
  set B := C * ((2 : ℝ) ^ j) ^ Module.finrank ℝ E *
    (1 + 2 ^ j * |t|) ^ (-((Module.finrank ℝ E : ℝ) - 1) / 2)
  -- The localized symbol `ψⱼ exp(2πit‖·‖)` as a Schwartz function.
  set σ : 𝓢(E, ℂ) :=
    φ.littlewoodPaleyPiece (contDiffOn_phaseSymbol_sqrtNegLaplacianSymbol (E := E) t) j
  have hσ : ⇑σ = fun ξ ↦ phaseSymbol sqrtNegLaplacianSymbol t ξ * φ.littlewoodPaley j ξ := by
    rw [coe_littlewoodPaleyPiece]
    funext ξ
    rw [Complex.real_smul, mul_comm]
  -- `W₊(t) Pⱼ` is the multiplier with the Schwartz symbol `σ`.
  have hop : halfWavePropagator F t (Lp.fourierMultiplierCLM F m f) =
      Lp.fourierMultiplierCLM F (σ.toLp ∞) f := by
    rw [halfWavePropagator_def, phasePropagator_def,
      Lp.fourierMultiplierCLM_fourierMultiplierCLM_apply]
    congr 2
    apply Lp.ext
    filter_upwards [Lp.coeFn_lpSMul (r := ∞) ((memLp_phaseSymbol sqrtNegLaplacianSymbol t).toLp _)
      m, (memLp_phaseSymbol (E := E) sqrtNegLaplacianSymbol t).coeFn_toLp, hm,
      σ.coeFn_toLp ∞] with ξ h₁ h₂ h₃ h₄
    rw [h₁, Pi.smul_apply', h₂, h₃, h₄, hσ, smul_eq_mul]
  have hK : ∀ z, ‖𝓕⁻ (σ : E → ℂ) z‖ ≤ B := fun z ↦ by
    rw [hσ]
    exact hC j t z
  have hbound : ∀ᵐ x ∂volume,
      ‖halfWavePropagator F t (Lp.fourierMultiplierCLM F m f) x‖ ≤ B * ∫ y, ‖f y‖ := by
    rw [hop]
    filter_upwards [SchwartzMap.coeFn_fourierMultiplierCLM_toLp σ f] with x hx
    rw [hx, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hf.norm.const_mul _) (Eventually.of_forall fun y ↦ ?_)
    rw [norm_smul, SchwartzMap.fourierInv_coe]
    exact mul_le_mul_of_nonneg_right (hK _) (norm_nonneg _)
  have hB : 0 ≤ B := (norm_nonneg _).trans (hK 0)
  rw [eLpNorm_exponent_top, eLpNorm_one_eq_lintegral_eNorm,
    ← ofReal_integral_norm_eq_lintegral_eNorm hf, ← ENNReal.ofReal_mul hB]
  · exact eLpNormEssSup_le_of_ae_bound hbound
  all_goals exact Lp.aestronglyMeasurable _

end ContDiffBump
