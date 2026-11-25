/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Little
public import TauCeti.Analysis.Pseudodifferential.SchwartzMapping
public import TauCeti.Analysis.Sobolev.BesselPotential.Besov
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.Fourier.FourierChar.Deriv
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.FourierMultiplier
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Multiplication
import TauCeti.Analysis.PositiveDefinite.FourierAtom
import TauCeti.Analysis.Pseudodifferential.Sobolev
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import TauCeti.MeasureTheory.Integral.MinkowskiIntegral

/-!
# Pseudodifferential operators with compact spatial support on Besov spaces

Let `a` be a scalar symbol of order `m` on `ℝⁿ` (`TauCeti.Symbol n ℂ ℂ m`) that vanishes for
positions outside a compact set. Its left quantization `Op(a)` loses at most `m` derivatives on the
Besov scale `B^s_{p,∞}`, for every real `s` and every `1 ≤ p ≤ ∞`: on Schwartz functions

`‖Op(a) u‖_{B^{s-m}_{p,∞}} ≤ C ‖u‖_{B^s_{p,∞}}`

with `C` independent of `p`
(`TauCeti.Symbol.HasCompactSpatialSupport.exists_norm_toBesovSpaceCLM_quantizeUniformCLM_le`).
For `p = ∞` this is the Hölder–Zygmund estimate `‖Op(a) u‖_{𝒞^{s-m}} ≤ C ‖u‖_{𝒞^s}` for Schwartz
`u`, on the scale `𝒞^s = B^s_{∞,∞}`, where operators of order `0` need not be bounded on `L^∞`.
Consequently `Op(a)` extends to a bounded operator `b^s_{p,∞} → b^{s-m}_{p,∞}` between the little
Besov spaces, the closures of the Schwartz functions (`TauCeti.Symbol.quantizeLittleBesov`), with
operator norm bounded uniformly in `p`; for `p = ∞` these are the little Hölder–Zygmund spaces.
For operator-valued symbols `TauCeti.Symbol n V W m` between finite-dimensional spaces, the
Hölder–Zygmund estimate (`p = q = ∞`) is the theorem
`HasCompactSpatialSupport.exists_norm_toBesovSpaceCLM_quantizeUniformCLM_le_of_finiteDimensional`
in `TauCeti.Analysis.Pseudodifferential.Zygmund`.

## The argument

Write `g_η(ζ) = â(η, 2πζ)` for the Fourier transform of `a` in the position, at the angular
frequency `2πζ`. Fourier inversion in the position writes `Op(a)` as a superposition of modulated
Fourier multipliers,

`Op(a) u (x) = ∫ exp(2πi ⟪η, x⟫) (g_η(D) u)(x) dη`,

and the same holds for every Littlewood–Paley block `Δⱼ Op(a) u`, by Fubini's theorem. Each `g_η`
is a symbol of order `m` in `ζ` whose constants decay faster than any power of `⟨η⟩`
(`TauCeti.Symbol.HasCompactSpatialSupport.exists_norm_iteratedFDeriv_fourier_slice_smul_le`), so
`g_η(D) : B^s_{p,∞} → B^{s-m}_{p,∞}` has norm `O(⟨η⟩ ^ (-r))` for every `r`
(`TauCeti.BesovSpace.exists_toDistr_eq_fourierMultiplierCLM_and_norm_le`). Multiplication by the
plane wave `exp(2πi ⟪η, x⟫)` costs only a polynomial factor in `η` on `B^{s-m}_{p,∞}`, by the
derivative bounds `(2π ‖η‖) ^ k` (`Real.norm_iteratedFDeriv_fourierChar_inner_le`) and
`TauCeti.BesovSpace.exists_toDistr_eq_smulLeftCLM_and_norm_le`.
The `j`-th weighted block of the modulated piece of frequency `η` is therefore bounded by an
integrable function of `η`, and Minkowski's integral inequality
(`TauCeti.eLpNorm_integral_le_lintegral_eLpNorm`) sums these bounds over `η`, block by block.

## Main declarations

* `TauCeti.Symbol.HasCompactSpatialSupport.exists_norm_toBesovSpaceCLM_quantizeUniformCLM_le`:
  the estimate `B^s_{p,∞} → B^{s-m}_{p,∞}` on Schwartz functions, uniformly in `p`.
* `TauCeti.Symbol.quantizeLittleBesov`: the bounded extension `b^s_{p,∞} → b^{s-m}_{p,∞}` between
  the little Besov spaces, with its values on Schwartz functions
  (`TauCeti.Symbol.coe_quantizeLittleBesov_toLittleBesovCLM`) and a bound on its operator norm
  uniform in `p` (`TauCeti.Symbol.exists_norm_quantizeLittleBesov_le`).

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (3.31)
  (the Fourier transform in the position of a symbol with compact spatial support) and
  (3.32)–(3.34) (pseudodifferential operators on the Zygmund spaces).
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Section 2.7 (Besov spaces).
* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed.,
  Theorem 6.19 (Minkowski's integral inequality).
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform
open scoped ENNReal NNReal SchwartzMap RealInnerProductSpace ContDiff

namespace TauCeti

namespace Symbol

variable {n : ℕ}

/-! ### Plane waves -/

/-- The derivatives of order at most `N` of the plane wave of frequency `η` are bounded by
`(2π) ^ N (1 + ‖η‖) ^ N`. -/
private theorem norm_iteratedFDeriv_fourierChar_inner_le_pow (η : CoordinateSpace n) {N k : ℕ}
    (hk : k ≤ N) (x : CoordinateSpace n) :
    ‖iteratedFDeriv ℝ k (fun x : CoordinateSpace n ↦ (𝐞 ⟪x, η⟫ : ℂ)) x‖ ≤
      (2 * π) ^ N * (1 + ‖η‖) ^ N := by
  refine (Real.norm_iteratedFDeriv_fourierChar_inner_le η k x).trans ?_
  have h1 : 1 ≤ 2 * π * (1 + ‖η‖) := by
    nlinarith [Real.two_le_pi, norm_nonneg η]
  calc (2 * π * ‖η‖) ^ k ≤ (2 * π * (1 + ‖η‖)) ^ k := by
        gcongr
        linarith
    _ ≤ (2 * π * (1 + ‖η‖)) ^ N := pow_le_pow_right₀ h1 hk
    _ = _ := mul_pow _ _ _

/-! ### The multipliers of the position-Fourier slices -/

variable {m : ℝ} {a : Symbol n ℂ ℂ m}

/-- Evaluation at `1`, which identifies `ℂ →L[ℂ] ℂ` with `ℂ`, as a real-linear map. -/
private def applyOne : (ℂ →L[ℂ] ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).restrictScalars ℝ

/-- The scalar multiplier `ζ ↦ â(η, 2πζ)`: the Fourier transform in the position of a scalar
symbol, at the angular frequency `2πζ`. -/
private def sliceMultiplier (a : Symbol n ℂ ℂ m) (η ζ : CoordinateSpace n) : ℂ :=
  applyOne (𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) η)

/-- A scalar operator `L : ℂ →L[ℂ] ℂ` is multiplication by `L 1`. -/
private theorem fourier_slice_apply (η ζ : CoordinateSpace n) (w : ℂ) :
    𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) η w = sliceMultiplier a η ζ • w := by
  set L := 𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) η
  have h : L w = w • L 1 := by rw [← L.map_smul, smul_eq_mul, mul_one]
  rw [h]
  simp [L, sliceMultiplier, applyOne, mul_comm w]

private theorem HasCompactSpatialSupport.contDiff_sliceMultiplier
    (ha : a.HasCompactSpatialSupport) (η : CoordinateSpace n) :
    ContDiff ℝ ∞ (sliceMultiplier a η) :=
  applyOne.contDiff.comp (ha.contDiff_fourier_slice_smul η)

/-- `‖D^i â(η, 2πζ)‖ ≤ B ⟨ζ⟩ ^ (m - i) ⟨η⟩ ^ (-r)`, for every `i` and `r`. -/
private theorem HasCompactSpatialSupport.exists_norm_iteratedFDeriv_sliceMultiplier_le
    (ha : a.HasCompactSpatialSupport) (i : ℕ) (r : ℝ) :
    ∃ B, 0 ≤ B ∧ ∀ η ζ : CoordinateSpace n,
      ‖iteratedFDeriv ℝ i (sliceMultiplier a η) ζ‖ ≤
        B * (1 + ‖ζ‖ ^ 2) ^ ((m - i) / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  obtain ⟨B, hB0, hB⟩ := ha.exists_norm_iteratedFDeriv_fourier_slice_smul_le i r
  refine ⟨‖applyOne‖ * B, by positivity, fun η ζ ↦ ?_⟩
  refine (applyOne.norm_iteratedFDeriv_comp_left
    (ha.contDiff_fourier_slice_smul η).contDiffAt (mod_cast le_top)).trans ?_
  rw [mul_assoc, mul_assoc]
  gcongr
  rw [← mul_assoc]
  exact hB η ζ

private theorem HasCompactSpatialSupport.hasTemperateGrowth_sliceMultiplier
    (ha : a.HasCompactSpatialSupport) (η : CoordinateSpace n) :
    (sliceMultiplier a η).HasTemperateGrowth :=
  .of_norm_iteratedFDeriv_le_one_add_norm_sq_rpow (ha.contDiff_sliceMultiplier η) fun i ↦ by
    obtain ⟨B, -, hB⟩ := ha.exists_norm_iteratedFDeriv_sliceMultiplier_le i 0
    exact ⟨B * (1 + ‖η‖ ^ 2) ^ (-(0 : ℝ) / 2), fun ζ ↦ (hB η ζ).trans_eq (by ring)⟩

private theorem HasCompactSpatialSupport.continuous_sliceMultiplier
    (ha : a.HasCompactSpatialSupport) :
    Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ sliceMultiplier a q.1 q.2 :=
  applyOne.continuous.comp (ha.continuous_fourier_slice.comp
    (continuous_fst.prodMk ((continuous_const_smul (2 * π)).comp continuous_snd)))

/-- The multiplier `â(η, 2πζ)` is bounded by `B ⟨ζ⟩ ^ m ⟨η⟩ ^ (-(n + 1))`. -/
private theorem HasCompactSpatialSupport.exists_norm_sliceMultiplier_le
    (ha : a.HasCompactSpatialSupport) :
    ∃ B, 0 ≤ B ∧ ∀ η ζ : CoordinateSpace n, ‖sliceMultiplier a η ζ‖ ≤
      B * (1 + ‖ζ‖ ^ 2) ^ (m / 2) * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
  obtain ⟨B, hB0, hB⟩ := ha.exists_norm_iteratedFDeriv_sliceMultiplier_le 0 ((n : ℝ) + 1)
  exact ⟨B, hB0, fun η ζ ↦ by simpa using hB η ζ⟩

/-! ### The superposition of modulated multipliers -/

/-- The modulated piece `x ↦ exp(2πi ⟪x, η⟫) (g_η(D) u)(x)` with the Fourier multiplier
`g_η(ζ) = â(η, 2πζ)`. Its integral over `η` is `Op(a) u`. -/
private def modulatedPiece (a : Symbol n ℂ ℂ m) (u : 𝓢(CoordinateSpace n, ℂ))
    (η : CoordinateSpace n) : 𝓢(CoordinateSpace n, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x ↦ (𝐞 ⟪x, η⟫ : ℂ))
    (SchwartzMap.fourierMultiplierCLM ℂ (sliceMultiplier a η) u)

private theorem HasCompactSpatialSupport.modulatedPiece_apply (ha : a.HasCompactSpatialSupport)
    (u : 𝓢(CoordinateSpace n, ℂ)) (η x : CoordinateSpace n) :
    modulatedPiece a u η x =
      (𝐞 ⟪η, x⟫ : ℂ) • ∫ ζ, (𝐞 ⟪ζ, x⟫ : ℂ) • (sliceMultiplier a η ζ • 𝓕 u ζ) := by
  rw [modulatedPiece,
    SchwartzMap.smulLeftCLM_apply_apply (Real.hasTemperateGrowth_fourierChar_inner η),
    SchwartzMap.fourierMultiplierCLM_apply, SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
  simp only [SchwartzMap.smulLeftCLM_apply_apply (ha.hasTemperateGrowth_sliceMultiplier η),
    Circle.smul_def, real_inner_comm η x]

/-- The modulated pieces are bounded by `C ⟨η⟩ ^ (-(n + 1))`, uniformly in the position. -/
private theorem HasCompactSpatialSupport.exists_norm_modulatedPiece_le
    (ha : a.HasCompactSpatialSupport) (u : 𝓢(CoordinateSpace n, ℂ)) :
    ∃ C, 0 ≤ C ∧ ∀ η x : CoordinateSpace n,
      ‖modulatedPiece a u η x‖ ≤ C * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
  obtain ⟨B, hB0, hB⟩ := ha.exists_norm_sliceMultiplier_le
  set I := ∫ ζ : CoordinateSpace n, (1 + ‖ζ‖ ^ 2) ^ (m / 2) * ‖𝓕 u ζ‖
  have : 0 ≤ I := integral_nonneg fun _ ↦ by positivity
  refine ⟨B * I, by positivity, fun η x ↦ ?_⟩
  rw [ha.modulatedPiece_apply, norm_smul, Circle.norm_coe, one_mul]
  refine (norm_integral_le_integral_norm _).trans ?_
  calc ∫ ζ, ‖(𝐞 ⟪ζ, x⟫ : ℂ) • (sliceMultiplier a η ζ • 𝓕 u ζ)‖
      ≤ ∫ ζ, B * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) *
          ((1 + ‖ζ‖ ^ 2) ^ (m / 2) * ‖𝓕 u ζ‖) := by
        refine integral_mono_of_nonneg (.of_forall fun _ ↦ norm_nonneg _)
          (((𝓕 u).integrable_one_add_norm_sq_rpow_mul_norm (m / 2)).const_mul _)
          (.of_forall fun ζ ↦ ?_)
        simp only [norm_smul, Circle.norm_coe, one_mul]
        calc ‖sliceMultiplier a η ζ‖ * ‖𝓕 u ζ‖
            ≤ B * (1 + ‖ζ‖ ^ 2) ^ (m / 2) * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) * ‖𝓕 u ζ‖ := by
              gcongr
              exact hB η ζ
          _ = _ := by ring
    _ = B * I * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
        rw [integral_const_mul]
        ring

/-- The modulated pieces depend continuously on the frequency and the position jointly. -/
private theorem HasCompactSpatialSupport.continuous_modulatedPiece
    (ha : a.HasCompactSpatialSupport) (u : 𝓢(CoordinateSpace n, ℂ)) :
    Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ modulatedPiece a u q.1 q.2 := by
  obtain ⟨B, hB0, hB⟩ := ha.exists_norm_sliceMultiplier_le
  simp only [ha.modulatedPiece_apply]
  refine Real.continuous_fourierChar_inner.smul (continuous_of_dominated
    (bound := fun ζ ↦ B * ((1 + ‖ζ‖ ^ 2) ^ (m / 2) * ‖𝓕 u ζ‖)) (fun q ↦ ?_)
    (fun q ↦ .of_forall fun ζ ↦ ?_)
    (((𝓕 u).integrable_one_add_norm_sq_rpow_mul_norm (m / 2)).const_mul B)
    (.of_forall fun ζ ↦ ?_))
  · exact ((Real.continuous_fourierChar_inner.comp (continuous_id.prodMk continuous_const)).smul
      ((ha.continuous_sliceMultiplier.comp (continuous_const.prodMk continuous_id)).smul
        (𝓕 u).continuous)).aestronglyMeasurable
  · simp only [norm_smul, Circle.norm_coe, one_mul]
    have hρ : (1 + ‖q.1‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖q.1‖])
        (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith)
    calc ‖sliceMultiplier a q.1 ζ‖ * ‖𝓕 u ζ‖
        ≤ B * (1 + ‖ζ‖ ^ 2) ^ (m / 2) * 1 * ‖𝓕 u ζ‖ := by
          gcongr
          exact (hB q.1 ζ).trans (by gcongr)
      _ = _ := by ring
  · exact (Real.continuous_fourierChar_inner.comp (continuous_const.prodMk continuous_snd)).smul
      ((ha.continuous_sliceMultiplier.comp (continuous_fst.prodMk continuous_const)).smul
        continuous_const)

/-- **The superposition formula.** For a scalar symbol `a` with compact spatial support,
`Op(a) u (x) = ∫ exp(2πi ⟪η, x⟫) (g_η(D) u)(x) dη`, with the Fourier multipliers
`g_η(ζ) = â(η, 2πζ)` given by the Fourier transform of `a` in the position. -/
private theorem HasCompactSpatialSupport.quantizeSchwartzValue_eq_integral_modulatedPiece
    (ha : a.HasCompactSpatialSupport) (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n) :
    quantizeSchwartzValue a.coefficient u x = ∫ η, modulatedPiece a u η x := by
  obtain ⟨B, -, hB⟩ := ha.exists_norm_iteratedFDeriv_fourier_slice_smul_le 0 ((n : ℝ) + 1)
  -- The slice at `2πζ` is the inverse Fourier transform of its Fourier transform in the position.
  have hslice (ζ : CoordinateSpace n) : a.coefficient (x, (2 * π) • ζ) =
      ∫ η, (𝐞 ⟪η, x⟫ : ℂ) • 𝓕 (fun y ↦ a.coefficient (y, (2 * π) • ζ)) η := by
    have h := congrFun (ha.fourierInv_fourier_slice ((2 * π) • ζ)) x
    rw [Real.fourierInv_eq] at h
    simpa only [Circle.smul_def] using h.symm
  rw [quantizeSchwartzValue_eq_integral_smul_fourierInv (C := B) (M := m)
    (ha.continuous_fourier_slice.comp
      (continuous_fst.prodMk ((continuous_const_smul (2 * π)).comp continuous_snd)))
    integrable_one_add_norm_sq_rpow_neg_succ_div_two (fun η ζ ↦ by simpa using hB η ζ) hslice u]
  refine integral_congr_ae (.of_forall fun η ↦ ?_)
  simp only [ha.modulatedPiece_apply, Real.fourierInv_eq, Circle.smul_def, fourier_slice_apply]

/-! ### Littlewood–Paley blocks of the superposition -/

variable {φ : ContDiffBump (0 : CoordinateSpace n)}

/-- **The superposition formula for the blocks.** The Littlewood–Paley block `Δⱼ Op(a) u` is the
superposition of the blocks of the modulated pieces. -/
private theorem HasCompactSpatialSupport.fourierMultiplierCLM_quantizeUniformCLM_eq_integral
    (ha : a.HasCompactSpatialSupport) (u : 𝓢(CoordinateSpace n, ℂ)) (j : ℕ)
    (x : CoordinateSpace n) :
    SchwartzMap.fourierMultiplierCLM ℂ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ))
        (quantizeUniformCLM a ha.isUniform u) x =
      ∫ η, SchwartzMap.fourierMultiplierCLM ℂ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ))
        (modulatedPiece a u η) x := by
  obtain ⟨C, -, hC⟩ := ha.exists_norm_modulatedPiece_le u
  set k : 𝓢(CoordinateSpace n, ℂ) := 𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j)
  have hk : Integrable fun y ↦ k (x - y) := k.integrable.comp_sub_left x
  -- The integrand is dominated by `C ‖k (x - y)‖ ⟨η⟩ ^ (-(n + 1))`.
  have hG : Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦
      k (x - q.1) • modulatedPiece a u q.2 q.1) (volume.prod volume) := by
    refine ((hk.norm.mul_prod integrable_one_add_norm_sq_rpow_neg_succ_div_two).const_mul C).mono'
      ?_ (.of_forall fun q ↦ ?_)
    · exact ((k.continuous.comp (continuous_const.sub continuous_fst)).smul
        ((ha.continuous_modulatedPiece u).comp continuous_swap)).aestronglyMeasurable
    · rw [norm_smul]
      calc ‖k (x - q.1)‖ * ‖modulatedPiece a u q.2 q.1‖
          ≤ ‖k (x - q.1)‖ * (C * (1 + ‖q.2‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)) := by
            gcongr
            exact hC _ _
        _ = _ := by ring
  rw [SchwartzMap.fourierMultiplierCLM_inhomogeneousLittlewoodPaley_apply_eq_integral]
  calc ∫ y, k (x - y) • quantizeUniformCLM a ha.isUniform u y
      = ∫ y, ∫ η, k (x - y) • modulatedPiece a u η y := by
        refine integral_congr_ae (.of_forall fun y ↦ ?_)
        beta_reduce
        rw [quantizeUniformCLM_apply, ha.quantizeSchwartzValue_eq_integral_modulatedPiece,
          integral_smul]
    _ = ∫ η, ∫ y, k (x - y) • modulatedPiece a u η y := integral_integral_swap hG
    _ = _ := by
        refine integral_congr_ae (.of_forall fun η ↦ ?_)
        beta_reduce
        rw [SchwartzMap.fourierMultiplierCLM_inhomogeneousLittlewoodPaley_apply_eq_integral]

/-- The blocks of the modulated pieces are jointly a.e. strongly measurable in the position and the
frequency. -/
private theorem HasCompactSpatialSupport.aestronglyMeasurable_fourierMultiplierCLM_modulatedPiece
    (ha : a.HasCompactSpatialSupport) (u : 𝓢(CoordinateSpace n, ℂ)) (j : ℕ) :
    AEStronglyMeasurable (Function.uncurry fun x η ↦
      SchwartzMap.fourierMultiplierCLM ℂ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ))
        (modulatedPiece a u η) x) (volume.prod volume) := by
  have h : (Function.uncurry fun x η ↦
      SchwartzMap.fourierMultiplierCLM ℂ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ))
        (modulatedPiece a u η) x) = fun q ↦
      ∫ y, 𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j) (q.1 - y) • modulatedPiece a u q.2 y := by
    funext q
    exact SchwartzMap.fourierMultiplierCLM_inhomogeneousLittlewoodPaley_apply_eq_integral φ j _ q.1
  rw [h]
  exact (((𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j)).continuous.comp
    (continuous_fst.fst.sub continuous_snd)).smul ((ha.continuous_modulatedPiece u).comp
      (continuous_fst.snd.prodMk continuous_snd))).aestronglyMeasurable.integral_prod_right'

/-! ### The Besov estimate -/

/-- `(1 + ‖η‖) ^ N ⟨η⟩ ^ (-(N + n + 1)) ≤ √2 ^ N ⟨η⟩ ^ (-(n + 1))`. -/
private theorem one_add_norm_pow_mul_rpow_le (η : CoordinateSpace n) (N : ℕ) :
    (1 + ‖η‖) ^ N * (1 + ‖η‖ ^ 2) ^ (-((N : ℝ) + n + 1) / 2) ≤
      √2 ^ N * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
  have hη : 0 < 1 + ‖η‖ ^ 2 := by positivity
  have hsq : √(1 + ‖η‖ ^ 2) ^ N = (1 + ‖η‖ ^ 2) ^ ((N : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hη.le]
    ring_nf
  calc (1 + ‖η‖) ^ N * (1 + ‖η‖ ^ 2) ^ (-((N : ℝ) + n + 1) / 2)
      ≤ (√2 * √(1 + ‖η‖ ^ 2)) ^ N * (1 + ‖η‖ ^ 2) ^ (-((N : ℝ) + n + 1) / 2) := by
        gcongr
        exact one_add_norm_le_sqrt_two_mul_sqrt η
    _ = √2 ^ N * ((1 + ‖η‖ ^ 2) ^ ((N : ℝ) / 2) *
          (1 + ‖η‖ ^ 2) ^ (-((N : ℝ) + n + 1) / 2)) := by
        rw [mul_pow, hsq, mul_assoc]
    _ = _ := by
        rw [← Real.rpow_add hη]
        ring_nf

/-- **Besov bounds of the modulated pieces.** The modulated piece of frequency `η` has norm in
`B^{s-m}_{p,q}` at most `K ⟨η⟩ ^ (-(n + 1))` times the norm of `u` in `B^s_{p,q}`. The plane wave
costs a polynomial factor in `η` (`TauCeti.BesovSpace.exists_toDistr_eq_smulLeftCLM_and_norm_le`),
which the decay in `η` of the multiplier `â(η, 2πζ)` of order `m`
(`TauCeti.BesovSpace.exists_toDistr_eq_fourierMultiplierCLM_and_norm_le`) absorbs. -/
private theorem HasCompactSpatialSupport.exists_norm_toBesovSpaceCLM_modulatedPiece_le
    (ha : a.HasCompactSpatialSupport) (φ : ContDiffBump (0 : CoordinateSpace n)) (s : ℝ) :
    ∃ K, 0 ≤ K ∧ ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (u : 𝓢(CoordinateSpace n, ℂ))
      (η : CoordinateSpace n),
      ‖SchwartzMap.toBesovSpaceCLM ℂ φ (s - m) p q (modulatedPiece a u η)‖ ≤
        K * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) * ‖SchwartzMap.toBesovSpaceCLM ℂ φ s p q u‖ := by
  set N : ℕ := ⌊|s - m|⌋₊ + 1
  have hN : |s - m| < N := by push_cast [N]; exact Nat.lt_floor_add_one _
  obtain ⟨Cf, hCf0, hCf⟩ :=
    BesovSpace.exists_toDistr_eq_fourierMultiplierCLM_and_norm_le (F := ℂ) φ m (s := s) rfl
  obtain ⟨Cm, hCm0, hCm⟩ :=
    BesovSpace.exists_toDistr_eq_smulLeftCLM_and_norm_le (F := ℂ) φ (s := s - m) hN
  choose B hB0 hB using fun i : ℕ ↦
    ha.exists_norm_iteratedFDeriv_sliceMultiplier_le i ((N : ℝ) + n + 1)
  set S : ℝ := ∑ i ∈ Finset.range (n + 2), B i
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ hB0 i
  refine ⟨Cm * (2 * π) ^ N * Cf * S * √2 ^ N, by positivity, fun {p q} _ _ u η ↦ ?_⟩
  set ρ : ℝ := (1 + ‖η‖ ^ 2) ^ (-((N : ℝ) + n + 1) / 2)
  have : 0 ≤ ρ := by positivity
  -- The symbol estimates of the multiplier, with the constant `S ρ`.
  have hW : ∀ i ≤ Module.finrank ℝ (CoordinateSpace n) + 1, ∀ ζ,
      ‖iteratedFDeriv ℝ i (sliceMultiplier a η) ζ‖ ≤ S * ρ * (1 + ‖ζ‖ ^ 2) ^ ((m - i) / 2) := by
    intro i hi ζ
    rw [finrank_euclideanSpace_fin] at hi
    refine (hB i η ζ).trans ?_
    rw [mul_right_comm]
    gcongr
    exact Finset.single_le_sum (fun i _ ↦ hB0 i) (Finset.mem_range.2 (by omega))
  obtain ⟨v₁, hv₁, hv₁n⟩ :=
    hCf (ha.hasTemperateGrowth_sliceMultiplier η) hW (SchwartzMap.toBesovSpaceCLM ℂ φ s p q u)
  obtain ⟨v₂, hv₂, hv₂n⟩ := hCm (Real.hasTemperateGrowth_fourierChar_inner η)
    (fun k hk x ↦ norm_iteratedFDeriv_fourierChar_inner_le_pow η hk x) v₁
  have hv : SchwartzMap.toBesovSpaceCLM ℂ φ (s - m) p q (modulatedPiece a u η) = v₂ :=
    BesovSpace.ext <| by
      rw [SchwartzMap.toDistr_toBesovSpaceCLM, hv₂, hv₁, SchwartzMap.toDistr_toBesovSpaceCLM,
        TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq
          (ha.hasTemperateGrowth_sliceMultiplier η),
        TemperedDistribution.smulLeftCLM_toTemperedDistributionCLM_eq, modulatedPiece]
  have hρη := one_add_norm_pow_mul_rpow_le η N
  rw [hv]
  calc ‖v₂‖ ≤ Cm * ((2 * π) ^ N * (1 + ‖η‖) ^ N) * ‖v₁‖ := hv₂n
    _ ≤ Cm * ((2 * π) ^ N * (1 + ‖η‖) ^ N) *
          (Cf * (S * ρ) * ‖SchwartzMap.toBesovSpaceCLM ℂ φ s p q u‖) := by gcongr
    _ = Cm * (2 * π) ^ N * Cf * S * ((1 + ‖η‖) ^ N * ρ) *
          ‖SchwartzMap.toBesovSpaceCLM ℂ φ s p q u‖ := by ring
    _ ≤ Cm * (2 * π) ^ N * Cf * S * (√2 ^ N * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)) *
          ‖SchwartzMap.toBesovSpaceCLM ℂ φ s p q u‖ := by gcongr
    _ = _ := by ring

/-- **Block bounds of the modulated pieces.** The `j`-th Littlewood–Paley block of the modulated
piece of frequency `η` has `Lᵖ` norm at most `2^{-j(s-m)} K ⟨η⟩ ^ (-(n + 1))` times the norm of `u`
in `B^s_{p,∞}`. -/
private theorem HasCompactSpatialSupport.exists_eLpNorm_fourierMultiplierCLM_modulatedPiece_le
    (ha : a.HasCompactSpatialSupport) (φ : ContDiffBump (0 : CoordinateSpace n)) (s : ℝ) :
    ∃ K, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : 𝓢(CoordinateSpace n, ℂ)) (j : ℕ)
      (η : CoordinateSpace n),
      eLpNorm (SchwartzMap.fourierMultiplierCLM ℂ
        (fun ξ : CoordinateSpace n ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ))
          (modulatedPiece a u η)) p volume ≤
        ENNReal.ofReal (2 ^ (-((s - m) * j)) * K * ‖SchwartzMap.toBesovSpaceCLM ℂ φ s p ∞ u‖ *
          (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)) := by
  obtain ⟨K, hK0, hK⟩ := ha.exists_norm_toBesovSpaceCLM_modulatedPiece_le φ s
  refine ⟨K, hK0, fun {p} _ u j η ↦ ?_⟩
  set Δ := SchwartzMap.fourierMultiplierCLM ℂ
    (fun ξ : CoordinateSpace n ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ))
  have h := (BesovSpace.rpow_mul_norm_block_le
    (SchwartzMap.toBesovSpaceCLM ℂ φ (s - m) p ∞ (modulatedPiece a u η)) j).trans (hK u η)
  rw [BesovSpace.block_toBesovSpaceCLM, SchwartzMap.norm_toLp] at h
  rw [← ENNReal.ofReal_toReal ((Δ (modulatedPiece a u η)).memLp p volume).eLpNorm_ne_top]
  refine ENNReal.ofReal_le_ofReal ?_
  have : (0 : ℝ) < 2 ^ ((s - m) * j) := by positivity
  calc (eLpNorm (Δ (modulatedPiece a u η)) p volume).toReal
      = (2 ^ ((s - m) * j))⁻¹ *
          (2 ^ ((s - m) * j) * (eLpNorm (Δ (modulatedPiece a u η)) p volume).toReal) := by
        field_simp
    _ ≤ (2 ^ ((s - m) * j))⁻¹ * (K * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) *
          ‖SchwartzMap.toBesovSpaceCLM ℂ φ s p ∞ u‖) := by gcongr
    _ = _ := by
        rw [Real.rpow_neg zero_le_two]
        ring

/-- **Besov mapping of pseudodifferential operators with compact spatial support.** Let `a` be a
scalar symbol of order `m` with compact spatial support and `s` real. There is `C ≥ 0` such that
for every `1 ≤ p ≤ ∞` and every Schwartz function `u`,

`‖Op(a) u‖_{B^{s-m}_{p,∞}} ≤ C ‖u‖_{B^s_{p,∞}}`.

For `p = ∞` this is the Hölder–Zygmund estimate `‖Op(a) u‖_{𝒞^{s-m}} ≤ C ‖u‖_{𝒞^s}`. The constant
does not depend on `p`. -/
theorem HasCompactSpatialSupport.exists_norm_toBesovSpaceCLM_quantizeUniformCLM_le
    (ha : a.HasCompactSpatialSupport) (φ : ContDiffBump (0 : CoordinateSpace n)) (s : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : 𝓢(CoordinateSpace n, ℂ)),
      ‖SchwartzMap.toBesovSpaceCLM ℂ φ (s - m) p ∞ (quantizeUniformCLM a ha.isUniform u)‖ ≤
        C * ‖SchwartzMap.toBesovSpaceCLM ℂ φ s p ∞ u‖ := by
  obtain ⟨K, hK0, hK⟩ := ha.exists_eLpNorm_fourierMultiplierCLM_modulatedPiece_le φ s
  have hρ := integrable_one_add_norm_sq_rpow_neg_succ_div_two (n := n)
    (μ := (volume : Measure (CoordinateSpace n)))
  set I := ∫ η : CoordinateSpace n, (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)
  have : 0 ≤ I := integral_nonneg fun _ ↦ by positivity
  refine ⟨K * I, by positivity, fun {p} _ u ↦ ?_⟩
  set U := ‖SchwartzMap.toBesovSpaceCLM ℂ φ s p ∞ u‖
  rw [BesovSpace.norm_eq_ciSup]
  refine ciSup_le fun j ↦ ?_
  set Δ := SchwartzMap.fourierMultiplierCLM ℂ
    (fun ξ : CoordinateSpace n ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ))
  set c : ℝ := 2 ^ (-((s - m) * j)) * K * U
  have : 0 ≤ c := by positivity
  -- Minkowski's integral inequality sums the block bounds of the modulated pieces.
  have hmin := eLpNorm_integral_le_lintegral_eLpNorm
    (F := fun x η ↦ Δ (modulatedPiece a u η) x)
    (ha.aestronglyMeasurable_fourierMultiplierCLM_modulatedPiece u j)
    (fun η ↦ (Δ (modulatedPiece a u η)).continuous) (Fact.out : 1 ≤ p)
  have hfun : (fun x ↦ ∫ η, Δ (modulatedPiece a u η) x) =
      ⇑(Δ (quantizeUniformCLM a ha.isUniform u)) :=
    funext fun x ↦ (ha.fourierMultiplierCLM_quantizeUniformCLM_eq_integral u j x).symm
  rw [hfun] at hmin
  have hbound : eLpNorm (Δ (quantizeUniformCLM a ha.isUniform u)) p volume ≤
      ENNReal.ofReal (c * I) := by
    refine hmin.trans ((lintegral_mono fun η ↦ hK u j η).trans_eq ?_)
    rw [← ofReal_integral_eq_lintegral_ofReal (hρ.const_mul c)
      (.of_forall fun η ↦ by positivity), integral_const_mul]
  rw [BesovSpace.block_toBesovSpaceCLM, SchwartzMap.norm_toLp]
  calc 2 ^ ((s - m) * j) * (eLpNorm (Δ (quantizeUniformCLM a ha.isUniform u)) p volume).toReal
      ≤ 2 ^ ((s - m) * j) * (c * I) := by
        gcongr
        exact ENNReal.toReal_le_of_le_ofReal (by positivity) hbound
    _ = K * I * U := by
        simp only [c, Real.rpow_neg zero_le_two]
        field_simp

/-! ### The operator on the little Besov spaces -/

/-- `Op(a)` on Schwartz functions, with values in the little Besov space `b^{s-m}_{p,∞}`. -/
private def quantizeToLittleBesov (ha : a.HasCompactSpatialSupport)
    (φ : ContDiffBump (0 : CoordinateSpace n)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    𝓢(CoordinateSpace n, ℂ) →ₗ[ℂ] BesovSpace.littleBesov ℂ φ (s - m) p :=
  (SchwartzMap.toLittleBesovCLM ℂ φ (s - m) p).toLinearMap ∘ₗ
    (quantizeUniformCLM a ha.isUniform).toLinearMap

/-- The Besov estimate for `Op(a)`, read in the little Besov spaces. -/
private theorem exists_norm_quantizeToLittleBesov_le (ha : a.HasCompactSpatialSupport)
    (φ : ContDiffBump (0 : CoordinateSpace n)) (s : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : 𝓢(CoordinateSpace n, ℂ)),
      ‖quantizeToLittleBesov ha φ s p u‖ ≤
        C * ‖(SchwartzMap.toLittleBesovCLM ℂ φ s p).toLinearMap u‖ := by
  obtain ⟨C, hC0, hC⟩ := ha.exists_norm_toBesovSpaceCLM_quantizeUniformCLM_le φ s
  refine ⟨C, hC0, fun u ↦ ?_⟩
  simpa only [quantizeToLittleBesov, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    ← Submodule.norm_coe, SchwartzMap.coe_toLittleBesovCLM_apply] using hC u

/-- **Pseudodifferential operators with compact spatial support on little Besov spaces.** Let `a`
be a scalar symbol of order `m` with compact spatial support, `s` real and `1 ≤ p ≤ ∞`. The
quantization `Op(a)` extends from Schwartz functions to a bounded operator
`b^s_{p,∞} → b^{s-m}_{p,∞}` between the little Besov spaces, the closures of the Schwartz functions
in `B^s_{p,∞}` and `B^{s-m}_{p,∞}`. For `p = ∞` these are the little Hölder–Zygmund spaces. On a
Schwartz function `u` it is `Op(a) u`
(`TauCeti.Symbol.coe_quantizeLittleBesov_toLittleBesovCLM`), and by density of the Schwartz
functions it is the unique continuous linear map with this property
(`TauCeti.BesovSpace.littleBesov_continuousLinearMap_ext`). -/
def quantizeLittleBesov (a : Symbol n ℂ ℂ m) (ha : a.HasCompactSpatialSupport)
    (φ : ContDiffBump (0 : CoordinateSpace n)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    BesovSpace.littleBesov ℂ φ s p →L[ℂ] BesovSpace.littleBesov ℂ φ (s - m) p :=
  (quantizeToLittleBesov ha φ s p).extendOfNorm (SchwartzMap.toLittleBesovCLM ℂ φ s p).toLinearMap

/-- On a Schwartz function `u`, the operator `Op(a) : b^s_{p,∞} → b^{s-m}_{p,∞}` gives `Op(a) u`. -/
@[simp]
theorem coe_quantizeLittleBesov_toLittleBesovCLM (ha : a.HasCompactSpatialSupport)
    (φ : ContDiffBump (0 : CoordinateSpace n)) (s : ℝ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : 𝓢(CoordinateSpace n, ℂ)) :
    (a.quantizeLittleBesov ha φ s p (SchwartzMap.toLittleBesovCLM ℂ φ s p u) :
        BesovSpace ℂ φ (s - m) p ∞) =
      SchwartzMap.toBesovSpaceCLM ℂ φ (s - m) p ∞ (quantizeUniformCLM a ha.isUniform u) := by
  obtain ⟨C, -, hC⟩ := exists_norm_quantizeToLittleBesov_le ha φ s
  rw [quantizeLittleBesov,
    ← ContinuousLinearMap.coe_coe (SchwartzMap.toLittleBesovCLM ℂ φ s p),
    LinearMap.extendOfNorm_eq (SchwartzMap.denseRange_toLittleBesovCLM (F := ℂ) φ s p) ⟨C, hC⟩ u,
    quantizeToLittleBesov, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.coe_coe, SchwartzMap.coe_toLittleBesovCLM_apply]

/-- **The norm of `Op(a)` on the little Besov spaces.** The operator norm of
`Op(a) : b^s_{p,∞} → b^{s-m}_{p,∞}` is bounded uniformly in `1 ≤ p ≤ ∞`. -/
theorem exists_norm_quantizeLittleBesov_le (ha : a.HasCompactSpatialSupport)
    (φ : ContDiffBump (0 : CoordinateSpace n)) (s : ℝ) :
    ∃ C, ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)], ‖a.quantizeLittleBesov ha φ s p‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_quantizeToLittleBesov_le ha φ s
  exact ⟨C, LinearMap.opNorm_extendOfNorm_le
    (SchwartzMap.denseRange_toLittleBesovCLM (F := ℂ) φ s _) hC0 hC⟩

end Symbol

end TauCeti
