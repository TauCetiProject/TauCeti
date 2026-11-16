/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
public import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Cpow
import Mathlib.Tactic.Module
import TauCeti.Analysis.Distribution.TemperateGrowth

/-!
# Bessel potentials of complex order on Schwartz space

Let `E` be a finite-dimensional real inner product space. The Bessel potential of complex order
`z` (`SchwartzMap.besselPotentialCLM z`) is the Fourier multiplier `J^z` on Schwartz functions
whose symbol is the complex power `⟨ξ⟩ ^ z` of the Japanese bracket
(`TauCeti.japaneseBracketCpow`). For real `z = s` it is the Bessel potential of order `s`, and the
orders add under composition.

For Schwartz functions with values in a complex Hilbert space, the `H^r` norm of `J^z u` is the
`H^{r + re z}` norm of `u`, so imaginary orders act isometrically on every `H^r`, and `z ↦ J^z u` is
holomorphic with values in every `H^r = H^{r,2}`. These are the analytic families of weights used in
Stein's interpolation argument.

## Main declarations

* `SchwartzMap.besselPotentialCLM z`: the Bessel potential `J^z` of complex order on Schwartz
  space, with `SchwartzMap.fourier_besselPotentialCLM_apply`,
  `SchwartzMap.besselPotentialCLM_besselPotentialCLM_apply` and the comparison
  `SchwartzMap.toTemperedDistributionCLM_besselPotentialCLM_ofReal` with Mathlib's
  `TemperedDistribution.besselPotential` at real orders.
* `SchwartzMap.norm_toBesselPotentialSpaceCLM_besselPotentialCLM`:
  `‖J^z u‖_{H^r} = ‖u‖_{H^{r + re z}}`.
* `SchwartzMap.hasDerivAt_toBesselPotentialSpaceCLM_besselPotentialCLM`: `z ↦ J^z u` is holomorphic
  with values in `H^r`.
-/

public section

noncomputable section

open MeasureTheory FourierTransform Complex
open scoped ENNReal SchwartzMap BesselPotentialSpace

namespace SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section Normed

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The **Bessel potential of complex order** `z` on Schwartz functions: the Fourier multiplier
`J^z u = 𝓕⁻ (⟨ξ⟩ ^ z 𝓕 u)` whose symbol is the complex power `⟨ξ⟩ ^ z` of the Japanese bracket
`⟨ξ⟩ = (1 + ‖ξ‖ ^ 2) ^ (1 / 2)`. For real `z = s` it is the Bessel potential of order `s`
(`SchwartzMap.besselPotentialCLM_ofReal`), and the orders add under composition
(`SchwartzMap.besselPotentialCLM_besselPotentialCLM_apply`). -/
def besselPotentialCLM (z : ℂ) : 𝓢(E, F) →L[ℂ] 𝓢(E, F) :=
  fourierMultiplierCLM F (TauCeti.japaneseBracketCpow z)

theorem besselPotentialCLM_def (z : ℂ) :
    besselPotentialCLM (E := E) (F := F) z =
      fourierMultiplierCLM F (TauCeti.japaneseBracketCpow z) :=
  (rfl)

/-- At a real order `s` the Bessel potential is the Fourier multiplier with symbol
`(1 + ‖ξ‖ ^ 2) ^ (s / 2)`, the one defining the inclusion of Schwartz functions into `H^{s,p}`. -/
theorem besselPotentialCLM_ofReal (s : ℝ) :
    besselPotentialCLM (E := E) (F := F) (s : ℂ) =
      fourierMultiplierCLM F (fun ξ : E ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) := by
  rw [besselPotentialCLM]
  congr 1
  funext ξ
  exact TauCeti.japaneseBracketCpow_ofReal s ξ

variable [CompleteSpace F]

/-- The Fourier transform of `J^z u` is `⟨ξ⟩ ^ z 𝓕 u`. -/
@[simp]
theorem fourier_besselPotentialCLM_apply (z : ℂ) (u : 𝓢(E, F)) (ξ : E) :
    𝓕 (besselPotentialCLM z u) ξ = TauCeti.japaneseBracketCpow z ξ • 𝓕 u ξ := by
  rw [besselPotentialCLM, fourierMultiplierCLM_apply, fourier_fourierInv_eq,
    smulLeftCLM_apply_apply (TauCeti.hasTemperateGrowth_japaneseBracketCpow z)]

@[simp]
theorem besselPotentialCLM_zero :
    besselPotentialCLM (E := E) (F := F) 0 = ContinuousLinearMap.id ℂ _ := by
  have h : TauCeti.japaneseBracketCpow (0 : ℂ) = fun _ : E ↦ (1 : ℂ) :=
    funext TauCeti.japaneseBracketCpow_zero
  rw [besselPotentialCLM, h, fourierMultiplierCLM_const, one_smul]

/-- The orders of Bessel potentials add: `J^w (J^z u) = J^(z + w) u`. -/
@[simp]
theorem besselPotentialCLM_besselPotentialCLM_apply (z w : ℂ) (u : 𝓢(E, F)) :
    besselPotentialCLM w (besselPotentialCLM z u) = besselPotentialCLM (z + w) u := by
  simp only [besselPotentialCLM]
  rw [fourierMultiplierCLM_fourierMultiplierCLM_apply
    (TauCeti.hasTemperateGrowth_japaneseBracketCpow w)
    (TauCeti.hasTemperateGrowth_japaneseBracketCpow z)]
  congr 2
  funext ξ
  rw [Pi.mul_apply, TauCeti.japaneseBracketCpow_add, mul_comm]

/-- The orders of Bessel potentials add: `J^w ∘ J^z = J^(z + w)`. -/
theorem besselPotentialCLM_compL_besselPotentialCLM (z w : ℂ) :
    besselPotentialCLM (E := E) (F := F) w ∘L besselPotentialCLM z =
      besselPotentialCLM (z + w) := by
  ext1 u
  exact besselPotentialCLM_besselPotentialCLM_apply z w u

/-- At a real order `s`, the Bessel potential of a Schwartz function is Mathlib's Bessel potential
`TemperedDistribution.besselPotential E F s` of the corresponding tempered distribution. -/
theorem toTemperedDistributionCLM_besselPotentialCLM_ofReal (s : ℝ) (u : 𝓢(E, F)) :
    (besselPotentialCLM (s : ℂ) u : 𝓢'(E, F)) =
      TemperedDistribution.besselPotential E F s (u : 𝓢'(E, F)) := by
  rw [besselPotentialCLM_ofReal, TemperedDistribution.besselPotential,
    TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop)]

/-- The `Lᵖ` part of a Schwartz function in `H^{r,p}` is its Bessel potential of order `r`. -/
theorem toLp_toBesselPotentialSpaceCLM_eq_besselPotentialCLM (r : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : 𝓢(E, F)) :
    (toBesselPotentialSpaceCLM r p u).toLp = (besselPotentialCLM (r : ℂ) u).toLp p := by
  rw [toLp_toBesselPotentialSpaceCLM, besselPotentialCLM_ofReal]

end Normed

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The Bessel potentials shift the order of the `H^r` norms.** The `H^r` norm of `J^z u` is the
`H^{r + re z}` norm of `u`; in particular imaginary orders act isometrically on every `H^r`. -/
@[simp]
theorem norm_toBesselPotentialSpaceCLM_besselPotentialCLM (r : ℝ) (z : ℂ) (u : 𝓢(E, H)) :
    ‖toBesselPotentialSpaceCLM r 2 (besselPotentialCLM z u)‖ =
      ‖toBesselPotentialSpaceCLM (r + z.re) 2 u‖ := by
  rw [norm_toBesselPotentialSpaceCLM, norm_toBesselPotentialSpaceCLM]
  congr 1
  refine eLpNorm_congr_norm_ae (memLp_one_add_norm_sq_rpow_smul_fourier _ _ 2).aestronglyMeasurable
    (memLp_one_add_norm_sq_rpow_smul_fourier _ _ 2).aestronglyMeasurable (.of_forall fun ξ ↦ ?_)
  have h1 : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  simp only [fourier_besselPotentialCLM_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos h1 _), TauCeti.norm_japaneseBracketCpow]
  rw [← mul_assoc, ← Real.rpow_add h1]
  ring_nf

/-- **The Bessel potentials depend holomorphically on the order.** For a Schwartz function `u`
and every real `r`, the map `z ↦ J^z u` into `H^r` is complex differentiable, with derivative
`J^z (log ⟨D⟩ u)`, where `log ⟨D⟩` is the Fourier multiplier with symbol
`log ⟨ξ⟩ = log (1 + ‖ξ‖ ^ 2) / 2`. -/
theorem hasDerivAt_toBesselPotentialSpaceCLM_besselPotentialCLM (r : ℝ) (u : 𝓢(E, H)) (z : ℂ) :
    HasDerivAt (fun w ↦ toBesselPotentialSpaceCLM r 2 (besselPotentialCLM w u))
      (toBesselPotentialSpaceCLM r 2 (besselPotentialCLM z
        (fourierMultiplierCLM H (fun ξ : E ↦ ((Real.log (1 + ‖ξ‖ ^ 2) / 2 : ℝ) : ℂ)) u))) z := by
  set ℓ : E → ℂ := fun ξ ↦ ((Real.log (1 + ‖ξ‖ ^ 2) / 2 : ℝ) : ℂ) with hℓ_def
  have hℓ : ℓ.HasTemperateGrowth := by
    have : ℓ = fun ξ : E ↦ (((1 / 2 : ℝ) * Real.log (1 + ‖ξ‖ ^ 2) : ℝ) : ℂ) := by
      funext ξ
      simp only [hℓ_def]
      ring_nf
    rw [this]
    fun_prop
  set R := r + z.re + 3
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  refine (Asymptotics.IsBigO.of_bound ‖toBesselPotentialSpaceCLM R 2 u‖ ?_).trans_isLittleO
    (Asymptotics.isLittleO_pow_id one_lt_two)
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) zero_lt_one] with h hh
  rw [Metric.mem_closedBall, dist_zero_right] at hh
  rw [← map_smul, ← map_sub, ← map_sub, norm_toBesselPotentialSpaceCLM,
    norm_toBesselPotentialSpaceCLM, norm_pow, mul_comm]
  -- The Fourier transform of the remainder is the remainder of the symbol times `𝓕 u`.
  have hrem (ξ : E) : 𝓕 (besselPotentialCLM (z + h) u - besselPotentialCLM z u -
      h • besselPotentialCLM z (fourierMultiplierCLM H ℓ u)) ξ =
      (TauCeti.japaneseBracketCpow (z + h) ξ - TauCeti.japaneseBracketCpow z ξ -
        h * (TauCeti.japaneseBracketCpow z ξ * ℓ ξ)) • 𝓕 u ξ := by
    simp only [sub_eq_add_neg, FourierAdd.fourier_add, FourierTransform.fourier_neg,
      FourierSMul.fourier_smul, add_apply, neg_apply, smul_apply, fourier_besselPotentialCLM_apply]
    rw [fourierMultiplierCLM_apply, fourier_fourierInv_eq, smulLeftCLM_apply_apply hℓ]
    module
  set w := besselPotentialCLM (z + h) u - besselPotentialCLM z u -
    h • besselPotentialCLM z (fourierMultiplierCLM H ℓ u)
  have hbound : eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (r / 2) : ℝ) : ℂ) • 𝓕 w ξ) 2 volume ≤
      ENNReal.ofReal (‖h‖ ^ 2) *
        eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (R / 2) : ℝ) : ℂ) • 𝓕 u ξ) 2 volume := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      (memLp_one_add_norm_sq_rpow_smul_fourier r w 2).aestronglyMeasurable (.of_forall fun ξ ↦ ?_) 2
    have h1 : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
    simp only [hrem, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos h1 _)]
    have hr := TauCeti.norm_japaneseBracketCpow_add_sub_sub_le z hh ξ
    calc (1 + ‖ξ‖ ^ 2) ^ (r / 2) * (‖TauCeti.japaneseBracketCpow (z + h) ξ -
          TauCeti.japaneseBracketCpow z ξ - h * (TauCeti.japaneseBracketCpow z ξ * ℓ ξ)‖ *
            ‖𝓕 u ξ‖)
        ≤ (1 + ‖ξ‖ ^ 2) ^ (r / 2) * ((‖h‖ ^ 2 * (1 + ‖ξ‖ ^ 2) ^ ((z.re + 3) / 2)) *
            ‖𝓕 u ξ‖) := by gcongr
      _ = ‖h‖ ^ 2 * ((1 + ‖ξ‖ ^ 2) ^ (R / 2) * ‖𝓕 u ξ‖) := by
        rw [show R / 2 = r / 2 + (z.re + 3) / 2 by ring, Real.rpow_add h1]
        ring
  have hfin := (memLp_one_add_norm_sq_rpow_smul_fourier R u 2).eLpNorm_ne_top
  calc (eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (r / 2) : ℝ) : ℂ) • 𝓕 w ξ) 2 volume).toReal
      ≤ (ENNReal.ofReal (‖h‖ ^ 2) *
          eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (R / 2) : ℝ) : ℂ) • 𝓕 u ξ) 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hbound
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

end Hilbert

end SchwartzMap
