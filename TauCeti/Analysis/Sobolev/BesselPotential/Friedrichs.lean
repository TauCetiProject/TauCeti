/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.Distribution.SchwartzSpace.Convolution
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Distribution.TemperedDistribution.FourierMultiplier
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.Fourier.L2Multiplier
import TauCeti.Analysis.Sobolev.BesselPotential.Multiplication
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Friedrichs' commutator estimate on the Bessel-potential spaces `H^s(ℝⁿ)`

Let `E` be a finite-dimensional real inner product space and `F` a complex Hilbert space. A
*Friedrichs mollifier* is the family of Fourier multipliers

`J_ε u = 𝓕⁻ (θ(ε ·) 𝓕 u)`, `ε ∈ ℝ`,

for a scalar Schwartz function `θ`. When `θ = 𝓕 ρ` for a Schwartz function `ρ` of integral one
and `ε ≠ 0`, `J_ε` is convolution with the rescaled kernel `ρ_ε = |ε|⁻ⁿ ρ(· / ε)`, the
convolution regularizer of the theory of weak solutions; `J_0` is multiplication by the constant
`θ 0`. This file proves **Friedrichs' lemma** on the Bessel-potential
scale: for a scalar Schwartz function `φ`, the commutator `[M_φ, J_ε] = M_φ J_ε - J_ε M_φ` of
`J_ε` with multiplication by `φ` gains one derivative, uniformly in `ε`. For every real `s`
and `|ε| ≤ 1` it maps `H^s(E, F)` to `H^{s+1}(E, F)` with

`‖φ J_ε u - J_ε (φ u)‖_{H^{s+1}} ≤ C ‖u‖_{H^s}`,

where `C = 2 ^ (|s| / 2) √2 (p₀₁(θ) + p₁₁(θ)) ∫ ⟨ζ⟩ ^ (|s| + 2) ‖𝓕 φ ζ‖ dζ` does not depend on
`ε`; here `p_{k,1}(θ) = sup ‖x‖ ^ k ‖Dθ(x)‖` are Schwartz seminorms and
`⟨ζ⟩ = (1 + ‖ζ‖ ^ 2) ^ (1 / 2)` is the Japanese bracket
(`TemperedDistribution.exists_besselPotential_smulLeftCLM_fourierMultiplierCLM_sub_eq_and_norm_le`).
Each of `φ J_ε u` and `J_ε (φ u)` separately is bounded in `H^s` uniformly in `|ε| ≤ 1`, but not
uniformly in `H^{s+1}`; only the commutator gains the derivative uniformly. When `θ 0 = 1` the
mollifiers themselves are bounded on every `H^s` by `sup ‖θ‖`, uniformly in `ε`, and `J_ε u → u`
in `H^s` as `ε → 0`
(`TemperedDistribution.exists_besselPotential_fourierMultiplierCLM_eq_and_norm_le_and_tendsto`).

Since `J_ε` commutes with derivatives, the same holds for the commutator with a differential
operator `φ ∂^m` of order `k`, which maps `H^s` to `H^{s - k + 1}` uniformly in `ε`
(`exists_besselPotential_smulLeftCLM_iteratedLineDerivOp_fourierMultiplierCLM_sub_eq_and_norm_le`
in the namespace `TemperedDistribution`).
This uniform gain of one derivative is what lets mollification prove regularity of weak solutions
of elliptic equations: for an operator `P = ∑ φ_m ∂^m` of order two with Schwartz coefficients,
`P J_ε u - J_ε P u` stays bounded in `H^{s-1}` for `u ∈ H^s` as `ε → 0`.

## The Fourier argument

On the Fourier side `J_ε` multiplies by `θ(ε ξ)` and multiplication by `φ` is convolution with
`𝓕 φ`, so for a Schwartz function `u`

`𝓕 (φ J_ε u - J_ε (φ u)) ξ = ∫ 𝓕 φ (ξ - η) (θ(ε η) - θ(ε ξ)) 𝓕 u η dη`.

The difference of the symbols is small exactly where the convolution kernel is large:

`⟨ξ⟩ ‖θ(ε η) - θ(ε ξ)‖ ≤ √2 (p₀₁(θ) + p₁₁(θ)) ⟨ξ - η⟩ ^ 2` for `|ε| ≤ 1`

(`SchwartzMap.one_add_norm_sq_rpow_mul_norm_comp_smul_sub_le`). Indeed by the mean value theorem
the difference is at most `‖ξ - η‖` times `|ε| ‖Dθ(ε w)‖` at some `w` between `η` and `ξ`, and
`⟨w⟩ |ε| ‖Dθ(ε w)‖ ≤ p₀₁(θ) + p₁₁(θ)`, while Peetre's inequality gives
`⟨ξ⟩ ≤ √2 ⟨w⟩ ⟨ξ - w⟩ ≤ √2 ⟨w⟩ ⟨ξ - η⟩` (`TauCeti.one_add_norm_sq_rpow_le_of_mem_segment`). The
extra factor `⟨ξ⟩` is the gained derivative. With Peetre's inequality for `⟨ξ⟩ ^ s` this bounds
`⟨ξ⟩ ^ (s + 1)` times the integrand by a convolution of the integrable kernel
`⟨·⟩ ^ (|s| + 2) ‖𝓕 φ‖` with `⟨·⟩ ^ s ‖𝓕 u‖`, and Schur's test
(`SchwartzMap.eLpNorm_rpow_smul_fourier_le_of_eq_integral`) bounds its `L²` norm
(`SchwartzMap.eLpNorm_rpow_smul_fourier_smulLeftCLM_fourierMultiplierCLM_sub_le`). The estimate
passes from Schwartz functions to `H^s` by density, as for multiplication by `φ` in
`TauCeti.Analysis.Sobolev.BesselPotential.Multiplication`
(`TemperedDistribution.exists_besselPotential_apply_eq_and_norm_le_of_norm_toLp_le`).

## Main declarations

* `SchwartzMap.one_add_norm_sq_rpow_mul_norm_comp_smul_sub_le`: the symbol difference estimate.
* `SchwartzMap.eLpNorm_rpow_smul_fourier_smulLeftCLM_fourierMultiplierCLM_sub_le`,
  `SchwartzMap.norm_toLp_fourierMultiplierCLM_smulLeftCLM_fourierMultiplierCLM_sub_le`: Friedrichs'
  estimate for Schwartz functions.
* `TemperedDistribution.exists_besselPotential_smulLeftCLM_fourierMultiplierCLM_sub_eq_and_norm_le`:
  Friedrichs' estimate `H^s → H^{s+1}` on tempered distributions, and
  `TemperedDistribution.MemSobolev.smulLeftCLM_fourierMultiplierCLM_sub`: the commutator maps
  `H^s` into `H^{s+1}`.
* `exists_besselPotential_smulLeftCLM_iteratedLineDerivOp_fourierMultiplierCLM_sub_eq_and_norm_le`
  (in the namespace `TemperedDistribution`): the commutator with `φ ∂^m`.
* `TemperedDistribution.exists_besselPotential_fourierMultiplierCLM_eq_and_norm_le_and_tendsto`:
  the mollifiers are uniformly bounded on `H^s` and converge strongly to the identity.

## References

* K. O. Friedrichs, *The identity of weak and strong extensions of differential operators*,
  Trans. Amer. Math. Soc. 55 (1944), 132–151.
* G. B. Folland, *Introduction to Partial Differential Equations*, 2nd ed., Princeton University
  Press, 1995, Chapter 6 (Sobolev spaces on `ℝⁿ`, Friedrichs mollifiers and interior elliptic
  regularity).
-/

public section

noncomputable section

open MeasureTheory FourierTransform Filter Topology
open scoped ENNReal SchwartzMap BesselPotentialSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]

namespace SchwartzMap

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The derivative of `x ↦ θ(ε x)` at `w` has norm at most `|ε| ‖Dθ(ε w)‖`, and for `|ε| ≤ 1`
this decays like `⟨w⟩⁻¹`: `(1 + ‖w‖) |ε| ‖Dθ(ε w)‖ ≤ p₀₁(θ) + p₁₁(θ)`, uniformly in `ε`. -/
private theorem one_add_norm_mul_abs_mul_norm_fderiv_comp_smul_le (θ : 𝓢(E, ℂ)) {ε : ℝ}
    (hε : |ε| ≤ 1) (w : E) :
    (1 + ‖w‖) * (|ε| * ‖fderiv ℝ θ (ε • w)‖) ≤
      SchwartzMap.seminorm ℝ 0 1 θ + SchwartzMap.seminorm ℝ 1 1 θ := by
  have h0 := SchwartzMap.le_seminorm ℝ 0 1 θ (ε • w)
  have h1 := SchwartzMap.le_seminorm ℝ 1 1 θ (ε • w)
  rw [norm_iteratedFDeriv_one, pow_zero, one_mul] at h0
  rw [norm_iteratedFDeriv_one, pow_one, norm_smul, Real.norm_eq_abs] at h1
  calc (1 + ‖w‖) * (|ε| * ‖fderiv ℝ θ (ε • w)‖)
      = |ε| * ‖fderiv ℝ θ (ε • w)‖ + |ε| * ‖w‖ * ‖fderiv ℝ θ (ε • w)‖ := by ring
    _ ≤ 1 * ‖fderiv ℝ θ (ε • w)‖ + |ε| * ‖w‖ * ‖fderiv ℝ θ (ε • w)‖ := by gcongr
    _ ≤ _ := by linarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The symbol difference estimate behind Friedrichs' lemma.** For a scalar Schwartz function
`θ` and `|ε| ≤ 1`, the difference `θ(ε η) - θ(ε ξ)` is small compared with `⟨ξ⟩⁻¹` when `η` is
close to `ξ`:

`⟨ξ⟩ ‖θ(ε η) - θ(ε ξ)‖ ≤ √2 (p₀₁(θ) + p₁₁(θ)) ⟨ξ - η⟩ ^ 2`,

where `⟨ξ⟩ = (1 + ‖ξ‖ ^ 2) ^ (1 / 2)` and `p_{k,1}(θ) = sup ‖x‖ ^ k ‖Dθ(x)‖`. -/
theorem one_add_norm_sq_rpow_mul_norm_comp_smul_sub_le (θ : 𝓢(E, ℂ)) {ε : ℝ} (hε : |ε| ≤ 1)
    (ξ η : E) :
    (1 + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ) * ‖θ (ε • η) - θ (ε • ξ)‖ ≤
      √2 * (SchwartzMap.seminorm ℝ 0 1 θ + SchwartzMap.seminorm ℝ 1 1 θ) *
        (1 + ‖ξ - η‖ ^ 2) := by
  set D := SchwartzMap.seminorm ℝ 0 1 θ + SchwartzMap.seminorm ℝ 1 1 θ
  -- Write `⟨x⟩` for the Japanese bracket.
  set jb : E → ℝ := fun x ↦ (1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ)
  have hjb_pos (x : E) : 0 < jb x := by positivity
  -- The derivative of `x ↦ θ(ε x)` is `ε Dθ(ε x)`, and `(1 + ‖w‖) |ε| ‖Dθ(ε w)‖ ≤ D`.
  set f' : E → E →L[ℝ] ℂ := fun w ↦ (fderiv ℝ θ (ε • w)).comp (ε • ContinuousLinearMap.id ℝ E)
  have hf (w : E) : HasFDerivAt (fun x ↦ θ (ε • x)) (f' w) w :=
    (θ.differentiableAt.hasFDerivAt).comp w ((hasFDerivAt_id w).const_smul ε)
  have hf'_le (w : E) : (1 + ‖w‖) * ‖f' w‖ ≤ D := by
    refine le_trans ?_ (one_add_norm_mul_abs_mul_norm_fderiv_comp_smul_le θ hε w)
    gcongr
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [mul_comm, norm_smul, Real.norm_eq_abs]
    gcongr
    exact mul_le_of_le_one_right (abs_nonneg ε) ContinuousLinearMap.norm_id_le
  have hbound : ∀ w ∈ segment ℝ ξ η, ‖f' w‖ ≤ √2 * D * jb (ξ - η) / jb ξ := by
    intro w hw
    rw [le_div_iff₀ (hjb_pos ξ)]
    calc ‖f' w‖ * jb ξ ≤ ‖f' w‖ * (√2 * (1 + ‖w‖) * jb (ξ - η)) := by
          gcongr
          exact TauCeti.one_add_norm_sq_rpow_le_of_mem_segment hw
      _ = √2 * jb (ξ - η) * ((1 + ‖w‖) * ‖f' w‖) := by ring
      _ ≤ √2 * jb (ξ - η) * D := by gcongr; exact hf'_le w
      _ = √2 * D * jb (ξ - η) := by ring
  have hmv := (convex_segment ξ η).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun w _ ↦ (hf w).hasFDerivWithinAt) hbound (left_mem_segment ℝ ξ η)
    (right_mem_segment ℝ ξ η)
  calc jb ξ * ‖θ (ε • η) - θ (ε • ξ)‖
      ≤ jb ξ * (√2 * D * jb (ξ - η) / jb ξ * ‖η - ξ‖) := by gcongr
    _ = √2 * D * (jb (ξ - η) * ‖ξ - η‖) := by
        rw [norm_sub_rev η ξ]
        field_simp [(hjb_pos ξ).ne']
    _ ≤ √2 * D * (jb (ξ - η) * jb (ξ - η)) := by
        gcongr
        simp only [jb, ← Real.sqrt_eq_rpow]
        exact Real.le_sqrt_of_sq_le (by linarith)
    _ = √2 * D * (1 + ‖ξ - η‖ ^ 2) := by
        simp only [jb, ← Real.sqrt_eq_rpow]
        rw [Real.mul_self_sqrt (by positivity)]

section NormedSpace

variable [NormedSpace ℂ F]

private theorem integrable_fourier_sub_smul_fourier (φ : 𝓢(E, ℂ)) (f : 𝓢(E, F)) (ξ : E) :
    Integrable (fun y ↦ 𝓕 φ (ξ - y) • 𝓕 f y) :=
  ((𝓕 φ).integrable.comp_sub_left ξ).smul_of_top_left ((𝓕 f).memLp ⊤)

section CompleteSpace

variable [CompleteSpace F]

/-- The Fourier transform of the commutator `φ J_ε f - J_ε (φ f)` of the Friedrichs mollifier
`J_ε` with symbol `θ(ε ·)` and multiplication by `φ`. -/
private theorem fourier_smulLeftCLM_fourierMultiplierCLM_sub_apply (φ θ : 𝓢(E, ℂ)) (ε : ℝ)
    (f : 𝓢(E, F)) (ξ : E) :
    𝓕 (smulLeftCLM F (φ : E → ℂ) (fourierMultiplierCLM F (fun ζ ↦ θ (ε • ζ)) f) -
        fourierMultiplierCLM F (fun ζ ↦ θ (ε • ζ)) (smulLeftCLM F (φ : E → ℂ) f)) ξ =
      ∫ y, 𝓕 φ (ξ - y) • ((θ (ε • y) - θ (ε • ξ)) • 𝓕 f y) := by
  have hg : (fun ζ : E ↦ θ (ε • ζ)).HasTemperateGrowth := by fun_prop
  have hJ (v : 𝓢(E, F)) (x : E) :
      𝓕 (fourierMultiplierCLM F (fun ζ ↦ θ (ε • ζ)) v) x = θ (ε • x) • 𝓕 v x := by
    rw [fourierMultiplierCLM_apply, fourier_fourierInv_eq, smulLeftCLM_apply_apply hg]
  have h := integral_sub (integrable_fourier_sub_smul_fourier φ
    (fourierMultiplierCLM F (fun ζ ↦ θ (ε • ζ)) f) ξ)
    ((integrable_fourier_sub_smul_fourier φ f ξ).smul (θ (ε • ξ)))
  simp only [Pi.smul_apply, integral_smul] at h
  rw [fourier_sub, sub_apply, fourier_smulLeftCLM_apply_eq_integral_sub, hJ,
    fourier_smulLeftCLM_apply_eq_integral_sub, ← h]
  refine integral_congr_ae (.of_forall fun y ↦ ?_)
  simp only [hJ]
  module

end CompleteSpace

/-- **Friedrichs' estimate on the Fourier side**, for Schwartz functions. For `|ε| ≤ 1`,

`‖⟨ξ⟩ ^ (s + 1) 𝓕 (φ J_ε f - J_ε (φ f))‖_{L²} ≤ C ‖⟨ξ⟩ ^ s 𝓕 f‖_{L²}`

with `C = 2 ^ (|s| / 2) √2 (p₀₁(θ) + p₁₁(θ)) ∫ ⟨ζ⟩ ^ (|s| + 2) ‖𝓕 φ ζ‖ dζ`, where `J_ε` is the
Fourier multiplier with symbol `θ(ε ·)`. -/
theorem eLpNorm_rpow_smul_fourier_smulLeftCLM_fourierMultiplierCLM_sub_le (s : ℝ)
    (φ θ : 𝓢(E, ℂ)) {ε : ℝ} (hε : |ε| ≤ 1) (f : 𝓢(E, F)) :
    eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((s + 1) / 2) : ℝ) : ℂ) •
        𝓕 (smulLeftCLM F (φ : E → ℂ) (fourierMultiplierCLM F (fun ζ ↦ θ (ε • ζ)) f) -
          fourierMultiplierCLM F (fun ζ ↦ θ (ε • ζ)) (smulLeftCLM F (φ : E → ℂ) f)) ξ)
        2 volume ≤
      ENNReal.ofReal (2 ^ (|s| / 2) *
          (√2 * (SchwartzMap.seminorm ℝ 0 1 θ + SchwartzMap.seminorm ℝ 1 1 θ)) *
            ∫ ζ, (1 + ‖ζ‖ ^ 2) ^ ((|s| + 2) / 2) * ‖𝓕 φ ζ‖) *
        eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 f ξ) 2 volume := by
  by_cases hF : CompleteSpace F
  swap
  · simp [fourier_eq_zero_of_not_completeSpace hF]
  set K := √2 * (SchwartzMap.seminorm ℝ 0 1 θ + SchwartzMap.seminorm ℝ 1 1 θ)
  rw [← integral_const_mul]
  refine eLpNorm_rpow_smul_fourier_le_of_eq_integral
    (((𝓕 φ).integrable_one_add_norm_sq_rpow_mul_norm ((|s| + 2) / 2)).const_mul _) (by fun_prop)
    (fun ζ ↦ by positivity) (fourier_smulLeftCLM_fourierMultiplierCLM_sub_apply φ θ ε f)
    fun ξ y ↦ ?_
  -- Peetre's inequality for `⟨ξ⟩ ^ s` and the symbol difference estimate for `⟨ξ⟩`.
  have hP := TauCeti.one_add_norm_add_sq_rpow_le_mul s y (ξ - y)
  rw [add_sub_cancel] at hP
  have hθ := one_add_norm_sq_rpow_mul_norm_comp_smul_sub_le θ hε ξ y
  have hsplit : (1 + ‖ξ‖ ^ 2) ^ ((s + 1) / 2) =
      (1 + ‖ξ‖ ^ 2) ^ (s / 2) * (1 + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add (by positivity)]
    ring_nf
  have hsplit' : (1 + ‖ξ - y‖ ^ 2) ^ ((|s| + 2) / 2) =
      (1 + ‖ξ - y‖ ^ 2) ^ (|s| / 2) * (1 + ‖ξ - y‖ ^ 2) := by
    rw [← Real.rpow_add_one (by positivity)]
    ring_nf
  rw [norm_smul, norm_smul, hsplit, hsplit']
  calc (1 + ‖ξ‖ ^ 2) ^ (s / 2) * (1 + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ) *
        (‖𝓕 φ (ξ - y)‖ * (‖θ (ε • y) - θ (ε • ξ)‖ * ‖𝓕 f y‖))
      = (1 + ‖ξ‖ ^ 2) ^ (s / 2) *
          ((1 + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ) * ‖θ (ε • y) - θ (ε • ξ)‖) *
            (‖𝓕 φ (ξ - y)‖ * ‖𝓕 f y‖) := by ring
    _ ≤ (2 ^ (|s| / 2) * (1 + ‖y‖ ^ 2) ^ (s / 2) * (1 + ‖ξ - y‖ ^ 2) ^ (|s| / 2)) *
          (K * (1 + ‖ξ - y‖ ^ 2)) * (‖𝓕 φ (ξ - y)‖ * ‖𝓕 f y‖) := by
      gcongr
    _ = _ := by ring

end NormedSpace

end SchwartzMap

section InnerProductSpace

variable [InnerProductSpace ℂ F] [CompleteSpace F]

namespace SchwartzMap

/-- **Friedrichs' estimate** for Schwartz functions, with the Bessel-potential norms of Mathlib's
`H^s`: for `|ε| ≤ 1`,

`‖J^{s+1} (φ J_ε f - J_ε (φ f))‖_{L²} ≤ C ‖J^s f‖_{L²}`,

where `J^t` is the Fourier multiplier with symbol `⟨ξ⟩ ^ t`, `J_ε` the one with symbol `θ(ε ·)`,
and `C = 2 ^ (|s| / 2) √2 (p₀₁(θ) + p₁₁(θ)) ∫ ⟨ζ⟩ ^ (|s| + 2) ‖𝓕 φ ζ‖ dζ`. -/
theorem norm_toLp_fourierMultiplierCLM_smulLeftCLM_fourierMultiplierCLM_sub_le (s : ℝ)
    (φ θ : 𝓢(E, ℂ)) {ε : ℝ} (hε : |ε| ≤ 1) (f : 𝓢(E, F)) :
    ‖(fourierMultiplierCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ ((s + 1) / 2) : ℝ) : ℂ))
        (smulLeftCLM F (φ : E → ℂ) (fourierMultiplierCLM F (fun ζ ↦ θ (ε • ζ)) f) -
          fourierMultiplierCLM F (fun ζ ↦ θ (ε • ζ)) (smulLeftCLM F (φ : E → ℂ) f))).toLp 2‖ ≤
      (2 ^ (|s| / 2) * (√2 * (SchwartzMap.seminorm ℝ 0 1 θ + SchwartzMap.seminorm ℝ 1 1 θ)) *
          ∫ ζ, (1 + ‖ζ‖ ^ 2) ^ ((|s| + 2) / 2) * ‖𝓕 φ ζ‖) *
        ‖(fourierMultiplierCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) f).toLp 2‖ :=
  norm_toLp_fourierMultiplierCLM_le_of_eLpNorm_le (by positivity)
    (eLpNorm_rpow_smul_fourier_smulLeftCLM_fourierMultiplierCLM_sub_le s φ θ hε f)

end SchwartzMap

namespace TemperedDistribution

open scoped LineDeriv

/-- **Friedrichs' lemma on the Bessel-potential scale.** Let `J_ε` be the Fourier multiplier with
symbol `θ(ε ·)` for a scalar Schwartz function `θ`, and `φ` a scalar Schwartz function. If the
tempered distribution `u` lies in `H^s`, with `J^s u = v ∈ L²`, then for `|ε| ≤ 1` the commutator
`φ J_ε u - J_ε (φ u)` lies in `H^{s+1}`: `J^{s+1} (φ J_ε u - J_ε (φ u)) = v'` for some `v' ∈ L²`
with `‖v'‖ ≤ C ‖v‖`, where `C = 2 ^ (|s| / 2) √2 (p₀₁(θ) + p₁₁(θ)) ∫ ⟨ζ⟩ ^ (|s| + 2) ‖𝓕 φ ζ‖ dζ`
does not depend on `ε`. -/
theorem exists_besselPotential_smulLeftCLM_fourierMultiplierCLM_sub_eq_and_norm_le (s : ℝ)
    (φ θ : 𝓢(E, ℂ)) {ε : ℝ} (hε : |ε| ≤ 1) {u : 𝓢'(E, F)} {v : Lp F 2 (volume : Measure E)}
    (hv : besselPotential E F s u = v) :
    ∃ v' : Lp F 2 (volume : Measure E),
      besselPotential E F (s + 1)
          (smulLeftCLM F (φ : E → ℂ) (fourierMultiplierCLM F (fun ζ ↦ θ (ε • ζ)) u) -
            fourierMultiplierCLM F (fun ζ ↦ θ (ε • ζ)) (smulLeftCLM F (φ : E → ℂ) u)) = v' ∧
        ‖v'‖ ≤ (2 ^ (|s| / 2) *
            (√2 * (SchwartzMap.seminorm ℝ 0 1 θ + SchwartzMap.seminorm ℝ 1 1 θ)) *
              ∫ ζ, (1 + ‖ζ‖ ^ 2) ^ ((|s| + 2) / 2) * ‖𝓕 φ ζ‖) * ‖v‖ := by
  have hg : (fun ζ : E ↦ θ (ε • ζ)).HasTemperateGrowth := by fun_prop
  exact exists_besselPotential_apply_eq_and_norm_le_of_norm_toLp_le
    (smulLeftCLM F (φ : E → ℂ) ∘L fourierMultiplierCLM F (fun ζ ↦ θ (ε • ζ)) -
      fourierMultiplierCLM F (fun ζ ↦ θ (ε • ζ)) ∘L smulLeftCLM F (φ : E → ℂ))
    (SchwartzMap.smulLeftCLM F (φ : E → ℂ) ∘L
        SchwartzMap.fourierMultiplierCLM F (fun ζ ↦ θ (ε • ζ)) -
      SchwartzMap.fourierMultiplierCLM F (fun ζ ↦ θ (ε • ζ)) ∘L
        SchwartzMap.smulLeftCLM F (φ : E → ℂ))
    (fun f ↦ by
      simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply, map_sub,
        smulLeftCLM_toTemperedDistributionCLM_eq,
        fourierMultiplierCLM_toTemperedDistributionCLM_eq hg])
    (SchwartzMap.norm_toLp_fourierMultiplierCLM_smulLeftCLM_fourierMultiplierCLM_sub_le s φ θ hε)
    hv

/-- **Friedrichs' lemma**, membership form: for every real `s` and every `ε`, the commutator
`φ J_ε u - J_ε (φ u)` of the Friedrichs mollifier `J_ε` with symbol `θ(ε ·)` and multiplication by
a Schwartz function `φ` maps `H^s` into `H^{s+1}`. Only the bound of
`TemperedDistribution.exists_besselPotential_smulLeftCLM_fourierMultiplierCLM_sub_eq_and_norm_le`
needs `|ε| ≤ 1`: for `ε ≠ 0` the symbol `θ(ε ·)` is itself a Schwartz function. -/
theorem MemSobolev.smulLeftCLM_fourierMultiplierCLM_sub {s : ℝ} {u : 𝓢'(E, F)}
    (hu : MemSobolev s 2 u) (φ θ : 𝓢(E, ℂ)) (ε : ℝ) :
    MemSobolev (s + 1) 2
      (smulLeftCLM F (φ : E → ℂ) (fourierMultiplierCLM F (fun ζ ↦ θ (ε • ζ)) u) -
        fourierMultiplierCLM F (fun ζ ↦ θ (ε • ζ)) (smulLeftCLM F (φ : E → ℂ) u)) := by
  obtain ⟨v, hv⟩ := hu
  rcases eq_or_ne ε 0 with rfl | hε
  · obtain ⟨v', hv', -⟩ :=
      exists_besselPotential_smulLeftCLM_fourierMultiplierCLM_sub_eq_and_norm_le s φ θ (ε := 0)
        (by simp) hv
    exact ⟨v', hv'⟩
  · -- Rescale: `θ(ε ·)` is the symbol `θ'(1 ·)` of the Schwartz function `θ' = θ(ε ·)`.
    set θ' : 𝓢(E, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (LinearEquiv.smulOfNeZero ℝ E ε hε).toContinuousLinearEquiv θ
    have hθ' : (fun ζ : E ↦ θ' ((1 : ℝ) • ζ)) = fun ζ ↦ θ (ε • ζ) := by
      ext ζ
      simp [θ']
    obtain ⟨v', hv', -⟩ :=
      exists_besselPotential_smulLeftCLM_fourierMultiplierCLM_sub_eq_and_norm_le s φ θ' (ε := 1)
        (by simp) hv
    rw [hθ'] at hv'
    exact ⟨v', hv'⟩

/-- **Friedrichs' lemma for differential operators.** The commutator of the Friedrichs mollifier
`J_ε` with symbol `θ(ε ·)` and the operator `φ ∂^m` of order `k`, where `φ` is a scalar Schwartz
function and `∂^m` the iterated directional derivative along `m : Fin k → E`, maps `H^s` to
`H^{s - k + 1}` uniformly in `|ε| ≤ 1`: if `J^{s-k} (∂^m u) = v ∈ L²`, which holds for every
`u ∈ H^s`, then `J^{s-k+1} (φ ∂^m (J_ε u) - J_ε (φ ∂^m u)) = v'` with `‖v'‖ ≤ C ‖v‖`, and `C` is
the constant of
`TemperedDistribution.exists_besselPotential_smulLeftCLM_fourierMultiplierCLM_sub_eq_and_norm_le`
at the order `s - k`. -/
theorem
    exists_besselPotential_smulLeftCLM_iteratedLineDerivOp_fourierMultiplierCLM_sub_eq_and_norm_le
    (s : ℝ) (φ θ : 𝓢(E, ℂ)) {ε : ℝ} (hε : |ε| ≤ 1) {k : ℕ} (m : Fin k → E) {u : 𝓢'(E, F)}
    {v : Lp F 2 (volume : Measure E)} (hv : besselPotential E F (s - k) (∂^{m} u) = v) :
    ∃ v' : Lp F 2 (volume : Measure E),
      besselPotential E F (s - k + 1)
          (smulLeftCLM F (φ : E → ℂ) (∂^{m} (fourierMultiplierCLM F (fun ζ ↦ θ (ε • ζ)) u)) -
            fourierMultiplierCLM F (fun ζ ↦ θ (ε • ζ)) (smulLeftCLM F (φ : E → ℂ) (∂^{m} u))) =
          v' ∧
        ‖v'‖ ≤ (2 ^ (|s - k| / 2) *
            (√2 * (SchwartzMap.seminorm ℝ 0 1 θ + SchwartzMap.seminorm ℝ 1 1 θ)) *
              ∫ ζ, (1 + ‖ζ‖ ^ 2) ^ ((|s - k| + 2) / 2) * ‖𝓕 φ ζ‖) * ‖v‖ := by
  rw [iteratedLineDerivOp_fourierMultiplierCLM (by fun_prop)]
  exact exists_besselPotential_smulLeftCLM_fourierMultiplierCLM_sub_eq_and_norm_le (s - k) φ θ hε
    hv

/-- **The Friedrichs mollifier is uniformly bounded on `H^s` and tends to the identity.** Let
`J_ε` be the Fourier multiplier with symbol `θ(ε ·)` for a scalar Schwartz function `θ` with
`θ 0 = 1`. If the tempered distribution `u` lies in `H^s`, with `J^s u = v ∈ L²`, then
`J^s (J_ε u) = w ε` for elements `w ε ∈ L²` with `‖w ε‖ ≤ sup ‖θ‖ ‖v‖`, and `w ε → v` in `L²` as
`ε → 0`; that is, `J_ε u → u` in `H^s`. -/
theorem exists_besselPotential_fourierMultiplierCLM_eq_and_norm_le_and_tendsto (s : ℝ) (θ : 𝓢(E, ℂ))
    (hθ : θ 0 = 1) {u : 𝓢'(E, F)} {v : Lp F 2 (volume : Measure E)}
    (hv : besselPotential E F s u = v) :
    ∃ w : ℝ → Lp F 2 (volume : Measure E),
      (∀ ε, besselPotential E F s (fourierMultiplierCLM F (fun ζ ↦ θ (ε • ζ)) u) = w ε ∧
        ‖w ε‖ ≤ SchwartzMap.seminorm ℝ 0 0 θ * ‖v‖) ∧ Tendsto w (𝓝 0) (𝓝 v) := by
  have hg (ε : ℝ) : (fun ζ : E ↦ θ (ε • ζ)).HasTemperateGrowth := by fun_prop
  have hb (ε : ℝ) (ζ : E) : ‖θ (ε • ζ)‖ ≤ SchwartzMap.seminorm ℝ 0 0 θ :=
    SchwartzMap.norm_le_seminorm ℝ θ _
  have hm (ε : ℝ) : MemLp (fun ζ : E ↦ θ (ε • ζ)) ∞ volume :=
    memLp_top_of_bound (hg ε).1.continuous.aestronglyMeasurable _ (.of_forall (hb ε))
  refine ⟨fun ε ↦ Lp.fourierMultiplierCLM F ((hm ε).toLp _) v, fun ε ↦ ⟨?_, ?_⟩, ?_⟩
  · rw [besselPotential_fourierMultiplierCLM (hg ε), hv,
      Lp.fourierMultiplierCLM_toTemperedDistribution_eq (hg := hg ε) (hg' := hm ε)]
  · exact (Lp.fourierMultiplierCLM F _).le_of_opNorm_le
      (Lp.norm_fourierMultiplierCLM_toLp_le (hm ε) (by positivity) (.of_forall (hb ε))) v
  · -- Along every sequence `εₙ → 0`, dominated convergence on the Fourier side applies, since
    -- `θ(εₙ ζ) → θ 0 = 1` for every `ζ` and `‖θ(εₙ ζ)‖ ≤ sup ‖θ‖`.
    have h1 : MemLp (fun _ : E ↦ (1 : ℂ)) ∞ volume := memLp_top_const 1
    have hid : Lp.fourierMultiplierCLM F (h1.toLp _) v = v := by
      rw [Lp.fourierMultiplierCLM_of_ae_eq_const h1.coeFn_toLp]
      simp
    rw [show 𝓝 v = 𝓝 (Lp.fourierMultiplierCLM F (h1.toLp _) v) by rw [hid]]
    refine tendsto_iff_seq_tendsto.2 fun e he ↦ ?_
    refine Lp.tendsto_fourierMultiplierCLM_apply (l := atTop) (m := fun n ↦ (hm (e n)).toLp _)
      (C := SchwartzMap.seminorm ℝ 0 0 θ)
      (.of_forall fun n ↦ Lp.norm_le_of_ae_bound_top (by positivity) ?_) ?_ v
    · filter_upwards [(hm (e n)).coeFn_toLp] with ζ hζ
      rw [hζ]
      exact hb (e n) ζ
    · filter_upwards [ae_all_iff.2 fun n ↦ (hm (e n)).coeFn_toLp, h1.coeFn_toLp] with ζ hζ hζ1
      simp only [hζ, hζ1]
      rw [← hθ, ← zero_smul ℝ ζ]
      exact (θ.continuous.tendsto _).comp (he.smul_const ζ)

end TemperedDistribution

end InnerProductSpace
