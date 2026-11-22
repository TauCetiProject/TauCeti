/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre
import TauCeti.MeasureTheory.Function.L2Space.Basic
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Equivalent Fourier weights for the Sobolev norms `H^s`

Mathlib's Bessel-potential space `H^s = H^{s,2}(E, F)`, for a complex Hilbert space `F`, is normed
through the Fourier transform with the weight `⟨ξ⟩ ^ s = (1 + ‖ξ‖ ^ 2) ^ (s / 2)` in the Fourier
variable `ξ` of Mathlib's normalization `e^{-2πi⟪x, ξ⟫}`. Pseudodifferential operators and
differential operators are written in the *angular* frequency `2π ξ`, in which `-i ∂_j` has symbol
the `j`-th coordinate, and the Sobolev scale is often normed there with the bracket
`⟨2π ξ⟩ ^ s` or with the inhomogeneous weight `(1 + ‖2π ξ‖) ^ s`. This file shows that each of
these weights defines an equivalent norm on all of `H^s`, for every real `s`, with explicit
constants.

The weighted norms are integrals of the Fourier transform of `u ∈ H^s`, which is a function but in
general not an `L²` function. It is `BesselPotentialSpace.fourierFun u`, the function
`ξ ↦ ⟨ξ⟩ ^ (-s) 𝓕 (J^s u) ξ`, where `J^s u` is the `L²` part `u.toLp` of `u`. For a Schwartz
function it is its Fourier transform, almost everywhere
(`SchwartzMap.fourierFun_toBesselPotentialSpaceCLM`); it does not depend on the order `s` at which
`u` is regarded (`BesselPotentialSpace.fourierFun_inclusion`), and `⟨ξ⟩ ^ s` times it is the `L²`
function `𝓕 (J^s u)`, which represents `⟨ξ⟩ ^ s 𝓕 u`
(`BesselPotentialSpace.one_add_norm_sq_rpow_smul_fourierFun`). By Plancherel

`‖u‖² = ∫ (1 + ‖ξ‖ ^ 2) ^ s ‖𝓕 u ξ‖² dξ`

(`BesselPotentialSpace.norm_sq_eq_integral_one_add_norm_sq_rpow_mul_norm_fourierFun_sq`). Hence a
weight `W` with `c ⟨ξ⟩ ^ (2s) ≤ W ξ ≤ C ⟨ξ⟩ ^ (2s)` gives
`c ‖u‖² ≤ ∫ W ξ ‖𝓕 u ξ‖² dξ ≤ C ‖u‖²`
(`BesselPotentialSpace.mul_norm_sq_le_integral_mul_norm_fourierFun_sq`,
`BesselPotentialSpace.integral_mul_norm_fourierFun_sq_le`). The pointwise comparisons are

* `⟨2π ξ⟩ ^ s ≤ (2π) ^ |s| ⟨ξ⟩ ^ s` and `⟨ξ⟩ ^ s ≤ (2π) ^ |s| ⟨2π ξ⟩ ^ s`, by rescaling;
* `min 1 (2 ^ s) ⟨η⟩ ^ (2s) ≤ (1 + ‖η‖) ^ (2s) ≤ max 1 (2 ^ s) ⟨η⟩ ^ (2s)`, from
  `1 + ‖η‖ ^ 2 ≤ (1 + ‖η‖) ^ 2 ≤ 2 (1 + ‖η‖ ^ 2)`
  (`TauCeti.one_add_norm_rpow_le_max_mul_one_add_norm_sq_rpow`,
  `TauCeti.min_mul_one_add_norm_sq_rpow_le_one_add_norm_rpow`).

The weight `(1 + ‖η‖) ^ s` is not smooth at `η = 0`, so it is not a Fourier multiplier on
tempered distributions; it is only used through these integrals. Since the norms are equivalent on
Schwartz functions (`SchwartzMap.integral_one_add_norm_two_pi_smul_rpow_mul_norm_fourier_sq_le`,
`SchwartzMap.mul_norm_sq_le_integral_one_add_norm_two_pi_smul_rpow_mul_norm_fourier_sq`), which
are dense in `H^s`, the completion of the Schwartz functions for any of these weighted norms is
`H^s`, with an equivalent norm.

## Main declarations

* `BesselPotentialSpace.fourierFun`: the Fourier transform of `u ∈ H^s` as a function, with
  `BesselPotentialSpace.one_add_norm_sq_rpow_smul_fourierFun` relating it to `J^s u`; it is
  linear almost everywhere (`BesselPotentialSpace.fourierFun_add`,
  `BesselPotentialSpace.fourierFun_smul`).
* `BesselPotentialSpace.norm_sq_eq_integral_one_add_norm_sq_rpow_mul_norm_fourierFun_sq`:
  Plancherel's formula for the `H^s` norm.
* `BesselPotentialSpace.mul_norm_sq_le_integral_mul_norm_fourierFun_sq`,
  `BesselPotentialSpace.integral_mul_norm_fourierFun_sq_le`: a weight comparable to `⟨ξ⟩ ^ (2s)`
  defines an equivalent norm on `H^s`.
* `BesselPotentialSpace.integral_one_add_norm_two_pi_smul_sq_rpow_mul_norm_fourierFun_sq_le`
  and its lower bound
  `inv_mul_norm_sq_le_integral_one_add_norm_two_pi_smul_sq_rpow_mul_norm_fourierFun_sq`
  in the same namespace: the bracket in the angular frequency.
* `BesselPotentialSpace.integral_one_add_norm_two_pi_smul_rpow_mul_norm_fourierFun_sq_le`
  and its lower bound
  `mul_norm_sq_le_integral_one_add_norm_two_pi_smul_rpow_mul_norm_fourierFun_sq`
  in the same namespace: the inhomogeneous weight `(1 + ‖2π ξ‖) ^ (2s)` in the angular
  frequency.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley, 1999,
  §9.3 (the Sobolev spaces `H_s` defined by the weight `(1 + 4π² |ξ|²) ^ (s / 2)`).
* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §1 (the
  Sobolev spaces `H^s(ℝⁿ)` defined by the weight `⟨ξ⟩ ^ s` in the angular frequency).
-/

public section

noncomputable section

open MeasureTheory FourierTransform TemperedDistribution Real
open scoped ENNReal SchwartzMap BesselPotentialSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] {s : ℝ}

namespace BesselPotentialSpace

/-- The Fourier transform of `u ∈ H^s` as a function, `ξ ↦ ⟨ξ⟩ ^ (-s) 𝓕 (J^s u) ξ`, where `J^s u`
is the `L²` part `u.toLp` of `u` and `⟨ξ⟩ = (1 + ‖ξ‖ ^ 2) ^ (1 / 2)`. It is defined up to a null
set; `⟨ξ⟩ ^ s` times it is the `L²` function `𝓕 (J^s u)`, which represents the tempered
distribution `⟨ξ⟩ ^ s 𝓕 u` (`BesselPotentialSpace.toTemperedDistribution_fourier_toLp`), and for a
Schwartz function it is the Fourier transform. -/
def fourierFun (u : H^{s}(E, F)) (ξ : E) : F :=
  (((1 + ‖ξ‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ) • 𝓕 u.toLp ξ

/-- The defining formula `𝓕 u ξ = ⟨ξ⟩ ^ (-s) 𝓕 (J^s u) ξ` of the Fourier transform of `u ∈ H^s`. -/
theorem fourierFun_apply (u : H^{s}(E, F)) (ξ : E) :
    u.fourierFun ξ = (((1 + ‖ξ‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ) • 𝓕 u.toLp ξ := (rfl)

/-- `⟨ξ⟩ ^ s` times the Fourier transform of `u ∈ H^s` is the `L²` Fourier transform of its `L²`
part `J^s u`. -/
theorem one_add_norm_sq_rpow_smul_fourierFun (u : H^{s}(E, F)) (ξ : E) :
    (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • u.fourierFun ξ = 𝓕 u.toLp ξ := by
  rw [fourierFun_apply, smul_smul, ← Complex.ofReal_mul, mul_comm,
    TauCeti.one_add_norm_sq_rpow_neg_mul_rpow, Complex.ofReal_one, one_smul]

/-- The norm of the Fourier transform of `u ∈ H^s` is `⟨ξ⟩ ^ (-s) ‖𝓕 (J^s u) ξ‖`. -/
theorem norm_fourierFun (u : H^{s}(E, F)) (ξ : E) :
    ‖u.fourierFun ξ‖ = (1 + ‖ξ‖ ^ 2) ^ (-s / 2) * ‖𝓕 u.toLp ξ‖ := by
  rw [fourierFun_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

/-- The Fourier transform of `u ∈ H^s` is almost everywhere strongly measurable. -/
theorem aestronglyMeasurable_fourierFun (u : H^{s}(E, F)) :
    AEStronglyMeasurable u.fourierFun volume := by
  have hw : (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  exact hw.1.continuous.aestronglyMeasurable.smul (Lp.aestronglyMeasurable _)

/-- The Fourier transform on `H^s` is additive, almost everywhere. -/
theorem fourierFun_add (u v : H^{s}(E, F)) :
    (u + v).fourierFun =ᵐ[volume] u.fourierFun + v.fourierFun := by
  filter_upwards [Lp.coeFn_add (𝓕 u.toLp) (𝓕 v.toLp)] with ξ hξ
  rw [Pi.add_apply, fourierFun_apply, fourierFun_apply, fourierFun_apply, toLp_add,
    FourierTransform.fourier_add, hξ, Pi.add_apply, smul_add]

/-- The Fourier transform on `H^s` is homogeneous, almost everywhere. -/
theorem fourierFun_smul (a : ℂ) (u : H^{s}(E, F)) :
    (a • u).fourierFun =ᵐ[volume] a • u.fourierFun := by
  filter_upwards [Lp.coeFn_smul a (𝓕 u.toLp)] with ξ hξ
  rw [Pi.smul_apply, fourierFun_apply, fourierFun_apply, toLp_smul,
    FourierTransform.fourier_smul, hξ, Pi.smul_apply, smul_comm]

/-- The Fourier transform of an element of `H^s` does not depend on the order at which it is
regarded: its image in `H^r`, `r ≤ s`, has the same Fourier transform. -/
theorem fourierFun_inclusion {r : ℝ} (h : r ≤ s) (u : H^{s}(E, F)) :
    (inclusion h u).fourierFun =ᵐ[volume] u.fourierFun := by
  filter_upwards [coeFn_fourier_toLp_inclusion h u] with ξ hξ
  rw [fourierFun_apply, hξ, smul_smul, ← Complex.ofReal_mul, ← TauCeti.one_add_norm_sq_rpow_add,
    fourierFun_apply]
  congr 4
  ring

/-- The pointwise form of Plancherel's formula: `‖𝓕 (J^s u) ξ‖² = ⟨ξ⟩ ^ (2s) ‖𝓕 u ξ‖²`. -/
private theorem norm_fourier_toLp_sq (u : H^{s}(E, F)) (ξ : E) :
    ‖𝓕 u.toLp ξ‖ ^ 2 = (1 + ‖ξ‖ ^ 2) ^ s * ‖u.fourierFun ξ‖ ^ 2 := by
  rw [← one_add_norm_sq_rpow_smul_fourierFun u ξ, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul
    (by positivity)]
  norm_num

/-- **Plancherel's formula for the `H^s` norm.** For `u ∈ H^s`,
`‖u‖² = ∫ (1 + ‖ξ‖ ^ 2) ^ s ‖𝓕 u ξ‖² dξ`, with `𝓕 u` the function
`BesselPotentialSpace.fourierFun u`. -/
theorem norm_sq_eq_integral_one_add_norm_sq_rpow_mul_norm_fourierFun_sq (u : H^{s}(E, F)) :
    ‖u‖ ^ 2 = ∫ ξ, (1 + ‖ξ‖ ^ 2) ^ s * ‖u.fourierFun ξ‖ ^ 2 := by
  rw [← norm_fourier_toLp_eq, ← Lp.integral_norm_sq_eq_norm_sq]
  exact integral_congr_ae (.of_forall (norm_fourier_toLp_sq u))

/-- The Plancherel integrand `(1 + ‖ξ‖ ^ 2) ^ s ‖𝓕 u ξ‖²` of `u ∈ H^s` is integrable. -/
theorem integrable_one_add_norm_sq_rpow_mul_norm_fourierFun_sq (u : H^{s}(E, F)) :
    Integrable fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ s * ‖u.fourierFun ξ‖ ^ 2 :=
  (Lp.integrable_sq_norm (𝓕 u.toLp)).congr (.of_forall (norm_fourier_toLp_sq u))

section Weight

variable {W : E → ℝ} {c C : ℝ}

/-- The weighted integrand `W ξ ‖𝓕 u ξ‖²` of `u ∈ H^s` is integrable for every measurable weight
`W` lying between two multiples of `⟨ξ⟩ ^ (2s) = (1 + ‖ξ‖ ^ 2) ^ s`. -/
theorem integrable_mul_norm_fourierFun_sq (u : H^{s}(E, F)) (hW : AEStronglyMeasurable W volume)
    (hc : ∀ ξ, c * (1 + ‖ξ‖ ^ 2) ^ s ≤ W ξ) (hC : ∀ ξ, W ξ ≤ C * (1 + ‖ξ‖ ^ 2) ^ s) :
    Integrable fun ξ ↦ W ξ * ‖u.fourierFun ξ‖ ^ 2 := by
  refine ((integrable_one_add_norm_sq_rpow_mul_norm_fourierFun_sq u).const_mul (max |c| |C|)).mono'
    (hW.mul ((aestronglyMeasurable_fourierFun u).norm.pow 2)) (.of_forall fun ξ ↦ ?_)
  have hξ : 0 ≤ (1 + ‖ξ‖ ^ 2) ^ s := by positivity
  have hW' : |W ξ| ≤ max |c| |C| * (1 + ‖ξ‖ ^ 2) ^ s := abs_le.2
    ⟨by nlinarith [hc ξ, neg_abs_le c, le_max_left |c| |C|],
      by nlinarith [hC ξ, le_abs_self C, le_max_right |c| |C|]⟩
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖u.fourierFun ξ‖), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hW' (by positivity)

/-- **Lower bound for a weighted Fourier norm.** If the weight satisfies
`c ⟨ξ⟩ ^ (2s) ≤ W ξ ≤ C ⟨ξ⟩ ^ (2s)`, then `c ‖u‖² ≤ ∫ W ξ ‖𝓕 u ξ‖² dξ` for every `u ∈ H^s`. -/
theorem mul_norm_sq_le_integral_mul_norm_fourierFun_sq (u : H^{s}(E, F))
    (hW : AEStronglyMeasurable W volume) (hc : ∀ ξ, c * (1 + ‖ξ‖ ^ 2) ^ s ≤ W ξ)
    (hC : ∀ ξ, W ξ ≤ C * (1 + ‖ξ‖ ^ 2) ^ s) :
    c * ‖u‖ ^ 2 ≤ ∫ ξ, W ξ * ‖u.fourierFun ξ‖ ^ 2 := by
  rw [norm_sq_eq_integral_one_add_norm_sq_rpow_mul_norm_fourierFun_sq, ← integral_const_mul]
  refine integral_mono ((integrable_one_add_norm_sq_rpow_mul_norm_fourierFun_sq u).const_mul c)
    (integrable_mul_norm_fourierFun_sq u hW hc hC) fun ξ ↦ ?_
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hc ξ) (by positivity)

/-- **Upper bound for a weighted Fourier norm.** If the weight satisfies
`c ⟨ξ⟩ ^ (2s) ≤ W ξ ≤ C ⟨ξ⟩ ^ (2s)`, then `∫ W ξ ‖𝓕 u ξ‖² dξ ≤ C ‖u‖²` for every `u ∈ H^s`. -/
theorem integral_mul_norm_fourierFun_sq_le (u : H^{s}(E, F)) (hW : AEStronglyMeasurable W volume)
    (hc : ∀ ξ, c * (1 + ‖ξ‖ ^ 2) ^ s ≤ W ξ) (hC : ∀ ξ, W ξ ≤ C * (1 + ‖ξ‖ ^ 2) ^ s) :
    ∫ ξ, W ξ * ‖u.fourierFun ξ‖ ^ 2 ≤ C * ‖u‖ ^ 2 := by
  rw [norm_sq_eq_integral_one_add_norm_sq_rpow_mul_norm_fourierFun_sq, ← integral_const_mul]
  refine integral_mono (integrable_mul_norm_fourierFun_sq u hW hc hC)
    ((integrable_one_add_norm_sq_rpow_mul_norm_fourierFun_sq u).const_mul C) fun ξ ↦ ?_
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hC ξ) (by positivity)

end Weight

/-! ### Weights in the angular frequency -/

private theorem measurable_one_add_norm_two_pi_smul_sq_rpow (s : ℝ) :
    AEStronglyMeasurable (fun ξ : E ↦ (1 + ‖(2 * π) • ξ‖ ^ 2) ^ s) volume :=
  ((by fun_prop : Continuous fun ξ : E ↦ 1 + ‖(2 * π) • ξ‖ ^ 2).rpow_const
    fun _ ↦ Or.inl (by positivity)).aestronglyMeasurable

private theorem measurable_one_add_norm_two_pi_smul_rpow (s : ℝ) :
    AEStronglyMeasurable (fun ξ : E ↦ (1 + ‖(2 * π) • ξ‖) ^ (2 * s)) volume :=
  ((by fun_prop : Continuous fun ξ : E ↦ 1 + ‖(2 * π) • ξ‖).rpow_const
    fun _ ↦ Or.inl (by positivity)).aestronglyMeasurable

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The bracket in the angular frequency is comparable to the bracket:
`⟨2π ξ⟩ ^ (2s) ≤ (2π) ^ (2|s|) ⟨ξ⟩ ^ (2s)` and `⟨ξ⟩ ^ (2s) ≤ (2π) ^ (2|s|) ⟨2π ξ⟩ ^ (2s)`. -/
private theorem one_add_norm_two_pi_smul_sq_rpow_bounds (ξ : E) :
    (1 + ‖(2 * π) • ξ‖ ^ 2) ^ s ≤ (2 * π) ^ (2 * |s|) * (1 + ‖ξ‖ ^ 2) ^ s ∧
      (1 + ‖ξ‖ ^ 2) ^ s ≤ (2 * π) ^ (2 * |s|) * (1 + ‖(2 * π) • ξ‖ ^ 2) ^ s := by
  have hπ : 1 ≤ 2 * π := by linarith [Real.two_le_pi]
  have h2s : 2 * s / 2 = s := by ring
  have habs : |2 * s| = 2 * |s| := by rw [abs_mul, abs_two]
  have h₁ := TauCeti.one_add_norm_smul_sq_rpow_le hπ (2 * s) ξ
  have h₂ := TauCeti.one_add_norm_sq_rpow_le_of_norm_le_mul hπ (2 * s) (x := ξ)
    (y := (2 * π) • ξ) (by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      exact (le_mul_of_one_le_left (norm_nonneg ξ) hπ).trans
        (le_mul_of_one_le_left (by positivity) hπ))
    (by rw [norm_smul, Real.norm_of_nonneg (by positivity)])
  rw [h2s, habs] at h₁ h₂
  exact ⟨h₁, h₂⟩

/-- **The bracket in the angular frequency, upper bound.** For `u ∈ H^s`,
`∫ (1 + ‖2π ξ‖ ^ 2) ^ s ‖𝓕 u ξ‖² dξ ≤ (2π) ^ (2|s|) ‖u‖²`. -/
theorem integral_one_add_norm_two_pi_smul_sq_rpow_mul_norm_fourierFun_sq_le (u : H^{s}(E, F)) :
    ∫ ξ, (1 + ‖(2 * π) • ξ‖ ^ 2) ^ s * ‖u.fourierFun ξ‖ ^ 2 ≤
      (2 * π) ^ (2 * |s|) * ‖u‖ ^ 2 := by
  have hpos : 0 < (2 * π) ^ (2 * |s|) := by positivity
  refine integral_mul_norm_fourierFun_sq_le (c := ((2 * π) ^ (2 * |s|))⁻¹) u
    (measurable_one_add_norm_two_pi_smul_sq_rpow s) (fun ξ ↦ ?_)
    fun ξ ↦ (one_add_norm_two_pi_smul_sq_rpow_bounds ξ).1
  rw [inv_mul_le_iff₀ hpos]
  exact (one_add_norm_two_pi_smul_sq_rpow_bounds ξ).2

/-- **The bracket in the angular frequency, lower bound.** For `u ∈ H^s`,
`(2π) ^ (-2|s|) ‖u‖² ≤ ∫ (1 + ‖2π ξ‖ ^ 2) ^ s ‖𝓕 u ξ‖² dξ`. -/
theorem inv_mul_norm_sq_le_integral_one_add_norm_two_pi_smul_sq_rpow_mul_norm_fourierFun_sq
    (u : H^{s}(E, F)) :
    ((2 * π) ^ (2 * |s|))⁻¹ * ‖u‖ ^ 2 ≤
      ∫ ξ, (1 + ‖(2 * π) • ξ‖ ^ 2) ^ s * ‖u.fourierFun ξ‖ ^ 2 := by
  have hpos : 0 < (2 * π) ^ (2 * |s|) := by positivity
  refine mul_norm_sq_le_integral_mul_norm_fourierFun_sq u
    (measurable_one_add_norm_two_pi_smul_sq_rpow s) (fun ξ ↦ ?_)
    fun ξ ↦ (one_add_norm_two_pi_smul_sq_rpow_bounds ξ).1
  rw [inv_mul_le_iff₀ hpos]
  exact (one_add_norm_two_pi_smul_sq_rpow_bounds ξ).2

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The inhomogeneous weight in the angular frequency is comparable to the bracket:
`min 1 (2 ^ s) (2π) ^ (-2|s|) ⟨ξ⟩ ^ (2s) ≤ (1 + ‖2π ξ‖) ^ (2s) ≤
max 1 (2 ^ s) (2π) ^ (2|s|) ⟨ξ⟩ ^ (2s)`. -/
private theorem one_add_norm_two_pi_smul_rpow_bounds (ξ : E) :
    min 1 (2 ^ s) * ((2 * π) ^ (2 * |s|))⁻¹ * (1 + ‖ξ‖ ^ 2) ^ s ≤
        (1 + ‖(2 * π) • ξ‖) ^ (2 * s) ∧
      (1 + ‖(2 * π) • ξ‖) ^ (2 * s) ≤
        max 1 (2 ^ s) * (2 * π) ^ (2 * |s|) * (1 + ‖ξ‖ ^ 2) ^ s := by
  obtain ⟨h₁, h₂⟩ := one_add_norm_two_pi_smul_sq_rpow_bounds (s := s) ξ
  have hlo := TauCeti.min_mul_one_add_norm_sq_rpow_le_one_add_norm_rpow ((2 * π) • ξ) (2 * s)
  have hhi := TauCeti.one_add_norm_rpow_le_max_mul_one_add_norm_sq_rpow ((2 * π) • ξ) (2 * s)
  have h2s : 2 * s / 2 = s := by ring
  rw [h2s] at hlo hhi
  have hpos : 0 < (2 * π) ^ (2 * |s|) := by positivity
  refine ⟨le_trans ?_ hlo, hhi.trans ?_⟩
  · rw [mul_assoc]
    gcongr
    rw [inv_mul_le_iff₀ hpos]
    exact h₂
  · rw [mul_assoc]
    gcongr

/-- **The inhomogeneous weight in the angular frequency, upper bound.** For `u ∈ H^s`,
`∫ (1 + ‖2π ξ‖) ^ (2s) ‖𝓕 u ξ‖² dξ ≤ max 1 (2 ^ s) (2π) ^ (2|s|) ‖u‖²`. -/
theorem integral_one_add_norm_two_pi_smul_rpow_mul_norm_fourierFun_sq_le (u : H^{s}(E, F)) :
    ∫ ξ, (1 + ‖(2 * π) • ξ‖) ^ (2 * s) * ‖u.fourierFun ξ‖ ^ 2 ≤
      max 1 (2 ^ s) * (2 * π) ^ (2 * |s|) * ‖u‖ ^ 2 :=
  integral_mul_norm_fourierFun_sq_le u (measurable_one_add_norm_two_pi_smul_rpow s)
    (fun ξ ↦ (one_add_norm_two_pi_smul_rpow_bounds ξ).1)
    fun ξ ↦ (one_add_norm_two_pi_smul_rpow_bounds ξ).2

/-- **The inhomogeneous weight in the angular frequency, lower bound.** For `u ∈ H^s`,
`min 1 (2 ^ s) (2π) ^ (-2|s|) ‖u‖² ≤ ∫ (1 + ‖2π ξ‖) ^ (2s) ‖𝓕 u ξ‖² dξ`. -/
theorem mul_norm_sq_le_integral_one_add_norm_two_pi_smul_rpow_mul_norm_fourierFun_sq
    (u : H^{s}(E, F)) :
    min 1 (2 ^ s) * ((2 * π) ^ (2 * |s|))⁻¹ * ‖u‖ ^ 2 ≤
      ∫ ξ, (1 + ‖(2 * π) • ξ‖) ^ (2 * s) * ‖u.fourierFun ξ‖ ^ 2 :=
  mul_norm_sq_le_integral_mul_norm_fourierFun_sq u (measurable_one_add_norm_two_pi_smul_rpow s)
    (fun ξ ↦ (one_add_norm_two_pi_smul_rpow_bounds ξ).1)
    fun ξ ↦ (one_add_norm_two_pi_smul_rpow_bounds ξ).2

end BesselPotentialSpace

namespace SchwartzMap

open BesselPotentialSpace

/-- For a Schwartz function `u`, the Fourier transform of `u` regarded in `H^s` is its Fourier
transform `𝓕 u`, almost everywhere. -/
theorem fourierFun_toBesselPotentialSpaceCLM (u : 𝓢(E, F)) :
    (toBesselPotentialSpaceCLM s 2 u).fourierFun =ᵐ[volume] ⇑(𝓕 u : 𝓢(E, F)) := by
  have hw : (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  filter_upwards [(smulLeftCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ))
    (𝓕 u)).coeFn_toLp 2 volume] with ξ hξ
  rw [fourierFun_apply, fourier_toLp_toBesselPotentialSpaceCLM, hξ,
    smulLeftCLM_apply_apply hw, smul_smul, ← Complex.ofReal_mul,
    TauCeti.one_add_norm_sq_rpow_neg_mul_rpow, Complex.ofReal_one, one_smul]

/-- **The inhomogeneous angular weight on Schwartz functions, upper bound.**
`∫ (1 + ‖2π ξ‖) ^ (2s) ‖𝓕 u ξ‖² dξ ≤ max 1 (2 ^ s) (2π) ^ (2|s|) ‖u‖²_{H^s}`. -/
theorem integral_one_add_norm_two_pi_smul_rpow_mul_norm_fourier_sq_le (u : 𝓢(E, F)) :
    ∫ ξ, (1 + ‖(2 * π) • ξ‖) ^ (2 * s) * ‖𝓕 u ξ‖ ^ 2 ≤
      max 1 (2 ^ s) * (2 * π) ^ (2 * |s|) * ‖toBesselPotentialSpaceCLM s 2 u‖ ^ 2 := by
  refine le_of_eq_of_le (integral_congr_ae ?_)
    (integral_one_add_norm_two_pi_smul_rpow_mul_norm_fourierFun_sq_le _)
  filter_upwards [fourierFun_toBesselPotentialSpaceCLM (s := s) u] with ξ hξ
  rw [hξ]

/-- **The inhomogeneous angular weight on Schwartz functions, lower bound.**
`min 1 (2 ^ s) (2π) ^ (-2|s|) ‖u‖²_{H^s} ≤ ∫ (1 + ‖2π ξ‖) ^ (2s) ‖𝓕 u ξ‖² dξ`. -/
theorem mul_norm_sq_le_integral_one_add_norm_two_pi_smul_rpow_mul_norm_fourier_sq
    (u : 𝓢(E, F)) :
    min 1 (2 ^ s) * ((2 * π) ^ (2 * |s|))⁻¹ * ‖toBesselPotentialSpaceCLM s 2 u‖ ^ 2 ≤
      ∫ ξ, (1 + ‖(2 * π) • ξ‖) ^ (2 * s) * ‖𝓕 u ξ‖ ^ 2 := by
  refine (mul_norm_sq_le_integral_one_add_norm_two_pi_smul_rpow_mul_norm_fourierFun_sq _).trans_eq
    (integral_congr_ae ?_)
  filter_upwards [fourierFun_toBesselPotentialSpaceCLM (s := s) u] with ξ hξ
  rw [hξ]

end SchwartzMap
