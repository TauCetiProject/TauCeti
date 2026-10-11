/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Fourier multipliers on `L²`

Let `E` be a finite-dimensional real inner product space and `F` a complex Hilbert space. For an
essentially bounded symbol `m ∈ L^∞(E)`, the **Fourier multiplier** with symbol `m` is the
operator

`T_m f = 𝓕⁻ (m • 𝓕 f)`

on `L²(E, F)`, where `𝓕 = MeasureTheory.Lp.fourierTransformₗᵢ` is the Fourier transform on `L²`.
By Plancherel's theorem it is bounded, with `‖T_m‖ ≤ ‖m‖_∞`.

Mathlib defines Fourier multipliers on Schwartz functions and on tempered distributions
(`SchwartzMap.fourierMultiplierCLM`, `TemperedDistribution.fourierMultiplierCLM`), but they are
meaningful only for symbols of temperate growth, which are in particular smooth. The symbols
of the classical singular integral operators are bounded but not smooth at the origin: the
Riesz transforms have symbols `-i ξⱼ / ‖ξ‖`, and `∂ⱼ∂ₖ Δ⁻¹` has symbol `ξⱼ ξₖ / ‖ξ‖²`. The `L²`
multiplier accepts any essentially bounded symbol, and it is the `L²`-bounded operator that the
Calderón–Zygmund theory and the Mihlin–Hörmander multiplier theorem start from. Where both are
defined, it agrees with Mathlib's multipliers.

## Main declarations

* `MeasureTheory.Lp.fourierMultiplierCLM`: the Fourier multiplier on `L²` with symbol in `L^∞`.
* `MeasureTheory.Lp.fourier_fourierMultiplierCLM`: `𝓕 (T_m f) = m • 𝓕 f`, and
  `MeasureTheory.Lp.eq_fourierMultiplierCLM_iff`, which characterizes `T_m` by it.
* `MeasureTheory.Lp.norm_fourierMultiplierCLM_le`: the bound `‖T_m‖ ≤ ‖m‖_∞`.
* `MeasureTheory.Lp.fourierMultiplierCLM_compL_fourierMultiplierCLM`: `T_{m₁} ∘ T_{m₂} =
  T_{m₁ m₂}`, with linearity in the symbol and `T_c = c • id` for a constant symbol.
* `MeasureTheory.Lp.adjoint_fourierMultiplierCLM`: the adjoint of `T_m` is `T_{star m}`.
* `SchwartzMap.toLp_fourierMultiplierCLM_eq` and
  `MeasureTheory.Lp.fourierMultiplierCLM_toTemperedDistribution_eq`: for a bounded symbol of
  temperate growth, `T_m` agrees with Mathlib's multipliers on Schwartz functions and, as a
  tempered distribution, on every `f ∈ L²`.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Section 2.5.
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter IV, §3.
-/

public section

noncomputable section

open scoped ENNReal FourierTransform ComplexInnerProductSpace SchwartzMap InnerProduct
open FourierTransform ContinuousLinearMap

namespace MeasureTheory.Lp

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

variable (F) in
/-- The **Fourier multiplier** on `L²(E, F)` with symbol `m ∈ L^∞(E)`: the bounded operator
`f ↦ 𝓕⁻ (m • 𝓕 f)`, where `𝓕` is the Fourier transform on `L²`. -/
def fourierMultiplierCLM (m : Lp ℂ ∞ (volume : Measure E)) :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  fourierInvCLM ℂ (Lp F 2 (volume : Measure E)) ∘L
    (lsmul ℂ ℂ : ℂ →L[ℂ] F →L[ℂ] F).holderL volume ∞ 2 2 m ∘L
      fourierCLM ℂ (Lp F 2 (volume : Measure E))

variable (m m₁ m₂ : Lp ℂ ∞ (volume : Measure E)) (f : Lp F 2 (volume : Measure E))

theorem fourierMultiplierCLM_apply :
    fourierMultiplierCLM F m f = 𝓕⁻ (m • 𝓕 f : Lp F 2 (volume : Measure E)) := by
  rw [fourierMultiplierCLM, comp_apply, comp_apply, fourierCLM_apply, fourierInvCLM_apply]
  refine congrArg 𝓕⁻ (Lp.ext ?_)
  filter_upwards [(lsmul ℂ ℂ : ℂ →L[ℂ] F →L[ℂ] F).coeFn_holder (r := 2) m (𝓕 f),
    coeFn_lpSMul (r := 2) m (𝓕 f)] with x h₁ h₂
  simp [h₁, h₂]

/-- On the Fourier side, the multiplier with symbol `m` is multiplication by `m`. -/
@[simp]
theorem fourier_fourierMultiplierCLM :
    𝓕 (fourierMultiplierCLM F m f) = (m • 𝓕 f : Lp F 2 (volume : Measure E)) := by
  rw [fourierMultiplierCLM_apply, fourier_fourierInv_eq]

variable {m} in
/-- A bounded operator on `L²` is the multiplier with symbol `m` if and only if it acts as
multiplication by `m` on the Fourier side. -/
theorem eq_fourierMultiplierCLM_iff
    {T : Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E)} :
    T = fourierMultiplierCLM F m ↔ ∀ f, 𝓕 (T f) = (m • 𝓕 f : Lp F 2 (volume : Measure E)) := by
  refine ⟨fun h f ↦ h ▸ fourier_fourierMultiplierCLM m f, fun h ↦ ?_⟩
  ext1 f
  exact (fourierTransformₗᵢ E F).injective ((h f).trans (fourier_fourierMultiplierCLM m f).symm)

/-- The multiplier with symbol `m` changes the `L²` norm by at most the factor `‖m‖_∞`. -/
theorem norm_fourierMultiplierCLM_apply_le : ‖fourierMultiplierCLM F m f‖ ≤ ‖m‖ * ‖f‖ := by
  rw [← norm_fourier_eq, fourier_fourierMultiplierCLM, ← norm_fourier_eq f]
  exact Lp.norm_smul_le m (𝓕 f)

/-- **Plancherel bound** for Fourier multipliers: `‖T_m‖ ≤ ‖m‖_∞`. -/
theorem norm_fourierMultiplierCLM_le : ‖fourierMultiplierCLM (E := E) F m‖ ≤ ‖m‖ :=
  opNorm_le_bound _ (norm_nonneg m) (norm_fourierMultiplierCLM_apply_le m)

/-! ### Dependence on the symbol -/

@[simp]
theorem fourierMultiplierCLM_zero :
    fourierMultiplierCLM F (0 : Lp ℂ ∞ (volume : Measure E)) = 0 := by
  ext1 f
  simp [fourierMultiplierCLM_apply]

theorem fourierMultiplierCLM_add :
    fourierMultiplierCLM F (m₁ + m₂) = fourierMultiplierCLM F m₁ + fourierMultiplierCLM F m₂ := by
  ext1 f
  simp [fourierMultiplierCLM_apply, Lp.smul_add]

theorem fourierMultiplierCLM_smul (c : ℂ) :
    fourierMultiplierCLM F (c • m) = c • fourierMultiplierCLM F m := by
  ext1 f
  simp [fourierMultiplierCLM_apply, Lp.smul_assoc]

variable {m} in
/-- A multiplier whose symbol is almost everywhere the constant `c` is multiplication by `c`. -/
theorem fourierMultiplierCLM_of_ae_eq_const {c : ℂ} (hm : m =ᵐ[volume] fun _ ↦ c) :
    fourierMultiplierCLM F m = c • ContinuousLinearMap.id ℂ (Lp F 2 (volume : Measure E)) := by
  ext1 f
  have : (m • 𝓕 f : Lp F 2 (volume : Measure E)) = c • 𝓕 f := by
    apply Lp.ext
    filter_upwards [coeFn_lpSMul (r := 2) m (𝓕 f), Lp.coeFn_smul c (𝓕 f), hm] with x h₁ h₂ h₃
    simp [h₁, h₂, h₃]
  simp [fourierMultiplierCLM_apply, this]

/-- The composition of two multipliers is the multiplier with the product symbol. -/
theorem fourierMultiplierCLM_compL_fourierMultiplierCLM :
    fourierMultiplierCLM F m₁ ∘L fourierMultiplierCLM F m₂ =
      fourierMultiplierCLM F (m₁ • m₂ : Lp ℂ ∞ (volume : Measure E)) := by
  refine eq_fourierMultiplierCLM_iff.2 fun f ↦ Lp.ext ?_
  simp only [comp_apply, fourier_fourierMultiplierCLM]
  filter_upwards [coeFn_lpSMul (r := 2) m₁ (m₂ • 𝓕 f : Lp F 2 (volume : Measure E)),
    coeFn_lpSMul (r := 2) m₂ (𝓕 f),
    coeFn_lpSMul (r := 2) (m₁ • m₂ : Lp ℂ ∞ (volume : Measure E)) (𝓕 f),
    coeFn_lpSMul (r := ∞) m₁ m₂] with x h₁ h₂ h₃ h₄
  simp [h₁, h₂, h₃, h₄, smul_smul]

theorem fourierMultiplierCLM_fourierMultiplierCLM_apply :
    fourierMultiplierCLM F m₁ (fourierMultiplierCLM F m₂ f) =
      fourierMultiplierCLM F (m₁ • m₂ : Lp ℂ ∞ (volume : Measure E)) f := by
  rw [← fourierMultiplierCLM_compL_fourierMultiplierCLM, comp_apply]

/-- The adjoint of the multiplier with symbol `m` is the multiplier with the complex conjugate
symbol `star m`. In particular a real symbol gives a self-adjoint multiplier. -/
theorem adjoint_fourierMultiplierCLM :
    (fourierMultiplierCLM (E := E) F m)† = fourierMultiplierCLM F (star m) := by
  refine ((eq_adjoint_iff _ _).2 fun f g ↦ ?_).symm
  rw [← inner_fourier_eq, fourier_fourierMultiplierCLM, ← inner_fourier_eq f,
    fourier_fourierMultiplierCLM, L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_lpSMul (r := 2) (star m) (𝓕 f), coeFn_lpSMul (r := 2) m (𝓕 g),
    Lp.coeFn_star m] with x h₁ h₂ h₃
  simp [h₁, h₂, h₃, inner_smul_left, inner_smul_right]

/-! ### Comparison with multipliers on Schwartz functions and tempered distributions -/

variable {g : E → ℂ}

/-- On Schwartz functions, the `L²` multiplier with a bounded symbol `g` of temperate growth is
the Schwartz-space multiplier `SchwartzMap.fourierMultiplierCLM F g`. -/
theorem _root_.SchwartzMap.toLp_fourierMultiplierCLM_eq (hg : g.HasTemperateGrowth)
    (hg' : MemLp g ∞) (f : 𝓢(E, F)) :
    fourierMultiplierCLM F (hg'.toLp g) (f.toLp 2) =
      (SchwartzMap.fourierMultiplierCLM F g f).toLp 2 := by
  have : (hg'.toLp g • 𝓕 (f.toLp 2) : Lp F 2 (volume : Measure E)) =
      (SchwartzMap.smulLeftCLM F g (𝓕 f)).toLp 2 := by
    apply Lp.ext
    filter_upwards [coeFn_lpSMul (r := 2) (hg'.toLp g) (𝓕 (f.toLp 2)), hg'.coeFn_toLp,
      (𝓕 f).coeFn_toLp 2, (SchwartzMap.smulLeftCLM F g (𝓕 f)).coeFn_toLp 2] with x h₁ h₂ h₃ h₄
    rw [SchwartzMap.toLp_fourier_eq] at h₁
    simp [h₁, h₂, h₃, h₄, SchwartzMap.smulLeftCLM_apply_apply hg]
  rw [fourierMultiplierCLM_apply, this, SchwartzMap.toLp_fourierInv_eq,
    SchwartzMap.fourierMultiplierCLM_apply]

/-- For a bounded symbol `g` of temperate growth, the `L²` multiplier agrees with the multiplier
`TemperedDistribution.fourierMultiplierCLM F g` on tempered distributions: for every `f ∈ L²`,
both send `f` to the same tempered distribution. -/
theorem fourierMultiplierCLM_toTemperedDistribution_eq (hg : g.HasTemperateGrowth)
    (hg' : MemLp g ∞) :
    TemperedDistribution.fourierMultiplierCLM F g (f : 𝓢'(E, F)) =
      (fourierMultiplierCLM F (hg'.toLp g) f : 𝓢'(E, F)) := by
  refine DenseRange.induction_on
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f ?_ fun f ↦ ?_
  · exact isClosed_eq
      (TemperedDistribution.fourierMultiplierCLM F g ∘L toTemperedDistributionCLM F volume 2).cont
      (toTemperedDistributionCLM F volume 2 ∘L fourierMultiplierCLM F (hg'.toLp g)).cont
  · simp [SchwartzMap.toLp_fourierMultiplierCLM_eq hg hg',
      TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq hg]

end MeasureTheory.Lp
