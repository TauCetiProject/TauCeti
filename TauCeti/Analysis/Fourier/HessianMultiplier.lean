/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
public import TauCeti.Analysis.Fourier.L2Multiplier

/-!
# Second derivatives as a Fourier multiplier of the Laplacian

On the Fourier side, `∂_v ∂_w` is multiplication by `-(2π)² ⟪ξ, v⟫ ⟪ξ, w⟫` and the Laplacian `Δ` is
multiplication by `-(2π)² ‖ξ‖²`. The operator `∂_v ∂_w Δ⁻¹` is therefore the Fourier multiplier
with symbol

`m_{v,w}(ξ) = ⟪ξ, v⟫ ⟪ξ, w⟫ / ‖ξ‖²` (`TauCeti.hessianSymbol`),

which is bounded by `‖v‖ ‖w‖` but, for nonzero `v` and `w`, not continuous at the origin. It lies
in `L^∞` (`TauCeti.hessianSymbolLp`), so the `L²` multiplier
`MeasureTheory.Lp.fourierMultiplierCLM` defines `T_{m_{v,w}}` as a bounded operator on `L²(E, F)`,
and for every Schwartz function `u`

`∂_v ∂_w u = T_{m_{v,w}} (Δ u)` in `L²`
(`SchwartzMap.toLp_lineDerivOp_lineDerivOp_eq_fourierMultiplierCLM`).

In particular `‖∂_v ∂_w u‖_{L²} ≤ ‖v‖ ‖w‖ ‖Δ u‖_{L²}`.

This realizes `D² Δ⁻¹` as an `L²`-bounded operator, which is the starting point of the
Calderón–Zygmund theory: combined with the standard bounds on its kernel, the Hessian of the
Newtonian kernel, that theory upgrades the `L²` bound to `‖∂_v ∂_w u‖_{Lᵖ} ≤ C ‖Δ u‖_{Lᵖ}` for
`1 < p < ∞`.

## Main declarations

* `TauCeti.hessianSymbol`: the symbol `ξ ↦ ⟪ξ, v⟫ ⟪ξ, w⟫ / ‖ξ‖²` of `∂_v ∂_w Δ⁻¹`, with the bound
  `TauCeti.norm_hessianSymbol_le`.
* `TauCeti.hessianSymbolLp`: the same symbol as an element of `L^∞`.
* `SchwartzMap.fourier_lineDerivOp_lineDerivOp_apply_eq_hessianSymbol_smul`: pointwise on the
  Fourier side, `𝓕 (∂_v ∂_w u) = m_{v,w} • 𝓕 (Δ u)`.
* `SchwartzMap.toLp_lineDerivOp_lineDerivOp_eq_fourierMultiplierCLM`:
  `∂_v ∂_w u = T_{m_{v,w}} (Δ u)` in `L²`.
* `SchwartzMap.norm_toLp_lineDerivOp_lineDerivOp_le`: `‖∂_v ∂_w u‖_{L²} ≤ ‖v‖ ‖w‖ ‖Δ u‖_{L²}`.

## References

* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter III,
  §1.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 9.4.
-/

public section

noncomputable section

open scoped ENNReal FourierTransform SchwartzMap RealInnerProductSpace Real Laplacian LineDeriv
open FourierTransform MeasureTheory

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The symbol `ξ ↦ ⟪ξ, v⟫ ⟪ξ, w⟫ / ‖ξ‖²` of the operator `∂_v ∂_w Δ⁻¹`. At the origin it takes
the value `0`. -/
def hessianSymbol (v w : E) (ξ : E) : ℂ :=
  ((⟪ξ, v⟫ * ⟪ξ, w⟫ / ‖ξ‖ ^ 2 : ℝ) : ℂ)

theorem hessianSymbol_apply (v w ξ : E) :
    hessianSymbol v w ξ = ((⟪ξ, v⟫ * ⟪ξ, w⟫ / ‖ξ‖ ^ 2 : ℝ) : ℂ) := (rfl)

/-- Multiplying the symbol of `∂_v ∂_w Δ⁻¹` by the symbol `‖ξ‖²` of `-(2π)⁻² Δ` gives the symbol
`⟪ξ, v⟫ ⟪ξ, w⟫` of `-(2π)⁻² ∂_v ∂_w`, at every point including the origin. -/
theorem hessianSymbol_mul_norm_sq (v w ξ : E) :
    hessianSymbol v w ξ * ((‖ξ‖ ^ 2 : ℝ) : ℂ) = ((⟪ξ, v⟫ * ⟪ξ, w⟫ : ℝ) : ℂ) := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [hessianSymbol]
  · rw [hessianSymbol, ← Complex.ofReal_mul, div_mul_cancel₀ _ (by positivity)]

/-- The symbol of `∂_v ∂_w Δ⁻¹` is bounded by `‖v‖ ‖w‖`, by the Cauchy–Schwarz inequality. -/
theorem norm_hessianSymbol_le (v w ξ : E) : ‖hessianSymbol v w ξ‖ ≤ ‖v‖ * ‖w‖ := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simpa [hessianSymbol] using by positivity
  rw [hessianSymbol, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖ξ‖ ^ 2), div_le_iff₀ (by positivity)]
  calc |⟪ξ, v⟫| * |⟪ξ, w⟫| ≤ (‖ξ‖ * ‖v‖) * (‖ξ‖ * ‖w‖) := by
        gcongr <;> exact abs_real_inner_le_norm _ _
    _ = ‖v‖ * ‖w‖ * ‖ξ‖ ^ 2 := by ring

variable [MeasurableSpace E]

@[fun_prop]
theorem measurable_hessianSymbol [OpensMeasurableSpace E] (v w : E) :
    Measurable (hessianSymbol v w) := by
  unfold hessianSymbol
  fun_prop

/-- The symbol of `∂_v ∂_w Δ⁻¹` is essentially bounded for every measure. -/
theorem memLp_hessianSymbol [OpensMeasurableSpace E] (v w : E) (μ : Measure E) :
    MemLp (hessianSymbol v w) ∞ μ :=
  memLp_top_of_bound (measurable_hessianSymbol v w).aestronglyMeasurable _
    (.of_forall (norm_hessianSymbol_le v w))

variable [BorelSpace E] [FiniteDimensional ℝ E]

/-- The symbol `ξ ↦ ⟪ξ, v⟫ ⟪ξ, w⟫ / ‖ξ‖²` of `∂_v ∂_w Δ⁻¹`, as an element of `L^∞`. -/
def hessianSymbolLp (v w : E) : Lp ℂ ∞ (volume : Measure E) :=
  (memLp_hessianSymbol v w volume).toLp _

theorem coeFn_hessianSymbolLp (v w : E) : hessianSymbolLp v w =ᵐ[volume] hessianSymbol v w :=
  (memLp_hessianSymbol v w volume).coeFn_toLp

/-- The Hessian symbol is real, hence fixed by complex conjugation. -/
@[simp]
theorem star_hessianSymbolLp (v w : E) : star (hessianSymbolLp v w) = hessianSymbolLp v w := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (hessianSymbolLp v w), coeFn_hessianSymbolLp v w]
    with ξ hstar hξ
  rw [hstar]
  calc
    star ((hessianSymbolLp v w : E → ℂ) ξ) = star (hessianSymbol v w ξ) := congrArg star hξ
    _ = hessianSymbol v w ξ := by simp [hessianSymbol]
    _ = (hessianSymbolLp v w : E → ℂ) ξ := hξ.symm

/-- The `L^∞` norm of the symbol of `∂_v ∂_w Δ⁻¹` is at most `‖v‖ ‖w‖`. -/
theorem norm_hessianSymbolLp_le (v w : E) : ‖hessianSymbolLp v w‖ ≤ ‖v‖ * ‖w‖ := by
  rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable _)]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (eLpNormEssSup_le_of_ae_bound ?_)
  filter_upwards [coeFn_hessianSymbolLp v w] with ξ hξ
  rw [hξ]
  exact norm_hessianSymbol_le v w ξ

end TauCeti

namespace SchwartzMap

open TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]

/-- On the Fourier side, the second directional derivative `∂_v ∂_w u` of a Schwartz function is
the symbol `⟪ξ, v⟫ ⟪ξ, w⟫ / ‖ξ‖²` times the Fourier transform of `Δ u`. -/
theorem fourier_lineDerivOp_lineDerivOp_apply_eq_hessianSymbol_smul [NormedSpace ℂ F]
    (u : 𝓢(E, F)) (v w ξ : E) :
    𝓕 (∂_{v} (∂_{w} u)) ξ = hessianSymbol v w ξ • 𝓕 (Δ u) ξ := by
  rw [fourier_lineDerivOp_lineDerivOp_apply, fourier_laplacian_apply,
    RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  congr 1
  have := hessianSymbol_mul_norm_sq v w ξ
  push_cast at this ⊢
  linear_combination ((2 * π) ^ 2 : ℂ) * this

variable [InnerProductSpace ℂ F] [CompleteSpace F]

/-- In `L²`, the second directional derivative `∂_v ∂_w u` of a Schwartz function is the Fourier
multiplier with symbol `⟪ξ, v⟫ ⟪ξ, w⟫ / ‖ξ‖²` applied to `Δ u`: on Schwartz functions,
`∂_v ∂_w = T_{m_{v,w}} ∘ Δ`. -/
theorem toLp_lineDerivOp_lineDerivOp_eq_fourierMultiplierCLM (u : 𝓢(E, F)) (v w : E) :
    (∂_{v} (∂_{w} u)).toLp 2 =
      Lp.fourierMultiplierCLM F (hessianSymbolLp v w) ((Δ u).toLp 2) := by
  refine (fourierInv_fourier_eq (F := Lp F 2 (volume : Measure E)) _).symm.trans ?_
  rw [Lp.fourierMultiplierCLM_apply, toLp_fourier_eq, toLp_fourier_eq]
  congr 1
  apply Lp.ext
  filter_upwards [coeFn_toLp (𝓕 (∂_{v} (∂_{w} u))) 2,
    Lp.coeFn_lpSMul (r := 2) (hessianSymbolLp v w) ((𝓕 (Δ u)).toLp 2),
    coeFn_hessianSymbolLp v w, coeFn_toLp (𝓕 (Δ u)) 2] with ξ h₁ h₂ h₃ h₄
  rw [h₁, h₂, Pi.smul_apply', h₃, h₄, fourier_lineDerivOp_lineDerivOp_apply_eq_hessianSymbol_smul]

/-- The Laplacian bounds every second directional derivative in `L²`:
`‖∂_v ∂_w u‖_{L²} ≤ ‖v‖ ‖w‖ ‖Δ u‖_{L²}` for a Schwartz function `u`. -/
theorem norm_toLp_lineDerivOp_lineDerivOp_le (u : 𝓢(E, F)) (v w : E) :
    ‖(∂_{v} (∂_{w} u)).toLp 2‖ ≤ ‖v‖ * ‖w‖ * ‖(Δ u).toLp 2‖ := by
  rw [toLp_lineDerivOp_lineDerivOp_eq_fourierMultiplierCLM]
  exact (Lp.norm_fourierMultiplierCLM_apply_le _ _).trans
    (mul_le_mul_of_nonneg_right (norm_hessianSymbolLp_le v w) (norm_nonneg _))

end SchwartzMap
