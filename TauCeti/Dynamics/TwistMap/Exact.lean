/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.TwistMap.OpenStrip
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.FDeriv.Prod

/-!
# Exact maps of an open strip

Fix a period `ℓ`, an open interval `J` of heights and a function `g` on the strip `ℝ × J`, the
coefficient of the primitive `λ = g dx` of the area form `ω = −dλ = ∂_y g dx ∧ dy`. A map
`F = (F₁, F₂)` of the strip is *exact* for `λ` when `F*λ − λ = dS` for an `ℓ`-periodic `C¹`
function `S` on the strip (`TauCeti.IsExactForPrimitive`). In coordinates,
`(F*λ)_p = g(F p) dF₁(p)`, so the condition reads
`dS_p = g(F p) (dF_p)₁ − g(p) dx` at every point `p` of the strip.

For `g = y` this is the convention of exact symplectic twist maps of the annulus: the shear
`(x, y) ↦ (x + y, y)` is exact with `S = y²/2`, while the shifted shear `(x + y, y + c)` with
`c ≠ 0` preserves area but is not exact, since `∂ₓS = c` along `y = 0` contradicts periodicity
(the flux of `F` is `c`).

## Main declarations

* `TauCeti.IsExactForPrimitive`: exactness of a map of the strip for the primitive `λ = g dx`.
* `TauCeti.IsExactForPrimitive.integral_flux_eq_zero`: for an exact map, the integral of
  `F*λ − λ` over a period of a horizontal line vanishes.
* `TauCeti.IsExactForPrimitive.eq_zero_of_flux`: in particular, a constant flux along a
  horizontal line is zero.

## References

* M. R. Herman, *Sur les courbes invariantes par les difféomorphismes de l'anneau, Vol. 1*,
  Astérisque 103–104, 1983, Chapitre I, §4.3.
-/

public section

open Set MeasureTheory

namespace TauCeti

/-- A map `F` of the open strip `ℝ × J` is *exact* for the primitive `λ = g dx` with period `ℓ`
when `F*λ − λ = dS` for an `ℓ`-periodic `C¹` function `S` on the strip: at every point `p` of the
strip, `dS_p = g(F p) (dF_p)₁ − g(p) dx`. -/
def IsExactForPrimitive (ℓ : ℝ) (J : Set ℝ) (F : ℝ × ℝ → ℝ × ℝ)
    (g : ℝ × ℝ → ℝ) : Prop :=
  ∃ S : ℝ × ℝ → ℝ, ContDiffOn ℝ 1 S (univ ×ˢ J) ∧ (∀ x, ∀ y ∈ J, S (x + ℓ, y) = S (x, y)) ∧
    ∀ p ∈ univ ×ˢ J, HasFDerivAt S (g (F p) • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (fderiv ℝ F p) - g p • ContinuousLinearMap.fst ℝ ℝ ℝ) p

/-- Unfolding `TauCeti.IsExactForPrimitive`. -/
theorem isExactForPrimitive_iff {ℓ : ℝ} {J : Set ℝ} {F : ℝ × ℝ → ℝ × ℝ}
    {g : ℝ × ℝ → ℝ} : IsExactForPrimitive ℓ J F g ↔
      ∃ S : ℝ × ℝ → ℝ, ContDiffOn ℝ 1 S (univ ×ˢ J) ∧ (∀ x, ∀ y ∈ J, S (x + ℓ, y) = S (x, y)) ∧
        ∀ p ∈ univ ×ˢ J, HasFDerivAt S (g (F p) • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
          (fderiv ℝ F p) - g p • ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
  Iff.rfl

/-- **The flux obstruction.** If `F` is exact for `λ = g dx` with period `ℓ`, then along any
height `y₀ ∈ J` the integral of `F*λ − λ` evaluated on `∂ₓ`, that is of
`g(F(x, y₀)) ∂ₓF₁(x, y₀) − g(x, y₀)`, over a period `[a, a + ℓ]` vanishes: it is the increment of
the periodic function `S` over a period. -/
theorem IsExactForPrimitive.integral_flux_eq_zero {ℓ : ℝ} {J : Set ℝ} {F : ℝ × ℝ → ℝ × ℝ}
    {g : ℝ × ℝ → ℝ} (hF : IsExactForPrimitive ℓ J F g) {y₀ : ℝ} (hy₀ : y₀ ∈ J) (a : ℝ) :
    ∫ x in a..a + ℓ, (g (F (x, y₀)) * (fderiv ℝ F (x, y₀) (1, 0)).1 - g (x, y₀)) = 0 := by
  obtain ⟨S, hC, hper, hS⟩ := hF
  -- Along the horizontal line, the derivative of `x ↦ S (x, y₀)` is the integrand.
  have hd (x : ℝ) : HasDerivAt (fun x => S (x, y₀))
      (g (F (x, y₀)) * (fderiv ℝ F (x, y₀) (1, 0)).1 - g (x, y₀)) x :=
    ((hS (x, y₀) ⟨mem_univ _, hy₀⟩).comp_hasDerivAt x
      (hasDerivAt_prodMk_left x y₀)).congr_deriv (by simp)
  -- The restriction of the `C¹` function `S` to the line is `C¹`, so the integrand, its
  -- derivative, is continuous.
  have hC₀ : ContDiff ℝ 1 fun x => S (x, y₀) :=
    contDiffOn_univ.1 <| hC.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      fun _ _ => ⟨mem_univ _, hy₀⟩
  have hint : Continuous fun x => g (F (x, y₀)) * (fderiv ℝ F (x, y₀) (1, 0)).1 - g (x, y₀) := by
    simpa only [funext fun x => (hd x).deriv] using hC₀.continuous_deriv le_rfl
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (hint.intervalIntegrable _ _), hper a y₀ hy₀, sub_self]

/-- If `F` is exact for `λ = g dx` with period `ℓ ≠ 0` and, along a height `y₀ ∈ J`, the one-form
`F*λ − λ` evaluated on `∂ₓ` is a constant `c`, that is
`g(F(x, y₀)) ∂ₓF₁(x, y₀) − g(x, y₀) = c` for every `x`, then `c = 0`: by
`TauCeti.IsExactForPrimitive.integral_flux_eq_zero`, its integral `c ℓ` over a period vanishes. -/
theorem IsExactForPrimitive.eq_zero_of_flux {ℓ : ℝ} {J : Set ℝ} {F : ℝ × ℝ → ℝ × ℝ}
    {g : ℝ × ℝ → ℝ} (hF : IsExactForPrimitive ℓ J F g) (hℓ : ℓ ≠ 0) {y₀ : ℝ} (hy₀ : y₀ ∈ J)
    {c : ℝ} (hc : ∀ x, g (F (x, y₀)) * (fderiv ℝ F (x, y₀) (1, 0)).1 - g (x, y₀) = c) :
    c = 0 := by
  have hfun : (fun x => g (F (x, y₀)) * (fderiv ℝ F (x, y₀) (1, 0)).1 - g (x, y₀)) =
      fun _ => c := funext hc
  have h := hF.integral_flux_eq_zero hy₀ 0
  rw [hfun, intervalIntegral.integral_const, smul_eq_mul] at h
  simpa [hℓ] using h

end TauCeti
