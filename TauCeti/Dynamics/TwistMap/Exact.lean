/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Prod
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
* `TauCeti.IsExactForPrimitive.comp_fiber`: exactness is invariant under fibre-preserving changes
  of coordinates `(x, y) ↦ (x, φ(x, y))` that transport the primitive.

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

/-- **Exactness is invariant under fibre-preserving changes of coordinates.** Let
`Φ(x, y) = (x, φ(x, y))` and `Ψ(x, y) = (x, ψ(x, y))`, where `Ψ` maps `ℝ × J'` into `ℝ × J` and is
a right inverse of `Φ` there (`ψ(x, y) ∈ J` and `φ(x, ψ(x, y)) = y` for `y ∈ J'`), `ψ` is `C¹`,
differentiable and `ℓ`-periodic in `x` on `ℝ × J'`, and `φ` is differentiable on `ℝ × J`. Let `Φ`
transport the primitive `λ' = g' dx` to `λ = g dx`, that is `g' ∘ Φ = g` on `ℝ × J` (`Φ*λ' = λ`
because `Φ` preserves `x`). If `F` maps `ℝ × J` to itself, is differentiable there and is exact
for `λ`, then `Φ ∘ F ∘ Ψ` is exact for `λ'`. -/
theorem IsExactForPrimitive.comp_fiber {ℓ : ℝ} {J J' : Set ℝ} {F : ℝ × ℝ → ℝ × ℝ}
    {g g' φ ψ : ℝ × ℝ → ℝ} (hF : IsExactForPrimitive ℓ J F g)
    (hFJ : MapsTo F (univ ×ˢ J) (univ ×ˢ J)) (hFd : ∀ p ∈ univ ×ˢ J, DifferentiableAt ℝ F p)
    (hφd : ∀ p ∈ univ ×ˢ J, DifferentiableAt ℝ φ p) (hψ : ContDiffOn ℝ 1 ψ (univ ×ˢ J'))
    (hψd : ∀ q ∈ univ ×ˢ J', DifferentiableAt ℝ ψ q) (hψJ : ∀ x, ∀ y ∈ J', ψ (x, y) ∈ J)
    (hφψ : ∀ x, ∀ y ∈ J', φ (x, ψ (x, y)) = y) (hψper : ∀ x, ∀ y ∈ J', ψ (x + ℓ, y) = ψ (x, y))
    (hg : ∀ p ∈ univ ×ˢ J, g' (p.1, φ p) = g p) :
    IsExactForPrimitive ℓ J' ((fun p => (p.1, φ p)) ∘ F ∘ fun q => (q.1, ψ q)) g' := by
  obtain ⟨S, hC, hper, hS⟩ := hF
  set Φ : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, φ p)
  set Ψ : ℝ × ℝ → ℝ × ℝ := fun q => (q.1, ψ q)
  have hΨJ : MapsTo Ψ (univ ×ˢ J') (univ ×ˢ J) := fun q hq =>
    ⟨mem_univ _, hψJ q.1 q.2 hq.2⟩
  -- The derivatives of `Φ` and `Ψ` preserve the first coordinate.
  have hΦ' (p : ℝ × ℝ) (hp : p ∈ univ ×ˢ J) :
      HasFDerivAt Φ ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (fderiv ℝ φ p)) p :=
    hasFDerivAt_fst.prodMk (hφd p hp).hasFDerivAt
  have hΨ' (q : ℝ × ℝ) (hq : q ∈ univ ×ˢ J') :
      HasFDerivAt Ψ ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (fderiv ℝ ψ q)) q :=
    hasFDerivAt_fst.prodMk (hψd q hq).hasFDerivAt
  refine ⟨S ∘ Ψ, hC.comp (contDiffOn_fst.prodMk hψ) hΨJ, fun x y hy => ?_, fun q hq => ?_⟩
  · simp only [Function.comp_apply, Ψ, hψper x y hy]
    exact hper x _ (hψJ x y hy)
  set p := Ψ q
  have hp : p ∈ univ ×ˢ J := hΨJ hq
  have hFp := (hFd p hp).hasFDerivAt
  have hcomp := ((hΦ' (F p) (hFJ hp)).comp q (hFp.comp q (hΨ' q hq)))
  have hgq : g' q = g p := by
    rw [← hg p hp]
    simp only [p, Ψ, hφψ q.1 q.2 hq.2]
  convert (hS p hp).comp q (hΨ' q hq) using 1
  rw [hcomp.fderiv, Function.comp_apply, Function.comp_apply, hg (F p) (hFJ hp), hgq]
  ext <;> simp

end TauCeti
