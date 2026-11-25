/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.TwistMap.OpenStrip
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue

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

## References

* M. R. Herman, *Sur les courbes invariantes par les difféomorphismes de l'anneau, Vol. 1*,
  Astérisque 103–104, 1983, Chapitre I, §4.3.
-/

public section

open Set

namespace TauCeti

/-- A map `F` of the open strip `ℝ × J` is *exact* for the primitive `λ = g dx` with period `ℓ`
when `F*λ − λ = dS` for an `ℓ`-periodic `C¹` function `S` on the strip: at every point `p` of the
strip, `dS_p = g(F p) (dF_p)₁ − g(p) dx`. -/
def IsExactForPrimitive (ℓ : ℝ) (J : Set ℝ) (F : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ))
    (g : ℝ × ℝ → ℝ) : Prop :=
  ∃ S : ℝ × ℝ → ℝ, ContDiffOn ℝ 1 S (univ ×ˢ J) ∧ (∀ x, ∀ y ∈ J, S (x + ℓ, y) = S (x, y)) ∧
    ∀ p ∈ univ ×ˢ J, HasFDerivAt S (g (F p) • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (fderiv ℝ F p) - g p • ContinuousLinearMap.fst ℝ ℝ ℝ) p

/-- Unfolding `TauCeti.IsExactForPrimitive`. -/
theorem isExactForPrimitive_iff {ℓ : ℝ} {J : Set ℝ} {F : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    {g : ℝ × ℝ → ℝ} : IsExactForPrimitive ℓ J F g ↔
      ∃ S : ℝ × ℝ → ℝ, ContDiffOn ℝ 1 S (univ ×ˢ J) ∧ (∀ x, ∀ y ∈ J, S (x + ℓ, y) = S (x, y)) ∧
        ∀ p ∈ univ ×ˢ J, HasFDerivAt S (g (F p) • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
          (fderiv ℝ F p) - g p • ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
  Iff.rfl

/-- **The flux obstruction.** If `F` is exact for `λ = g dx` with period `ℓ ≠ 0` and, along a
height `y₀ ∈ J`, the one-form `F*λ − λ` evaluated on `∂ₓ` is a constant `c`, that is
`g(F(x, y₀)) ∂ₓF₁(x, y₀) − g(x, y₀) = c` for every `x`, then `c = 0`: the integral of `F*λ − λ`
over a period of the horizontal line is `c ℓ`, and it is the increment of the periodic function
`S` over a period. -/
theorem IsExactForPrimitive.eq_zero_of_flux {ℓ : ℝ} {J : Set ℝ}
    {F : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)} {g : ℝ × ℝ → ℝ}
    (hF : IsExactForPrimitive ℓ J F g) (hℓ : ℓ ≠ 0) {y₀ : ℝ} (hy₀ : y₀ ∈ J) {c : ℝ}
    (hc : ∀ x, g (F (x, y₀)) * (fderiv ℝ F (x, y₀) (1, 0)).1 - g (x, y₀) = c) : c = 0 := by
  obtain ⟨S, -, hper, hS⟩ := hF
  -- Along the horizontal line, `x ↦ S (x, y₀) − c x` has derivative zero, hence is constant.
  have hd (x : ℝ) : HasDerivAt (fun x => S (x, y₀)) c x := by
    have h := HasFDerivAt.comp_hasDerivAt x (hS (x, y₀) ⟨mem_univ _, hy₀⟩)
      ((hasDerivAt_id x).prodMk (hasDerivAt_const x y₀))
    convert h using 1
    · rfl
    · rw [← hc x]
      simp
  have hd' (x : ℝ) : HasDerivAt (fun x => S (x, y₀) - c * x) 0 x := by
    simpa using (hd x).fun_sub ((hasDerivAt_id' x).const_mul c)
  have hconst : ∀ x, S (x, y₀) - c * x = S (0, y₀) - c * 0 := fun x =>
    is_const_of_deriv_eq_zero (f := fun x => S (x, y₀) - c * x)
      (fun x => (hd' x).differentiableAt) (fun x => (hd' x).deriv) x 0
  have h := hconst ℓ
  rw [show (ℓ : ℝ) = 0 + ℓ by ring, hper 0 y₀ hy₀] at h
  have : c * ℓ = 0 := by linarith
  exact (mul_eq_zero.1 this).resolve_right hℓ

end TauCeti
