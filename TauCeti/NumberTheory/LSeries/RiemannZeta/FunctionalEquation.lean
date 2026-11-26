/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.LogDeriv
public import Mathlib.NumberTheory.LSeries.RiemannZeta

import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.Analysis.Calculus.LogDeriv.Symmetry

/-!
# Uncompleted forms of the zeta functional equation

Off the zeros and poles of both zeta factors, the completed functional equation gives

`ζ'/ζ(s) + ζ'/ζ(1 - s) = -Γℝ'/Γℝ(s) - Γℝ'/Γℝ(1 - s)`.

Unlike the asymmetric tangent formula, this identity applies at integers as well, provided
neither side meets a zero or pole. The digamma form makes its gamma contribution explicit.
We also record the reflection identity for the logarithmic derivative of the completion;
this holds everywhere, including at its totalized pole values.

Without logarithmic derivatives, the functional equation also reads
`ζ(s) = ζ(1 - s) Γℝ(1 - s) / Γℝ(s)` for `s ≠ 0` with `Γℝ(1 - s) ≠ 0`, the form used to reflect
bounds for `ζ` from a right half-plane to the left one.

The functional equation also reflects zeros: if `ζ(s) = 0` and `s` is not a trivial zero
`-2(n + 1)`, then `ζ(1 - s) = 0`.

## Main results

* `TauCeti.riemannZeta_eq_riemannZeta_one_sub_mul_Gammaℝ_div`: the uncompleted functional
  equation `ζ(s) = ζ(1 - s) Γℝ(1 - s) / Γℝ(s)`.
* `TauCeti.riemannZeta_one_sub_eq_zero`: the reflection `s ↦ 1 - s` sends a zero of `ζ` that is
  not a trivial zero to a zero.
* `TauCeti.logDeriv_riemannZeta_add_one_sub` and
  `TauCeti.logDeriv_riemannZeta_add_one_sub_eq_digamma`: the symmetric functional equation for
  `ζ'/ζ`, with gamma or digamma terms.

## References

* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §2.1.
* NIST Digital Library of Mathematical Functions, §25.4.
* David Loeffler, `riemannZeta_one_sub` in `Mathlib.NumberTheory.LSeries.RiemannZeta`; Michael
  Stoll, David Loeffler and Terence Tao, `riemannZeta_eq_zero_iff_of_re_nonpos` in
  `Mathlib.NumberTheory.LSeries.Nonvanishing`; used for the reflection of zeros.
-/

public section

open Complex Filter Topology

namespace TauCeti

/-- The logarithmic derivative of the completed zeta function changes sign under `s ↦ 1 - s`.
The identity holds even at zeros and at the totalized values at poles. -/
theorem logDeriv_completedRiemannZeta_one_sub (s : ℂ) :
    logDeriv completedRiemannZeta (1 - s) = -logDeriv completedRiemannZeta s := by
  have h := congrArg (fun f : ℂ → ℂ ↦ logDeriv f s)
    (funext completedRiemannZeta_one_sub)
  rw [logDeriv_comp_const_sub] at h
  exact neg_eq_iff_eq_neg.mp h

/-- **The uncompleted functional equation in quotient form.** For `s ≠ 0` with
`Γℝ(1 - s) ≠ 0`, that is `s` not one of `1, 3, 5, …`,
`ζ(s) = ζ(1 - s) Γℝ(1 - s) / Γℝ(s)`. At the trivial zeros `s = -2, -4, …` both sides are `0`. -/
theorem riemannZeta_eq_riemannZeta_one_sub_mul_Gammaℝ_div {s : ℂ} (hs : s ≠ 0)
    (hΓ : Gammaℝ (1 - s) ≠ 0) :
    riemannZeta s = riemannZeta (1 - s) * (Gammaℝ (1 - s) / Gammaℝ s) := by
  have hs₁ : 1 - s ≠ 0 := fun h ↦ hΓ (Gammaℝ_eq_zero_iff.mpr ⟨0, by simp [h]⟩)
  rw [riemannZeta_def_of_ne_zero hs, riemannZeta_def_of_ne_zero hs₁, completedRiemannZeta_one_sub,
    div_mul_div_cancel₀ hΓ]

/-- If `s` is a zero of `riemannZeta` other than a trivial zero `-2(n + 1)`, then `1 - s` is
also a zero. -/
theorem riemannZeta_one_sub_eq_zero {s : ℂ} (hs : riemannZeta s = 0)
    (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) : riemannZeta (1 - s) = 0 := by
  -- a nontrivial zero has positive real part, so `riemannZeta_one_sub` applies
  have hpos : 0 < s.re := not_le.mp fun h => htriv ((riemannZeta_eq_zero_iff_of_re_nonpos h).1 hs)
  have hn : ∀ n : ℕ, s ≠ -n := fun n h => by
    have : s.re = -n := by simp [h]
    linarith [n.cast_nonneg (α := ℝ)]
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact riemannZeta_one_ne_zero hs
  rw [riemannZeta_one_sub hn hs1, hs, mul_zero]

/-- Away from the origin, a nonzero zeta value excludes a zero of the real-place gamma factor. -/
theorem Gammaℝ_ne_zero_of_riemannZeta_ne_zero {s : ℂ} (hs : s ≠ 0)
    (hζ : riemannZeta s ≠ 0) : Gammaℝ s ≠ 0 := by
  intro hΓ
  apply hζ
  rw [riemannZeta_def_of_ne_zero hs, hΓ, div_zero]

/-- Away from the pole and zeros, the logarithmic derivative of zeta is that of its completion
minus the real-place gamma term. The origin is excluded because completion and gamma both
have poles there. -/
theorem logDeriv_riemannZeta_eq_completedRiemannZeta_sub_Gammaℝ {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) :
    logDeriv riemannZeta s =
      logDeriv completedRiemannZeta s - logDeriv Gammaℝ s := by
  have hΓ := Gammaℝ_ne_zero_of_riemannZeta_ne_zero hs₀ hζ
  have hΛ : completedRiemannZeta s ≠ 0 := by
    intro hz
    apply hζ
    rw [riemannZeta_def_of_ne_zero hs₀, hz, zero_div]
  have heq : riemannZeta =ᶠ[𝓝 s] fun z ↦ completedRiemannZeta z / Gammaℝ z := by
    filter_upwards [eventually_ne_nhds hs₀] with z hz
    exact riemannZeta_def_of_ne_zero hz
  rw [(logDeriv_congr_nhds heq).eq_of_nhds,
    logDeriv_fun_div s hΛ hΓ (differentiableAt_completedZeta hs₀ hs₁)
      (analyticAt_Gammaℝ_of_ne_zero hΓ).differentiableAt]

/-- **The symmetric logarithmic functional equation.** At every point off the zeros and poles
of the two zeta factors, including admissible integers, their logarithmic derivatives sum to
minus the two real-place gamma logarithmic derivatives. -/
theorem logDeriv_riemannZeta_add_one_sub {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) (hζ' : riemannZeta (1 - s) ≠ 0) :
    logDeriv riemannZeta s + logDeriv riemannZeta (1 - s) =
      -logDeriv Gammaℝ s - logDeriv Gammaℝ (1 - s) := by
  rw [logDeriv_riemannZeta_eq_completedRiemannZeta_sub_Gammaℝ hs₀ hs₁ hζ,
    logDeriv_riemannZeta_eq_completedRiemannZeta_sub_Gammaℝ (sub_ne_zero.mpr hs₁.symm)
      (by simpa using hs₀) hζ', logDeriv_completedRiemannZeta_one_sub]
  ring

/-- The symmetric logarithmic functional equation with both gamma terms expressed using
`digamma`; the hypotheses also exclude the poles of those gamma terms. -/
theorem logDeriv_riemannZeta_add_one_sub_eq_digamma {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) (hζ' : riemannZeta (1 - s) ≠ 0) :
    logDeriv riemannZeta s + logDeriv riemannZeta (1 - s) =
      (Real.log Real.pi : ℂ) - digamma (s / 2) / 2 - digamma ((1 - s) / 2) / 2 := by
  have hp (z : ℂ) (hz : z ≠ 0) (h : riemannZeta z ≠ 0) :
      ∀ n : ℕ, z ≠ -(2 * (n : ℂ)) := by
    intro n hn
    exact Gammaℝ_ne_zero_of_riemannZeta_ne_zero hz h (Gammaℝ_eq_zero_iff.mpr ⟨n, hn⟩)
  rw [logDeriv_riemannZeta_add_one_sub hs₀ hs₁ hζ hζ',
    logDeriv_Gammaℝ (hp s hs₀ hζ),
    logDeriv_Gammaℝ (hp (1 - s) (sub_ne_zero.mpr hs₁.symm) hζ')]
  ring

end TauCeti
