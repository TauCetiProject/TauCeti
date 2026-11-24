/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import TauCeti.Analysis.Contour.Curve.Circle.Lift
import TauCeti.Analysis.Contour.Winding.Number.Circle.Basic
import TauCeti.Analysis.Contour.Winding.Number.Periodic
import TauCeti.Analysis.Contour.Winding.Number.Reparam

/-!
# The winding number of a function along a loop in a circle

Let `ℓ : ℝ → ℂ` be a `C¹` curve with values in the circle of radius `r > 0` about `c`, closed on
`[a, b]` in the sense that `ℓ a = ℓ b`, and let `g` be a `C¹` function near that circle without
zeros on it. The loop `g ∘ ℓ` winds around `0` as many times as `g` does along the circle,
multiplied by the number of times `ℓ` runs around the circle:

`n(g ∘ ℓ, 0) = n(ℓ, c) · n(g ∘ circleMap c r, 0)`

(`TauCeti.Contour.windingNumber_comp_eq_mul_of_mem_sphere`). This is the degree law for the
winding number: `n(ℓ, c)` is the degree of `ℓ` as a map from the source interval, closed up, to
the circle.

The curve `ℓ` lifts to a `C¹` angle, `ℓ t = circleMap c r (φ t)`
(`TauCeti.Contour.exists_contDiff_eq_circleMap`), a smooth phase of the unimodular map
`(ℓ - c) / r`. Since `ℓ` is closed, `φ b - φ a = 2π n(ℓ, c)`. Reparametrizing by `φ`
(`TauCeti.Contour.windingNumber_comp_reparam`) turns the winding number of
`g ∘ ℓ = (g ∘ circleMap c r) ∘ φ` into that of the periodic curve `g ∘ circleMap c r` over
`n(ℓ, c)` periods, which is `n(ℓ, c)` times its winding number over one period
(`TauCeti.Contour.windingNumber_add_mul_eq_of_periodic`).

## References

* L. Ahlfors, *Complex Analysis*, Chapter 4.
-/

public section

noncomputable section

open Complex Set
open scoped Real Interval

namespace TauCeti.Contour

variable {ℓ : ℝ → ℂ} {c : ℂ} {r : ℝ}

/-- **The degree law for the winding number.** Let `ℓ : ℝ → ℂ` be a `C¹` curve with values in the
circle of radius `r > 0` about `c` and with `ℓ a = ℓ b`, and let `g` be `C¹` near that circle and
nonzero on it. Then the winding number of `g ∘ ℓ` around `0` is the winding number of `ℓ` around
`c` times the winding number of `g` along the circle, traversed once counterclockwise from any
starting angle `s`. -/
theorem windingNumber_comp_eq_mul_of_mem_sphere {g : ℂ → ℂ} (hr : 0 < r)
    (hg : ∀ w ∈ Metric.sphere c r, ContDiffAt ℝ 1 g w) (hg₀ : ∀ w ∈ Metric.sphere c r, g w ≠ 0)
    (hℓ : ContDiff ℝ 1 ℓ) (hs : ∀ t, ℓ t ∈ Metric.sphere c r) {a b : ℝ} (hab : ℓ a = ℓ b)
    (s : ℝ) :
    windingNumber (g ∘ ℓ) a b 0 =
      windingNumber ℓ a b c * windingNumber (g ∘ circleMap c r) s (s + 2 * π) 0 := by
  obtain ⟨φ, hφ, hℓφ⟩ := exists_contDiff_eq_circleMap (n := 1) hℓ hr hs
  have hℓ' : ℓ = circleMap c r ∘ φ := funext hℓφ
  have hφd (t : ℝ) : HasDerivAt φ (deriv φ t) t := (hφ.differentiable one_ne_zero t).hasDerivAt
  have hφc : ContinuousOn (deriv φ) (uIcc a b) := (hφ.continuous_deriv le_rfl).continuousOn
  -- The function `g` along the circle.
  set G : ℝ → ℂ := g ∘ circleMap c r with hGdef
  have hG : ContDiff ℝ 1 G := contDiff_iff_contDiffAt.2 fun u ↦
    (hg _ (circleMap_mem_sphere c hr.le u)).comp u (contDiff_circleMap c r).contDiffAt
  have hG₀ (u : ℝ) : G u ≠ 0 := hg₀ _ (circleMap_mem_sphere c hr.le u)
  -- Since `ℓ` is closed, the angle increases by a whole number `n` of turns.
  obtain ⟨n, hn⟩ : ∃ n : ℤ, φ b = φ a + n * (2 * π) := by
    have h := hab
    rw [hℓφ a, hℓφ b, circleMap, circleMap, add_right_inj,
      mul_right_inj' (ofReal_ne_zero.2 hr.ne')] at h
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h.symm
    exact ⟨n, by simpa using congrArg Complex.im hn⟩
  -- So `ℓ` winds `n` times around `c`, and `g ∘ ℓ = G ∘ φ` winds as `G` does over `n` periods.
  have hwℓ : windingNumber ℓ a b c = n := by
    rw [hℓ', windingNumber_comp_reparam (fun t _ ↦ hφd t) hφc
      (fun u _ ↦ (differentiable_circleMap c r).differentiableAt)
      (continuous_deriv_circleMap c r).continuousOn (fun u _ ↦ circleMap_ne_center hr.ne'),
      windingNumber_circleMap_center hr.ne', hn]
    push_cast
    field_simp
    ring
  rw [hwℓ, hℓ', ← Function.comp_assoc, ← hGdef,
    windingNumber_comp_reparam (fun t _ ↦ hφd t) hφc
      (fun u _ ↦ (hG.differentiable one_ne_zero).differentiableAt)
      (hG.continuous_deriv le_rfl).continuousOn (fun u _ ↦ hG₀ u), hn,
    windingNumber_add_mul_eq_of_periodic hG (fun u ↦ by simp [hGdef, periodic_circleMap c r u])
      hG₀ n (φ a) s]

end TauCeti.Contour
