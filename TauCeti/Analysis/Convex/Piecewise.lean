/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Slope

/-!
# Gluing convex functions at a point

A real function which is convex on `(-∞, a]` and on `[a, ∞)` is convex on all of `ℝ` as soon as
its left derivative at `a` is at most its right derivative there. This is the standard way to
prove convexity of a function given by different formulas on the two sides of a point, for
instance a function of `|x|`, and complements the monotone and antitone gluing lemmas of
`Mathlib.Analysis.Convex.Piecewise`.

## Main statements

* `TauCeti.convexOn_univ_of_convexOn_Iic_Ici`: a function convex on both sides of `a` whose
  one-sided derivatives at `a` satisfy `f'(a⁻) ≤ f'(a⁺)` is convex on `ℝ`.
-/

public section

namespace TauCeti

open Set

/-- Gluing convex functions: if `f : ℝ → ℝ` is convex on `(-∞, a]` and on `[a, ∞)`, and its
derivative `m₁` at `a` within `(-∞, a]` is at most its derivative `m₂` at `a` within `[a, ∞)`,
then `f` is convex on `ℝ`. -/
theorem convexOn_univ_of_convexOn_Iic_Ici {f : ℝ → ℝ} {a m₁ m₂ : ℝ}
    (hl : ConvexOn ℝ (Iic a) f) (hr : ConvexOn ℝ (Ici a) f)
    (hl' : HasDerivWithinAt f m₁ (Iic a) a) (hr' : HasDerivWithinAt f m₂ (Ici a) a)
    (hm : m₁ ≤ m₂) : ConvexOn ℝ univ f := by
  -- Secants ending at `a` have slope at most `m₂`, secants starting at `a` slope at least `m₂`.
  have hla : ∀ x < a, (f a - f x) / (a - x) ≤ m₂ := fun x hx => by
    have := hl.slope_le_of_hasDerivWithinAt (mem_Iic.2 hx.le) self_mem_Iic hx hl'
    rw [slope_def_field] at this
    exact this.trans hm
  have hra : ∀ z, a < z → m₂ ≤ (f z - f a) / (z - a) := fun z hz => by
    have := hr.le_slope_of_hasDerivWithinAt self_mem_Ici (mem_Ici.2 hz.le) hz hr'
    rwa [slope_def_field] at this
  -- For `u < v < w`, the slope on `[u, w]` is a weighted average of those on `[u, v]`, `[v, w]`.
  have avg : ∀ {u v w : ℝ}, u < v → v < w →
      (f w - f u) / (w - u) * (w - u) =
        (f v - f u) / (v - u) * (v - u) + (f w - f v) / (w - v) * (w - v) := by
    intro u v w huv hvw
    rw [div_mul_cancel₀ _ (sub_pos.2 (huv.trans hvw)).ne', div_mul_cancel₀ _ (sub_pos.2 huv).ne',
      div_mul_cancel₀ _ (sub_pos.2 hvw).ne']
    ring
  refine convexOn_of_slope_mono_adjacent convex_univ fun {x y z} _ _ hxy hyz => ?_
  rcases le_or_gt z a with hza | haz
  · exact hl.slope_mono_adjacent (mem_Iic.2 ((hxy.trans hyz).le.trans hza)) (mem_Iic.2 hza)
      hxy hyz
  rcases le_or_gt a x with hax | hxa
  · exact hr.slope_mono_adjacent (mem_Ici.2 hax) (mem_Ici.2 (hax.trans (hxy.trans hyz).le))
      hxy hyz
  -- It remains to treat `x < a < z`.
  rcases lt_trichotomy y a with hya | rfl | hay
  · -- The slope on `[y, z]` is at least the slope on `[y, a]`, which bounds that on `[x, y]`.
    refine (hl.slope_mono_adjacent (mem_Iic.2 (hxy.trans hya).le) self_mem_Iic hxy hya).trans ?_
    have h₁ := hla y hya
    have h₂ := hra z haz
    have h := avg hya haz
    refine le_of_mul_le_mul_right ?_ (sub_pos.2 hyz)
    rw [h]
    linarith [mul_le_mul_of_nonneg_right (h₁.trans h₂) (sub_pos.2 haz).le]
  · exact (hla x hxa).trans (hra z haz)
  · -- The slope on `[x, y]` is at most the slope on `[a, y]`, which bounds that on `[y, z]`.
    refine le_trans ?_ (hr.slope_mono_adjacent self_mem_Ici (mem_Ici.2 (hay.trans hyz).le) hay hyz)
    have h₁ := hla x hxa
    have h₂ := hra y hay
    have h := avg hxa hay
    refine le_of_mul_le_mul_right ?_ (sub_pos.2 hxy)
    rw [h]
    linarith [mul_le_mul_of_nonneg_right (h₁.trans h₂) (sub_pos.2 hxa).le]

end TauCeti
