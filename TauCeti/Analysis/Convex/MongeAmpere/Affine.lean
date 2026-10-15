/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.MongeAmpere.Basic

/-!
# Affine renormalization of the Monge–Ampère measure

Adding the affine function `x ↦ ⟪x, q⟫ + c` to a function `f : E → EReal` translates every
subdifferential, and hence every subgradient image, by `q`
(`TauCeti.subgradientImage_add_affine`). It also preserves convexity of the real epigraph and
the effective domain, so the Aleksandrov Monge–Ampère measure with respect to an additive Haar
measure is unchanged.

This invariance permits the standard normalization of a convex function by subtracting a
supporting plane before studying its sections.

## Main statements

* `TauCeti.mongeAmpereMeasure_add_affine` proves invariance of the Aleksandrov Monge–Ampère
  measure under addition of an affine function.

## References

* C. E. Gutiérrez, *The Monge–Ampère Equation*, 2nd ed., Progress in Nonlinear Differential
  Equations and Their Applications 89, Birkhäuser, 2016, §1.1.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Measure Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Affine invariance of the Aleksandrov Monge–Ampère measure.** Adding an affine function
`x ↦ ⟪x, q⟫ + c` to `f : E → EReal` does not change its Monge–Ampère measure with respect to an
additive Haar measure. -/
theorem mongeAmpereMeasure_add_affine (f : E → EReal) (q : E) (c : ℝ) :
    mongeAmpereMeasure μ (fun x ↦ f x + ((inner ℝ x q + c : ℝ) : EReal)) =
      mongeAmpereMeasure μ f := by
  set g : E → EReal := fun x ↦ f x + ((inner ℝ x q + c : ℝ) : EReal)
  have hconv : Convex ℝ {p : E × ℝ | g p.1 ≤ p.2} ↔ Convex ℝ {p : E × ℝ | f p.1 ≤ p.2} := by
    simpa only [innerₗ_apply_apply] using convex_epigraph_add_affine_iff (innerₗ E) (f := f) q c
  by_cases hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}
  swap
  · have hg : ¬Convex ℝ {p : E × ℝ | g p.1 ≤ p.2} := fun hg ↦ hf (hconv.1 hg)
    rw [mongeAmpereMeasure_eq_zero_of_not_convex μ hf,
      mongeAmpereMeasure_eq_zero_of_not_convex μ hg]
  by_cases hbot : ∀ x, f x ≠ ⊥
  swap
  · obtain ⟨x, hx⟩ := not_forall_not.1 hbot
    rw [mongeAmpereMeasure_eq_zero_of_eq_bot μ hx,
      mongeAmpereMeasure_eq_zero_of_eq_bot μ (x := x) (by simp [g, hx])]
  have hgbot (x : E) : g x ≠ ⊥ := by simp [g, hbot x]
  have hdom : {x | g x ≠ ⊤} = {x | f x ≠ ⊤} := by
    ext x
    exact EReal.add_ne_top_iff_ne_top_left (EReal.coe_ne_bot _) (EReal.coe_ne_top _)
  ext s hs
  rw [mongeAmpereMeasure_apply μ (hconv.2 hf) hgbot AbsolutelyContinuous.rfl hs,
    mongeAmpereMeasure_apply μ hf hbot AbsolutelyContinuous.rfl hs, hdom]
  have h := subgradientImage_add_affine (innerₗ E) (f := f) q c (s ∩ interior {x | f x ≠ ⊤})
  simp only [innerₗ_apply_apply] at h
  rw [h]
  simpa only [sub_eq_add_neg, add_comm] using
    measure_preimage_add μ (-q) (subgradientImage (innerₗ E) f (s ∩ interior {x | f x ≠ ⊤}))

end TauCeti
