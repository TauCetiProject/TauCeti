/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Abel

/-!
# Directional derivatives

For a function `f : 𝕜 → F` of one variable, the directional derivative in the direction `1` is
the ordinary derivative. This identifies the weak directional derivatives of
`TauCeti.HasWeakLineDerivOn` on the real line with one-variable derivatives.

Outside the topological support of a function, its directional derivatives vanish. This is the
directional counterpart of Mathlib's `fderiv_of_notMem_tsupport`. Both results require no
differentiability hypothesis, which matters for Lipschitz functions.

The average `y ↦ ∫₀¹ g (y - t h) dt` of translates of a continuous real function `g` has directional
derivative `g y - g (y - h)` in the direction `h`, by the fundamental theorem of calculus.
-/

public section

namespace TauCeti

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The directional derivative of a function of one variable in the direction `1` is its
derivative. No differentiability hypothesis is needed. -/
@[simp]
theorem lineDeriv_one {f : 𝕜 → F} {x : 𝕜} : lineDeriv 𝕜 f x 1 = deriv f x := by
  simp [lineDeriv, deriv_comp_const_add]

/-- Outside the topological support of `f`, every directional derivative of `f` vanishes. No
differentiability hypothesis is needed. -/
@[simp]
theorem lineDeriv_of_notMem_tsupport {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : E → F} {x : E} (h : x ∉ tsupport f) (v : E) : lineDeriv 𝕜 f x v = 0 := by
  rw [(notMem_tsupport_iff_eventuallyEq.1 h).lineDeriv_eq]
  simp [lineDeriv]

/-- The function `y ↦ ∫₀¹ g (y - t h) dt` of a continuous `g` has directional derivative
`g y - g (y - h)` in the direction `h`. -/
theorem _root_.Continuous.hasLineDerivAt_intervalIntegral_comp_sub {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {h : E}
    {g : E → G} (hg : Continuous g) (y : E) :
    HasLineDerivAt ℝ (fun y => ∫ t in (0 : ℝ)..1, g (y - t • h)) (g y - g (y - h)) y h := by
  -- `s ↦ Φ (y + s h)` differentiates by the fundamental theorem of calculus, as
  -- `Φ (y + s h) = ∫_{-s}^{1-s} g (y - t h) dt`.
  set f : ℝ → G := fun t => g (y - t • h)
  have hf : Continuous f := hg.comp (by fun_prop)
  have hline : (fun s : ℝ => ∫ t in (0 : ℝ)..1, g (y + s • h - t • h)) =
      fun s => (∫ t in (0 : ℝ)..1 - s, f t) - ∫ t in (0 : ℝ)..-s, f t := by
    funext s
    rw [intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _)]
    have hshift := intervalIntegral.integral_comp_sub_right f s (a := 0) (b := 1)
    rw [zero_sub, sub_eq_add_neg 1 s, ← sub_eq_add_neg] at hshift
    rw [← hshift]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [f, sub_smul]
    congr 1
    abel
  -- `HasLineDerivAt` is by definition the derivative at `0` of `s ↦ Φ (y + s • h)`.
  have hlin : HasLineDerivAt ℝ (fun y => ∫ t in (0 : ℝ)..1, g (y - t • h)) (f 0 - f 1) y h := by
    unfold HasLineDerivAt
    rw [hline]
    have h1 := ((hf.integral_hasStrictDerivAt 0 (1 - 0)).hasDerivAt.scomp 0
      ((hasDerivAt_id (0 : ℝ)).const_sub 1))
    have h2 := ((hf.integral_hasStrictDerivAt 0 (-0)).hasDerivAt.scomp 0
      (hasDerivAt_id (0 : ℝ)).neg)
    exact (h1.sub h2).congr_deriv (by simp [sub_eq_add_neg, add_comm])
  simpa [f] using hlin

end TauCeti
