/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RealChart
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Periodic integrals along vertical sides in real coordinates

A map `f : ℂ → ℂ` that is periodic of period one in the direction of `i`, such as the end lift of
a cylindrical end of a punctured sphere, sends a vertical segment of length one onto a closed
loop. The integral of a period-one function along the image under the real chart of `f` of the
vertical side `s = s₀` of a rectangle therefore does not depend on where the segment starts: it
may be taken over `[0, 1]` instead of `[-1/2, 1/2]`
(`TauCeti.Complex.intervalIntegral_realChart_eq_of_periodic`).

This is kept apart from `TauCeti.Analysis.Complex.RealChart` so that the real chart itself does not
depend on interval integration.
-/

public section

namespace TauCeti.Complex

/-- If `f` is periodic of period one in the direction of `i` along the vertical line `s = s₀`, the
integral of a period-one function `G` along the image under the real chart of `f` of the side
`s = s₀` of a rectangle may be taken over `[0, 1]` instead of `[-1/2, 1/2]`. -/
theorem intervalIntegral_realChart_eq_of_periodic {X E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℂ → ℂ} {s : ℝ}
    (hf : Function.Periodic (fun t : ℝ => f (s + t * Complex.I)) 1) {G : ℝ → X → E}
    (hG : Function.Periodic G 1) (u : ℝ × ℝ → X) :
    ∫ t in (-1 / 2 : ℝ)..1 / 2, G t (u (realChart f (s, t))) =
      ∫ t in (0 : ℝ)..1, G t (u (Complex.equivRealProdCLM (f (s + t * Complex.I)))) := by
  have hper : Function.Periodic
      (fun t : ℝ => G t (u (Complex.equivRealProdCLM (f (s + t * Complex.I))))) 1 := fun t => by
    have h' : f (s + ((t + 1 : ℝ) : ℂ) * Complex.I) = f (s + t * Complex.I) := hf t
    simp only [hG t, h']
  have h := Function.Periodic.intervalIntegral_add_eq hper (-1 / 2) 0
  rw [show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, zero_add] at h
  simp only [realChart_apply, Complex.equivRealProdCLM_symm_apply]
  exact h

end TauCeti.Complex
