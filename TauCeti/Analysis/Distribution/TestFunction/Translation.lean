/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction

/-!
# Translation of test functions

This file translates a test function on an open set `V` in the opposite direction to a vector
`h`, producing a test function on any open set `Ω` that contains `V + h`. This is the common
test-function operation used to prove translation invariance of weak derivatives.

## Main declarations

* `TauCeti.translateTestFunction`: translate a test function while changing its domain.
* `TauCeti.translateTestFunction_apply`: evaluation of a translated test function.
* `TauCeti.lineDeriv_translateTestFunction`: directional derivatives commute with translation.
-/

public section

noncomputable section

namespace TauCeti

open Set TopologicalSpace
open scoped Distributions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Omega V : Opens E} {h : E}

/-- Translate a test function in the opposite direction, regarding it as a test function on an
open set containing the translated support. -/
def translateTestFunction (hVO : MapsTo (· + h) V Omega) (phi : 𝓓(V, ℝ)) :
    𝓓(Omega, ℝ) :=
  ⟨fun y => phi (y - h),
    phi.contDiff.comp (contDiff_id.sub contDiff_const),
    by
      simpa [sub_eq_add_neg, Function.comp_def, Homeomorph.addRight] using
        phi.hasCompactSupport.comp_homeomorph (Homeomorph.addRight (-h)),
    by
      intro y hy
      have hy' : y + -h ∈ tsupport (phi : E → ℝ) := by
        have hfun : (fun z => phi (z - h)) =
            (phi : E → ℝ) ∘ (Homeomorph.addRight (-h) : E → E) := by
          funext z
          simp only [Function.comp_apply, sub_eq_add_neg]
          apply congrArg phi
          rfl
        have hycomp : y ∈ tsupport
            ((phi : E → ℝ) ∘ (Homeomorph.addRight (-h) : E → E)) := by
          rw [← hfun]
          exact hy
        rw [tsupport_comp_eq_preimage] at hycomp
        exact hycomp
      simpa only [sub_eq_add_neg, neg_add_cancel_right] using hVO (phi.tsupport_subset hy')⟩

/-- Translating a test function evaluates it at the oppositely translated point. -/
theorem translateTestFunction_apply (hVO : MapsTo (· + h) V Omega)
    (phi : 𝓓(V, ℝ)) (y : E) : translateTestFunction hVO phi y = phi (y - h) :=
  (rfl)

/-- The directional derivative of a translated test function is the translated directional
derivative. -/
theorem lineDeriv_translateTestFunction (hVO : MapsTo (· + h) V Omega)
    (phi : 𝓓(V, ℝ)) (y w : E) :
    lineDeriv ℝ (translateTestFunction hVO phi : E → ℝ) y w =
      lineDeriv ℝ (phi : E → ℝ) (y - h) w := by
  simp only [lineDeriv, translateTestFunction_apply, sub_eq_add_neg]
  congr 1
  funext t
  congr 1
  abel

end TauCeti
