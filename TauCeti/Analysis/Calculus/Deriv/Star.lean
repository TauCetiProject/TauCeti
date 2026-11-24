/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Derivatives of functions that commute with conjugation

If `f (conj w) = conj (f w)` for every `w`, then the derivative of `f` commutes with conjugation
too. This is Mathlib's `deriv_conj_conj` for a function with `conj ∘ f ∘ conj = f`.

## Main results

* `TauCeti.deriv_conj_of_forall_conj` — `deriv f (conj z) = conj (deriv f z)` when `f` commutes with
  conjugation.
-/

public section

open scoped ComplexConjugate

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [StarRing 𝕜] [NormedStarGroup 𝕜]

namespace TauCeti

/-- If `f` commutes with conjugation, then so does its derivative. -/
theorem deriv_conj_of_forall_conj {f : 𝕜 → 𝕜} (hf : ∀ w, f (conj w) = conj (f w)) (z : 𝕜) :
    deriv f (conj z) = conj (deriv f z) := by
  have h : conj ∘ f ∘ conj = f := funext fun w => by simp [hf]
  simpa [h] using congrFun (deriv_conj_conj (f := f)) (conj z)

end TauCeti
