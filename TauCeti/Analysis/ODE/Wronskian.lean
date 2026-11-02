/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue

/-!
# The Wronskian of a scalar second-order linear equation

For two solutions `φ`, `ψ` of the real equation `f'' = q f` without a first-order term, the
Wronskian `ψ φ' - φ ψ'` has derivative `ψ q φ - φ q ψ = 0`, so it is constant. For the
fundamental pair with `φ(a) = 0`, `φ'(a) = 1`, `ψ(a) = 1` and `ψ'(a) = 0` it is identically one.

## Main results

* `TauCeti.wronskian_eq_of_hasDerivAt`: the Wronskian of two solutions of `f'' = q f` is
  constant.
* `TauCeti.wronskian_eq_one_of_hasDerivAt`: the Wronskian of the fundamental pair is one.
-/

public section

namespace TauCeti

variable {q φ φ' ψ ψ' : ℝ → ℝ}

/-- The Wronskian `ψ φ' - φ ψ'` of two solutions of `f'' = q f` on `ℝ` is constant. -/
theorem wronskian_eq_of_hasDerivAt
    (hφ : ∀ t, HasDerivAt φ (φ' t) t) (hφ' : ∀ t, HasDerivAt φ' (q t * φ t) t)
    (hψ : ∀ t, HasDerivAt ψ (ψ' t) t) (hψ' : ∀ t, HasDerivAt ψ' (q t * ψ t) t) (t a : ℝ) :
    ψ t * φ' t - φ t * ψ' t = ψ a * φ' a - φ a * ψ' a := by
  have hderiv : ∀ t, HasDerivAt (fun r ↦ ψ r * φ' r - φ r * ψ' r) 0 t := fun t ↦
    (((hψ t).mul (hφ' t)).sub ((hφ t).mul (hψ' t))).congr_deriv (by ring)
  exact is_const_of_deriv_eq_zero (fun t ↦ (hderiv t).differentiableAt)
    (fun t ↦ (hderiv t).deriv) t a

/-- The Wronskian `ψ φ' - φ ψ'` of the fundamental pair of solutions of `f'' = q f` at `a`, with
`φ(a) = 0`, `φ'(a) = 1`, `ψ(a) = 1` and `ψ'(a) = 0`, is identically one. -/
theorem wronskian_eq_one_of_hasDerivAt {a : ℝ}
    (hφ : ∀ t, HasDerivAt φ (φ' t) t) (hφ' : ∀ t, HasDerivAt φ' (q t * φ t) t)
    (hψ : ∀ t, HasDerivAt ψ (ψ' t) t) (hψ' : ∀ t, HasDerivAt ψ' (q t * ψ t) t)
    (hφa : φ a = 0) (hφ'a : φ' a = 1) (hψa : ψ a = 1) (hψ'a : ψ' a = 0) (t : ℝ) :
    ψ t * φ' t - φ t * ψ' t = 1 := by
  rw [wronskian_eq_of_hasDerivAt hφ hφ' hψ hψ' t a, hφa, hφ'a, hψa, hψ'a]
  ring

end TauCeti
