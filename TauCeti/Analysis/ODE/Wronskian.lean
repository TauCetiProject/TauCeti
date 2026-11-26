/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Calculus.IteratedDeriv.Basic

/-!
# The Wronskian of a scalar second-order linear equation

For two solutions `φ`, `ψ` of the equation `f'' = q f` on a preconnected open subset of `ℝ` or
`ℂ`, with values in a normed commutative algebra and without a first-order term, the Wronskian
`ψ φ' - φ ψ'` has derivative `ψ q φ - φ q ψ = 0`, so it is constant. For the fundamental pair of
global solutions with `φ(a) = 0`, `φ'(a) = 1` and `ψ(a) = 1` it is identically one.

## Main results

* `TauCeti.wronskian_eq_of_hasDerivAt`: the Wronskian of two solutions of `f'' = q f` on a
  preconnected open set is constant.
* `TauCeti.wronskian_eq_of_iteratedDeriv_eq_mul`: the same for `C²` solutions, with the equation
  written with `iteratedDeriv 2` and the Wronskian with `deriv`.
* `TauCeti.wronskian_eq_one_of_hasDerivAt`: the Wronskian of the fundamental pair is one.
-/

public section

open Set

namespace TauCeti

variable {𝕜 𝔸 : Type*} [RCLike 𝕜] [NormedCommRing 𝔸] [NormedAlgebra 𝕜 𝔸]
  {q φ φ' ψ ψ' u w : 𝕜 → 𝔸} {s : Set 𝕜}

/-- The Wronskian `ψ φ' - φ ψ'` of two solutions of `f'' = q f` on a preconnected open set `s`
of `ℝ` or `ℂ` is constant on `s`. -/
theorem wronskian_eq_of_hasDerivAt (hs : IsOpen s) (hs' : IsPreconnected s)
    (hφ : ∀ t ∈ s, HasDerivAt φ (φ' t) t) (hφ' : ∀ t ∈ s, HasDerivAt φ' (q t * φ t) t)
    (hψ : ∀ t ∈ s, HasDerivAt ψ (ψ' t) t) (hψ' : ∀ t ∈ s, HasDerivAt ψ' (q t * ψ t) t)
    {t a : 𝕜} (ht : t ∈ s) (ha : a ∈ s) :
    ψ t * φ' t - φ t * ψ' t = ψ a * φ' a - φ a * ψ' a := by
  have hderiv (r : 𝕜) (hr : r ∈ s) : HasDerivAt (fun r ↦ ψ r * φ' r - φ r * ψ' r) 0 r :=
    (((hψ r hr).mul (hφ' r hr)).sub ((hφ r hr).mul (hψ' r hr))).congr_deriv (by ring)
  exact hs.is_const_of_deriv_eq_zero hs'
    (fun r hr ↦ (hderiv r hr).differentiableAt.differentiableWithinAt)
    (fun r hr ↦ (hderiv r hr).deriv) ht ha

/-- **The Wronskian of `C²` solutions is constant.** For two solutions `u`, `w` of `w'' = q w`,
`C²` on a preconnected open set `s`, the Wronskian `u w' - u' w` takes the same value at any two
points of `s`. No continuity of `q` is needed. -/
theorem wronskian_eq_of_iteratedDeriv_eq_mul (hs : IsOpen s) (hs' : IsPreconnected s)
    (hu : ContDiffOn 𝕜 2 u s) (huq : ∀ x ∈ s, iteratedDeriv 2 u x = q x * u x)
    (hw : ContDiffOn 𝕜 2 w s) (hwq : ∀ x ∈ s, iteratedDeriv 2 w x = q x * w x) {x y : 𝕜}
    (hx : x ∈ s) (hy : y ∈ s) :
    u x * deriv w x - deriv u x * w x = u y * deriv w y - deriv u y * w y := by
  rw [mul_comm (deriv u x), mul_comm (deriv u y)]
  exact wronskian_eq_of_hasDerivAt hs hs' (fun t ht ↦ (hw.hasDerivAt_and_hasDerivAt_deriv hs ht).1)
    (fun t ht ↦ hwq t ht ▸ (hw.hasDerivAt_and_hasDerivAt_deriv hs ht).2)
    (fun t ht ↦ (hu.hasDerivAt_and_hasDerivAt_deriv hs ht).1)
    (fun t ht ↦ huq t ht ▸ (hu.hasDerivAt_and_hasDerivAt_deriv hs ht).2) hx hy

/-- The Wronskian `ψ φ' - φ ψ'` of the fundamental pair of solutions of `f'' = q f` at `a`, with
`φ(a) = 0`, `φ'(a) = 1` and `ψ(a) = 1`, is identically one. The value `ψ'(a)` is irrelevant,
since it is multiplied by `φ(a) = 0`. -/
theorem wronskian_eq_one_of_hasDerivAt {a : 𝕜}
    (hφ : ∀ t, HasDerivAt φ (φ' t) t) (hφ' : ∀ t, HasDerivAt φ' (q t * φ t) t)
    (hψ : ∀ t, HasDerivAt ψ (ψ' t) t) (hψ' : ∀ t, HasDerivAt ψ' (q t * ψ t) t)
    (hφa : φ a = 0) (hφ'a : φ' a = 1) (hψa : ψ a = 1) (t : 𝕜) :
    ψ t * φ' t - φ t * ψ' t = 1 := by
  rw [wronskian_eq_of_hasDerivAt isOpen_univ isPreconnected_univ (fun t _ ↦ hφ t)
    (fun t _ ↦ hφ' t) (fun t _ ↦ hψ t) (fun t _ ↦ hψ' t) (mem_univ t) (mem_univ a), hφa, hφ'a,
    hψa]
  ring

end TauCeti
