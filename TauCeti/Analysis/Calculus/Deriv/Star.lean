/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Derivatives and the star operation

If `f (conj w) = conj (f w)` for every `w`, then the derivative of `f` commutes with conjugation
too. This is Mathlib's `deriv_conj_conj` for a function with `conj ∘ f ∘ conj = f`.

If a curve `f` in a normed star algebra preserves `a` in the sense that `star (f s) * a * f s = a`
near `t`, its derivative is skew for `a`: `star f' * a * f t + star (f t) * a * f' = 0`. At a
point where `f t = 1` this says that `a * f'` is skew-adjoint; for matrices it says that the
velocity at the identity of a curve in the unitary group of a Gram matrix lies in its Lie algebra.

## Main results

* `TauCeti.deriv_conj_of_forall_conj` — `deriv f (conj z) = conj (deriv f z)` when `f` commutes with
  conjugation.
* `HasDerivAt.star_mul_mul_add_star_mul_mul_eq_zero` — the derivative of a curve preserving `a` is
  skew for `a`.
-/

public section

open scoped ComplexConjugate
open Filter Topology

/-- **Velocities of curves preserving a form are skew.** If `star (f s) * a * f s = a` for `s` near
`t` and `f` has derivative `f'` at `t`, then `star f' * a * f t + star (f t) * a * f' = 0`. -/
theorem HasDerivAt.star_mul_mul_add_star_mul_mul_eq_zero {𝕜 𝔸 : Type*}
    [NontriviallyNormedField 𝕜] [StarRing 𝕜] [TrivialStar 𝕜] [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸]
    [StarRing 𝔸] [StarModule 𝕜 𝔸] [ContinuousStar 𝔸] {f : 𝕜 → 𝔸} {f' a : 𝔸} {t : 𝕜}
    (hf : HasDerivAt f f' t) (ha : ∀ᶠ s in 𝓝 t, star (f s) * a * f s = a) :
    star f' * a * f t + star (f t) * a * f' = 0 :=
  ((hf.star.mul_const a).mul hf).unique ((hasDerivAt_const t a).congr_of_eventuallyEq ha)

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [StarRing 𝕜] [NormedStarGroup 𝕜]

namespace TauCeti

/-- If `f` commutes with conjugation, then so does its derivative. -/
theorem deriv_conj_of_forall_conj {f : 𝕜 → 𝕜} (hf : ∀ w, f (conj w) = conj (f w)) (z : 𝕜) :
    deriv f (conj z) = conj (deriv f z) := by
  have h : conj ∘ f ∘ conj = f := funext fun w => by simp [hf]
  simpa [h] using congrFun (deriv_conj_conj (f := f)) (conj z)

end TauCeti
