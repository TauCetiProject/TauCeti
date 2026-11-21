/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue

/-!
# The Wronskian of a scalar second-order linear equation

For two solutions `φ`, `ψ` of the equation `f'' = q f` over `ℝ` or `ℂ`, without a first-order
term, the Wronskian `ψ φ' - φ ψ'` has derivative `ψ q φ - φ q ψ = 0`, so it is constant. For the
fundamental pair with `φ(a) = 0`, `φ'(a) = 1` and `ψ(a) = 1` it is identically one.

With a first-order term, Abel's identity holds pointwise over any nontrivially normed field: if
`f` and `g` satisfy `y'' + p y' + q y = 0` at a point `t`, the Wronskian `f g' - f' g` has
derivative `-p (f g' - f' g)` at `t`.

## Main results

* `TauCeti.wronskian_eq_of_hasDerivAt`: the Wronskian of two solutions of `f'' = q f` is
  constant.
* `TauCeti.wronskian_eq_one_of_hasDerivAt`: the Wronskian of the fundamental pair is one.
* `TauCeti.hasDerivAt_wronskian_of_hasDerivAt`: Abel's identity at a point, for
  `y'' + p y' + q y = 0`.
-/

public section

namespace TauCeti

/-- **Abel's identity** at a point: if `f` and `g` have derivatives `f'`, `g'` at `t`, these have
derivatives `f''`, `g''` at `t`, and both satisfy `y'' + p y' + q y = 0` at `t`, then the
Wronskian `f g' - f' g` has derivative `-p (f g' - f' g)` at `t`. -/
theorem hasDerivAt_wronskian_of_hasDerivAt {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {f f' g g' : 𝕜 → 𝕜} {f'' g'' p q t : 𝕜}
    (hf : HasDerivAt f (f' t) t) (hf' : HasDerivAt f' f'' t)
    (hg : HasDerivAt g (g' t) t) (hg' : HasDerivAt g' g'' t)
    (hfe : f'' + p * f' t + q * f t = 0) (hge : g'' + p * g' t + q * g t = 0) :
    HasDerivAt (fun s ↦ f s * g' s - f' s * g s) (-p * (f t * g' t - f' t * g t)) t :=
  ((hf.mul hg').sub (hf'.mul hg)).congr_deriv (by linear_combination f t * hge - g t * hfe)

variable {𝕜 : Type*} [RCLike 𝕜] {q φ φ' ψ ψ' : 𝕜 → 𝕜}

/-- The Wronskian `ψ φ' - φ ψ'` of two solutions of `f'' = q f` on `ℝ` or `ℂ` is constant. -/
theorem wronskian_eq_of_hasDerivAt
    (hφ : ∀ t, HasDerivAt φ (φ' t) t) (hφ' : ∀ t, HasDerivAt φ' (q t * φ t) t)
    (hψ : ∀ t, HasDerivAt ψ (ψ' t) t) (hψ' : ∀ t, HasDerivAt ψ' (q t * ψ t) t) (t a : 𝕜) :
    ψ t * φ' t - φ t * ψ' t = ψ a * φ' a - φ a * ψ' a := by
  have hderiv : ∀ t, HasDerivAt (fun r ↦ ψ r * φ' r - φ r * ψ' r) 0 t := fun t ↦
    (((hψ t).mul (hφ' t)).sub ((hφ t).mul (hψ' t))).congr_deriv (by ring)
  exact is_const_of_deriv_eq_zero (fun t ↦ (hderiv t).differentiableAt)
    (fun t ↦ (hderiv t).deriv) t a

/-- The Wronskian `ψ φ' - φ ψ'` of the fundamental pair of solutions of `f'' = q f` at `a`, with
`φ(a) = 0`, `φ'(a) = 1` and `ψ(a) = 1`, is identically one. The value `ψ'(a)` is irrelevant,
since it is multiplied by `φ(a) = 0`. -/
theorem wronskian_eq_one_of_hasDerivAt {a : 𝕜}
    (hφ : ∀ t, HasDerivAt φ (φ' t) t) (hφ' : ∀ t, HasDerivAt φ' (q t * φ t) t)
    (hψ : ∀ t, HasDerivAt ψ (ψ' t) t) (hψ' : ∀ t, HasDerivAt ψ' (q t * ψ t) t)
    (hφa : φ a = 0) (hφ'a : φ' a = 1) (hψa : ψ a = 1) (t : 𝕜) :
    ψ t * φ' t - φ t * ψ' t = 1 := by
  rw [wronskian_eq_of_hasDerivAt hφ hφ' hψ hψ' t a, hφa, hφ'a, hψa]
  ring

end TauCeti
