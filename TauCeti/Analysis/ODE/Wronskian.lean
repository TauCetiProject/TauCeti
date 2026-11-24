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
derivative `-p (f g' - f' g)` at `t`. For `P y'' + Q y' + R y = 0` at a point `t` with
`P t ≠ 0` this gives `-(Q t / P t) (f g' - f' g)`.

## Main results

* `TauCeti.wronskian_eq_of_hasDerivAt`: the Wronskian of two solutions of `f'' = q f` is
  constant.
* `TauCeti.wronskian_eq_one_of_hasDerivAt`: the Wronskian of the fundamental pair is one.
* `HasDerivAt.wronskian_of_secondOrderLinearEquation`: Abel's identity at a point, for
  `y'' + p y' + q y = 0`.
* `DifferentiableAt.hasDerivAt_wronskian_of_secondOrderLinearEquation`: Abel's identity at a
  point `t` for `P y'' + Q y' + R y = 0` with `P t ≠ 0`, written with `deriv`.
-/

public section

namespace TauCeti

/-- **Abel's identity** at a point: if `f` and `g` have derivatives `f'`, `g'` at `t`, these have
derivatives `f''`, `g''` at `t`, and both satisfy `y'' + p y' + q y = 0` at `t`, then the
Wronskian `f g' - f' g` has derivative `-p (f g' - f' g)` at `t`. -/
theorem _root_.HasDerivAt.wronskian_of_secondOrderLinearEquation {𝕜 : Type*}
    [NontriviallyNormedField 𝕜] {f f' g g' : 𝕜 → 𝕜} {f'' g'' p q t : 𝕜}
    (hf : HasDerivAt f (f' t) t) (hf' : HasDerivAt f' f'' t)
    (hg : HasDerivAt g (g' t) t) (hg' : HasDerivAt g' g'' t)
    (hfe : f'' + p * f' t + q * f t = 0) (hge : g'' + p * g' t + q * g t = 0) :
    HasDerivAt (fun s ↦ f s * g' s - f' s * g s) (-p * (f t * g' t - f' t * g t)) t :=
  ((hf.mul hg').sub (hf'.mul hg)).congr_deriv (by linear_combination f t * hge - g t * hfe)

/-- **Abel's identity** at a point `t` for the equation `P y'' + Q y' + R y = 0` with leading
coefficient `P t ≠ 0`: if `f`, `g`, `f'` and `g'` are differentiable at `t` and `f`, `g` satisfy
the equation at `t`, then the Wronskian `f g' - f' g` has derivative
`-(Q t / P t) (f g' - f' g)` at `t`. -/
theorem _root_.DifferentiableAt.hasDerivAt_wronskian_of_secondOrderLinearEquation {𝕜 : Type*}
    [NontriviallyNormedField 𝕜] {f g : 𝕜 → 𝕜} {P Q R t : 𝕜} (hP : P ≠ 0)
    (hf : DifferentiableAt 𝕜 f t) (hdf : DifferentiableAt 𝕜 (deriv f) t)
    (hg : DifferentiableAt 𝕜 g t) (hdg : DifferentiableAt 𝕜 (deriv g) t)
    (hfe : P * deriv (deriv f) t + Q * deriv f t + R * f t = 0)
    (hge : P * deriv (deriv g) t + Q * deriv g t + R * g t = 0) :
    HasDerivAt (fun s ↦ f s * deriv g s - deriv f s * g s)
      (-(Q / P) * (f t * deriv g t - deriv f t * g t)) t := by
  -- Divided by `P`, the equation is `y'' + p y' + q y = 0`.
  refine hf.hasDerivAt.wronskian_of_secondOrderLinearEquation (q := R / P) hdf.hasDerivAt
    hg.hasDerivAt hdg.hasDerivAt ?_ ?_
  · field_simp
    linear_combination hfe
  · field_simp
    linear_combination hge

variable {𝕜 : Type*} [RCLike 𝕜] {q φ φ' ψ ψ' : 𝕜 → 𝕜}

/-- The Wronskian `ψ φ' - φ ψ'` of two solutions of `f'' = q f` on `ℝ` or `ℂ` is constant. -/
theorem wronskian_eq_of_hasDerivAt
    (hφ : ∀ t, HasDerivAt φ (φ' t) t) (hφ' : ∀ t, HasDerivAt φ' (q t * φ t) t)
    (hψ : ∀ t, HasDerivAt ψ (ψ' t) t) (hψ' : ∀ t, HasDerivAt ψ' (q t * ψ t) t) (t a : 𝕜) :
    ψ t * φ' t - φ t * ψ' t = ψ a * φ' a - φ a * ψ' a := by
  -- Abel's identity with no first-order term: the Wronskian has derivative `0`.
  have hderiv : ∀ t, HasDerivAt (fun r ↦ ψ r * φ' r - φ r * ψ' r) 0 t := fun t ↦ by
    have h := (hψ t).wronskian_of_secondOrderLinearEquation (hψ' t) (hφ t) (hφ' t)
      (p := 0) (q := -q t) (by ring) (by ring)
    simp only [neg_zero, zero_mul] at h
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r ↦ by ring)
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
