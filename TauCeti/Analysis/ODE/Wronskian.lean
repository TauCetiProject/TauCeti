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

For an equation in Sturm–Liouville form `(p f')' + q f = 0`, written out as
`p f'' + p' f' + q f = 0`, the product `p (f g' - f' g)` of `p` with the Wronskian of two
solutions has derivative `(q₁ - q₂) f g` when `f` solves the equation with `q₁` and `g` with
`q₂` (Lagrange's identity). For a common `q` this is Abel's identity: `p (f g' - f' g)` is
constant on every open preconnected set where both solve the equation. Only the values of `p'` and
`q` at the points of the set enter, so no regularity of `q` is needed, and `p` may vanish.

## Main results

* `TauCeti.wronskian_eq_of_hasDerivAt`: the Wronskian of two solutions of `f'' = q f` is
  constant.
* `TauCeti.wronskian_eq_one_of_hasDerivAt`: the Wronskian of the fundamental pair is one.
* `TauCeti.hasDerivAt_mul_wronskian_of_sturmLiouville`: Lagrange's identity
  `(p (f g' - f' g))' = (q₁ - q₂) f g` for the expanded Sturm–Liouville equation.
* `TauCeti.mul_wronskian_eq_of_sturmLiouville`: Abel's identity, `p (f g' - f' g)` is constant on
  an open preconnected set.

## References

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems*, §3.7 (Abel's identity)
  and Ch. 5 (Sturm–Liouville equations and Lagrange's identity).
-/

public section

namespace TauCeti

variable {𝕜 : Type*}

section RCLike

variable [RCLike 𝕜] {q φ φ' ψ ψ' : 𝕜 → 𝕜}

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

end RCLike

section SturmLiouville

variable {p f g : 𝕜 → 𝕜}

/-- **Lagrange's identity** for the Sturm–Liouville equation `(p f')' + q f = 0`, written out as
`p f'' + p' f' + q f = 0`. If `f` solves it at `z` with `q = q₁` and `g` with `q = q₂`, then
`p (f g' - f' g)` has derivative `(q₁ - q₂) f g` at `z`. -/
theorem hasDerivAt_mul_wronskian_of_sturmLiouville [NontriviallyNormedField 𝕜] {p' q₁ q₂ z : 𝕜}
    (hp : HasDerivAt p p' z)
    (hf : DifferentiableAt 𝕜 f z) (hf' : DifferentiableAt 𝕜 (deriv f) z)
    (hg : DifferentiableAt 𝕜 g z) (hg' : DifferentiableAt 𝕜 (deriv g) z)
    (hfq : p z * deriv (deriv f) z + p' * deriv f z + q₁ * f z = 0)
    (hgq : p z * deriv (deriv g) z + p' * deriv g z + q₂ * g z = 0) :
    HasDerivAt (fun x ↦ p x * (f x * deriv g x - deriv f x * g x)) ((q₁ - q₂) * f z * g z) z := by
  convert hp.mul ((hf.hasDerivAt.mul hg'.hasDerivAt).sub (hf'.hasDerivAt.mul hg.hasDerivAt))
    using 1
  simp only [Pi.sub_apply, Pi.mul_apply]
  linear_combination g z * hfq - f z * hgq

variable [RCLike 𝕜] {p' q : 𝕜 → 𝕜} {V : Set 𝕜}

/-- **Abel's identity** for the Sturm–Liouville equation `p f'' + p' f' + q f = 0`: the product
`p (f g' - f' g)` of `p` with the Wronskian of two solutions is constant on every open
preconnected set on which both solve the equation. -/
theorem mul_wronskian_eq_of_sturmLiouville (hV : IsOpen V) (hVc : IsPreconnected V)
    (hp : ∀ z ∈ V, HasDerivAt p (p' z) z)
    (hf : DifferentiableOn 𝕜 f V) (hf' : DifferentiableOn 𝕜 (deriv f) V)
    (hg : DifferentiableOn 𝕜 g V) (hg' : DifferentiableOn 𝕜 (deriv g) V)
    (hfq : ∀ z ∈ V, p z * deriv (deriv f) z + p' z * deriv f z + q z * f z = 0)
    (hgq : ∀ z ∈ V, p z * deriv (deriv g) z + p' z * deriv g z + q z * g z = 0)
    {x z : 𝕜} (hx : x ∈ V) (hz : z ∈ V) :
    p x * (f x * deriv g x - deriv f x * g x) = p z * (f z * deriv g z - deriv f z * g z) := by
  have hW (y : 𝕜) (hy : y ∈ V) :
      HasDerivAt (fun x ↦ p x * (f x * deriv g x - deriv f x * g x)) 0 y := by
    have hV' := hV.mem_nhds hy
    simpa using hasDerivAt_mul_wronskian_of_sturmLiouville (hp y hy) (hf.differentiableAt hV')
      (hf'.differentiableAt hV') (hg.differentiableAt hV') (hg'.differentiableAt hV')
      (hfq y hy) (hgq y hy)
  exact hV.is_const_of_deriv_eq_zero hVc
    (fun y hy ↦ (hW y hy).differentiableAt.differentiableWithinAt) (fun y hy ↦ (hW y hy).deriv)
    hx hz

end SturmLiouville

end TauCeti
