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

For an equation in Sturm–Liouville form `(p f')' + q f = 0`, written out as
`p f'' + p' f' + q f = 0`, the product `p (f g' - f' g)` of `p` with the Wronskian of two
solutions has derivative `(q₁ - q₂) f g` when `f` solves the equation with `q₁` and `g` with
`q₂` (Lagrange's identity). For a common `q` this is Abel's identity: `p (f g' - f' g)` is
constant on every open preconnected set where both solve the equation. Only the values of `p'` and
`q` at the points of the set enter, so no regularity of `q` is needed, and `p` may vanish.

With a first-order term, Abel's identity holds pointwise over any nontrivially normed field: if
`f` and `g` satisfy `y'' + p y' + q y = 0` at a point `t`, the Wronskian `f g' - f' g` has
derivative `-p (f g' - f' g)` at `t`. For `P y'' + Q y' + R y = 0` at a point `t`, where the
scalars `P`, `Q`, `R` are the coefficients evaluated at `t` and `P ≠ 0`, this gives
`-(Q / P) (f g' - f' g)`.

## Main results

* `TauCeti.wronskian_eq_of_hasDerivAt`: the Wronskian of two solutions of `f'' = q f` on a
  preconnected open set is constant.
* `TauCeti.wronskian_eq_of_iteratedDeriv_eq_mul`: the same for `C²` solutions, with the equation
  written with `iteratedDeriv 2` and the Wronskian with `deriv`.
* `TauCeti.wronskian_eq_one_of_hasDerivAt`: the Wronskian of the fundamental pair is one.
* `TauCeti.hasDerivAt_mul_wronskian_of_sturmLiouville`: Lagrange's identity
  `(p (f g' - f' g))' = (q₁ - q₂) f g` for the expanded Sturm–Liouville equation.
* `TauCeti.mul_wronskian_eq_of_sturmLiouville`: Abel's identity, `p (f g' - f' g)` is constant on
  an open preconnected set.
* `HasDerivAt.wronskian_of_secondOrderLinearEquation`: Abel's identity at a point, for
  `y'' + p y' + q y = 0`.
* `DifferentiableAt.hasDerivAt_wronskian_of_secondOrderLinearEquation`: Abel's identity at a
  point `t` for `P y'' + Q y' + R y = 0` with scalar coefficients `P ≠ 0`, `Q`, `R` (the
  coefficients evaluated at `t`), written with `deriv`.

## References

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems*, §3.7 (Abel's identity)
  and Ch. 5 (Sturm–Liouville equations and Lagrange's identity).
-/

public section

open Set

namespace TauCeti

variable {𝕜 : Type*}

section FirstOrderTerm

variable [NontriviallyNormedField 𝕜]

/-- **Abel's identity** at a point: if `f` and `g` have derivatives `f'`, `g'` at `t`, these have
derivatives `f''`, `g''` at `t`, and both satisfy `y'' + p y' + q y = 0` at `t`, then the
Wronskian `f g' - f' g` has derivative `-p (f g' - f' g)` at `t`. -/
theorem _root_.HasDerivAt.wronskian_of_secondOrderLinearEquation {f f' g g' : 𝕜 → 𝕜}
    {f'' g'' p q t : 𝕜}
    (hf : HasDerivAt f (f' t) t) (hf' : HasDerivAt f' f'' t)
    (hg : HasDerivAt g (g' t) t) (hg' : HasDerivAt g' g'' t)
    (hfe : f'' + p * f' t + q * f t = 0) (hge : g'' + p * g' t + q * g t = 0) :
    HasDerivAt (fun s ↦ f s * g' s - f' s * g s) (-p * (f t * g' t - f' t * g t)) t :=
  ((hf.mul hg').sub (hf'.mul hg)).congr_deriv (by linear_combination f t * hge - g t * hfe)

/-- **Abel's identity** at a point `t` for the equation `P y'' + Q y' + R y = 0`, where the
scalars `P`, `Q`, `R` are the coefficients evaluated at `t` and the leading one is `P ≠ 0`: if
`f`, `g`, `f'` and `g'` are differentiable at `t` and `f`, `g` satisfy the equation at `t`, then
the Wronskian `f g' - f' g` has derivative `-(Q / P) (f g' - f' g)` at `t`. -/
theorem _root_.DifferentiableAt.hasDerivAt_wronskian_of_secondOrderLinearEquation {f g : 𝕜 → 𝕜}
    {P Q R t : 𝕜} (hP : P ≠ 0)
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

end FirstOrderTerm

section RCLike

variable {𝔸 : Type*} [RCLike 𝕜] [NormedCommRing 𝔸] [NormedAlgebra 𝕜 𝔸]
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
