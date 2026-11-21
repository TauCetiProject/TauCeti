/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Deriv
import TauCeti.Analysis.Calculus.Taylor.Integral
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# First- and second-order conditions for signed strong convexity

A function `f` on a real normed space that is `m`-strongly convex on a set `s`, in Mathlib's sense
`StrongConvexOn s m f`, lies above each of its tangent paraboloids: if `f` has derivative `f'`
within `s` at `x ∈ s`, then for every `y ∈ s`

`f x + f' (y - x) + m / 2 * ‖y - x‖ ^ 2 ≤ f y`.

Only the derivative of `f` at `x` along the direction `y - x` enters, so the inequality is proved
for a line derivative first and the Fréchet version is deduced from it.

For `m = 0` this is the familiar statement that a differentiable convex function lies above its
tangent hyperplanes. The parameter `m` may be negative, in which case the paraboloid opens
downwards. In an inner product space, with `f'` given by the gradient, this is the inequality that
makes the gradient of a strongly convex potential a subgradient of its potential energy on the
Wasserstein space.

Uniform concavity is preserved by translation. Restriction to an affine line rescales a signed
strong modulus by the squared direction norm. At a point where the derivative is differentiable,
strong concavity and convexity bound the diagonal second derivative; differentiability of the
original function is needed only in a neighbourhood, not continuity of its second derivative.

## References

* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture

## Main results

* `StrongConvexOn.add_add_le_of_hasLineDerivWithinAt`: the first-order condition for strong
  convexity, for a line derivative.
* `StrongConvexOn.add_add_le_of_hasFDerivWithinAt`: the first-order condition for strong convexity,
  for a Fréchet derivative.
-/

public section

open Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {m d : ℝ} {f : E → ℝ}
  {f' : E →L[ℝ] ℝ} {x y : E}

/-- Signed strong concavity is uniform concavity with the quadratic modulus. -/
theorem TauCeti.strongConcaveOn_iff_uniformConcaveOn :
    StrongConcaveOn s m f ↔ UniformConcaveOn s (fun r ↦ m / 2 * r ^ 2) f := Iff.rfl

/-- Negation turns signed strong convexity into signed strong concavity. -/
nonrec theorem StrongConvexOn.neg (hf : StrongConvexOn s m f) : StrongConcaveOn s m (-f) :=
  hf.neg

/-- Negation turns signed strong concavity into signed strong convexity. -/
nonrec theorem StrongConcaveOn.neg (hf : StrongConcaveOn s m f) : StrongConvexOn s m (-f) :=
  hf.neg

/-- **The first-order condition for strong convexity**, for a line derivative. If `f` is
`m`-strongly convex on `s` and has line derivative `d` within `s` at a point `x ∈ s` in the
direction `y - x` of a point `y ∈ s`, then `f x + d + m / 2 * ‖y - x‖ ^ 2 ≤ f y`. -/
theorem StrongConvexOn.add_add_le_of_hasLineDerivWithinAt (hf : StrongConvexOn s m f) (hx : x ∈ s)
    (hy : y ∈ s) (hd : HasLineDerivWithinAt ℝ f d s x (y - x)) :
    f x + d + m / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  -- Restrict `f` to the line through `x` and `y`; the segment between them lies in `s`.
  set g : ℝ → ℝ := fun t ↦ f (x + t • (y - x))
  have hg : HasDerivWithinAt g d (Ioi 0) 0 :=
    HasDerivWithinAt.mono_of_mem_nhdsWithin hd <| mem_of_superset (Ioo_mem_nhdsGT zero_lt_one)
      fun _ ht ↦ hf.1.add_smul_sub_mem hx hy (Ioo_subset_Icc_self ht)
  have hgs : Tendsto (slope g 0) (𝓝[>] 0) (𝓝 d) :=
    (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).1 hg
  -- On `(0, 1)`, strong convexity bounds the slopes of `g` at `0`.
  have hslope : ∀ t ∈ Ioo (0 : ℝ) 1, slope g 0 t ≤
      f y - f x - (1 - t) * (m / 2 * ‖y - x‖ ^ 2) := by
    intro t ht
    have hconv := hf.2 hx hy (sub_nonneg.2 ht.2.le) ht.1.le (sub_add_cancel 1 t)
    have hxy : (1 - t) • x + t • y = x + t • (y - x) := by module
    simp only [hxy, smul_eq_mul, norm_sub_rev x y] at hconv
    simp only [slope_def_field, g, sub_zero, zero_smul, add_zero]
    rw [div_le_iff₀ ht.1]
    nlinarith
  have hlim : Tendsto (fun t : ℝ ↦ f y - f x - (1 - t) * (m / 2 * ‖y - x‖ ^ 2)) (𝓝[>] 0)
      (𝓝 (f y - f x - (1 - 0) * (m / 2 * ‖y - x‖ ^ 2))) :=
    (by fun_prop : Continuous _).continuousWithinAt
  have := le_of_tendsto_of_tendsto hgs hlim (mem_of_superset (Ioo_mem_nhdsGT zero_lt_one) hslope)
  linarith

/-- **The first-order condition for strong convexity.** If `f` is `m`-strongly convex on `s` and
has derivative `f'` within `s` at a point `x ∈ s`, then `f` lies above its tangent paraboloid at `x`
on `s`: `f x + f' (y - x) + m / 2 * ‖y - x‖ ^ 2 ≤ f y` for every `y ∈ s`. -/
theorem StrongConvexOn.add_add_le_of_hasFDerivWithinAt (hf : StrongConvexOn s m f) (hx : x ∈ s)
    (hy : y ∈ s) (hd : HasFDerivWithinAt f f' s x) :
    f x + f' (y - x) + m / 2 * ‖y - x‖ ^ 2 ≤ f y :=
  hf.add_add_le_of_hasLineDerivWithinAt hx hy (hd.hasLineDerivWithinAt _)

/-- Uniform concavity depends only on the values of the function on its domain. -/
theorem UniformConcaveOn.congr {f g : E → ℝ} {ψ : ℝ → ℝ} {s : Set E}
    (hf : UniformConcaveOn s ψ f) (hfg : EqOn f g s) : UniformConcaveOn s ψ g := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy a b ha hb hab
  simpa only [hfg hx, hfg hy, hfg (hf.1 hx hy ha hb hab)] using hf.2 hx hy ha hb hab

/-- Restricting to a convex subset preserves the uniform concavity modulus. -/
theorem UniformConcaveOn.subset {f : E → ℝ} {ψ : ℝ → ℝ} {s T : Set E}
    (hf : UniformConcaveOn T ψ f) (hst : s ⊆ T) (hs : Convex ℝ s) :
    UniformConcaveOn s ψ f :=
  ⟨hs, fun _ hx _ hy _ _ ha hb hab ↦ hf.2 (hst hx) (hst hy) ha hb hab⟩

/-- Signed strong concavity depends only on values on the domain. -/
nonrec theorem StrongConcaveOn.congr {g : E → ℝ} (hf : StrongConcaveOn s m f)
    (hfg : EqOn f g s) : StrongConcaveOn s m g :=
  hf.congr hfg

/-- Restriction to a convex subset preserves signed strong concavity. -/
nonrec theorem StrongConcaveOn.subset {T : Set E} (hf : StrongConcaveOn T m f)
    (hst : s ⊆ T) (hs : Convex ℝ s) : StrongConcaveOn s m f :=
  hf.subset hst hs

/-- Translating arguments preserves a uniform concavity modulus on any convex subset
whose translated points belong to the original domain. -/
theorem UniformConcaveOn.comp_sub {f : E → ℝ} {ψ : ℝ → ℝ} {s T : Set E}
    (hf : UniformConcaveOn T ψ f) (hs : Convex ℝ s) (t : E)
    (hsub : ∀ x ∈ s, x - t ∈ T) : UniformConcaveOn s ψ (fun x ↦ f (x - t)) := by
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := hf.2 (hsub x hx) (hsub y hy) ha hb hab
  have ht : a • (x - t) + b • (y - t) = (a • x + b • y) - t := by
    have hb : b = 1 - a := by linarith
    rw [hb]
    module
  simpa only [ht, sub_sub_sub_cancel_right] using h

/-- Restriction to an affine line rescales the signed strong concavity modulus by `‖v‖²`. -/
theorem StrongConcaveOn.comp_add_smul {f : E → ℝ} {U : Set E} {m : ℝ}
    (hconc : StrongConcaveOn U m f) (x v : E) :
    StrongConcaveOn ((fun t : ℝ ↦ x + t • v) ⁻¹' U) (m * ‖v‖ ^ 2)
      (fun t : ℝ ↦ f (x + t • v)) := by
  rw [TauCeti.strongConcaveOn_iff_uniformConcaveOn] at hconc ⊢
  have hA (s t a b : ℝ) (hab : a + b = 1) :
      a • (x + s • v) + b • (x + t • v) = x + (a * s + b * t) • v := by
    have hb : b = 1 - a := by linarith
    rw [hb]
    module
  refine ⟨?_, ?_⟩
  · intro s hs t ht a b ha hb hab
    simpa only [mem_preimage, smul_eq_mul, ← hA s t a b hab] using
      hconc.1 hs ht ha hb hab
  · intro s hs t ht a b ha hb hab
    have h := hconc.2 hs ht ha hb hab
    have hd : x + s • v - (x + t • v) = (s - t) • v := by module
    simp only [hA s t a b hab, hd, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs, smul_eq_mul] at h
    simp only [smul_eq_mul, Real.norm_eq_abs, sq_abs]
    convert h using 1; ring

/-- Restriction to an affine line rescales the signed strong convexity modulus by `‖v‖²`. -/
theorem StrongConvexOn.comp_add_smul {f : E → ℝ} {U : Set E} {m : ℝ}
    (hconv : StrongConvexOn U m f) (x v : E) :
    StrongConvexOn ((fun t : ℝ ↦ x + t • v) ⁻¹' U) (m * ‖v‖ ^ 2)
      (fun t : ℝ ↦ f (x + t • v)) := by
  simpa only [Pi.neg_def, neg_neg] using
    (StrongConcaveOn.comp_add_smul hconv.neg x v).neg

/-- Signed strong concavity bounds the second derivative at an interior point where the
first derivative is differentiable; the original function need only be differentiable nearby. -/
theorem StrongConcaveOn.fderiv_fderiv_self_le {f : E → ℝ} {U : Set E} {m : ℝ}
    (hconc : StrongConcaveOn U m f) {x : E} (hx : U ∈ 𝓝 x)
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y)
    (hf' : DifferentiableAt ℝ (fderiv ℝ f) x) (v : E) :
    fderiv ℝ (fderiv ℝ f) x v v ≤ -m * ‖v‖ ^ 2 := by
  let A : ℝ → E := fun t ↦ x + t • v
  let q : ℝ → ℝ := fun t ↦ f (A t) + (m * ‖v‖ ^ 2) / 2 * t ^ 2
  have htend : Tendsto A (𝓝 0) (𝓝 x) :=
    Continuous.tendsto' (by fun_prop) 0 x (by simp [A])
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), A t ∈ U ∧ DifferentiableAt ℝ f (A t) :=
    (htend.eventually_mem hx).and (htend.eventually hf)
  obtain ⟨r, hr, hrsub⟩ := Metric.eventually_nhds_iff_ball.1 hnear
  have hq : ConcaveOn ℝ (Metric.ball (0 : ℝ) r) q := by
    have hc := strongConcaveOn_iff_convex.mp (hconc.comp_add_smul x v)
    simpa only [q, A, Real.norm_eq_abs, sq_abs] using
      hc.subset (fun t ht ↦ mem_preimage.2 (hrsub t ht).1) (convex_ball _ _)
  have hd (t : ℝ) (ht : t ∈ Metric.ball (0 : ℝ) r) : DifferentiableAt ℝ q t :=
    ((hrsub t ht).2.comp t (by fun_prop : DifferentiableAt ℝ A t)).add (by fun_prop)
  have hn : deriv (deriv q) 0 ≤ 0 := by
    rw [← derivWithin_of_mem_nhds (Metric.ball_mem_nhds 0 hr)]
    exact (hq.antitoneOn_deriv hd).derivWithin_nonpos
  rw [TauCeti.deriv_deriv_quadratic_add_line hf hf' v (m * ‖v‖ ^ 2)] at hn
  linarith

/-- Signed strong convexity bounds the second derivative at an interior point where the
first derivative is differentiable; the original function need only be differentiable nearby. -/
theorem StrongConvexOn.le_fderiv_fderiv_self {f : E → ℝ} {U : Set E} {m : ℝ}
    (hconv : StrongConvexOn U m f) {x : E} (hx : U ∈ 𝓝 x)
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y)
    (hf' : DifferentiableAt ℝ (fderiv ℝ f) x) (v : E) :
    m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  have hneg : DifferentiableAt ℝ (fderiv ℝ (-f)) x := by
    have heq : fderiv ℝ (-f) = -(fderiv ℝ f) := funext fun _ ↦ fderiv_neg
    rw [heq]
    exact hf'.neg
  have h := StrongConcaveOn.fderiv_fderiv_self_le hconv.neg hx
    (hf.mono fun _ hy ↦ hy.neg) hneg v
  rw [TauCeti.fderiv_fderiv_neg] at h
  simpa only [neg_apply, neg_mul, neg_le_neg_iff] using h
