/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Rademacher
public import TauCeti.Analysis.Convex.EffectiveDomain
public import TauCeti.Analysis.Convex.Subdifferential
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Deriv

/-!
# Differentiability of extended-real convex functions

A convex function `f : E → EReal` is one whose real epigraph `{(x, r) | f x ≤ r}` is convex, the
convention of `TauCeti.convex_epigraph_fenchelConjugate`; Legendre–Fenchel conjugates are the
basic examples. This file connects such functions to Mathlib's real-valued convexity and
differentiability theory.

The effective-domain and real-representative convexity bridges are in
`TauCeti.Analysis.Convex.EffectiveDomain`. In finite dimension, Rademacher's theorem for convex
functions applies: at almost every point of the effective domain, `f` is finite on a
neighbourhood and the real representative
is differentiable (`TauCeti.ae_eventually_ne_top_and_differentiableAt_toReal`). This is the
almost-everywhere differentiability of convex potentials used to turn optimal plans into
transport maps, as in Brenier's theorem.

At such a point the subdifferential of `f` for a pairing `B` reduces to the derivative:
every subgradient `y` satisfies `D f (x) v = B v y` for all `v`
(`TauCeti.hasFDerivAt_apply_eq_of_mem_subdifferential`). This needs neither convexity nor finite
dimension. On a real inner product space, with the inner product as pairing, the subgradient is
then the gradient (`TauCeti.hasGradientAt_toReal_of_mem_subdifferential`): this is how the
gradient of a convex potential becomes a transport map. Conversely, for a convex `f` the
derivative at any point of the effective domain where the real representative is differentiable
is a subgradient (`TauCeti.mem_subdifferential_of_hasFDerivAt`), since a convex function of one
variable lies above its tangent lines; this is how the gradient of a convex potential is shown to
be an optimal transport map. Near such a point every subgradient is close to the gradient
(`TauCeti.eventually_forall_mem_subdifferential_norm_sub_le`): the subdifferential is outer
semicontinuous at points of differentiability, again with no convexity assumption.

## Main statements

* `TauCeti.ae_eventually_ne_top_and_differentiableAt_toReal` — **Rademacher's theorem for
  extended-real convex functions**: at almost every point of the effective domain, `f` is finite
  nearby and differentiable;
* `TauCeti.hasFDerivAt_apply_eq_of_mem_subdifferential` and
  `TauCeti.fderiv_apply_eq_of_mem_subdifferential` — at an interior point of the effective
  domain where `f` is differentiable, every subgradient is the derivative;
* `TauCeti.hasGradientAt_toReal_of_mem_subdifferential` and
  `TauCeti.gradient_toReal_eq_of_mem_subdifferential` — the same statement for the inner product,
  where every subgradient is the gradient;
* `TauCeti.mem_subdifferential_of_hasFDerivAt` and `TauCeti.gradient_toReal_mem_subdifferential`
  — for a convex function, the derivative, respectively the gradient, at a point of
  differentiability in the effective domain is a subgradient.
* `TauCeti.eventually_forall_mem_subdifferential_norm_sub_le` — near a point where `f` is finite
  nearby and differentiable, every subgradient is close to the gradient.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton Mathematical Series 28, 1970, §4 (effective
  domains), Theorem 25.1 (subgradients at points of differentiability) and Theorem 25.5
  (almost-everywhere differentiability).
* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003,
  §2.1, for the use of these facts in the proof of Brenier's theorem.
-/

public section

namespace TauCeti

open Filter MeasureTheory MeasureTheory.Measure Set
open scoped Topology

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal}

/-- **Rademacher's theorem for extended-real convex functions.** Let `f : E → EReal` have convex
real epigraph and never take the value `⊥`, on a finite-dimensional real normed space `E` with an
additive Haar measure `μ`. Then at `μ`-almost every point `x` of the effective domain, `f` is
finite on a neighbourhood of `x` and its real representative `x ↦ (f x).toReal` is
differentiable at `x`. -/
theorem ae_eventually_ne_top_and_differentiableAt_toReal [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsAddHaarMeasure μ]
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) :
    ∀ᵐ x ∂μ, f x ≠ ⊤ →
      (∀ᶠ x' in 𝓝 x, f x' ≠ ⊤) ∧ DifferentiableAt ℝ (fun x' => (f x').toReal) x := by
  filter_upwards [(convex_setOf_ne_top hf).ae_mem_interior,
    (convexOn_toReal hf hbot).ae_differentiableAt_of_mem_interior] with x h₁ h₂ hx
  exact ⟨mem_interior_iff_mem_nhds.1 (h₁ hx), h₂ (h₁ hx)⟩

variable {F : Type*} [AddCommMonoid F] [Module ℝ F] (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {x : E} {y : F}

/-- **Subgradients at a point of differentiability.** If `f : E → EReal` is finite near `x`, its
real representative has derivative `f'` at `x`, and `y` is a subgradient of `f` at `x` for the
pairing `B`, then `f' v = B v y` for every `v`: the subdifferential at `x` consists of
representatives of the derivative. -/
theorem hasFDerivAt_apply_eq_of_mem_subdifferential {f' : E →L[ℝ] ℝ}
    (hy : y ∈ subdifferential B f x) (hdom : ∀ᶠ x' in 𝓝 x, f x' ≠ ⊤)
    (hf : HasFDerivAt (fun x' => (f x').toReal) f' x) (v : E) : f' v = B v y := by
  -- Along the line `t ↦ x + t • v`, the function `t ↦ (f (x + t • v)).toReal - t * B v y`
  -- has a local minimum at `0`, by the subgradient inequality, and derivative `f' v - B v y`.
  obtain ⟨r, hr⟩ : ∃ r : ℝ, f x = r :=
    ⟨_, (EReal.coe_toReal (ne_top_of_mem_subdifferential B hy)
      (ne_bot_of_mem_subdifferential B hy)).symm⟩
  have hderiv : HasDerivAt (fun t : ℝ => (f (x + t • v)).toReal - t * B v y)
      (f' v - B v y) 0 := by
    have := (hf.hasLineDerivAt v).sub
      ((hasDerivAt_id (0 : ℝ)).mul_const (B v y))
    rw [one_mul] at this
    exact this
  have hmin : IsLocalMin (fun t : ℝ => (f (x + t • v)).toReal - t * B v y) 0 := by
    have hcont : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
      exact Continuous.tendsto' (by fun_prop) 0 x (by simp)
    filter_upwards [hcont.eventually hdom] with t ht
    have hle : ((r + t * B v y : ℝ) : EReal) ≤ f (x + t • v) := by
      have := add_le_of_mem_subdifferential B hy (x + t • v)
      have hpair : B (x + t • v - x) y = t * B v y := by simp
      simpa only [hr, hpair, EReal.coe_add, EReal.coe_mul] using this
    have := EReal.toReal_le_toReal hle (EReal.coe_ne_bot _) ht
    simp only [EReal.toReal_coe] at this
    simp only [zero_smul, add_zero, hr, EReal.toReal_coe, zero_mul, sub_zero]
    linarith
  exact sub_eq_zero.1 (hmin.hasDerivAt_eq_zero hderiv)

/-- The `fderiv` form of `TauCeti.hasFDerivAt_apply_eq_of_mem_subdifferential`: at a point where
`f` is finite nearby and differentiable, every subgradient `y` satisfies
`fderiv ℝ (fun x' => (f x').toReal) x v = B v y` for every `v`. -/
theorem fderiv_apply_eq_of_mem_subdifferential (hy : y ∈ subdifferential B f x)
    (hdom : ∀ᶠ x' in 𝓝 x, f x' ≠ ⊤) (hf : DifferentiableAt ℝ (fun x' => (f x').toReal) x)
    (v : E) : fderiv ℝ (fun x' => (f x').toReal) x v = B v y :=
  hasFDerivAt_apply_eq_of_mem_subdifferential B hy hdom hf.hasFDerivAt v

/-- **Derivatives of convex functions are subgradients.** Let `f : E → EReal` have convex real
epigraph and never take the value `⊥`, and let `x` be a point of the effective domain at which the
real representative `x' ↦ (f x').toReal` has derivative `f'`. If `y` represents `f'` for the
pairing `B`, that is `f' v = B v y` for every `v`, then `y` is a subgradient of `f` at `x`. -/
theorem mem_subdifferential_of_hasFDerivAt (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hbot : ∀ x, f x ≠ ⊥) (hx : f x ≠ ⊤) {f' : E →L[ℝ] ℝ}
    (hd : HasFDerivAt (fun x' => (f x').toReal) f' x) (hy : ∀ v, f' v = B v y) :
    y ∈ subdifferential B f x := by
  refine (mem_subdifferential_iff_forall_toReal_add_le B hbot hx).2 fun x' hx' => ?_
  -- On the segment from `x` to `x'`, which lies in the effective domain, the real representative
  -- is a convex function of one variable, with derivative `f' (x' - x)` at `0`.
  have hconv : ConvexOn ℝ (Icc 0 1) fun t : ℝ => (f (AffineMap.lineMap x x' t)).toReal :=
    ((convexOn_toReal hf hbot).comp_affineMap (AffineMap.lineMap x x')).subset
      (fun _ ht => (convex_setOf_ne_top hf).lineMap_mem hx hx' ht) (convex_Icc 0 1)
  have hderiv : HasDerivAt (fun t : ℝ => (f (AffineMap.lineMap x x' t)).toReal)
      (f' (x' - x)) 0 := by
    have hd' : HasFDerivAt (fun x' => (f x').toReal) f' (AffineMap.lineMap x x' (0 : ℝ)) := by
      rwa [AffineMap.lineMap_apply_zero]
    exact hd'.comp_hasDerivAt (0 : ℝ) AffineMap.hasDerivAt_lineMap
  have hslope := hconv.le_slope_of_hasDerivAt (left_mem_Icc.2 zero_le_one)
    (right_mem_Icc.2 zero_le_one) zero_lt_one hderiv
  rw [slope_def_field, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one, sub_zero,
    div_one, hy] at hslope
  linarith

end Normed

section InnerProduct

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → EReal} {x y : E}

/-- **Subgradients at a point of differentiability are gradients.** If `f : E → EReal` is finite
near `x`, its real representative is differentiable at `x`, and `y` is a subgradient of `f` at `x`
for the inner product, then `y` is the gradient of the real representative at `x`. -/
theorem hasGradientAt_toReal_of_mem_subdifferential (hy : y ∈ subdifferential (innerₗ E) f x)
    (hdom : ∀ᶠ x' in 𝓝 x, f x' ≠ ⊤) (hf : DifferentiableAt ℝ (fun x' => (f x').toReal) x) :
    HasGradientAt (fun x' => (f x').toReal) y x := by
  have hderiv : toDual ℝ E y = fderiv ℝ (fun x' => (f x').toReal) x := by
    ext v
    rw [fderiv_apply_eq_of_mem_subdifferential (innerₗ E) hy hdom hf v, toDual_apply_apply,
      innerₗ_apply_apply, real_inner_comm]
  rw [hasGradientAt_iff_hasFDerivAt, hderiv]
  exact hf.hasFDerivAt

/-- The `gradient` form of `TauCeti.hasGradientAt_toReal_of_mem_subdifferential`: at a point where
`f` is finite nearby and differentiable, every subgradient for the inner product is the gradient of
the real representative. -/
theorem gradient_toReal_eq_of_mem_subdifferential (hy : y ∈ subdifferential (innerₗ E) f x)
    (hdom : ∀ᶠ x' in 𝓝 x, f x' ≠ ⊤) (hf : DifferentiableAt ℝ (fun x' => (f x').toReal) x) :
    gradient (fun x' => (f x').toReal) x = y :=
  (hasGradientAt_toReal_of_mem_subdifferential hy hdom hf).gradient

/-- **Gradients of convex functions are subgradients.** If `f : E → EReal` has convex real
epigraph, never takes the value `⊥`, and is finite at `x`, where its real representative is
differentiable, then the gradient of the real representative at `x` is a subgradient of `f` at
`x` for the inner product. -/
theorem gradient_toReal_mem_subdifferential (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hbot : ∀ x, f x ≠ ⊥) (hx : f x ≠ ⊤)
    (hd : DifferentiableAt ℝ (fun x' => (f x').toReal) x) :
    gradient (fun x' => (f x').toReal) x ∈ subdifferential (innerₗ E) f x :=
  mem_subdifferential_of_hasFDerivAt (innerₗ E) hf hbot hx hd.hasFDerivAt fun v => by
    rw [← toDual_gradient, toDual_apply_apply, innerₗ_apply_apply, real_inner_comm]

/-- **Subgradients near a point of differentiability are close to the gradient.** If `f : E → EReal`
is finite near `x` and its real representative has gradient `y` at `x`, then for every `ε > 0`,
every subgradient of `f` at every point close enough to `x` lies within `ε` of `y`. No convexity
is needed. -/
theorem eventually_forall_mem_subdifferential_norm_sub_le
    (hdom : ∀ᶠ x' in 𝓝 x, f x' ≠ ⊤) (hd : HasGradientAt (fun x' => (f x').toReal) y x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x' in 𝓝 x, ∀ y' ∈ subdifferential (innerₗ E) f x', ‖y' - y‖ ≤ ε := by
  -- On a ball of radius `r` about `x`, `f` is finite and its real representative is within
  -- `ε / 6 * r` of its first-order expansion. A subgradient `y'` at a point `x'` of the ball of
  -- radius `r / 3` is tested along the step of length `r / 3` from `x'` in the direction `y' - y`.
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1
    (hdom.and ((hasGradientAt_iff_isLittleO.1 hd).def (show 0 < ε / 6 by positivity)))
  have hexp : ∀ z, dist z x < r →
      |(f z).toReal - (f x).toReal - ⟪y, z - x⟫_ℝ| ≤ ε / 6 * r := fun z hz => by
    have h := (hball hz).2
    rw [Real.norm_eq_abs] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [← dist_eq_norm]
    exact hz.le
  rw [Metric.eventually_nhds_iff]
  refine ⟨r / 3, by positivity, fun x' hx' y' hy' => ?_⟩
  rcases eq_or_ne y' y with rfl | hne
  · simpa using hε.le
  have hpos : 0 < ‖y' - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  set t := r / 3 / ‖y' - y‖
  set x'' := x' + t • (y' - y)
  have hxx : x'' - x = (x' - x) + t • (y' - y) := by
    simp only [x'']
    abel
  have hx'' : dist x'' x < r := by
    have : ‖t • (y' - y)‖ = r / 3 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), div_mul_cancel₀ _ hpos.ne']
    rw [dist_eq_norm, hxx]
    calc ‖x' - x + t • (y' - y)‖ ≤ ‖x' - x‖ + ‖t • (y' - y)‖ := norm_add_le _ _
      _ < r := by rw [this, ← dist_eq_norm]; linarith
  have hsub := toReal_add_le_toReal_of_mem_subdifferential (innerₗ E) hy' (hball hx'').1
  simp only [innerₗ_apply_apply, x'', add_sub_cancel_left, inner_smul_left,
    RCLike.conj_to_real] at hsub
  have h₁ := (abs_le.1 (hexp x'' hx'')).2
  have h₂ := (abs_le.1 (hexp x' (hx'.trans (by linarith)))).1
  rw [hxx, inner_add_right, inner_smul_right] at h₁
  have hw : ⟪y' - y, y'⟫_ℝ - ⟪y, y' - y⟫_ℝ = ‖y' - y‖ ^ 2 := by
    rw [real_inner_comm (y' - y) y, ← inner_sub_right, real_inner_self_eq_norm_sq]
  have ht : t * ‖y' - y‖ ^ 2 = r / 3 * ‖y' - y‖ := by
    simp only [t]
    field_simp
  have : r / 3 * ‖y' - y‖ ≤ r / 3 * ε := by
    rw [← ht, ← hw, mul_sub]
    linarith
  exact le_of_mul_le_mul_left this (by positivity)

end InnerProduct

end TauCeti
