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
import Mathlib.Analysis.Calculus.LocalExtr.Basic

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
gradient of a convex potential becomes a transport map.

## Main statements

* `TauCeti.ae_eventually_ne_top_and_differentiableAt_toReal` — **Rademacher's theorem for
  extended-real convex functions**: at almost every point of the effective domain, `f` is finite
  nearby and differentiable;
* `TauCeti.hasFDerivAt_apply_eq_of_mem_subdifferential` and
  `TauCeti.fderiv_apply_eq_of_mem_subdifferential` — at an interior point of the effective
  domain where `f` is differentiable, every subgradient is the derivative;
* `TauCeti.hasGradientAt_toReal_of_mem_subdifferential` and
  `TauCeti.gradient_toReal_eq_of_mem_subdifferential` — the same statement for the inner product,
  where every subgradient is the gradient.

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

end InnerProduct

end TauCeti
