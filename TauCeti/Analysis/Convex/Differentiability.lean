/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Rademacher
public import TauCeti.Analysis.Convex.Subdifferential
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Differentiability of extended-real convex functions

A convex function `f : E → EReal` is one whose real epigraph `{(x, r) | f x ≤ r}` is convex, the
convention of `TauCeti.convex_epigraph_fenchelConjugate`; Legendre–Fenchel conjugates are the
basic examples. This file connects such functions to Mathlib's real-valued convexity and
differentiability theory.

The *effective domain* `{x | f x ≠ ⊤}` is the image of the epigraph under the first projection,
hence convex (`TauCeti.convex_setOf_ne_top`). If `f` never takes the value `⊥`, then on the
effective domain `f` agrees with its real representative `x ↦ (f x).toReal`
(`EReal.coe_toReal`), which is convex there in Mathlib's sense (`TauCeti.convexOn_toReal`).
Consequently, in finite dimension, Rademacher's theorem for convex functions applies: at almost
every point of the effective domain, `f` is finite on a neighbourhood and the real representative
is differentiable (`TauCeti.ae_eventually_ne_top_and_differentiableAt_toReal`). This is the
almost-everywhere differentiability of convex potentials used to turn optimal plans into
transport maps, as in Brenier's theorem.

At such a point the subdifferential of `f` for a pairing `B` reduces to the derivative:
every subgradient `y` satisfies `D f (x) v = B v y` for all `v`
(`TauCeti.hasFDerivAt_apply_eq_of_mem_subdifferential`). This needs neither convexity nor finite
dimension.

## Main statements

* `TauCeti.convex_setOf_ne_top` — the effective domain of a convex function is convex;
* `TauCeti.convexOn_toReal` — a convex function that never takes the value `⊥` has a real
  representative that is convex on the effective domain;
* `TauCeti.ae_eventually_ne_top_and_differentiableAt_toReal` — **Rademacher's theorem for
  extended-real convex functions**: at almost every point of the effective domain, `f` is finite
  nearby and differentiable;
* `TauCeti.hasFDerivAt_apply_eq_of_mem_subdifferential` and
  `TauCeti.fderiv_apply_eq_of_mem_subdifferential` — at an interior point of the effective
  domain where `f` is differentiable, every subgradient is the derivative.

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

section Module

variable {E : Type*} [AddCommMonoid E] [Module ℝ E] {f : E → EReal}

/-- The effective domain `{x | f x ≠ ⊤}` of a function with convex real epigraph is convex: it is
the image of the epigraph under the first projection. -/
theorem convex_setOf_ne_top (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) :
    Convex ℝ {x | f x ≠ ⊤} := by
  have hdom : {x | f x ≠ ⊤} = Prod.fst '' {p : E × ℝ | f p.1 ≤ p.2} := by
    ext x
    simp only [mem_ofPred_eq, mem_image, Prod.exists, exists_and_right, exists_eq_right]
    exact ⟨fun h => ⟨_, EReal.le_coe_toReal h⟩,
      fun ⟨r, hr⟩ => ne_top_of_le_ne_top (EReal.coe_ne_top r) hr⟩
  rw [hdom]
  exact hf.is_linear_image (LinearMap.fst ℝ E ℝ).isLinear

/-- **The real representative of a convex function.** If `f : E → EReal` has convex real epigraph
and never takes the value `⊥`, then `x ↦ (f x).toReal` is convex on the effective domain
`{x | f x ≠ ⊤}`, where it agrees with `f` by `EReal.coe_toReal`. -/
theorem convexOn_toReal (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) :
    ConvexOn ℝ {x | f x ≠ ⊤} fun x => (f x).toReal := by
  refine ⟨convex_setOf_ne_top hf, fun x hx y hy a b ha hb hab => ?_⟩
  have h := hf (x := (x, (f x).toReal)) (y := (y, (f y).toReal))
    (EReal.le_coe_toReal hx) (EReal.le_coe_toReal hy) ha hb hab
  simp only [mem_ofPred_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
    smul_eq_mul] at h
  have h' : f (a • x + b • y) ≤ ((a * (f x).toReal + b * (f y).toReal : ℝ) : EReal) := by
    exact_mod_cast h
  have h'' := EReal.toReal_le_toReal h' (hbot _) (EReal.coe_ne_top _)
  rw [EReal.toReal_coe] at h''
  simpa only [smul_eq_mul] using h''

end Module

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
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hderiv : HasDerivAt (fun t : ℝ => (f (x + t • v)).toReal - t * B v y)
      (f' v - B v y) 0 := by
    have := (hf.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)).sub
      ((hasDerivAt_id (0 : ℝ)).mul_const (B v y))
    rw [one_mul] at this
    exact this
  have hmin : IsLocalMin (fun t : ℝ => (f (x + t • v)).toReal - t * B v y) 0 := by
    have hcont : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
      simpa using hline.continuousAt.tendsto
    filter_upwards [hcont.eventually hdom] with t ht
    have hle : ((r + t * B v y : ℝ) : EReal) ≤ f (x + t • v) := by
      have := add_le_of_mem_subdifferential B hy (x + t • v)
      rwa [hr, add_sub_cancel_left, map_smul, LinearMap.smul_apply, smul_eq_mul,
        ← EReal.coe_add] at this
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

end TauCeti
