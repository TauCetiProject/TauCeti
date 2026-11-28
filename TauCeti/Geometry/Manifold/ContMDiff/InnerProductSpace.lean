/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Smooth orthogonal projections in real inner product spaces

For a `C^k` map `s : M → E` into a real inner product space `E` and a `C^k` map `u : M → E`, the
complementary orthogonal projection `y ↦ (ℝ ∙ s y)ᗮ.starProjection (u y)` onto the hyperplane
orthogonal to `s y` is `C^k` wherever `s` is nonzero.

## Main results

* `TauCeti.contMDiffWithinAt_starProjection_orthogonal_span_singleton`,
  `TauCeti.contMDiffAt_starProjection_orthogonal_span_singleton`,
  `TauCeti.contMDiffOn_starProjection_orthogonal_span_singleton`,
  `TauCeti.contMDiff_starProjection_orthogonal_span_singleton`: `C^k` regularity of
  `y ↦ (ℝ ∙ s y)ᗮ.starProjection (u y)` away from zeros of `s`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 10.
-/

public noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

section OrthogonalSpanSingleton

variable {X H M E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace H] {I : ModelWithCorners ℝ X H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {k : ℕ∞ω} {s u : M → E}

/-- If `s` and `u` are `C^k` maps into an inner product space `E` within `t` at `x` with
`s x ≠ 0`, then `y ↦ (ℝ ∙ s y)ᗮ.starProjection (u y)` is `C^k` within `t` at `x`. -/
theorem contMDiffWithinAt_starProjection_orthogonal_span_singleton {t : Set M} {x : M}
    (hs : ContMDiffWithinAt I 𝓘(ℝ, E) k s t x) (hu : ContMDiffWithinAt I 𝓘(ℝ, E) k u t x)
    (hsx : s x ≠ 0) :
    ContMDiffWithinAt I 𝓘(ℝ, E) k (fun y ↦ (ℝ ∙ s y)ᗮ.starProjection (u y)) t x := by
  have hnum : ContMDiffWithinAt I 𝓘(ℝ) k (fun y ↦ inner ℝ (s y) (u y)) t x :=
    contDiff_inner.contMDiff.contMDiffAt.comp_contMDiffWithinAt x (hs.prodMk_space hu)
  have hden : ContMDiffWithinAt I 𝓘(ℝ) k (fun y ↦ inner ℝ (s y) (s y)) t x :=
    contDiff_inner.contMDiff.contMDiffAt.comp_contMDiffWithinAt x (hs.prodMk_space hs)
  have hsub : ContMDiffWithinAt I 𝓘(ℝ, E) k
      (fun y ↦ u y - (inner ℝ (s y) (u y) * (inner ℝ (s y) (s y))⁻¹) • s y) t x :=
    hu.sub ((hnum.mul (hden.inv₀ (inner_self_ne_zero.mpr hsx))).smul hs)
  have hformula (y : M) :
      (ℝ ∙ s y)ᗮ.starProjection (u y) =
        u y - (inner ℝ (s y) (u y) * (inner ℝ (s y) (s y))⁻¹) • s y := by
    simp only [Submodule.starProjection_orthogonal_val, Submodule.starProjection_singleton,
      RCLike.ofReal_real_eq_id, id_eq, div_eq_mul_inv, real_inner_self_eq_norm_sq]
  exact hsub.congr_of_eventuallyEq (Filter.Eventually.of_forall hformula) (hformula x)

/-- If `s` and `u` are `C^k` maps into an inner product space `E` at `x` with `s x ≠ 0`, then
`y ↦ (ℝ ∙ s y)ᗮ.starProjection (u y)` is `C^k` at `x`. -/
theorem contMDiffAt_starProjection_orthogonal_span_singleton {x : M}
    (hs : ContMDiffAt I 𝓘(ℝ, E) k s x) (hu : ContMDiffAt I 𝓘(ℝ, E) k u x) (hsx : s x ≠ 0) :
    ContMDiffAt I 𝓘(ℝ, E) k (fun y ↦ (ℝ ∙ s y)ᗮ.starProjection (u y)) x :=
  contMDiffWithinAt_univ.mp <|
    contMDiffWithinAt_starProjection_orthogonal_span_singleton
      (contMDiffWithinAt_univ.mpr hs) (contMDiffWithinAt_univ.mpr hu) hsx

/-- If `s` and `u` are `C^k` maps into an inner product space `E` on `t` with `s` nonzero on `t`,
then `y ↦ (ℝ ∙ s y)ᗮ.starProjection (u y)` is `C^k` on `t`. -/
theorem contMDiffOn_starProjection_orthogonal_span_singleton {t : Set M}
    (hs : ContMDiffOn I 𝓘(ℝ, E) k s t) (hu : ContMDiffOn I 𝓘(ℝ, E) k u t)
    (hsne : ∀ x ∈ t, s x ≠ 0) :
    ContMDiffOn I 𝓘(ℝ, E) k (fun y ↦ (ℝ ∙ s y)ᗮ.starProjection (u y)) t :=
  fun x hx ↦ contMDiffWithinAt_starProjection_orthogonal_span_singleton (hs x hx) (hu x hx)
    (hsne x hx)

/-- If `s` and `u` are `C^k` maps into an inner product space `E` with `s` nowhere zero, then
`y ↦ (ℝ ∙ s y)ᗮ.starProjection (u y)` is `C^k`. -/
theorem contMDiff_starProjection_orthogonal_span_singleton
    (hs : ContMDiff I 𝓘(ℝ, E) k s) (hu : ContMDiff I 𝓘(ℝ, E) k u) (hsne : ∀ x, s x ≠ 0) :
    ContMDiff I 𝓘(ℝ, E) k (fun y ↦ (ℝ ∙ s y)ᗮ.starProjection (u y)) :=
  fun x ↦ contMDiffAt_starProjection_orthogonal_span_singleton (hs x) (hu x) (hsne x)

end OrthogonalSpanSingleton

end TauCeti
