/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import TauCeti.Analysis.InnerProductSpace.OrthogonalSpanSingleton

/-!
# Weak derivatives from a normal and the tangential directions

Let `ν` be a nonzero vector of a real inner product space. Every direction `z` splits as
`(⟪z, ν⟫ / ‖ν‖²) ν` plus a remainder orthogonal to `ν`. Since the weak derivative is linear in the
direction (`TauCeti.HasWeakLineDerivOn.add_direction`, `TauCeti.HasWeakLineDerivOn.smul_direction`),
a function with an `Lᵖ(Ω)` weak derivative in the direction `ν` and in every direction orthogonal
to `ν` has one in every direction. This is the form in which boundary regularity on a half-space
`{x | c < ⟪x, ν⟫}` assembles the normal and the tangential derivatives. For a unit normal `e`, the
derivative along `z` is explicitly `⟪e, z⟫` times the one along `e` plus the one along the
projection of `z` onto `(ℝ ∙ e)ᗮ`.

## Main declarations

* `TauCeti.exists_hasWeakLineDerivOn_of_normal_of_tangential`: an `Lᵖ` weak derivative in one
  direction `ν` and in every direction orthogonal to `ν` gives one in every direction.
* `TauCeti.HasWeakLineDerivOn.smul_add_of_normal_tangential`: for a unit vector `e`, weak
  derivatives `G₁` along `e` and `G₂` along the projection of `z` onto `(ℝ ∙ e)ᗮ` give the weak
  derivative `⟪e, z⟫ G₁ + G₂` along `z`.
-/

public section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {mu : Measure E}
  {Omega : Opens E} {p : ENNReal}

/-- **Weak derivatives from a normal and the tangential directions.** If `u` has a weak
derivative in `Lᵖ(Ω)` in the direction `ν` and in every direction orthogonal to `ν`, then it has
one in every direction `z`: split `z` into `(⟪z, ν⟫ / ‖ν‖²) ν` and the remainder, which is
orthogonal to `ν`. -/
theorem exists_hasWeakLineDerivOn_of_normal_of_tangential {u : E → F} {ν : E}
    (hnor : ∃ G : Lp F p (mu.restrict Omega), HasWeakLineDerivOn mu Omega u G ν)
    (htan : ∀ τ, ⟪τ, ν⟫_ℝ = 0 →
      ∃ G : Lp F p (mu.restrict Omega), HasWeakLineDerivOn mu Omega u G τ)
    (z : E) : ∃ G : Lp F p (mu.restrict Omega), HasWeakLineDerivOn mu Omega u G z := by
  obtain ⟨G₁, h₁⟩ := hnor
  -- The tangential part of `z` is its projection onto `(ℝ ∙ ν)ᗮ`, and its normal part is
  -- `(⟪ν, z⟫ / ‖ν‖²) ν`, the projection onto `ℝ ∙ ν`.
  obtain ⟨G₂, h₂⟩ := htan ((ℝ ∙ ν)ᗮ.starProjection z)
    (Submodule.mem_orthogonal_singleton_iff_inner_left.1 ((ℝ ∙ ν)ᗮ.starProjection_apply_mem z))
  have h := (h₁.smul_direction (⟪ν, z⟫_ℝ / ‖ν‖ ^ 2)).add_direction h₂
  have hz : (⟪ν, z⟫_ℝ / ‖ν‖ ^ 2) • ν + (ℝ ∙ ν)ᗮ.starProjection z = z := by
    simpa only [Submodule.starProjection_singleton, RCLike.ofReal_real_eq_id, id_eq] using
      (ℝ ∙ ν).starProjection_add_starProjection_orthogonal z
  rw [hz] at h
  refine ⟨(⟪ν, z⟫_ℝ / ‖ν‖ ^ 2) • G₁ + G₂, h.congr_ae_deriv ?_⟩
  filter_upwards [Lp.coeFn_add ((⟪ν, z⟫_ℝ / ‖ν‖ ^ 2) • G₁) G₂,
    Lp.coeFn_smul (⟪ν, z⟫_ℝ / ‖ν‖ ^ 2) G₁] with x hx hx'
  rw [hx, Pi.add_apply, Pi.add_apply, hx']

/-- **The derivative along `z` from the normal and the tangential ones.** For a unit vector `e`,
weak derivatives `G₁` of `u` along `e` and `G₂` along the projection of `z` onto `(ℝ ∙ e)ᗮ`
combine into the weak derivative `⟪e, z⟫ G₁ + G₂` of `u` along `z`. -/
theorem HasWeakLineDerivOn.smul_add_of_normal_tangential {u : E → F} {e : E} (he : ‖e‖ = 1)
    {G₁ G₂ : Lp F p (mu.restrict Omega)} (h₁ : HasWeakLineDerivOn mu Omega u G₁ e) {z : E}
    (h₂ : HasWeakLineDerivOn mu Omega u G₂ ((ℝ ∙ e)ᗮ.starProjection z)) :
    HasWeakLineDerivOn mu Omega u (⟪e, z⟫_ℝ • G₁ + G₂ : Lp F p (mu.restrict Omega)) z := by
  have h := (h₁.smul_direction ⟪e, z⟫_ℝ).add_direction h₂
  rw [inner_smul_add_starProjection_eq ℝ he] at h
  refine h.congr_ae_deriv ?_
  filter_upwards [Lp.coeFn_add (⟪e, z⟫_ℝ • G₁) G₂, Lp.coeFn_smul ⟪e, z⟫_ℝ G₁] with x hx hx'
  rw [hx, Pi.add_apply, Pi.add_apply, hx']

end TauCeti
