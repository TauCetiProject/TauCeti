/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Analysis.InnerProductSpace.Euclidean.RadialContraction
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Radial contractions as local diffeomorphisms

On a finite-dimensional real normed space, the Euclidean radial contraction with a nonnegative
parameter is a local diffeomorphism. Families of these contractions preserve manifold smoothness
for every regularity at most `∞`.
-/

public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Pointwise

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ∞ω}

/-- A radial contraction with nonnegative parameter is a local diffeomorphism. -/
theorem isLocalDiffeomorph_radialContraction (c : E) (hn : n ≤ ∞) {κ : ℝ} (hκ : 0 ≤ κ) :
    IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) n (radialContraction c κ) := by
  rcases hκ.eq_or_lt with rfl | hκ
  · have : radialContraction c 0 = id := funext (radialContraction_zero c)
    rw [this]
    exact (Diffeomorph.refl 𝓘(ℝ, E) E n).isLocalDiffeomorph
  obtain ⟨Θ, hsource, hΘ, hΘsymm, hΘeq⟩ := exists_radialContraction_eq_openPartialHomeomorph c hκ
  exact fun y => isLocalDiffeomorphAt_of_eqOn
    (Φ := PartialDiffeomorph.ofOpenPartialHomeomorph Θ (hΘ.of_le hn) (hΘsymm.of_le hn))
    (by simp [hsource])
    fun z _ => by simp [← hΘeq]

/-- A `C^n` family of radial contractions with nonnegative parameters, applied to a `C^n`
family of points, is `C^n` for `n ≤ ∞`. -/
theorem contMDiff_radialContraction {E' H' X : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace X]
    [ChartedSpace H' X] (c : E) (hn : n ≤ ∞) {κ : X → ℝ} {y : X → E} (hκ : ContMDiff J 𝓘(ℝ) n κ)
    (hκ₀ : ∀ x, 0 ≤ κ x) (hy : ContMDiff J 𝓘(ℝ, E) n y) :
    ContMDiff J 𝓘(ℝ, E) n fun x => radialContraction c (κ x) (y x) :=
  ((contDiffOn_radialContraction c).of_le hn).contMDiffOn.comp_contMDiff (hκ.prodMk_space hy)
    fun x => add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (hκ₀ x) (sq_nonneg _))

end TauCeti
