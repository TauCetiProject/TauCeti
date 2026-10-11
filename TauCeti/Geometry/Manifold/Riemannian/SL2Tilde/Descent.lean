/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Descent
public import TauCeti.Geometry.Manifold.Riemannian.SL2Tilde.Projection

/-!
# Descending Sasaki isometries to the hyperbolic plane

An isometry of `SL₂ℝ~` carrying projection fibres onto projection fibres induces a unique
Riemannian isometry of the hyperbolic plane. An analytic section of the hyperbolic
projection and `Diffeomorph.existsUnique_descend` construct the base map and its smooth
inverse. The existing `SL2Tilde.exists_isometry_of_projection_eq` proves the isometry law
from preservation of the pullback metric.
Conversely, a commuting base isometry implies the precise fibre equivalence needed for
descent. No diffeomorphism of the base is assumed as input.

Reference: P. Scott, *The geometries of 3-manifolds*, Section 4, pp. 464–465.
-/

public noncomputable section

open scoped Manifold ContDiff

namespace TauCeti.SL2Tilde

local notation "P" => ℝ × ℝ × ℝ
local notation "Q" => WithLp 2 (ℝ × ℝ)
local notation "J" => 𝓘(ℝ, P)
local notation "K" => 𝓘(ℝ, Q)

/-- A Sasaki isometry carrying entire projection fibres onto projection fibres induces a
unique hyperbolic isometry. Smoothness of the induced map and its inverse is a conclusion. -/
theorem existsUnique_isometry_projection_eq (Φ : Isom J SL2Tilde)
    (hΦ : ∀ p q, projection (Φ p) = projection (Φ q) ↔ projection p = projection q) :
    ∃! Ψ : Isom K (UpperHalfSpace ℝ), ∀ p, Ψ (projection p) = projection (Φ p) := by
  obtain ⟨f, hf, _⟩ := Φ.toDiffeomorph.existsUnique_descend
    (contMDiff_projection.of_le le_top) (contMDiff_projection.of_le le_top)
    (contMDiff_projectionSection.of_le le_top) (contMDiff_projectionSection.of_le le_top)
    projection_projectionSection projection_projectionSection hΦ
  obtain ⟨Ψ, hΨ⟩ := exists_isometry_of_projection_eq Φ f (fun p => (hf p).symm)
  have hcomm (p : SL2Tilde) : Ψ (projection p) = projection (Φ p) := by
    rw [← RiemannianIsometry.coe_toDiffeomorph, hΨ]
    exact hf p
  refine ⟨Ψ, hcomm, ?_⟩
  intro Ψ' hΨ'
  apply RiemannianIsometry.ext
  intro q
  obtain ⟨p, rfl⟩ := projection_surjective q
  exact (hΨ' p).trans (hcomm p).symm

/-- Descent to a hyperbolic isometry is equivalent to carrying projection fibres onto
projection fibres. The condition includes injectivity of the induced base map. -/
theorem exists_isometry_projection_eq_iff (Φ : Isom J SL2Tilde) :
    (∃ Ψ : Isom K (UpperHalfSpace ℝ), ∀ p, Ψ (projection p) = projection (Φ p)) ↔
      ∀ p q, projection (Φ p) = projection (Φ q) ↔ projection p = projection q := by
  constructor
  · rintro ⟨Ψ, hΨ⟩ p q
    rw [← hΨ p, ← hΨ q]
    exact Ψ.injective.eq_iff
  · intro hΦ
    exact (existsUnique_isometry_projection_eq Φ hΦ).exists

end TauCeti.SL2Tilde
