/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.SL2Tilde.Descent
public import TauCeti.Geometry.Manifold.Riemannian.SL2Tilde.Vertical

/-!
# Descent of all `SL₂ℝ~` isometries

The vertical-fibre theorem shows that every Sasaki isometry of `SL₂ℝ~` maps each
hyperbolic projection fibre onto a fibre.  The descent construction therefore applies to
every isometry, producing a unique isometry of the hyperbolic plane.  This is the reduction
step used in the maximal-isometry-group classification of the `SL₂ℝ~` model.
-/

public noncomputable section

open scoped Manifold ContDiff

namespace TauCeti.SL2Tilde

local notation "P" => ℝ × ℝ × ℝ
local notation "Q" => WithLp 2 (ℝ × ℝ)
local notation "J" => 𝓘(ℝ, P)
local notation "K" => 𝓘(ℝ, Q)

/-- An isometry of `SL₂ℝ~` preserves the fibres of the hyperbolic projection. -/
theorem isometry_preserves_projection_fibres (Φ : Isom J SL2Tilde) (p q : SL2Tilde) :
    projection (Φ p) = projection (Φ q) ↔ projection p = projection q := by
  rw [projection_eq_projection_iff, projection_eq_projection_iff]
  constructor
  · intro h
    have hq : Φ q ∈ {r : SL2Tilde | r.x = (Φ p).x ∧ r.y = (Φ p).y} := by
      simp [h]
    have hq' : Φ q ∈ Φ '' {r : SL2Tilde | r.x = p.x ∧ r.y = p.y} := by
      rw [image_vertical_fiber]
      exact hq
    obtain ⟨r, hr, hΦr⟩ := hq'
    have hqr : q = r := Φ.injective hΦr.symm
    rcases hr with ⟨hrx, hry⟩
    exact ⟨hrx.symm.trans (by rw [hqr]), hry.symm.trans (by rw [hqr])⟩
  · intro h
    have hq : q ∈ {r : SL2Tilde | r.x = p.x ∧ r.y = p.y} := by
      simp [h]
    have hq' : Φ q ∈ Φ '' {r : SL2Tilde | r.x = p.x ∧ r.y = p.y} := ⟨q, hq, rfl⟩
    rw [image_vertical_fiber] at hq'
    exact ⟨hq'.1.symm, hq'.2.symm⟩

/-- Every `SL₂ℝ~` isometry descends to a unique hyperbolic-plane isometry. -/
theorem existsUnique_isometry_projection_eq_of_isometry (Φ : Isom J SL2Tilde) :
    ∃! Ψ : Isom K (UpperHalfSpace ℝ), ∀ p, Ψ (projection p) = projection (Φ p) :=
  existsUnique_isometry_projection_eq Φ (isometry_preserves_projection_fibres Φ)

end TauCeti.SL2Tilde
