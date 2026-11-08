/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Coprime
public import TauCeti.LowDimTopology.SolidTorusNeighborhood.Basic
public import TauCeti.Topology.Circle.MatrixAction

/-!
# Torus maps fixing the meridian extend over the solid torus

A homeomorphism of the boundary torus `S¹ × S¹` of the solid torus `V = D² × S¹` induced by an
invertible integral matrix (`Matrix.GeneralLinearGroup.torusHomeomorph`) whose matrix fixes the
meridian `(1, 0)` up to sign, `(a, b) ↦ (a ^ ε * b ^ k, b ^ δ)` with `ε, δ = ±1`, extends to `V` as
`(z, b) ↦ (z * b ^ k, b ^ δ)`, with `z` replaced by its complex conjugate when `ε = -1`. This is
the step of the well-definedness of Dehn filling (Rolfsen, *Knots and Links*, 9F) that concerns
the filling solid torus.

## Main results

* `TauCeti.SolidTorus.exists_homeomorph_boundaryInclusion_torusHomeomorph`: matrices fixing the
  meridian up to sign act on the boundary torus by maps that extend over the solid torus.

## References

* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Chapter 9, Section 9F (a homeomorphism
  of the boundary torus preserving the meridian extends over the solid torus).
-/

public section

noncomputable section

open Set Metric

namespace TauCeti

namespace SolidTorus

/-- The homeomorphism `(z, b) ↦ (σ z * b ^ k, b ^ δ)` of the solid torus, with `σ` the identity
for `ε = 1` and complex conjugation for `ε = -1`. -/
private def extension (ε δ : ℤˣ) (k : ℤ) : SolidTorus ≃ₜ SolidTorus :=
  (if ε = 1 then Homeomorph.refl _ else conjDisc).trans
    ((twist k).trans (Homeomorph.prodCongr (Homeomorph.refl _)
      (if δ = 1 then Homeomorph.refl _ else Homeomorph.inv Circle)))

private theorem extension_boundaryInclusion (ε δ : ℤˣ) (k : ℤ) (q : Circle × Circle) :
    extension ε δ k (boundaryInclusion q) =
      boundaryInclusion (q.1 ^ (ε : ℤ) * q.2 ^ k, q.2 ^ (δ : ℤ)) := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;>
    rcases Int.units_eq_one_or δ with rfl | rfl <;>
    refine Prod.ext (Subtype.ext ?_) ?_ <;>
    simp [extension, ← Circle.coe_inv_eq_conj]

/-- **Torus maps fixing the meridian extend over the solid torus.** If an invertible integral
matrix `A` has `A₁₀ = 0`, so that it fixes the meridian class `(1, 0)` up to sign, the induced
homeomorphism `(a, b) ↦ (a ^ A₀₀ * b ^ A₀₁, b ^ A₁₁)` of the boundary torus `S¹ × S¹` is the
restriction of a homeomorphism of the solid torus `D² × S¹`. -/
theorem exists_homeomorph_boundaryInclusion_torusHomeomorph (A : GL (Fin 2) ℤ) (hA : A 1 0 = 0) :
    ∃ ψ : SolidTorus ≃ₜ SolidTorus,
      ∀ q, ψ (boundaryInclusion q) = boundaryInclusion (A.torusHomeomorph q) := by
  have h₀ := A.isCoprime_col 0
  have h₁ := A.isCoprime_row 1
  rw [hA, isCoprime_zero_right] at h₀
  rw [hA, isCoprime_zero_left] at h₁
  obtain ⟨ε, hε⟩ := h₀
  obtain ⟨δ, hδ⟩ := h₁
  refine ⟨extension ε δ (A 0 1), fun q ↦ ?_⟩
  rw [extension_boundaryInclusion, Matrix.GeneralLinearGroup.torusHomeomorph_apply, hA, hε, hδ,
    zpow_zero, one_mul]

end SolidTorus

end TauCeti
