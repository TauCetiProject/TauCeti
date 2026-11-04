/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Coprime
public import TauCeti.LowDimTopology.SolidTorusNeighborhood.Basic
public import TauCeti.Topology.Circle.MatrixAction

import Mathlib.Tactic.LinearCombination

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

/-- The identity of `ℂ` for `ε = 1` and complex conjugation for `ε = -1`; on the unit circle it
is `a ↦ a ^ ε` (`discSign_coe`). -/
private def discSign (ε : ℤˣ) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  if ε = 1 then LinearIsometryEquiv.refl ℝ ℂ else Complex.conjLIE

private theorem discSign_discSign (ε : ℤˣ) (z : ℂ) : discSign ε (discSign ε z) = z := by
  unfold discSign
  split_ifs <;> simp

private theorem discSign_coe (ε : ℤˣ) (a : Circle) :
    discSign ε a = ((a ^ (ε : ℤ) : Circle) : ℂ) := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simp [discSign]
  · rw [discSign, ite_eq_right (by decide), Complex.conjLIE_apply, Units.val_neg, Units.val_one,
      zpow_neg_one, Circle.coe_inv_eq_conj]

private theorem norm_discSign_mul (ε : ℤˣ) (z : ℂ) (c : Circle) : ‖discSign ε z * c‖ = ‖z‖ := by
  rw [norm_mul, LinearIsometryEquiv.norm_map, Circle.norm_coe, mul_one]

/-- The homeomorphism `(z, b) ↦ (σ z * b ^ k, b ^ δ)` of the solid torus, with `σ` the identity
for `ε = 1` and complex conjugation for `ε = -1`. -/
private def extension (ε δ : ℤˣ) (k : ℤ) : SolidTorus ≃ₜ SolidTorus where
  toFun p := (⟨discSign ε p.1 * (p.2 ^ k : Circle), by
    rw [mem_closedBall_zero_iff, norm_discSign_mul]; exact mem_closedBall_zero_iff.mp p.1.2⟩,
    p.2 ^ (δ : ℤ))
  invFun p := (⟨discSign ε (p.1 * (p.2 ^ (-((δ : ℤ) * k)) : Circle)), by
    rw [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map, norm_mul, Circle.norm_coe,
      mul_one]; exact mem_closedBall_zero_iff.mp p.1.2⟩,
    p.2 ^ (δ : ℤ))
  left_inv p := by
    have hδ := Int.units_coe_mul_self δ
    have h_exp : k + (δ : ℤ) * -((δ : ℤ) * k) = 0 := by
      linear_combination (-k) * hδ
    have hk : p.2 ^ k * (p.2 ^ (δ : ℤ)) ^ (-((δ : ℤ) * k)) = 1 := by
      rw [← zpow_mul, ← zpow_add, h_exp, zpow_zero]
    refine Prod.ext (Subtype.ext ?_) ?_
    · dsimp only
      rw [mul_assoc, ← Circle.coe_mul, hk, Circle.coe_one, mul_one, discSign_discSign]
    · dsimp only
      rw [← zpow_mul, hδ, zpow_one]
  right_inv p := by
    have hδ := Int.units_coe_mul_self δ
    refine Prod.ext (Subtype.ext ?_) ?_
    · dsimp only
      rw [discSign_discSign, mul_assoc, ← Circle.coe_mul, ← zpow_mul, ← zpow_add, neg_add_cancel,
        zpow_zero, Circle.coe_one, mul_one]
    · dsimp only
      rw [← zpow_mul, hδ, zpow_one]
  continuous_toFun := by
    have hc : Continuous ((↑) : Circle → ℂ) := continuous_subtype_val
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) (by fun_prop)
    exact ((discSign ε).continuous.comp (by fun_prop)).mul (hc.comp (by fun_prop))
  continuous_invFun := by
    have hc : Continuous ((↑) : Circle → ℂ) := continuous_subtype_val
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) (by fun_prop)
    exact (discSign ε).continuous.comp ((continuous_subtype_val.comp continuous_fst).mul
      (hc.comp (by fun_prop)))

private theorem extension_boundaryInclusion (ε δ : ℤˣ) (k : ℤ) (q : Circle × Circle) :
    extension ε δ k (boundaryInclusion q) =
      boundaryInclusion (q.1 ^ (ε : ℤ) * q.2 ^ k, q.2 ^ (δ : ℤ)) :=
  Prod.ext (Subtype.ext (by simp [extension, discSign_coe])) (by simp [extension])

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
