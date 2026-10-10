/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Prod.Ricci
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace.Curvature
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Isometries of hyperbolic space crossed with a line preserve the tangent splitting

Every isometry of `ℍⁿ × ℝ`, with `n ≥ 2`, preserves both tangent factors. The hyperbolic
factor has Ricci constant `-(n - 1)` and the line has zero Ricci curvature, so these are
distinguished by the Ricci tensor. With horizontal coordinate space `E = ℝ` this applies
to Thurston's product geometry `ℍ² × ℝ` and supplies the differential constraint needed
to identify its full isometry group. The results assert tangent preservation; they do
not yet assert a global decomposition of the isometry.

Reference: P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983),
Section 4 (the product geometries).
-/

public section

noncomputable section

open Bundle CovariantDerivative Manifold
open scoped Manifold ContDiff TauCeti

namespace TauCeti.RiemannianIsometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

local notation "H" => UpperHalfSpace E
local notation "hypModel" => 𝓘(ℝ, WithLp 2 (E × ℝ))
local notation "prodModel" => ModelWithCorners.prod hypModel 𝓘(ℝ)

/-- On `ℍⁿ × ℝ` for `n ≥ 2`, an isometry's differential preserves and reflects
membership in the vertical tangent line. -/
@[simp] theorem fst_mfderiv_eq_zero_iff_hyperbolic_prod_real
    (Φ : RiemannianIsometry prodModel prodModel (H × ℝ) (H × ℝ))
    (p : H × ℝ) (u : TangentSpace prodModel p) :
    (mfderiv prodModel prodModel Φ p u : WithLp 2 (E × ℝ) × ℝ).1 = 0 ↔
      (u : WithLp 2 (E × ℝ) × ℝ).1 = 0 := by
  refine Φ.fst_mfderiv_eq_zero_iff_of_ricciTensor_eq_smul_inner
    (a := -(Module.finrank ℝ E : ℝ)) (b := 0) UpperHalfSpace.ricciTensor_eq ?_ ?_ p u
  · intro x v w
    have hzero := (leviCivitaConnection 𝓘(ℝ) ℝ).ricciTensor_eq_zero_of_curvatureTensor_eq_zero x
      ((leviCivitaConnection 𝓘(ℝ) ℝ).curvatureTensor_eq_zero_of_finrank_le_one x
        (by simp [finrank_tangentSpace]))
    simp [hzero]
  · exact neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Module.finrank_pos.ne'))

/-- On `ℍⁿ × ℝ` for `n ≥ 2`, an isometry's differential preserves and reflects
membership in the horizontal tangent subspace. -/
@[simp] theorem snd_mfderiv_eq_zero_iff_hyperbolic_prod_real
    (Φ : RiemannianIsometry prodModel prodModel (H × ℝ) (H × ℝ))
    (p : H × ℝ) (u : TangentSpace prodModel p) :
    (mfderiv prodModel prodModel Φ p u : WithLp 2 (E × ℝ) × ℝ).2 = 0 ↔
      (u : WithLp 2 (E × ℝ) × ℝ).2 = 0 := by
  refine Φ.snd_mfderiv_eq_zero_iff_of_ricciTensor_eq_smul_inner
    (a := -(Module.finrank ℝ E : ℝ)) (b := 0) UpperHalfSpace.ricciTensor_eq ?_ ?_ p u
  · intro x v w
    have hzero := (leviCivitaConnection 𝓘(ℝ) ℝ).ricciTensor_eq_zero_of_curvatureTensor_eq_zero x
      ((leviCivitaConnection 𝓘(ℝ) ℝ).curvatureTensor_eq_zero_of_finrank_le_one x
        (by simp [finrank_tangentSpace]))
    simp [hzero]
  · exact neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Module.finrank_pos.ne'))

end TauCeti.RiemannianIsometry
