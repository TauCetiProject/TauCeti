/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Topology.Sets.Opens

import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Matrix.EuclideanLin

/-!
# The Jacobian matrix of an inverse map on Euclidean space

On `EuclideanSpace ℝ ι`, the derivative of a map at a point is the operator of its Jacobian matrix
under `Matrix.toEuclideanCLM`. For a map `Φ` differentiable on an open set `U` and mapping it into
an open set `V`, with an inverse `Ψ` differentiable on `V`, the derivatives compose to the identity
(`TauCeti.fderiv_comp_fderiv_eq_id_of_invOn`). In matrix form, the inverse of the Jacobian matrix
of `Φ` at `y` is the Jacobian matrix of `Ψ` at `Φ y`. This is the form in which the inverse
Jacobian enters coefficient formulas after a change of variables.

When instead `‖v‖ ≤ L' ‖DΦ(x) v‖` for every `v`, the operator of the inverse Jacobian matrix is a
two-sided inverse of `DΦ(x)` with norm at most `max L' 0`, and it depends Lipschitz continuously
on `x` wherever `DΦ` does. This is how the inverse Jacobian enters Lipschitz bounds for transformed
coefficients.

## Main results

* `TauCeti.toEuclideanCLM_inv_fderiv_of_invOn`: the operator of the inverse Jacobian matrix
  `DΦ(y)⁻¹` is `DΨ(Φ y)`.
* `TauCeti.toEuclideanCLM_inv_comp_fderiv`: under a lower bound `‖v‖ ≤ L' ‖DΦ(x) v‖`, the operator
  of the inverse Jacobian matrix is a two-sided inverse of `DΦ(x)`.
* `TauCeti.norm_le_and_lipschitzOnWith_toEuclideanCLM_inv_fderiv`: under that lower bound on `s`,
  the inverse Jacobian operator is bounded on `s`, and Lipschitz on `s` if `DΦ` is.
-/

public section

open Set TopologicalSpace
open scoped NNReal

namespace TauCeti

/-- For a map `Φ` of Euclidean space, differentiable on `U` and mapping it into `V`, with inverse
`Ψ` differentiable on `V`, the operator of the inverse Jacobian matrix of `Φ` at `y ∈ U` is
`DΨ(Φ y)`. -/
theorem toEuclideanCLM_inv_fderiv_of_invOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U V : Opens (EuclideanSpace ℝ ι)} {Φ Ψ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hΦ : DifferentiableOn ℝ Φ U) (hmaps : MapsTo Φ U V) (hΨ : DifferentiableOn ℝ Ψ V)
    (hΦΨ : RightInvOn Ψ Φ V) (hΨΦ : LeftInvOn Ψ Φ U) {y : EuclideanSpace ℝ ι}
    (hy : y ∈ (U : Set (EuclideanSpace ℝ ι))) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) ((Matrix.toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Φ y))⁻¹ =
      fderiv ℝ Ψ (Φ y) := by
  rw [Matrix.inv_eq_right_inv (B := (Matrix.toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Ψ (Φ y))),
    StarAlgEquiv.apply_symm_apply]
  rw [← map_mul, ContinuousLinearMap.mul_def,
    fderiv_comp_fderiv_eq_id_of_invOn hΦ hmaps hΨ hΦΨ hΨΦ hy, ← ContinuousLinearMap.one_def,
    map_one]

section Lipschitz

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {s : Set (EuclideanSpace ℝ ι)} {L' : ℝ}

/-- If `‖v‖ ≤ L' ‖DΦ(x) v‖` for every `v`, the map of the inverse Jacobian matrix is a two-sided
inverse of `DΦ(x)`. -/
theorem toEuclideanCLM_inv_comp_fderiv {x : EuclideanSpace ℝ ι}
    (hL' : ∀ v, ‖v‖ ≤ L' * ‖fderiv ℝ Φ x v‖) :
    (toEuclideanCLM (𝕜 := ℝ) ((toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Φ x))⁻¹).comp
        (fderiv ℝ Φ x) = ContinuousLinearMap.id ℝ _ ∧
      (fderiv ℝ Φ x).comp
        (toEuclideanCLM (𝕜 := ℝ) ((toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Φ x))⁻¹) =
        ContinuousLinearMap.id ℝ _ := by
  obtain ⟨N, hN⟩ : ∃ N, toEuclideanCLM (𝕜 := ℝ) N = fderiv ℝ Φ x :=
    ⟨_, StarAlgEquiv.apply_symm_apply _ _⟩
  -- `DΦ(x)` is injective, hence invertible, so its Jacobian matrix `N` has nonzero determinant.
  have hker : LinearMap.ker (fderiv ℝ Φ x : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) = ⊥ :=
    LinearMap.ker_eq_bot'.2 fun v hv => by
      have h := hL' v
      rw [ContinuousLinearMap.coe_coe] at hv
      rw [hv, norm_zero, mul_zero] at h
      exact norm_le_zero_iff.1 h
  have hdet : N.det ≠ 0 := by
    rw [← det_toEuclideanCLM, hN]
    exact ((LinearMap.isUnit_iff_isUnit_det _).1
      ((LinearMap.isUnit_iff_ker_eq_bot _).2 hker)).ne_zero
  simp only [← hN, StarAlgEquiv.symm_apply_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
    nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet), mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet),
    map_one, ContinuousLinearMap.one_def, and_self]

/-- The map of the inverse Jacobian matrix is bounded by `max L' 0` where `‖v‖ ≤ L' ‖DΦ(x) v‖`,
and Lipschitz on `s` with constant `(max L' 0)² K` where `DΦ` is `K`-Lipschitz on `s`. -/
theorem norm_le_and_lipschitzOnWith_toEuclideanCLM_inv_fderiv {KD : ℝ≥0}
    (hDΦ : LipschitzOnWith KD (fderiv ℝ Φ) s)
    (hL' : ∀ x ∈ s, ∀ v, ‖v‖ ≤ L' * ‖fderiv ℝ Φ x v‖) :
    (∀ x ∈ s, ‖toEuclideanCLM (𝕜 := ℝ) ((toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Φ x))⁻¹‖ ≤
      max L' 0) ∧
    LipschitzOnWith ((max L' 0).toNNReal ^ 2 * KD)
      (fun x => toEuclideanCLM (𝕜 := ℝ) ((toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Φ x))⁻¹) s := by
  set T : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι := fun x =>
    toEuclideanCLM (𝕜 := ℝ) ((toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Φ x))⁻¹
  set L₁ := max L' 0
  have hL₁0 : 0 ≤ L₁ := le_max_right _ _
  have hTb : ∀ x ∈ s, ‖T x‖ ≤ L₁ := fun x hx =>
    (T x).opNorm_le_bound hL₁0 fun w => by
      have h := hL' x hx (T x w)
      rw [← ContinuousLinearMap.comp_apply, (toEuclideanCLM_inv_comp_fderiv (hL' x hx)).2,
        ContinuousLinearMap.id_apply] at h
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  refine ⟨hTb, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
  -- `T x - T y = T x (DΦ(y) - DΦ(x)) T y`.
  have hsplit : T x - T y = (T x).comp ((fderiv ℝ Φ y - fderiv ℝ Φ x).comp (T y)) := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
      (toEuclideanCLM_inv_comp_fderiv (hL' y hy)).2, ← ContinuousLinearMap.comp_assoc,
      (toEuclideanCLM_inv_comp_fderiv (hL' x hx)).1, ContinuousLinearMap.comp_id,
      ContinuousLinearMap.id_comp]
  have hD : ‖fderiv ℝ Φ y - fderiv ℝ Φ x‖ ≤ KD * dist x y := by
    rw [← dist_eq_norm, dist_comm x y]
    exact hDΦ.dist_le_mul y hy x hx
  rw [dist_eq_norm, hsplit]
  calc ‖(T x).comp ((fderiv ℝ Φ y - fderiv ℝ Φ x).comp (T y))‖
      ≤ ‖T x‖ * (‖fderiv ℝ Φ y - fderiv ℝ Φ x‖ * ‖T y‖) :=
        ((T x).opNorm_comp_le _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ L₁ * (KD * dist x y * L₁) := by
        gcongr
        exacts [hTb x hx, hTb y hy]
    _ = (L₁.toNNReal ^ 2 * KD : ℝ≥0) * dist x y := by
        push_cast
        rw [Real.coe_toNNReal _ hL₁0]
        ring

end Lipschitz

end TauCeti
