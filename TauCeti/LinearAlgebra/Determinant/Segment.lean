/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Order.IntermediateValue

/-!
# The sign of the determinant along a segment of isomorphisms

Let `g₀` and `g₁` be linear isomorphisms between finite-dimensional real vector spaces `V` and `W`.
If every point `(1 - s) • g₀ + s • g₁`, `s ∈ [0, 1]`, of the segment between them is again an
isomorphism, then `g₀` and `g₁` induce the same orientation transport from `V` to `W`: the
automorphism `g₀⁻¹ ∘ g₁` of `V` has positive determinant
(`LinearEquiv.det_trans_symm_pos_of_forall_bijective`). Indeed `s ↦ det (g₀⁻¹ ∘ ((1 - s) • g₀ +
s • g₁))` is a polynomial in `s`, equal to `1` at `s = 0` and nowhere zero on `[0, 1]`.

This is how a construction depending on a choice from a convex set of admissible choices, such
as a right inverse of bounded norm, is shown to induce a well-defined orientation.

## Main results

* `LinearEquiv.det_trans_symm_pos_of_forall_bijective`: if the segment between `g₀` and `g₁`
  consists of isomorphisms, then `det (g₀⁻¹ ∘ g₁) > 0`.
-/

public section

open Module Set

namespace LinearEquiv

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [FiniteDimensional ℝ V]

/-- **Isomorphisms joined by a segment of isomorphisms.** If every point `(1 - s) • g₀ + s • g₁`,
`s ∈ [0, 1]`, of the segment between two isomorphisms `g₀ g₁ : V ≃ W` of finite-dimensional real
vector spaces is bijective, then the automorphism `g₀⁻¹ ∘ g₁` of `V` has positive determinant. -/
theorem det_trans_symm_pos_of_forall_bijective (g₀ g₁ : V ≃ₗ[ℝ] W)
    (h : ∀ s ∈ Icc (0 : ℝ) 1,
      Function.Bijective ((1 - s) • (g₀ : V →ₗ[ℝ] W) + s • (g₁ : V →ₗ[ℝ] W))) :
    0 < LinearMap.det (g₁.trans g₀.symm : V →ₗ[ℝ] V) := by
  set M : V →ₗ[ℝ] V := (g₁.trans g₀.symm).toLinearMap
  -- Read through `g₀⁻¹`, the segment is the segment from the identity to `M`.
  have hseg : ∀ s : ℝ, (1 - s) • LinearMap.id + s • M =
      (g₀.symm : W →ₗ[ℝ] V) ∘ₗ ((1 - s) • (g₀ : V →ₗ[ℝ] W) + s • (g₁ : V →ₗ[ℝ] W)) := fun s ↦ by
    ext v
    simp [M]
  set b := Module.finBasis ℝ V
  set φ : ℝ → ℝ := fun s ↦ LinearMap.det ((1 - s) • LinearMap.id + s • M)
  have hcont : Continuous φ := by
    have hφ : φ = fun s ↦ ((1 - s) • (1 : Matrix (Fin (finrank ℝ V)) (Fin (finrank ℝ V)) ℝ) +
        s • LinearMap.toMatrix b b M).det := by
      funext s
      simp [φ, ← LinearMap.det_toMatrix b]
    rw [hφ]
    exact (((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const)).matrix_det
  have hne : ∀ s ∈ Icc (0 : ℝ) 1, φ s ≠ 0 := fun s hs ↦ by
    simp only [φ, hseg s]
    exact (LinearEquiv.ofBijective ((g₀.symm : W →ₗ[ℝ] V) ∘ₗ
      ((1 - s) • (g₀ : V →ₗ[ℝ] W) + s • (g₁ : V →ₗ[ℝ] W)))
        (g₀.symm.bijective.comp (h s hs))).isUnit_det'.ne_zero
  have hsign := isPreconnected_Icc.sign_eq_of_continuousOn hcont.continuousOn hne
    (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
  simp only [φ, sub_zero, one_smul, zero_smul, add_zero, LinearMap.det_id, sign_one, sub_self,
    zero_add] at hsign
  exact sign_eq_one_iff.1 hsign.symm

end LinearEquiv
