/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.IntermediateValue

/-!
# Endomorphisms positive for a positive bilinear form have positive determinant

Let `W` be a finite-dimensional real vector space and `B` a bilinear form on `W` with
`0 < B x x` for every `x ≠ 0`, for instance an inner product. If an endomorphism `T` satisfies
`0 < B x (T x)` for every `x ≠ 0`, then `det T > 0`
(`LinearMap.det_pos_of_forall_pos`). Neither `B` nor `T` need be symmetric: on the segment
`T_t = (1 - t) • id + t • T`, `0 ≤ t ≤ 1`, every `T_t` is injective, since
`B x (T_t x) = (1 - t) B x x + t B x (T x) > 0` for `x ≠ 0`, so `det T_t` does not vanish and keeps
the sign of `det T_0 = 1`. In matrix terms, a real square matrix whose symmetric part is positive
definite has positive determinant.

The typical use compares two identifications of a pair of spaces of the same dimension. If
`β : W × U → ℝ` is bilinear and `e : W ≃ U` and `φ : W → U` are linear with `0 < β x (e x)` and
`0 < β x (φ x)` for every `x ≠ 0`, then the automorphism `e⁻¹ ∘ φ` of `W` has positive determinant
(`LinearMap.det_pos_of_forall_pos_of_forall_pos`), so `e` and `φ` carry each orientation of `W` to
the same orientation of `U`. For instance, two isomorphisms from the kernel of an operator onto its
cokernel, each positive for a pairing of the kernel with the cokernel, induce the same orientation
of its determinant line.

## Main results

* `LinearMap.det_pos_of_forall_pos`: `0 < B x x` and `0 < B x (T x)` for `x ≠ 0` give
  `0 < det T`.
* `LinearMap.det_pos_of_forall_pos_of_forall_pos`: two maps positive for the same pairing differ by
  an automorphism of positive determinant.
-/

public section

open Module

namespace LinearMap

variable {W U : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
  [AddCommGroup U] [Module ℝ U]

/-- **An endomorphism positive for a positive bilinear form has positive determinant.** If
`0 < B x x` and `0 < B x (T x)` for every `x ≠ 0`, then `0 < det T`. Neither `B` nor `T` need be
symmetric. -/
theorem det_pos_of_forall_pos (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) {T : W →ₗ[ℝ] W}
    (hB : ∀ x, x ≠ 0 → 0 < B x x) (hT : ∀ x, x ≠ 0 → 0 < B x (T x)) : 0 < T.det := by
  -- The segment `T_t = (1 - t) • id + t • T` from `id` to `T`.
  set S : ℝ → W →ₗ[ℝ] W := fun t => (1 - t) • id + t • T
  -- Every `T_t` with `0 ≤ t ≤ 1` has nonzero determinant.
  have hS : ∀ t ∈ Set.Icc (0 : ℝ) 1, (S t).det ≠ 0 := by
    rintro t ⟨ht₀, ht₁⟩ hdet
    obtain ⟨x, hSx, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (bot_lt_ker_of_det_eq_zero hdet).ne'
    have h0 : B x (S t x) = (1 - t) * B x x + t * B x (T x) := by
      simp [S]
    rw [mem_ker.1 hSx, map_zero, eq_comm] at h0
    rcases ht₀.eq_or_lt with rfl | ht₀
    · simp only [sub_zero, one_mul, zero_mul, add_zero] at h0
      exact (hB x hx).ne' h0
    · nlinarith [hB x hx, hT x hx]
  -- In a basis, `t ↦ det T_t` is the determinant of a continuous path of matrices.
  set b := finBasis ℝ W
  have hcont : Continuous fun t => (S t).det := by
    simp_rw [← det_toMatrix b]
    refine Continuous.matrix_det ?_
    simp only [S, map_add, map_smul, toMatrix_id]
    fun_prop
  -- By the intermediate value theorem, `det T_t` has the sign of `det T_0 = 1` on `[0, 1]`.
  have hS₀ : (S 0).det = 1 := by simp [S]
  have hS₁ : (S 1).det = T.det := by simp [S]
  by_contra hneg
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc' zero_le_one hcont.continuousOn
    ⟨hS₁ ▸ not_lt.1 hneg, hS₀ ▸ zero_le_one⟩
  exact hS t ht hzero

/-- **Two maps positive for one pairing induce the same orientation.** For a bilinear pairing `β`
of `W` with `U`, a linear equivalence `e : W ≃ U` and a linear map `φ : W → U` with
`0 < β x (e x)` and `0 < β x (φ x)` for every `x ≠ 0`, the automorphism `e⁻¹ ∘ φ` of `W` has
positive determinant. -/
theorem det_pos_of_forall_pos_of_forall_pos (β : W →ₗ[ℝ] U →ₗ[ℝ] ℝ) (e : W ≃ₗ[ℝ] U)
    {φ : W →ₗ[ℝ] U} (he : ∀ x, x ≠ 0 → 0 < β x (e x)) (hφ : ∀ x, x ≠ 0 → 0 < β x (φ x)) :
    0 < (e.symm.toLinearMap ∘ₗ φ).det :=
  det_pos_of_forall_pos (β.compl₂ e.toLinearMap) he fun x hx => by
    simpa using hφ x hx

end LinearMap
