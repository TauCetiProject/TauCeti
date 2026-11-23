/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Convex.FiniteMean
import TauCeti.Analysis.InnerProductSpace.Projection.Basic

/-!
# Orthogonal projection onto the constant vectors

In a finite Euclidean space, orthogonal projection onto the constant vectors replaces every
coordinate by the finite mean and preserves that mean. The orthogonal complement has dimension
one less than the number of coordinates, with truncated subtraction for the empty index type.
-/

public section

open scoped InnerProductSpace

namespace EuclideanSpace

open TauCeti

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι]

/-- Taking the inner product with the all-ones vector on the left sums the coordinates. -/
theorem inner_const_one_left (x : EuclideanSpace 𝕜 ι) :
    ⟪(WithLp.toLp 2 (fun _ ↦ 1) : EuclideanSpace 𝕜 ι), x⟫_𝕜 = ∑ i, x i := by
  simp [PiLp.inner_apply]

/-- Orthogonal projection onto the constant vectors replaces each entry by the finite mean. -/
theorem starProjection_span_const (x : EuclideanSpace 𝕜 ι) :
    (𝕜 ∙ WithLp.toLp 2 (fun _ ↦ 1)).starProjection x =
      finiteMean 𝕜 x.ofLp • WithLp.toLp 2 (fun _ ↦ 1) := by
  rw [Submodule.starProjection_singleton, inner_const_one_left]
  simp [finiteMean_eq_inv_smul_sum, EuclideanSpace.norm_sq_eq, div_eq_mul_inv, mul_comm]

/-- The orthogonal complement of the constant vectors has dimension `card ι - 1`. -/
theorem finrank_orthogonal_span_const :
    Module.finrank 𝕜 (𝕜 ∙ (WithLp.toLp 2 (fun _ ↦ 1) : EuclideanSpace 𝕜 ι))ᗮ =
      Fintype.card ι - 1 := by
  rcases isEmpty_or_nonempty ι with h | h
  · simp [Module.finrank_zero_of_subsingleton]
  · have hv : (WithLp.toLp 2 (fun _ ↦ 1) : EuclideanSpace 𝕜 ι) ≠ 0 := by
      obtain ⟨i⟩ := h
      intro he
      have := congrArg (fun (x : EuclideanSpace 𝕜 ι) ↦ x i) he
      simp at this
    simpa only [finrank_euclideanSpace] using
      Submodule.finrank_orthogonal_span_singleton_eq_finrank_sub_one (𝕜 := 𝕜) hv

/-- Orthogonal projection onto the constant vectors preserves the finite mean. -/
theorem finiteMean_starProjection_span_const (x : EuclideanSpace 𝕜 ι) :
    finiteMean 𝕜 ((𝕜 ∙ WithLp.toLp 2 (fun _ ↦ 1)).starProjection x).ofLp =
      finiteMean 𝕜 x.ofLp := by
  rcases isEmpty_or_nonempty ι with h | h
  · simp
  · have hc : (Fintype.card ι : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [starProjection_span_const]
    simp [finiteMean_eq_inv_smul_sum, hc, mul_comm, mul_left_comm]

end EuclideanSpace
