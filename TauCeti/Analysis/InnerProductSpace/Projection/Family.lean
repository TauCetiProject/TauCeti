/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.RingTheory.Idempotents

/-!
# Families of symmetric projections

A finite family of symmetric idempotents summing to the identity is a complete family of
orthogonal idempotents. In particular the product of two distinct projections is zero.
-/

public section

open LinearMap
open scoped InnerProductSpace

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι]

/-- Symmetric idempotents summing to the identity are orthogonal: a complete family of orthogonal
projections is a family of complete orthogonal idempotents. -/
theorem CompleteOrthogonalIdempotents.of_isSymmetricProjection {P : ι → E →ₗ[𝕜] E}
    (hP : ∀ j, (P j).IsSymmetricProjection) (hsum : ∑ j, P j = 1) :
    CompleteOrthogonalIdempotents P := by
  classical
  refine CompleteOrthogonalIdempotents.iff_ortho_complete.2 ⟨fun i j hij ↦ ?_, hsum⟩
  ext x
  set y := P j x
  have hidem (k : ι) (z : E) : P k (P k z) = P k z := by
    rw [← mul_apply_eq_comp, (hP k).isIdempotentElem.eq]
  have hnorm (k : ι) : RCLike.re ⟪P k y, y⟫_𝕜 = ‖P k y‖ ^ 2 := by
    rw [← hidem k y, (hP k).isSymmetric, hidem, inner_self_eq_norm_sq]
  have htotal : ∑ k, ‖P k y‖ ^ 2 = ‖y‖ ^ 2 := by
    have hy : ∑ k, P k y = y := by rw [← LinearMap.sum_apply, hsum, one_apply_eq_self]
    simp_rw [← hnorm, ← map_sum, ← sum_inner, hy, inner_self_eq_norm_sq]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), hidem, add_eq_left] at htotal
  have hi := (Finset.sum_eq_zero_iff_of_nonneg fun k _ ↦ sq_nonneg ‖P k y‖).1 htotal i
    (Finset.mem_erase.2 ⟨hij, Finset.mem_univ i⟩)
  rw [mul_apply_eq_comp, LinearMap.zero_apply]
  simpa using hi
