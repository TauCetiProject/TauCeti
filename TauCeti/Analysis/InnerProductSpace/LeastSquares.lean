/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Least-squares solutions

Let `X : E →ₗ[𝕜] F` be a linear map into an inner product space, for instance the design of a
linear model, and let `y : F`. A vector `b : E` is a *least-squares solution* when `X b` is a
point of the range of `X` nearest to `y`, that is `‖y - X b‖ ≤ ‖y - X b'‖` for every `b'`. No
rank condition is imposed on `X`.

The least-squares solutions are the vectors whose residual `y - X b` is orthogonal to the range
of `X`. Equivalently, the fitted value `X b` is the orthogonal projection of `y` onto the range,
and, in finite dimension, `b` solves the normal equations `X† (X b) = X† y`. A solution exists
when the range has an orthogonal projection, all solutions differ by elements of the kernel of
`X`, and exactly one of them lies in the orthogonal complement of the kernel. That one is the
unique least-squares solution of least norm.

## Main definitions

* `LinearMap.IsLeastSquares X y b`: `b` minimizes `‖y - X b‖`.

## Main statements

* `LinearMap.isLeastSquares_iff_sub_mem_orthogonal_range`: `b` is a least-squares solution if
  and only if the residual `y - X b` is orthogonal to the range of `X`.
* `LinearMap.isLeastSquares_iff_apply_eq_starProjection`: `b` is a least-squares solution if and
  only if `X b` is the orthogonal projection of `y` onto the range of `X`.
* `LinearMap.isLeastSquares_iff_adjoint_apply`: the normal equations `X† (X b) = X† y`.
* `LinearMap.exists_isLeastSquares`: a least-squares solution exists.
* `LinearMap.IsLeastSquares.isLeastSquares_iff_sub_mem_ker`: the least-squares solutions form
  the coset `b + ker X` of any one of them.
* `LinearMap.existsUnique_isLeastSquares_iff_injective`: the solution is unique if and only if
  `X` is injective.
* `LinearMap.existsUnique_isLeastSquares_mem_orthogonal_ker`: exactly one least-squares solution
  lies in `(ker X)ᗮ`.
* `LinearMap.IsLeastSquares.norm_le_of_mem_orthogonal_ker`,
  `LinearMap.IsLeastSquares.eq_of_norm_le`: that solution has the least norm, and every
  least-squares solution of at most its norm is equal to it.

The value of the least-squares objective itself is in
`TauCeti.Analysis.Optimization.LeastSquares`.

## References

* A. Ben-Israel, T. N. E. Greville, *Generalized Inverses: Theory and Applications*, 2nd ed.,
  CMS Books in Mathematics, Springer (2003), Chapter 3.
-/

public section

open Submodule

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]

section Def

variable {R : Type*} [Semiring R] [AddCommMonoid E] [Module R E] [SeminormedAddCommGroup F]
  [Module R F]

/-- `b` is a *least-squares solution* for the linear map `X` and the vector `y`: it minimizes
the residual norm `‖y - X b‖` over the source space. -/
def IsLeastSquares (X : E →ₗ[R] F) (y : F) (b : E) : Prop :=
  ∀ b' : E, ‖y - X b‖ ≤ ‖y - X b'‖

/-- Unfolding lemma for `LinearMap.IsLeastSquares`. -/
theorem isLeastSquares_def {X : E →ₗ[R] F} {y : F} {b : E} :
    X.IsLeastSquares y b ↔ ∀ b' : E, ‖y - X b‖ ≤ ‖y - X b'‖ :=
  Iff.rfl

end Def

section General

variable [AddCommMonoid E] [Module 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  {X : E →ₗ[𝕜] F} {y : F} {b b' : E}

/-- `b` is a least-squares solution if and only if the residual `y - X b` is orthogonal to the
range of `X`. -/
theorem isLeastSquares_iff_sub_mem_orthogonal_range :
    X.IsLeastSquares y b ↔ y - X b ∈ (range X)ᗮ := by
  -- The proof follows `ContinuousLinearMap.forall_norm_sub_apply_le_iff_adjoint_apply_sub_eq_zero`,
  -- which needs a continuous map and complete spaces.
  have hb : BddBelow (Set.range fun w : range X ↦ ‖y - w‖) :=
    ⟨0, by rintro - ⟨_, rfl⟩; positivity⟩
  rw [mem_orthogonal', ← (range X).norm_eq_iInf_iff_inner_eq_zero (mem_range_self X b),
    le_antisymm_iff, and_iff_left (ciInf_le hb ⟨X b, b, rfl⟩), le_ciInf_iff hb]
  simp [isLeastSquares_def]

/-- All least-squares solutions have the same fitted value. -/
theorem IsLeastSquares.apply_eq (hb : X.IsLeastSquares y b) (hb' : X.IsLeastSquares y b') :
    X b = X b' := by
  have h := sub_mem (isLeastSquares_iff_sub_mem_orthogonal_range.mp hb')
    (isLeastSquares_iff_sub_mem_orthogonal_range.mp hb)
  rw [sub_sub_sub_cancel_left] at h
  exact sub_eq_zero.mp <| disjoint_def.mp (range X).orthogonal_disjoint _
    (sub_mem (mem_range_self X b) (mem_range_self X b')) h

/-- `b` is a least-squares solution if and only if the fitted value `X b` is the orthogonal
projection of `y` onto the range of `X`. -/
theorem isLeastSquares_iff_apply_eq_starProjection [(range X).HasOrthogonalProjection] :
    X.IsLeastSquares y b ↔ X b = (range X).starProjection y := by
  rw [isLeastSquares_iff_sub_mem_orthogonal_range]
  refine ⟨fun h ↦ (eq_starProjection_of_mem_orthogonal (mem_range_self X b) h).symm,
    fun h ↦ ?_⟩
  rw [h]
  exact sub_starProjection_mem_orthogonal y

variable (X y) in
/-- A least-squares solution exists when the range has an orthogonal projection, for instance
when the target space is finite-dimensional. -/
theorem exists_isLeastSquares [(range X).HasOrthogonalProjection] :
    ∃ b, X.IsLeastSquares y b := by
  obtain ⟨b, hb⟩ := (range X).starProjection_apply_mem y
  exact ⟨b, isLeastSquares_iff_apply_eq_starProjection.mpr hb⟩

end General

section Kernel

variable [AddCommGroup E] [Module 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  {X : E →ₗ[𝕜] F} {y : F} {b b' : E}

/-- Given one least-squares solution `b`, the least-squares solutions are exactly the vectors
of the coset `b + ker X`. -/
theorem IsLeastSquares.isLeastSquares_iff_sub_mem_ker (hb : X.IsLeastSquares y b) :
    X.IsLeastSquares y b' ↔ b' - b ∈ ker X := by
  refine ⟨fun hb' ↦ by rw [mem_ker, map_sub, hb'.apply_eq hb, sub_self], fun h ↦ ?_⟩
  rw [mem_ker, map_sub, sub_eq_zero] at h
  rw [isLeastSquares_iff_sub_mem_orthogonal_range, h]
  exact isLeastSquares_iff_sub_mem_orthogonal_range.mp hb

variable (X y) in
/-- The least-squares solution is unique if and only if `X` is injective. -/
theorem existsUnique_isLeastSquares_iff_injective [(range X).HasOrthogonalProjection] :
    (∃! b, X.IsLeastSquares y b) ↔ Function.Injective X := by
  rw [← ker_eq_bot, Submodule.eq_bot_iff]
  refine ⟨fun ⟨c, hc, huniq⟩ k hk ↦ ?_, fun h ↦ ?_⟩
  · have hkc := huniq (k + c) (hc.isLeastSquares_iff_sub_mem_ker.mpr (by simpa using hk))
    simpa using hkc
  · obtain ⟨b, hb⟩ := X.exists_isLeastSquares y
    exact ⟨b, hb, fun b' hb' ↦ sub_eq_zero.mp (h _ (hb.isLeastSquares_iff_sub_mem_ker.mp hb'))⟩

end Kernel

section MinimalNorm

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 F] {X : E →ₗ[𝕜] F} {y : F} {b b' : E}

/-- At most one least-squares solution lies in the orthogonal complement of the kernel. -/
theorem IsLeastSquares.eq_of_mem_orthogonal_ker (hb : X.IsLeastSquares y b)
    (hbk : b ∈ (ker X)ᗮ) (hb' : X.IsLeastSquares y b') (hb'k : b' ∈ (ker X)ᗮ) : b = b' :=
  (sub_eq_zero.mp <| disjoint_def.mp (ker X).orthogonal_disjoint _
    (hb.isLeastSquares_iff_sub_mem_ker.mp hb') (sub_mem hb'k hbk)).symm

/-- A least-squares solution in the orthogonal complement of the kernel has the least norm
among all least-squares solutions. -/
theorem IsLeastSquares.norm_le_of_mem_orthogonal_ker (hb : X.IsLeastSquares y b)
    (hbk : b ∈ (ker X)ᗮ) (hb' : X.IsLeastSquares y b') : ‖b‖ ≤ ‖b'‖ := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero b (b' - b)
    (inner_left_of_mem_orthogonal (hb.isLeastSquares_iff_sub_mem_ker.mp hb') hbk)
  rw [add_sub_cancel] at h
  rw [mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _), h]
  exact le_add_of_nonneg_right (mul_self_nonneg _)

/-- A least-squares solution in the orthogonal complement of the kernel is the only
least-squares solution of least norm: every least-squares solution `b'` with `‖b'‖ ≤ ‖b‖` is
equal to `b`. -/
theorem IsLeastSquares.eq_of_norm_le (hb : X.IsLeastSquares y b) (hbk : b ∈ (ker X)ᗮ)
    (hb' : X.IsLeastSquares y b') (hle : ‖b'‖ ≤ ‖b‖) : b' = b := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero b (b' - b)
    (inner_left_of_mem_orthogonal (hb.isLeastSquares_iff_sub_mem_ker.mp hb') hbk)
  rw [add_sub_cancel] at h
  have h0 : ‖b' - b‖ * ‖b' - b‖ ≤ 0 := by nlinarith [norm_nonneg b']
  exact sub_eq_zero.mp <| norm_eq_zero.mp <| mul_self_eq_zero.mp <|
    le_antisymm h0 (mul_self_nonneg _)

variable (X y) in
/-- Exactly one least-squares solution lies in the orthogonal complement of the kernel. By
`LinearMap.IsLeastSquares.norm_le_of_mem_orthogonal_ker` and
`LinearMap.IsLeastSquares.eq_of_norm_le` it is the unique least-squares solution of least norm. -/
theorem existsUnique_isLeastSquares_mem_orthogonal_ker [(range X).HasOrthogonalProjection]
    [(ker X).HasOrthogonalProjection] :
    ∃! b, X.IsLeastSquares y b ∧ b ∈ (ker X)ᗮ := by
  obtain ⟨b, hb⟩ := X.exists_isLeastSquares y
  have hb₀ : X.IsLeastSquares y (b - (ker X).starProjection b) :=
    hb.isLeastSquares_iff_sub_mem_ker.mpr (by simp)
  exact ⟨_, ⟨hb₀, sub_starProjection_mem_orthogonal b⟩,
    fun c hc ↦ hc.1.eq_of_mem_orthogonal_ker hc.2 hb₀ (sub_starProjection_mem_orthogonal b)⟩

end MinimalNorm

section FiniteDimensional

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {X : E →ₗ[𝕜] F} {y : F} {b : E}

/-- **Normal equations.** For a linear map `X` of any rank, `b` is a least-squares solution if
and only if `X† (X b) = X† y`. -/
theorem isLeastSquares_iff_adjoint_apply :
    X.IsLeastSquares y b ↔ X.adjoint (X b) = X.adjoint y := by
  rw [isLeastSquares_iff_sub_mem_orthogonal_range, orthogonal_range, mem_ker, map_sub,
    sub_eq_zero, eq_comm]

end FiniteDimensional

end LinearMap
