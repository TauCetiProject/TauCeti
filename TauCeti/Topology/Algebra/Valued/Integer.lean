/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Module
public import Mathlib.Topology.Algebra.Valued.LocallyCompact

import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
# The valuation ring of a nonarchimedean normed field

Let `K` be a nontrivially normed field with an ultrametric norm, with valuation ring `𝒪[K]` (the
closed unit ball) and maximal ideal `𝓂[K]` (the open unit ball).

Every `𝒪[K]`-linear map between finite products of copies of `K` is `K`-linear, since `K` is the
fraction field of `𝒪[K]`; hence it is continuous and carries bounded sets to bounded sets. If the
norm of `K` is dense, for instance if its value group is all of `ℝ_{>0}`, the maximal ideal
`𝓂[K]` is not finitely generated.

## Main results

* `Valued.integer.mem_maximalIdeal_iff`: the maximal ideal of `𝒪[K]` is the open unit ball.
* `Valued.integer.dvd_of_norm_le`: divisibility in `𝒪[K]` is comparison of norms.
* `Valued.integer.submodule_mem_of_norm_le`: an `𝒪[K]`-submodule of `K` contains every element
  of norm at most that of one of its elements.
* `LinearMap.continuous_of_integer`: an `𝒪[K]`-linear map from `ι → K`, `ι` finite, to a normed
  `K`-space is continuous.
* `LinearEquiv.isBounded_image_iff_of_integer`: `𝒪[K]`-linear equivalences between finite
  products of `K` preserve and reflect bounded sets.
* `TauCeti.not_fg_maximalIdeal_integer`: for a densely normed field the maximal ideal of `𝒪[K]`
  is not finitely generated.
-/

public section

open IsLocalRing Bornology
open scoped NormedField

section Integer

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- An element of the valuation ring of a nonarchimedean field lies in its maximal ideal exactly
when its norm is less than `1`. -/
theorem Valued.integer.mem_maximalIdeal_iff {x : Valued.integer K} :
    x ∈ IsLocalRing.maximalIdeal (Valued.integer K) ↔ ‖x‖ < 1 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, Valued.integer.isUnit_iff_norm_eq_one,
    (Valued.integer.norm_le_one x).lt_iff_ne]

/-- In the valuation ring of a nonarchimedean field, `b` divides `a` as soon as `‖a‖ ≤ ‖b‖`. -/
theorem Valued.integer.dvd_of_norm_le {a b : Valued.integer K} (h : ‖(a : K)‖ ≤ ‖(b : K)‖) :
    b ∣ a :=
  (Valuation.integer.integers _).dvd_of_le (by
    simpa [NormedField.v_eq_valuation, Algebra.algebraMap_ofSubsemiring_apply,
      ← NNReal.coe_le_coe] using h)

/-- An `𝒪[K]`-submodule of `K` containing `y` contains every `x` with `‖x‖ ≤ ‖y‖`. -/
theorem Valued.integer.submodule_mem_of_norm_le {M : Submodule (Valued.integer K) K} {x y : K}
    (hy : y ∈ M) (h : ‖x‖ ≤ ‖y‖) : x ∈ M := by
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [norm_zero, norm_le_zero_iff] at h
    exact h ▸ M.zero_mem
  have hc : x / y ∈ Valued.integer K :=
    Valued.integer.mem_iff.2 (by rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _))
  have := M.smul_mem ⟨x / y, hc⟩ hy
  rwa [Subring.smul_def, smul_eq_mul, div_mul_cancel₀ _ hy0] at this

variable {ι F : Type*} [NormedAddCommGroup F] [NormedSpace K F] [Module (Valued.integer K) F]
  [IsScalarTower (Valued.integer K) K F]

/-- An `𝒪[K]`-linear map from a finite product of copies of `K` to a normed `K`-space is
continuous: it is `K`-linear, since `K` is the fraction field of `𝒪[K]`. -/
theorem LinearMap.continuous_of_integer [Finite ι] (f : (ι → K) →ₗ[Valued.integer K] F) :
    Continuous f :=
  (f.extendScalarsOfIsLocalization (nonZeroDivisors (Valued.integer K)) K).continuous_on_pi

/-- An `𝒪[K]`-linear map from a finite product of copies of `K` to a normed `K`-space carries
bounded sets to bounded sets. -/
theorem LinearMap.isBounded_image_of_integer [Finite ι] (f : (ι → K) →ₗ[Valued.integer K] F)
    {s : Set (ι → K)} (hs : IsBounded s) : IsBounded (f '' s) := by
  cases nonempty_fintype ι
  let g : (ι → K) →L[K] F :=
    ⟨f.extendScalarsOfIsLocalization (nonZeroDivisors (Valued.integer K)) K,
      f.continuous_of_integer⟩
  have hg : (g : (ι → K) → F) = f := by
    simp only [g]
    exact funext (LinearMap.extendScalarsOfIsLocalization_apply' (nonZeroDivisors _) K f)
  exact hg ▸ g.lipschitzWith.isBounded_image hs

/-- An `𝒪[K]`-linear equivalence between finite products of copies of `K` preserves and reflects
bounded sets. In particular a submodule `M` is bounded exactly when `M.map e` is. -/
theorem LinearEquiv.isBounded_image_iff_of_integer [Finite ι] {ι' : Type*} [Finite ι']
    (e : (ι → K) ≃ₗ[Valued.integer K] (ι' → K)) {s : Set (ι → K)} :
    IsBounded (e '' s) ↔ IsBounded s := by
  cases nonempty_fintype ι
  cases nonempty_fintype ι'
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [Set.image_image] using e.symm.toLinearMap.isBounded_image_of_integer (F := ι → K) h
  · simpa using e.toLinearMap.isBounded_image_of_integer (F := ι' → K) h

end Integer

namespace TauCeti

variable {K : Type*} [DenselyNormedField K] [IsUltrametricDist K]

/-- The maximal ideal of the valuation ring of a densely normed nonarchimedean field is not
finitely generated: a generator would bound the norms of all elements of the open unit ball. -/
theorem not_fg_maximalIdeal_integer : ¬ (maximalIdeal (Valued.integer K)).FG := by
  intro hfg
  obtain ⟨π, hπ⟩ := (IsBezout.isPrincipal_of_FG _ hfg).principal
  have hπm : π ∈ maximalIdeal (Valued.integer K) := hπ ▸ Submodule.mem_span_singleton_self π
  obtain ⟨x, hπx, hx1⟩ :=
    NormedField.exists_lt_norm_lt K (norm_nonneg π) (Valued.integer.mem_maximalIdeal_iff.1 hπm)
  -- The element `y = x` of `𝒪[K]` lies in the open unit ball, but not in the closed ball of
  -- radius `‖π‖` that `Ideal.span {π}` is.
  let y : Valued.integer K := ⟨x, Valued.integer.mem_iff.2 hx1.le⟩
  have hy : ‖y‖ = ‖x‖ := AddSubgroupClass.coe_norm (Valued.integer K) y
  have hym : y ∈ Submodule.span (Valued.integer K) {π} :=
    hπ ▸ Valued.integer.mem_maximalIdeal_iff.2 (hy ▸ hx1)
  have hyπ : y ∈ Metric.closedBall 0 ‖π‖ :=
    Valued.integer.coe_span_singleton_eq_closedBall π ▸ SetLike.mem_coe.2 hym
  rw [mem_closedBall_zero_iff, hy] at hyπ
  exact hyπ.not_gt hπx

end TauCeti
