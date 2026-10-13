/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpHolder
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.LinearMap

/-!
# Bounded diagonal operators on sequence spaces

A bounded scalar family defines coordinatewise multiplication on `lp` for every exponent
`1 ≤ p ≤ ∞`. The operator norm is the supremum of the coefficient norms. Finite coordinate
truncations have rank at most the number of retained coordinates, and the discarded coefficients
bound their error in operator norm. These estimates provide finite-rank approximations of
diagonal operators.

The construction uses Mathlib's `lp.mapCLM` for uniformly bounded families of operators.
-/

public section

open scoped lp ENNReal NNReal

namespace lp

variable {ι 𝕜 : Type*} [NontriviallyNormedField 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Coordinatewise multiplication by a bounded scalar family on `lp`. -/
noncomputable def diagonalCLM (d : ℓ^∞(ι, 𝕜)) : ℓ^p(ι, 𝕜) →L[𝕜] ℓ^p(ι, 𝕜) :=
  mapCLM p (fun i ↦ d i • ContinuousLinearMap.id 𝕜 𝕜) (norm_nonneg d)
    (fun i ↦ by
      rw [norm_smul, ContinuousLinearMap.norm_id, mul_one]
      exact norm_apply_le_norm ENNReal.top_ne_zero d i)

/-- The coordinates of a diagonal operator are the coefficientwise products. -/
@[simp]
theorem diagonalCLM_apply (d : ℓ^∞(ι, 𝕜)) (x : ℓ^p(ι, 𝕜)) (i : ι) :
    diagonalCLM d x i = d i * x i := by
  simp [diagonalCLM]

/-- Diagonal operators act diagonally on the coordinate vectors. -/
@[simp]
theorem diagonalCLM_single [DecidableEq ι] (d : ℓ^∞(ι, 𝕜)) (i : ι) (a : 𝕜) :
    diagonalCLM d (lp.single p i a) = lp.single p i (d i * a) := by
  ext j
  by_cases h : j = i
  · subst j; simp
  · simp [lp.single_apply, h]

/-- The operator norm of a diagonal multiplier equals the supremum norm of its coefficients. -/
@[simp]
theorem norm_diagonalCLM (d : ℓ^∞(ι, 𝕜)) : ‖diagonalCLM (p := p) d‖ = ‖d‖ := by
  classical
  refine le_antisymm (norm_mapCLM_le _ _ _ _) ?_
  refine norm_le_of_forall_le (norm_nonneg _) fun i ↦ ?_
  have h := (diagonalCLM (p := p) d).le_opNorm (lp.single p i 1)
  simpa [lp.norm_single (zero_lt_one.trans_le (Fact.out : 1 ≤ p))] using h

/-- The diagonal multiplier with all coefficients zero is zero. -/
@[simp]
theorem diagonalCLM_zero : diagonalCLM (p := p) (0 : ℓ^∞(ι, 𝕜)) = 0 := by
  ext x i
  simp

variable [DecidableEq ι]

/-- Retain the coefficients of a diagonal operator on a finite set of coordinates. -/
noncomputable def diagonalTruncation (d : ℓ^∞(ι, 𝕜)) (s : Finset ι) :
    ℓ^p(ι, 𝕜) →L[𝕜] ℓ^p(ι, 𝕜) :=
  ∑ i ∈ s, (d i • singleContinuousLinearMap 𝕜 (fun _ : ι ↦ 𝕜) p i).comp
    (evalCLM 𝕜 (fun _ : ι ↦ 𝕜) p i)

/-- A finite diagonal truncation is the original multiplier on the retained coordinates
and zero elsewhere. -/
@[simp]
theorem diagonalTruncation_apply (d : ℓ^∞(ι, 𝕜)) (s : Finset ι)
    (x : ℓ^p(ι, 𝕜)) (i : ι) :
    diagonalTruncation d s x i = if i ∈ s then d i * x i else 0 := by
  -- Reify evaluation before rewriting sums: simplifying the `PreLp` coercion first
  -- produces an expression which the rewrite matcher cannot type-check.
  change (evalₗ (𝕜 := 𝕜) (fun _ : ι ↦ 𝕜) p i) (diagonalTruncation d s x) = _
  rw [diagonalTruncation, sum_apply, map_sum]
  simp [singleContinuousLinearMap_apply, evalCLM, lp.single_apply, Pi.single_apply]

/-- A finite diagonal truncation has rank at most the number of retained coordinates. -/
theorem rank_diagonalTruncation_le (d : ℓ^∞(ι, 𝕜)) (s : Finset ι) :
    (diagonalTruncation (p := p) d s).rank ≤ s.card := by
  classical
  let v : ι → ℓ^p(ι, 𝕜) := fun i ↦ lp.single p i 1
  have hrange : LinearMap.range (diagonalTruncation (p := p) d s).toLinearMap ≤
      Submodule.span 𝕜 (v '' (s : Set ι)) := by
    rintro _ ⟨x, rfl⟩
    have hx : diagonalTruncation d s x = ∑ i ∈ s, (d i * x i) • v i := by
      ext j
      -- Keep evaluation bundled to avoid unfolding the `PreLp` coercion when rewriting sums.
      change (evalₗ (𝕜 := 𝕜) (fun _ : ι ↦ 𝕜) p j) (diagonalTruncation d s x) =
        (evalₗ (𝕜 := 𝕜) (fun _ : ι ↦ 𝕜) p j) (∑ i ∈ s, (d i * x i) • v i)
      rw [map_sum]
      simp [v, lp.single_apply, Pi.single_apply]
    simp only [ContinuousLinearMap.coe_coe]
    rw [hx]
    exact Submodule.sum_mem _ fun i hi ↦ Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, hi, rfl⟩)
  calc
    _ ≤ Module.rank 𝕜 (Submodule.span 𝕜 (v '' (s : Set ι))) := Submodule.rank_mono hrange
    _ ≤ s.card := by
      rw [← Finset.coe_image]
      exact (rank_span_finset_le _).trans (by exact_mod_cast Finset.card_image_le)

/-- A bound on the discarded coefficients bounds the operator-norm truncation error. -/
theorem norm_diagonalCLM_sub_diagonalTruncation_le (d : ℓ^∞(ι, 𝕜)) (s : Finset ι)
    {C : ℝ} (hC : 0 ≤ C) (hd : ∀ i ∉ s, ‖d i‖ ≤ C) :
    ‖diagonalCLM (p := p) d - diagonalTruncation d s‖ ≤ C := by
  have hp : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun x ↦ ?_
  calc
    ‖(diagonalCLM (p := p) d - diagonalTruncation (p := p) d s) x‖ ≤
        ‖(C : ℝ) • lp.toNorm x‖ := by
      refine norm_mono hp fun i ↦ ?_
      by_cases hi : i ∈ s
      · simpa [hi] using norm_nonneg (((C : ℝ) • lp.toNorm x) i)
      · simpa [hi, norm_mul, abs_of_nonneg hC] using
          mul_le_mul_of_nonneg_right (hd i hi) (norm_nonneg (x i))
    _ = C * ‖x‖ := by simp [norm_smul, abs_of_nonneg hC, norm_toNorm]

end lp
