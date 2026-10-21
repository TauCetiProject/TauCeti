/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpHolder
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import TauCeti.Analysis.Normed.Lp.Basic
public import TauCeti.Analysis.Normed.Operator.Compact.FiniteRank

/-!
# Bounded diagonal operators on sequence spaces

A bounded scalar family defines coordinatewise multiplication on `lp` for every exponent
`1 ≤ p ≤ ∞`. The operator norm is the supremum of the coefficient norms. Finite coordinate
truncations have rank at most the number of retained coordinates, and the discarded coefficients
bound their error in operator norm. These estimates provide finite-rank approximations of
diagonal operators. Over a locally compact scalar field, coefficients tending to
zero along the cofinite filter give a compact diagonal operator.

The construction uses Mathlib's `lp.mapCLM` for uniformly bounded families of operators.
-/

public section

open scoped lp ENNReal NNReal Topology
open Filter

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

/-- Adding coefficient families adds their diagonal multipliers. -/
@[simp]
theorem diagonalCLM_add (d e : ℓ^∞(ι, 𝕜)) :
    diagonalCLM (p := p) (d + e) = diagonalCLM d + diagonalCLM e := by
  ext x i
  simp [add_mul]

/-- Scaling a coefficient family scales its diagonal multiplier. -/
@[simp]
theorem diagonalCLM_smul (a : 𝕜) (d : ℓ^∞(ι, 𝕜)) :
    diagonalCLM (p := p) (a • d) = a • diagonalCLM d := by
  ext x i
  simp [mul_assoc]

/-- The constant-one coefficient family gives the identity operator. -/
@[simp]
theorem diagonalCLM_one :
    diagonalCLM (p := p) (1 : ℓ^∞(ι, 𝕜)) = ContinuousLinearMap.id 𝕜 ℓ^p(ι, 𝕜) := by
  ext x i
  simp

/-- Multiplying coefficient families composes their diagonal multipliers. -/
theorem diagonalCLM_mul (d e : ℓ^∞(ι, 𝕜)) :
    diagonalCLM (p := p) (d * e) = (diagonalCLM d).comp (diagonalCLM e) := by
  ext x i
  simp [mul_assoc]

variable [DecidableEq ι]

/-- Retain the coefficients of a diagonal operator on a finite set of coordinates. -/
noncomputable def diagonalTruncation (d : ℓ^∞(ι, 𝕜)) (s : Finset ι) :
    ℓ^p(ι, 𝕜) →L[𝕜] ℓ^p(ι, 𝕜) :=
  ∑ i ∈ s, (d i • singleContinuousLinearMap 𝕜 (fun _ : ι ↦ 𝕜) p i).comp
    (evalCLM 𝕜 (fun _ : ι ↦ 𝕜) p i)

/-- A finite diagonal truncation is a sum of scalar multiples of coordinate vectors. -/
theorem diagonalTruncation_apply_eq_sum_single (d : ℓ^∞(ι, 𝕜)) (s : Finset ι)
    (x : ℓ^p(ι, 𝕜)) :
    diagonalTruncation d s x = ∑ i ∈ s, (d i * x i) • lp.single p i 1 := by
  rw [diagonalTruncation, sum_apply]
  simp [singleContinuousLinearMap_apply, ← lp.single_smul]

/-- A finite diagonal truncation is the original multiplier on the retained coordinates
and zero elsewhere. -/
@[simp]
theorem diagonalTruncation_apply (d : ℓ^∞(ι, 𝕜)) (s : Finset ι)
    (x : ℓ^p(ι, 𝕜)) (i : ι) :
    diagonalTruncation d s x i = if i ∈ s then d i * x i else 0 := by
  rw [← evalCLM_apply (𝕜 := 𝕜) i (diagonalTruncation d s x),
    diagonalTruncation_apply_eq_sum_single, map_sum]
  simp [lp.single_apply, Pi.single_apply]

/-- Retaining no coordinates gives the zero operator. -/
@[simp]
theorem diagonalTruncation_empty (d : ℓ^∞(ι, 𝕜)) :
    diagonalTruncation (p := p) d ∅ = 0 := by
  simp [diagonalTruncation]

/-- A finite diagonal truncation retains exactly the coordinate vectors in its finite set. -/
@[simp]
theorem diagonalTruncation_single (d : ℓ^∞(ι, 𝕜)) (s : Finset ι) (i : ι) (a : 𝕜) :
    diagonalTruncation d s (lp.single p i a) =
      if i ∈ s then lp.single p i (d i * a) else 0 := by
  ext j
  by_cases h : j = i
  · subst j; by_cases hi : i ∈ s <;> simp [hi]
  · by_cases hi : i ∈ s <;> simp [hi, lp.single_apply, h]

/-- A finite diagonal truncation has rank at most the number of retained coordinates. -/
theorem rank_diagonalTruncation_le (d : ℓ^∞(ι, 𝕜)) (s : Finset ι) :
    (diagonalTruncation (p := p) d s).rank ≤ s.card := by
  classical
  let v : ι → ℓ^p(ι, 𝕜) := fun i ↦ lp.single p i 1
  have hrange : LinearMap.range (diagonalTruncation (p := p) d s).toLinearMap ≤
      Submodule.span 𝕜 (v '' (s : Set ι)) := by
    rintro _ ⟨x, rfl⟩
    simp only [ContinuousLinearMap.coe_coe]
    rw [diagonalTruncation_apply_eq_sum_single]
    exact Submodule.sum_mem _ fun i hi ↦ Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, hi, rfl⟩)
  calc
    _ ≤ Module.rank 𝕜 (Submodule.span 𝕜 (v '' (s : Set ι))) := Submodule.rank_mono hrange
    _ ≤ s.card := by
      rw [← Finset.coe_image]
      exact (rank_span_finset_le _).trans (by exact_mod_cast Finset.card_image_le)

/-- Retaining the first `n` coordinates gives an operator of rank at most `n`. -/
theorem rank_diagonalTruncation_range_le (d : ℓ^∞(ℕ, 𝕜)) (n : ℕ) :
    (diagonalTruncation (p := p) d (Finset.range n)).rank ≤ n := by
  simpa using rank_diagonalTruncation_le (p := p) d (Finset.range n)

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

/-- For decreasing coefficient magnitudes, the first discarded coefficient bounds the error. -/
theorem nnnorm_diagonalCLM_sub_diagonalTruncation_range_le (d : ℓ^∞(ℕ, 𝕜))
    (hd : Antitone fun i ↦ ‖d i‖) (n : ℕ) :
    ‖diagonalCLM (p := p) d - diagonalTruncation d (Finset.range n)‖₊ ≤ ‖d n‖₊ := by
  exact_mod_cast norm_diagonalCLM_sub_diagonalTruncation_le (p := p) d (Finset.range n)
    (norm_nonneg _) (fun i hi ↦ hd (by simpa using hi))

omit [DecidableEq ι] in
/-- A diagonal multiplier is compact if its coefficient norms tend to zero along cofinite. -/
theorem isCompactOperator_diagonalCLM [LocallyCompactSpace 𝕜]
    (d : ℓ^∞(ι, 𝕜)) (hd : Tendsto (fun i ↦ ‖d i‖) cofinite (𝓝 0)) :
    IsCompactOperator (diagonalCLM (p := p) d) := by
  classical
  have : ProperSpace 𝕜 := .of_locallyCompactSpace 𝕜
  apply isClosed_setOfPred_isCompactOperator.closure_subset
  refine Metric.mem_closure_iff.mpr fun ε hε ↦ ?_
  have hs : {i | ¬‖d i‖ < ε / 2}.Finite :=
    eventually_cofinite.mp (hd.eventually (gt_mem_nhds (half_pos hε)))
  let s := hs.toFinset
  have : Module.Finite 𝕜 (LinearMap.range (diagonalTruncation (p := p) d s).toLinearMap) :=
    Module.rank_lt_aleph0_iff.mp
      ((rank_diagonalTruncation_le (p := p) d s).trans_lt (Cardinal.natCast_lt_aleph0))
  refine ⟨diagonalTruncation d s,
    LinearMap.HasFiniteRange.isCompactOperator (Module.Finite.iff_fg.mp this), ?_⟩
  rw [dist_eq_norm]
  exact (norm_diagonalCLM_sub_diagonalTruncation_le d s (half_pos hε).le
    (fun i hi ↦ (by simpa [s] using hi : ‖d i‖ < ε / 2).le)).trans_lt (half_lt_self hε)

end lp
