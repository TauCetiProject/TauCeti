/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.RowCompact
public import TauCeti.Analysis.Normed.Operator.RingOpNorm.OpenMapping
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Complete continuity implies row compactness

Every row-compact map `u : C₀(J, R) →L[R] C₀(I, R)` between model spaces is completely continuous
(`ContinuousLinearMap.IsRowCompact.isCompletelyContinuous`). This file proves the converse,
*Serre's criterion*, whenever the finitely generated submodules of the target `C₀(I, R)` are
closed. In particular it holds over every complete ultrametric nontrivially normed field, with
no discreteness or spherical completeness assumption: there the matrix of a continuous linear map
between model spaces has row norms tending to zero exactly when the map is a limit of maps of
finite rank in operator norm.

The key step is that a map whose columns `u (single j 1)` are combinations of finitely many
fixed vectors `w k`, with uniformly bounded coefficients, has row decay: its `i`-th row is bounded
by a multiple of `∑ k, ‖w k i‖`, which tends to zero along the cofinite filter
(`ContinuousLinearMap.isRowCompact_of_apply_single_eq_sum`). The coefficient bound is where the
closedness hypothesis enters. A closed finitely generated submodule is a complete normed module,
so the quantitative open mapping theorem over Tate rings
(`TauCeti.exists_linearCombination_eq_and_norm_le`) writes each of its vectors in terms of a
finite generating family with coefficients bounded linearly by the norm of the vector. Hence maps
of finite rank are row compact (`ContinuousLinearMap.isRowCompact_of_isFiniteRank`), and closedness
of row compactness under operator-norm limits gives the criterion.

Over a general coefficient ring, closedness of finitely generated submodules is a genuine
hypothesis rather than a formal consequence of completeness, so it is kept explicit. The row-decay
theory itself, and the implication from row compactness to complete continuity, do not use it.

## Main results

* `ContinuousLinearMap.isRowCompact_of_apply_single_eq_sum`: columns that are uniformly bounded
  combinations of finitely many vectors give a row-compact map.
* `ContinuousLinearMap.isRowCompact_of_isFiniteRank`: if finitely generated submodules of
  `C₀(I, R)` are closed, continuous maps of finite rank into it are row compact.
* `ContinuousLinearMap.IsCompletelyContinuous.isRowCompact`,
  `ContinuousLinearMap.isRowCompact_iff_isCompletelyContinuous_of_isClosed`: under the same
  hypothesis, complete continuity is equivalent to row compactness.
* `ContinuousLinearMap.isRowCompact_iff_isCompletelyContinuous`: Serre's criterion over a complete
  ultrametric nontrivially normed field.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §3, Proposition 4 and its corollary.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.1.
-/

public section

open Filter Topology ZeroAtInftyContinuousMap
open scoped ZeroAtInfty

variable {I J R : Type*} [TopologicalSpace I] [DiscreteTopology I] [TopologicalSpace J]
  [DiscreteTopology J] [DecidableEq J]

namespace ContinuousLinearMap

open scoped TauCeti.RingOpNorm

/-- **Bounded finite expansions of the columns give row decay.** If every column
`u (single j 1)` of `u` is a combination `∑ k, a k • w k` of a fixed finite family `w` with
coefficients of norm at most `B`, then `u` is row compact: row `i` is bounded by
`∑ k, B * ‖w k i‖`. -/
theorem isRowCompact_of_apply_single_eq_sum [SeminormedRing R] {ι : Type*} [Fintype ι]
    {u : C₀(J, R) →L[R] C₀(I, R)} (w : ι → C₀(I, R)) {B : ℝ}
    (h : ∀ j, ∃ a : ι → R, (∀ k, ‖a k‖ ≤ B) ∧
      u (ZeroAtInftyContinuousMap.single j 1) = ∑ k, a k • w k) :
    u.IsRowCompact := by
  refine isRowCompact_of_norm_matrixCoeff_le (r := fun i ↦ ∑ k, B * ‖w k i‖) ?_ fun i j ↦ ?_
  · simpa using tendsto_finsetSum _ fun k _ ↦ (w k).tendsto_cofinite.norm.const_mul B
  · obtain ⟨a, ha, hj⟩ := h j
    calc ‖u.matrixCoeff i j‖ = ‖∑ k, a k * w k i‖ := by
          simp [matrixCoeff_apply, hj]
      _ ≤ ∑ k, ‖a k * w k i‖ := norm_sum_le _ _
      _ ≤ ∑ k, B * ‖w k i‖ := Finset.sum_le_sum fun k _ ↦
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (ha k) (norm_nonneg _))

section Tate

variable [NormedRing R] [IsUltrametricDist R] [CompleteSpace R] [TauCeti.NormedRing.IsTate R]

/-- **Maps of finite rank are row compact** when the finitely generated submodules of the target
model space are closed, over a complete ultrametric Tate ring. -/
theorem isRowCompact_of_isFiniteRank
    (hclosed : ∀ L : Submodule R C₀(I, R), L.FG → IsClosed (L : Set C₀(I, R)))
    {u : C₀(J, R) →L[R] C₀(I, R)} (hu : (u : C₀(J, R) →ₗ[R] C₀(I, R)).IsFiniteRank) :
    u.IsRowCompact := by
  obtain ⟨_, ⟨s, rfl⟩, hrange⟩ := LinearMap.isFiniteRank_iff_forall_mem.1 hu
  set L := Submodule.span R (s : Set C₀(I, R))
  have : CompleteSpace L := (hclosed L ⟨s, rfl⟩).completeSpace_coe
  let v : s → L := fun k ↦ ⟨k, Submodule.subset_span k.2⟩
  have hv : Submodule.span R (Set.range v) = ⊤ := by
    convert Submodule.span_span_coe_preimage (R := R) (s := (s : Set C₀(I, R))) using 2
    ext x
    exact ⟨by rintro ⟨k, rfl⟩; exact k.2, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
  obtain ⟨C, hC₀, hC⟩ := TauCeti.exists_linearCombination_eq_and_norm_le v hv
  refine isRowCompact_of_apply_single_eq_sum (fun k : s ↦ (k : C₀(I, R))) (B := C * ‖u‖)
    fun j ↦ ?_
  obtain ⟨c, hc, hcn⟩ := hC ⟨u (ZeroAtInftyContinuousMap.single j 1), hrange _⟩
  refine ⟨c, fun k ↦ (norm_le_pi_norm c k).trans (hcn.trans ?_), ?_⟩
  · refine mul_le_mul_of_nonneg_left ?_ hC₀.le
    simpa [norm_single] using le_ringOpNorm u (ZeroAtInftyContinuousMap.single j (1 : R))
  · simpa [v] using congrArg Subtype.val hc.symm

/-- **Serre's criterion**: if the finitely generated submodules of the target model space are
closed, every completely continuous map between model spaces over a complete ultrametric Tate
ring is row compact. -/
theorem IsCompletelyContinuous.isRowCompact
    (hclosed : ∀ L : Submodule R C₀(I, R), L.FG → IsClosed (L : Set C₀(I, R)))
    {u : C₀(J, R) →L[R] C₀(I, R)} (hu : u.IsCompletelyContinuous) : u.IsRowCompact := by
  choose v hv huv using fun n : ℕ ↦
    isCompletelyContinuous_iff_ringOpNorm.1 hu (1 / (n + 1)) Nat.one_div_pos_of_nat
  exact isRowCompact_of_tendsto
    (squeeze_zero (fun n ↦ ringOpNorm_nonneg _) (fun n ↦ (huv n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat)
    (Eventually.of_forall fun n ↦ isRowCompact_of_isFiniteRank hclosed (hv n))

/-- If the finitely generated submodules of the target model space are closed, a map between
model spaces over a complete ultrametric Tate ring is row compact exactly when it is completely
continuous. -/
theorem isRowCompact_iff_isCompletelyContinuous_of_isClosed
    (hclosed : ∀ L : Submodule R C₀(I, R), L.FG → IsClosed (L : Set C₀(I, R)))
    {u : C₀(J, R) →L[R] C₀(I, R)} : u.IsRowCompact ↔ u.IsCompletelyContinuous :=
  ⟨IsRowCompact.isCompletelyContinuous, IsCompletelyContinuous.isRowCompact hclosed⟩

end Tate

/-- **Serre's criterion over a field**: over a complete ultrametric nontrivially normed field `K`,
a continuous linear map between model spaces is row compact exactly when it is completely
continuous. Neither a discrete valuation nor spherical completeness is needed. -/
theorem isRowCompact_iff_isCompletelyContinuous {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] {u : C₀(J, K) →L[K] C₀(I, K)} :
    u.IsRowCompact ↔ u.IsCompletelyContinuous :=
  isRowCompact_iff_isCompletelyContinuous_of_isClosed fun L hL ↦
    have : FiniteDimensional K L := Module.Finite.iff_fg.2 hL
    L.closed_of_finiteDimensional

end ContinuousLinearMap
