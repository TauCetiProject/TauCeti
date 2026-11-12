/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Compactoid
public import TauCeti.Analysis.Normed.Operator.RowCompact
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Compactoid

/-!
# Row compactness is compactoid image

Let `K` be a nontrivially normed field and `I`, `J` discrete index types. For a continuous
linear map `u : C₀(J, K) →L[K] C₀(I, K)` between model spaces, the `i`-th coordinates of the
vectors `u x` with `‖x‖ ≤ 1` include the entries `u.matrixCoeff i j = u (single j 1) i` of the
`i`-th row of its matrix, and over an ultrametric field they are bounded by the row norm
`rᵢ(u)`. A subset of `C₀(I, K)` is compactoid exactly when it is bounded and its coordinates
decay uniformly (`TauCeti.isCompactoidSet_iff_isBounded_and_exists_finset_forall_norm_lt`), so
over an ultrametric field `u` is row compact exactly when it maps the closed unit ball to a
compactoid set (`ContinuousLinearMap.isRowCompact_iff_hasCompactoidImage`). Neither completeness,
nor discreteness of the valuation, nor spherical completeness is used.

Together with Serre's criterion `ContinuousLinearMap.isRowCompact_iff_isCompletelyContinuous`
this identifies, between model spaces over a complete ultrametric field, the three notions of
compact operator: row compactness, compactoid image and complete continuity. Every topologically
compact operator between model spaces is row compact (`IsCompactOperator.isRowCompact`), while
over a field such as `ℂ_p`, which is not locally compact, the converse fails already for the
identity of `C₀(I, K)` with `I` a singleton.

The ultrametric inequality is needed for the converse direction: over `ℝ`, the operator on
`C₀(ℕ, ℝ)` with entries `aᵢⱼ = 1 / (i + 1)` for `j ≤ i` and `0` otherwise has row norms
`1 / (i + 1)`, but maps the vectors that are `1` on `{0, …, n}` and `0` elsewhere to vectors whose
first `n + 1` coordinates are `1`.

## Main results

* `ContinuousLinearMap.HasCompactoidImage.isRowCompact`: a map between model spaces with
  compactoid image is row compact.
* `ContinuousLinearMap.IsRowCompact.hasCompactoidImage`: over an ultrametric field, a row-compact
  map has compactoid image.
* `ContinuousLinearMap.isRowCompact_iff_hasCompactoidImage`: the equivalence.
* `IsCompactOperator.isRowCompact`: compact operators between model spaces are row compact.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §3.
* W. H. Schikhof, *Banach spaces over nonarchimedean valued fields*, Topology Proceedings **24**
  (1999), 547–581, §2.15.
-/

public section

open Filter Metric Topology ZeroAtInftyContinuousMap TauCeti
open scoped ZeroAtInfty

variable {I J K : Type*} [TopologicalSpace I] [DiscreteTopology I] [TopologicalSpace J]
  [DiscreteTopology J] [DecidableEq J] [NontriviallyNormedField K]

namespace ContinuousLinearMap

/-- **A map between model spaces with compactoid image is row compact**: the entries of a row are
coordinates of images of the unit vectors, which lie in the closed unit ball. -/
theorem HasCompactoidImage.isRowCompact {u : C₀(J, K) →L[K] C₀(I, K)}
    (hu : u.HasCompactoidImage) : u.IsRowCompact := by
  refine isRowCompact_iff_tendsto_rowNorm.2 (tendsto_order.2 ⟨fun a ha ↦ Eventually.of_forall
    fun i ↦ ha.trans_le (u.rowNorm_nonneg i), fun ε hε ↦ ?_⟩)
  obtain ⟨T, hT⟩ := (hasCompactoidImage_iff.1 hu).exists_finset_forall_norm_lt (half_pos hε)
  refine eventually_cofinite.2 (T.finite_toSet.subset fun i hi ↦ by_contra fun hiT ↦ hi ?_)
  refine (rowNorm_le_of_forall_le (half_pos hε).le fun j ↦ ?_).trans_lt (half_lt_self hε)
  rw [matrixCoeff_apply]
  exact (hT _ (Set.mem_image_of_mem u (by simp [norm_single])) i hiT).le

/-- **A row-compact map between model spaces over an ultrametric field has compactoid image**:
the coordinates of the images of vectors of norm at most one are bounded by the row norms. -/
theorem IsRowCompact.hasCompactoidImage [IsUltrametricDist K] {u : C₀(J, K) →L[K] C₀(I, K)}
    (hu : u.IsRowCompact) : u.HasCompactoidImage := by
  rw [hasCompactoidImage_iff, isCompactoidSet_iff_isBounded_and_exists_finset_forall_norm_lt]
  refine ⟨isBounded_closedBall.image u, fun ε hε ↦ ?_⟩
  have hfin : {i | ¬u.rowNorm i < ε}.Finite :=
    eventually_cofinite.1 (hu.tendsto_rowNorm.eventually_lt_const hε)
  refine ⟨hfin.toFinset, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ i hi
  have hi : u.rowNorm i < ε := by simpa using hi
  calc ‖u x i‖ ≤ u.rowNorm i * ‖x‖ := u.norm_apply_apply_le_rowNorm_mul x i
    _ ≤ u.rowNorm i * 1 := mul_le_mul_of_nonneg_left (by simpa using hx) (u.rowNorm_nonneg i)
    _ < ε := by rwa [mul_one]

/-- **Row compactness is compactoid image**: over an ultrametric nontrivially normed field, a map
between model spaces is row compact exactly when it maps the closed unit ball to a compactoid
set. -/
theorem isRowCompact_iff_hasCompactoidImage [IsUltrametricDist K]
    {u : C₀(J, K) →L[K] C₀(I, K)} : u.IsRowCompact ↔ u.HasCompactoidImage :=
  ⟨IsRowCompact.hasCompactoidImage, HasCompactoidImage.isRowCompact⟩

end ContinuousLinearMap

/-- **Compact operators between model spaces are row compact.** -/
theorem IsCompactOperator.isRowCompact {u : C₀(J, K) →L[K] C₀(I, K)}
    (hu : IsCompactOperator u) : u.IsRowCompact :=
  hu.hasCompactoidImage.isRowCompact
