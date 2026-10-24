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
with range in a closed finitely generated submodule are row compact
(`ContinuousLinearMap.isRowCompact_of_fg_of_isClosed_of_range_le`), and closedness of row
compactness under operator-norm limits gives the criterion.

Over a general coefficient ring, closedness of finitely generated submodules is a genuine
hypothesis rather than a formal consequence of completeness, so it is kept explicit. The row-decay
theory itself, and the implication from row compactness to complete continuity, do not use it.

## Main results

* `ContinuousLinearMap.isRowCompact_of_fg_of_isClosed_of_range_le`: a continuous map whose range
  lies in a closed finitely generated submodule of `C₀(I, R)` is row compact.
* `ContinuousLinearMap.IsCompletelyContinuous.isRowCompact_of_forall_fg_isClosed`,
  `ContinuousLinearMap.isRowCompact_iff_isCompletelyContinuous_of_forall_fg_isClosed`: if
  finitely generated submodules of `C₀(I, R)` are closed, complete continuity is equivalent to
  row compactness.
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

section Tate

variable [NormedRing R] [IsUltrametricDist R] [CompleteSpace R] [TauCeti.NormedRing.IsTate R]

/-- **Maps with range in a closed finitely generated submodule are row compact** over a complete
ultrametric Tate ring. In particular, a map of finite rank is row compact as soon as some finitely
generated submodule containing its range is closed. -/
theorem isRowCompact_of_fg_of_isClosed_of_range_le {L : Submodule R C₀(I, R)} (hL : L.FG)
    (hLc : IsClosed (L : Set C₀(I, R))) {u : C₀(J, R) →L[R] C₀(I, R)}
    (hu : (u : C₀(J, R) →ₗ[R] C₀(I, R)).range ≤ L) : u.IsRowCompact := by
  obtain ⟨s, rfl⟩ := hL
  have : CompleteSpace (Submodule.span R (s : Set C₀(I, R))) := hLc.completeSpace_coe
  let v : s → Submodule.span R (s : Set C₀(I, R)) := fun k ↦ ⟨k, Submodule.subset_span k.2⟩
  have hv : Submodule.span R (Set.range v) = ⊤ := by
    convert Submodule.span_span_coe_preimage (R := R) (s := (s : Set C₀(I, R))) using 2
    ext x
    exact ⟨by rintro ⟨k, rfl⟩; exact k.2, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
  obtain ⟨C, hC₀, hC⟩ := TauCeti.exists_linearCombination_eq_and_norm_le v hv
  refine isRowCompact_of_apply_single_eq_sum (fun k : s ↦ (k : C₀(I, R))) (B := C * ‖u‖)
    fun j ↦ ?_
  obtain ⟨c, hc, hcn⟩ :=
    hC ⟨u (ZeroAtInftyContinuousMap.single j 1), hu (LinearMap.mem_range_self _ _)⟩
  refine ⟨c, fun k ↦ (norm_le_pi_norm c k).trans (hcn.trans ?_), ?_⟩
  · refine mul_le_mul_of_nonneg_left ?_ hC₀.le
    simpa [norm_single] using le_ringOpNorm u (ZeroAtInftyContinuousMap.single j (1 : R))
  · -- Leave the submodule: the coercion of `∑ k, c k • v k` is `∑ k, c k • (k : C₀(I, R))`,
    -- since `v k` is `k` itself.
    have hcoe := congrArg Subtype.val hc
    rw [Submodule.coe_sum] at hcoe
    exact hcoe.symm.trans (Finset.sum_congr rfl fun k _ ↦ Submodule.coe_smul (c k) (v k))

/-- **Serre's criterion**: if the finitely generated submodules of the target model space are
closed, every completely continuous map between model spaces over a complete ultrametric Tate
ring is row compact. -/
theorem IsCompletelyContinuous.isRowCompact_of_forall_fg_isClosed {u : C₀(J, R) →L[R] C₀(I, R)}
    (hu : u.IsCompletelyContinuous)
    (hclosed : ∀ L : Submodule R C₀(I, R), L.FG → IsClosed (L : Set C₀(I, R))) :
    u.IsRowCompact := by
  choose v hv huv using fun n : ℕ ↦
    isCompletelyContinuous_iff_ringOpNorm.1 hu (1 / (n + 1)) Nat.one_div_pos_of_nat
  refine isRowCompact_of_tendsto
    (squeeze_zero (fun n ↦ ringOpNorm_nonneg _) (fun n ↦ (huv n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat) (Eventually.of_forall fun n ↦ ?_)
  obtain ⟨L, hL, hrange⟩ := LinearMap.isFiniteRank_iff.1 (hv n)
  exact isRowCompact_of_fg_of_isClosed_of_range_le hL (hclosed L hL) hrange

/-- If the finitely generated submodules of the target model space are closed, a map between
model spaces over a complete ultrametric Tate ring is row compact exactly when it is completely
continuous. -/
theorem isRowCompact_iff_isCompletelyContinuous_of_forall_fg_isClosed
    (hclosed : ∀ L : Submodule R C₀(I, R), L.FG → IsClosed (L : Set C₀(I, R)))
    {u : C₀(J, R) →L[R] C₀(I, R)} : u.IsRowCompact ↔ u.IsCompletelyContinuous :=
  ⟨IsRowCompact.isCompletelyContinuous, fun hu ↦ hu.isRowCompact_of_forall_fg_isClosed hclosed⟩

end Tate

/-- **Serre's criterion over a field**: over a complete ultrametric nontrivially normed field `K`,
a continuous linear map between model spaces is row compact exactly when it is completely
continuous. Neither a discrete valuation nor spherical completeness is needed. -/
theorem isRowCompact_iff_isCompletelyContinuous {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] {u : C₀(J, K) →L[K] C₀(I, K)} :
    u.IsRowCompact ↔ u.IsCompletelyContinuous :=
  isRowCompact_iff_isCompletelyContinuous_of_forall_fg_isClosed fun L hL ↦
    have : FiniteDimensional K L := Module.Finite.iff_fg.2 hL
    L.closed_of_finiteDimensional

end ContinuousLinearMap
