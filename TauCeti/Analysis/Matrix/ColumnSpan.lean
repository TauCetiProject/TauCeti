/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Matrix columns and column spans in Euclidean space

For `X : Matrix α ι 𝕜`, `X.euclideanCol j : EuclideanSpace 𝕜 α` wraps `X.col j` in
`EuclideanSpace 𝕜 α`, and for `m : Finset ι`, `X.columnSpan m` is the `𝕜`-linear span of
`{X.euclideanCol j | j ∈ m}`, characterized via `Matrix.mem_columnSpan_iff` as the vectors
`Matrix.toEuclideanLin X β` with `β` supported in `m`.
-/

public section

open scoped InnerProductSpace Matrix

namespace Matrix

section EuclideanCol

variable {α ι 𝕜 : Type*}

/-- The `j`-th column of `X : Matrix α ι 𝕜`, viewed as a vector in `EuclideanSpace 𝕜 α`. -/
def euclideanCol (X : Matrix α ι 𝕜) (j : ι) : EuclideanSpace 𝕜 α :=
  WithLp.toLp 2 (X.col j)

/-- Unfolding lemma for `Matrix.euclideanCol`. -/
theorem euclideanCol_def (X : Matrix α ι 𝕜) (j : ι) : X.euclideanCol j = WithLp.toLp 2 (X.col j) :=
  (rfl)

/-- Unwrapping `WithLp.ofLp` of `X.euclideanCol j` recovers `X.col j`. -/
@[simp]
theorem ofLp_euclideanCol (X : Matrix α ι 𝕜) (j : ι) : (X.euclideanCol j).ofLp = X.col j := by
  rw [euclideanCol_def]

/-- Coordinate evaluation of `Matrix.euclideanCol`. -/
@[simp]
theorem euclideanCol_apply (X : Matrix α ι 𝕜) (j : ι) (i : α) : X.euclideanCol j i = X i j := by
  simp [euclideanCol_def]

/-- The inner product of two Euclidean columns is the corresponding entry of `Xᴴ * Y`. -/
theorem inner_euclideanCol [RCLike 𝕜] [Fintype α] (X : Matrix α ι 𝕜) {κ : Type*}
    (Y : Matrix α κ 𝕜) (j : ι) (k : κ) :
    ⟪X.euclideanCol j, Y.euclideanCol k⟫_𝕜 = (Xᴴ * Y) j k := by
  simp [euclideanCol_def, PiLp.inner_apply, Matrix.mul_apply, conjTranspose_apply, mul_comm]

/-- Applying `Matrix.toEuclideanLin X` to `EuclideanSpace.single j a` gives
`a • X.euclideanCol j`. -/
@[simp]
theorem toEuclideanLin_single [RCLike 𝕜] [Fintype ι] [DecidableEq ι] (X : Matrix α ι 𝕜)
    (j : ι) (a : 𝕜) :
    Matrix.toEuclideanLin X (EuclideanSpace.single j a) = a • X.euclideanCol j := by
  rw [Matrix.toLpLin_apply, EuclideanSpace.single, PiLp.ofLp_single,
    Matrix.mulVec_single, op_smul_eq_smul, WithLp.toLp_smul, euclideanCol_def]

/-- `Matrix.toEuclideanLin X β = ∑ j, β j • X.euclideanCol j`. -/
theorem toEuclideanLin_eq_sum_euclideanCol [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (X : Matrix α ι 𝕜) (β : EuclideanSpace 𝕜 ι) :
    Matrix.toEuclideanLin X β = ∑ j, β j • X.euclideanCol j := by
  have hβ : β = ∑ j, EuclideanSpace.single j (β j) := by ext j; simp
  conv_lhs => rw [hβ]
  rw [map_sum]; simp_rw [toEuclideanLin_single]

end EuclideanCol

section ColumnSpan

variable {α ι 𝕜 : Type*}

/-- The submodule of `EuclideanSpace 𝕜 α` spanned by the columns of `X` indexed by `m`. -/
noncomputable def columnSpan [Ring 𝕜] (X : Matrix α ι 𝕜) (m : Finset ι) :
    Submodule 𝕜 (EuclideanSpace 𝕜 α) :=
  Submodule.span 𝕜 (X.euclideanCol '' (m : Set ι))

/-- Unfolding lemma for `Matrix.columnSpan`. -/
theorem columnSpan_def [Ring 𝕜] (X : Matrix α ι 𝕜) (m : Finset ι) :
    X.columnSpan m = Submodule.span 𝕜 (X.euclideanCol '' (m : Set ι)) :=
  (rfl)

/-- The span of the empty set of columns is `⊥`. -/
@[simp]
theorem columnSpan_empty [Ring 𝕜] (X : Matrix α ι 𝕜) : X.columnSpan ∅ = ⊥ := by
  simp [columnSpan_def]

/-- The span of a single column `{j}` is the line spanned by `X.euclideanCol j`. -/
@[simp]
theorem columnSpan_singleton [Ring 𝕜] (X : Matrix α ι 𝕜) (j : ι) :
    X.columnSpan {j} = Submodule.span 𝕜 {X.euclideanCol j} := by simp [columnSpan_def]

/-- Every column indexed by an element of `m` belongs to `X.columnSpan m`. -/
theorem euclideanCol_mem_columnSpan [Ring 𝕜] (X : Matrix α ι 𝕜) {m : Finset ι} {j : ι}
    (hj : j ∈ m) : X.euclideanCol j ∈ X.columnSpan m :=
  Submodule.subset_span ⟨j, hj, rfl⟩

/-- `Matrix.columnSpan` is monotone in the column subset `m`. -/
@[gcongr]
theorem columnSpan_mono [Ring 𝕜] (X : Matrix α ι 𝕜) {m₁ m₂ : Finset ι} (h : m₁ ⊆ m₂) :
    X.columnSpan m₁ ≤ X.columnSpan m₂ :=
  Submodule.span_mono (Set.image_mono (Finset.coe_subset.mpr h))

/-- The column span of a union is the supremum of the column spans. -/
theorem columnSpan_union [Ring 𝕜] [DecidableEq ι] (X : Matrix α ι 𝕜) (m₁ m₂ : Finset ι) :
    X.columnSpan (m₁ ∪ m₂) = X.columnSpan m₁ ⊔ X.columnSpan m₂ := by
  simp only [columnSpan_def, Finset.coe_union, Set.image_union, Submodule.span_union]

/-- Inserting a column index joins its line to the column span. -/
theorem columnSpan_insert [Ring 𝕜] [DecidableEq ι] (X : Matrix α ι 𝕜) (j : ι) (m : Finset ι) :
    X.columnSpan (insert j m) = Submodule.span 𝕜 {X.euclideanCol j} ⊔ X.columnSpan m := by
  rw [← Finset.singleton_union, columnSpan_union, columnSpan_singleton]

/-- If every nonzero coordinate of `β` lies in `m`, then
`Matrix.toEuclideanLin X β ∈ X.columnSpan m`. -/
theorem toEuclideanLin_mem_columnSpan [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (X : Matrix α ι 𝕜) {m : Finset ι} {β : EuclideanSpace 𝕜 ι} (hβ : ∀ j, β j ≠ 0 → j ∈ m) :
    Matrix.toEuclideanLin X β ∈ X.columnSpan m := by
  rw [toEuclideanLin_eq_sum_euclideanCol]
  refine Submodule.sum_mem _ fun j _ ↦ ?_
  by_cases hj : β j = 0
  · simp [hj]
  · exact Submodule.smul_mem _ _ (X.euclideanCol_mem_columnSpan (hβ j hj))

/-- `v` belongs to `X.columnSpan m` iff `v = Matrix.toEuclideanLin X β` for some `β` supported in
`m`. -/
theorem mem_columnSpan_iff [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (X : Matrix α ι 𝕜) {m : Finset ι} {v : EuclideanSpace 𝕜 α} :
    v ∈ X.columnSpan m ↔
      ∃ β : EuclideanSpace 𝕜 ι, (∀ j, β j ≠ 0 → j ∈ m) ∧ Matrix.toEuclideanLin X β = v := by
  refine ⟨fun hv ↦ ?_, fun ⟨β, hβ, hv⟩ ↦ hv ▸ X.toEuclideanLin_mem_columnSpan hβ⟩
  rw [columnSpan_def, Finsupp.mem_span_image_iff_linearCombination] at hv
  obtain ⟨l, hl, rfl⟩ := hv
  refine ⟨WithLp.toLp 2 (l : ι → 𝕜), fun j hj ↦
    (Finsupp.mem_supported _ _).mp hl (Finsupp.mem_support_iff.mpr hj), ?_⟩
  rw [toEuclideanLin_eq_sum_euclideanCol, Finsupp.linearCombination_apply,
    Finsupp.sum_fintype l (fun i a ↦ a • X.euclideanCol i) (fun _ ↦ zero_smul _ _)]

/-- The span of all columns equals the range of `Matrix.toEuclideanLin X`. -/
@[simp]
theorem columnSpan_univ_eq_range_toEuclideanLin [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (X : Matrix α ι 𝕜) :
    X.columnSpan Finset.univ = LinearMap.range (Matrix.toEuclideanLin X) := by
  have hcomp : Matrix.toEuclideanLin X = (WithLp.linearEquiv 2 𝕜 (α → 𝕜)).symm.toLinearMap ∘ₗ
      X.mulVecLin ∘ₗ (WithLp.linearEquiv 2 𝕜 (ι → 𝕜)).toLinearMap := by
    ext x i; simp [Matrix.toLpLin_apply]
  rw [hcomp, LinearMap.range_comp, LinearEquiv.range_comp, Matrix.range_mulVecLin,
    Submodule.map_span, columnSpan_def, Finset.coe_univ, Set.image_univ, ← Set.range_comp]
  congr 1

/-- The dimension of `X.columnSpan m` is at most the number of selected columns `m.card`. -/
theorem finrank_columnSpan_le [Ring 𝕜] [StrongRankCondition 𝕜] (X : Matrix α ι 𝕜) (m : Finset ι) :
    Module.finrank 𝕜 (X.columnSpan m) ≤ m.card :=
  (finrank_span_le_ncard _ (m.finite_toSet.image _)).trans
    ((Set.ncard_image_le m.finite_toSet).trans_eq (Set.ncard_coe_finset m))

end ColumnSpan

end Matrix
