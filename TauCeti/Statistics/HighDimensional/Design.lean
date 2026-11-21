/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Design matrices: columns and column spans in Euclidean space

For `X : Matrix α ι 𝕜`, `X.designCol j : EuclideanSpace 𝕜 α` is its `j`-th column as a vector in
`EuclideanSpace 𝕜 α`, and for `m : Finset ι`, `X.columnSpan m` is the `𝕜`-linear span of
`{X.designCol j | j ∈ m}`.
-/

public section

open scoped InnerProductSpace Matrix

namespace Matrix

section DesignCol

variable {α ι 𝕜 : Type*}

/-- The `j`-th column of `X : Matrix α ι 𝕜`, viewed as a vector in `EuclideanSpace 𝕜 α`. -/
def designCol (X : Matrix α ι 𝕜) (j : ι) : EuclideanSpace 𝕜 α :=
  WithLp.toLp 2 (fun i ↦ X i j)

/-- Unfolding lemma for `Matrix.designCol`. -/
theorem designCol_def (X : Matrix α ι 𝕜) (j : ι) :
    X.designCol j = WithLp.toLp 2 (fun i ↦ X i j) :=
  (rfl)

/-- Unwrapping `WithLp.ofLp` of a design column recovers the column function `i ↦ X i j`. -/
theorem ofLp_designCol (X : Matrix α ι 𝕜) (j : ι) :
    WithLp.ofLp (X.designCol j) = fun i ↦ X i j := by rw [designCol_def]

/-- Coordinate evaluation of `Matrix.designCol`. -/
@[simp]
theorem designCol_apply (X : Matrix α ι 𝕜) (j : ι) (i : α) :
    X.designCol j i = X i j := by rw [designCol_def]

/-- The columns of the zero matrix are zero. -/
@[simp]
theorem designCol_zero [AddCommGroup 𝕜] (j : ι) : (0 : Matrix α ι 𝕜).designCol j = 0 :=
  WithLp.ofLp_injective 2 (by ext i; rfl)

/-- Column extraction commutes with matrix addition. -/
@[simp]
theorem designCol_add [AddCommGroup 𝕜] (X Y : Matrix α ι 𝕜) (j : ι) :
    (X + Y).designCol j = X.designCol j + Y.designCol j :=
  WithLp.ofLp_injective 2 (by ext i; rfl)

/-- Column extraction commutes with negation. -/
@[simp]
theorem designCol_neg [AddCommGroup 𝕜] (X : Matrix α ι 𝕜) (j : ι) :
    (-X).designCol j = -X.designCol j :=
  WithLp.ofLp_injective 2 (by ext i; rfl)

/-- Column extraction commutes with matrix subtraction. -/
@[simp]
theorem designCol_sub [AddCommGroup 𝕜] (X Y : Matrix α ι 𝕜) (j : ι) :
    (X - Y).designCol j = X.designCol j - Y.designCol j :=
  WithLp.ofLp_injective 2 (by ext i; rfl)

/-- Column extraction commutes with scalar multiplication. -/
@[simp]
theorem designCol_smul {R : Type*} [SMul R 𝕜] (c : R) (X : Matrix α ι 𝕜) (j : ι) :
    (c • X).designCol j = c • X.designCol j :=
  WithLp.ofLp_injective 2 (by ext i; rfl)

/-- The inner product of two design columns is the corresponding entry of `Xᴴ * Y`. -/
theorem inner_designCol [RCLike 𝕜] [Fintype α] (X : Matrix α ι 𝕜) {κ : Type*}
    (Y : Matrix α κ 𝕜) (j : ι) (k : κ) :
    ⟪X.designCol j, Y.designCol k⟫_𝕜 = (Xᴴ * Y) j k := by
  simp [designCol_def, PiLp.inner_apply, Matrix.mul_apply, conjTranspose_apply, mul_comm]

/-- Applying `Matrix.toEuclideanLin X` to `EuclideanSpace.single j a` gives `a • X.designCol j`. -/
@[simp]
theorem toEuclideanLin_single [RCLike 𝕜] [Fintype ι] [DecidableEq ι] (X : Matrix α ι 𝕜)
    (j : ι) (a : 𝕜) :
    Matrix.toEuclideanLin X (EuclideanSpace.single j a) = a • X.designCol j := by
  ext i; simp [Matrix.toLpLin_apply]

/-- `Matrix.toEuclideanLin X β = ∑ j, β j • X.designCol j`. -/
theorem toEuclideanLin_eq_sum_designCol [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (X : Matrix α ι 𝕜) (β : EuclideanSpace 𝕜 ι) :
    Matrix.toEuclideanLin X β = ∑ j, β j • X.designCol j := by
  ext i; simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, mul_comm]

end DesignCol

section ColumnSpan

variable {α ι 𝕜 : Type*}

/-- The submodule of `EuclideanSpace 𝕜 α` spanned by the columns of `X` indexed by `m`. -/
noncomputable def columnSpan [Ring 𝕜] (X : Matrix α ι 𝕜) (m : Finset ι) :
    Submodule 𝕜 (EuclideanSpace 𝕜 α) :=
  Submodule.span 𝕜 (X.designCol '' (m : Set ι))

/-- Unfolding lemma for `Matrix.columnSpan`. -/
theorem columnSpan_def [Ring 𝕜] (X : Matrix α ι 𝕜) (m : Finset ι) :
    X.columnSpan m = Submodule.span 𝕜 (X.designCol '' (m : Set ι)) :=
  (rfl)

/-- The span of the empty set of columns is `⊥`. -/
@[simp]
theorem columnSpan_empty [Ring 𝕜] (X : Matrix α ι 𝕜) : X.columnSpan ∅ = ⊥ := by
  simp [columnSpan_def]

/-- The span of a single column `{j}` is the line spanned by `X.designCol j`. -/
@[simp]
theorem columnSpan_singleton [Ring 𝕜] (X : Matrix α ι 𝕜) (j : ι) :
    X.columnSpan {j} = Submodule.span 𝕜 {X.designCol j} := by
  simp [columnSpan_def]

/-- Every column indexed by an element of `m` belongs to `X.columnSpan m`. -/
theorem designCol_mem_columnSpan [Ring 𝕜] (X : Matrix α ι 𝕜) {m : Finset ι} {j : ι}
    (hj : j ∈ m) :
    X.designCol j ∈ X.columnSpan m :=
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
    X.columnSpan (insert j m) = Submodule.span 𝕜 {X.designCol j} ⊔ X.columnSpan m := by
  rw [← Finset.singleton_union, columnSpan_union, columnSpan_singleton]

/-- If every nonzero coordinate of `β` lies in `m`, then
`Matrix.toEuclideanLin X β ∈ X.columnSpan m`. -/
theorem toEuclideanLin_mem_columnSpan [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (X : Matrix α ι 𝕜) {m : Finset ι} {β : EuclideanSpace 𝕜 ι}
    (hβ : ∀ j, β j ≠ 0 → j ∈ m) :
    Matrix.toEuclideanLin X β ∈ X.columnSpan m := by
  rw [toEuclideanLin_eq_sum_designCol]
  refine Submodule.sum_mem _ fun j _ ↦ ?_
  by_cases hj : β j = 0
  · simp [hj]
  · exact Submodule.smul_mem _ _ (X.designCol_mem_columnSpan (hβ j hj))

/-- The span of all columns equals the range of `Matrix.toEuclideanLin X`. -/
@[simp]
theorem columnSpan_univ_eq_range_toEuclideanLin [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (X : Matrix α ι 𝕜) :
    X.columnSpan Finset.univ = LinearMap.range (Matrix.toEuclideanLin X) := by
  refine le_antisymm ?_ fun _ ⟨β, hβ⟩ ↦
    hβ ▸ X.toEuclideanLin_mem_columnSpan fun _ _ ↦ Finset.mem_univ _
  rw [columnSpan_def, Submodule.span_le]
  rintro _ ⟨j, -, rfl⟩
  exact ⟨EuclideanSpace.single j (1 : 𝕜), by simp⟩

/-- The dimension of `X.columnSpan m` is at most the number of selected columns `m.card`. -/
theorem finrank_columnSpan_le [Ring 𝕜] [StrongRankCondition 𝕜] (X : Matrix α ι 𝕜)
    (m : Finset ι) :
    Module.finrank 𝕜 (X.columnSpan m) ≤ m.card :=
  (finrank_span_le_ncard _ (m.finite_toSet.image _)).trans
    ((Set.ncard_image_le m.finite_toSet).trans_eq (Set.ncard_coe_finset m))

end ColumnSpan

end Matrix
