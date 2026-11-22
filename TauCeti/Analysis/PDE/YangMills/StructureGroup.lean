/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Unitary.Matrix
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.Logic.Equiv.Fin.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.PosDef
import TauCeti.Analysis.Matrix.Frobenius

/-!
# Compact matrix structure groups

The gauge theory of connections on Euclidean space takes as structure group a compact group `G`
of unitary matrices, with Lie algebra `𝔤 = {X : exp (t X) ∈ G for all real t}` acting on itself
by `Ad(g) X = g X g⁻¹`, together with an inner product `⟨·,·⟩` on `𝔤` that is invariant under
`Ad(G)`. All pointwise norms of connections and curvatures, `|A|² = ∑ⱼ ⟨Aⱼ, Aⱼ⟩`, are formed
with this inner product, and its `Ad`-invariance is what makes them gauge invariant.

This file bundles such a triple as `TauCeti.CompactMatrixStructureGroup n`: a closed subgroup of
`Matrix.unitaryGroup n ℂ` (closed subgroups of `U(n)` are exactly the compact ones), with a
symmetric positive-definite `Ad`-invariant bilinear form on its Lie algebra
`ClosedSubgroup.matrixLieAlgebra`. The group need not be connected, so `Ad`-invariance is part of
the data: it implies that every `ad X` is skew-adjoint, but the converse fails for disconnected
groups.

## Main definitions

* `TauCeti.CompactMatrixStructureGroup`: a closed subgroup of `U(n)` with an `Ad`-invariant inner
  product on its Lie algebra.
* `TauCeti.CompactMatrixStructureGroup.ofTraceForm`: every closed subgroup of `U(n)` with the
  trace form `⟨X, Y⟩ = -Re tr (X Y)`.
* `TauCeti.CompactMatrixStructureGroup.unitary`,
  `TauCeti.CompactMatrixStructureGroup.specialUnitary`: `U(n)` and `SU(n)` with the trace form.
* `TauCeti.CompactMatrixStructureGroup.restrict`: the restriction to a closed subgroup.
* `TauCeti.CompactMatrixStructureGroup.tangentSpace`: the tangent space `g · 𝔤` of `S.group` at
  `g ∈ S.group`.
* `TauCeti.CompactMatrixStructureGroup.reindex`: transports a structure group along a bijection
  `e : n ≃ m`.
* `TauCeti.CompactMatrixStructureGroup.prod`: the block-diagonal product of two structure groups,
  with the orthogonal sum of the inner products.
* `TauCeti.CompactMatrixStructureGroup.blockProd`: the `Fin (N₁ + N₂)`-indexed block-diagonal
  product via `finSumFinEquiv`, with Lie-algebra isomorphism `blockProdLieEquiv`.

## Main results

* `TauCeti.CompactMatrixStructureGroup.innerForm_matrixAdjointRepresentation`: each `Ad(g)` is an
  isometry of the inner product.
* `TauCeti.CompactMatrixStructureGroup.innerForm_lie_left`: each `ad X` is skew-adjoint,
  `⟨[X, Y], Z⟩ = -⟨Y, [X, Z]⟩`.
* `TauCeti.CompactMatrixStructureGroup.ofTraceForm_neg_trace_mul`: for the trace form,
  `-tr (X Y)` is real and equals the inner product.
* `TauCeti.CompactMatrixStructureGroup.matrixLieAlgebra_eq_bot_of_finite`: finite structure
  groups have trivial Lie algebra `⊥`.
* `TauCeti.CompactMatrixStructureGroup.tangentSpace_eq_mulRight`,
  `TauCeti.CompactMatrixStructureGroup.range_mvfderiv_matrixInclusion`: the tangent space at `g`
  is `g · 𝔤 = 𝔤 · g`.

## References

* S.-J. Oh and D. Tataru, *The Yang–Mills heat flow and the caloric gauge*, Astérisque 436
  (2022), arXiv:1709.08599, Section 1 (the structure group and its invariant inner product).
* S.-J. Oh and D. Tataru, *The hyperbolic Yang–Mills equation for connections in an arbitrary
  topological class*, Comm. Math. Phys. 365 (2019), arXiv:1709.08604, Section 1.
-/

public section

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

open scoped Matrix

namespace TauCeti

/-- A **compact matrix structure group**: a closed (equivalently, compact) subgroup `group` of the
unitary group `U(n)`, together with an inner product `innerForm` on its Lie algebra
`group.matrixLieAlgebra`, given as a symmetric positive-definite real bilinear form invariant under
the adjoint action `Ad(g) X = g X g⁻¹` of every `g ∈ group`. -/
structure CompactMatrixStructureGroup (n : Type*) [Fintype n] [DecidableEq n] where
  /-- The structure group, a closed subgroup of the unitary group. -/
  group : ClosedSubgroup (Matrix.unitaryGroup n ℂ)
  /-- The inner product on the Lie algebra of the structure group. -/
  innerForm : LinearMap.BilinForm ℝ group.matrixLieAlgebra
  /-- The inner product is symmetric. -/
  isSymm_innerForm : innerForm.IsSymm
  /-- The inner product is positive definite. -/
  posDef_innerForm : innerForm.toQuadraticMap.PosDef
  /-- The inner product is invariant under the adjoint action of the structure group. -/
  isInvariantForm_innerForm :
    Representation.IsInvariantForm group.matrixAdjointRepresentation innerForm

namespace CompactMatrixStructureGroup

variable {n : Type*} [Fintype n] [DecidableEq n] (S : CompactMatrixStructureGroup n)

/-- Each `Ad(g)`, `g ∈ G`, is an isometry of the inner product. -/
@[simp]
theorem innerForm_matrixAdjointRepresentation (g : S.group) (X Y : S.group.matrixLieAlgebra) :
    S.innerForm (S.group.matrixAdjointRepresentation g X)
      (S.group.matrixAdjointRepresentation g Y) = S.innerForm X Y :=
  Representation.isInvariantForm_iff.mp S.isInvariantForm_innerForm g X Y

/-- The inner product is invariant under every `ad X`, in the sense of Mathlib's
`LinearMap.BilinForm.lieInvariant`. -/
theorem lieInvariant_innerForm : S.innerForm.lieInvariant S.group.matrixLieAlgebra :=
  ClosedSubgroup.lieInvariant_of_isInvariantForm S.isInvariantForm_innerForm

/-- Each `ad X` is skew-adjoint for the inner product: `⟨[X, Y], Z⟩ = -⟨Y, [X, Z]⟩`. -/
theorem innerForm_lie_left (X Y Z : S.group.matrixLieAlgebra) :
    S.innerForm ⁅X, Y⁆ Z = -S.innerForm Y ⁅X, Z⁆ :=
  S.lieInvariant_innerForm X Y Z

/-- The inner product is symmetric. -/
theorem innerForm_comm (X Y : S.group.matrixLieAlgebra) : S.innerForm X Y = S.innerForm Y X :=
  S.isSymm_innerForm.eq X Y

/-- The inner product of a nonzero element with itself is positive. -/
theorem innerForm_self_pos {X : S.group.matrixLieAlgebra} (hX : X ≠ 0) :
    0 < S.innerForm X X :=
  S.posDef_innerForm X hX

/-- The inner product of an element with itself is nonnegative. -/
theorem innerForm_self_nonneg (X : S.group.matrixLieAlgebra) : 0 ≤ S.innerForm X X :=
  S.posDef_innerForm.nonneg X

/-- An element is zero exactly when its inner product with itself vanishes. -/
@[simp]
theorem innerForm_self_eq_zero {X : S.group.matrixLieAlgebra} : S.innerForm X X = 0 ↔ X = 0 :=
  S.posDef_innerForm.anisotropic.eq_zero_iff

section OfTraceForm

/-- **Every closed subgroup of `U(n)` is a structure group** for the trace form
`⟨X, Y⟩ = -Re tr (X Y)`. -/
-- The type of `innerForm` depends on `group`, so its value can only be stated once `group` reduces.
@[expose]
def ofTraceForm (G : ClosedSubgroup (Matrix.unitaryGroup n ℂ)) :
    CompactMatrixStructureGroup n where
  group := G
  innerForm := G.matrixTraceForm
  isSymm_innerForm := ClosedSubgroup.isSymm_matrixTraceForm
  posDef_innerForm := ClosedSubgroup.posDef_matrixTraceForm
  isInvariantForm_innerForm := ClosedSubgroup.isInvariantForm_matrixTraceForm

@[simp]
theorem ofTraceForm_group (G : ClosedSubgroup (Matrix.unitaryGroup n ℂ)) :
    (ofTraceForm G).group = G :=
  (rfl)

theorem ofTraceForm_innerForm (G : ClosedSubgroup (Matrix.unitaryGroup n ℂ)) :
    (ofTraceForm G).innerForm = G.matrixTraceForm :=
  (rfl)

@[simp]
theorem ofTraceForm_innerForm_apply (G : ClosedSubgroup (Matrix.unitaryGroup n ℂ))
    (X Y : (ofTraceForm G).group.matrixLieAlgebra) :
    (ofTraceForm G).innerForm X Y = -Complex.re ((X : Matrix n n ℂ) * Y).trace :=
  ClosedSubgroup.matrixTraceForm_apply (G := G) X Y

/-- For the trace form, `-tr (X * Y)` is already real and coincides with the real inner product
`(ofTraceForm G).innerForm X Y`. -/
theorem ofTraceForm_neg_trace_mul (G : ClosedSubgroup (Matrix.unitaryGroup n ℂ))
    (X Y : G.matrixLieAlgebra) :
    -((X : Matrix n n ℂ) * (Y : Matrix n n ℂ)).trace = ((ofTraceForm G).innerForm X Y : ℂ) := by
  apply Complex.ext
  · have h := ofTraceForm_innerForm_apply G X Y
    simp [h]
  · have him := Matrix.im_trace_mul_eq_zero_of_conjTranspose_eq_neg
      (ClosedSubgroup.conjTranspose_eq_neg_of_mem_matrixLieAlgebra X.property)
      (ClosedSubgroup.conjTranspose_eq_neg_of_mem_matrixLieAlgebra Y.property)
    simpa [RCLike.im_to_complex] using him

variable (n) in
/-- The full unitary group `U(n)` as a compact matrix structure group with the trace form
`⟨X, Y⟩ = -Re tr (X Y)`. -/
@[expose]
def unitary : CompactMatrixStructureGroup n :=
  ofTraceForm (ClosedSubgroup.unitary n ℂ)

@[simp]
theorem unitary_group : (unitary n).group = ClosedSubgroup.unitary n ℂ :=
  (rfl)

theorem unitary_innerForm : (unitary n).innerForm = (ClosedSubgroup.unitary n ℂ).matrixTraceForm :=
  (rfl)

@[simp]
theorem unitary_innerForm_apply (X Y : (unitary n).group.matrixLieAlgebra) :
    (unitary n).innerForm X Y = -Complex.re ((X : Matrix n n ℂ) * Y).trace :=
  ofTraceForm_innerForm_apply (ClosedSubgroup.unitary n ℂ) X Y

/-- The Lie algebra of `U(n)` consists of all skew-Hermitian matrices `Xᴴ = -X`. -/
theorem mem_matrixLieAlgebra_unitary_iff (X : Matrix n n ℂ) :
    X ∈ (unitary n).group.matrixLieAlgebra ↔ Xᴴ = -X :=
  ClosedSubgroup.mem_matrixLieAlgebra_unitary_iff

variable (n) in
/-- The special unitary group `SU(n)` as a compact matrix structure group with the trace form
`⟨X, Y⟩ = -Re tr (X Y)`. -/
@[expose]
def specialUnitary : CompactMatrixStructureGroup n :=
  ofTraceForm (ClosedSubgroup.specialUnitary n ℂ)

@[simp]
theorem specialUnitary_group : (specialUnitary n).group = ClosedSubgroup.specialUnitary n ℂ :=
  (rfl)

theorem specialUnitary_innerForm :
    (specialUnitary n).innerForm = (ClosedSubgroup.specialUnitary n ℂ).matrixTraceForm :=
  (rfl)

@[simp]
theorem specialUnitary_innerForm_apply (X Y : (specialUnitary n).group.matrixLieAlgebra) :
    (specialUnitary n).innerForm X Y = -Complex.re ((X : Matrix n n ℂ) * Y).trace :=
  ofTraceForm_innerForm_apply (ClosedSubgroup.specialUnitary n ℂ) X Y

/-- The Lie algebra of `SU(n)` consists of the trace-free skew-Hermitian matrices
`Xᴴ = -X` and `tr X = 0`. -/
theorem mem_matrixLieAlgebra_specialUnitary_iff (X : Matrix n n ℂ) :
    X ∈ (specialUnitary n).group.matrixLieAlgebra ↔ Xᴴ = -X ∧ X.trace = 0 :=
  ClosedSubgroup.mem_matrixLieAlgebra_specialUnitary_iff

end OfTraceForm

section Finite

/-- A structure group with finite underlying subgroup has trivial Lie algebra `⊥`. -/
theorem matrixLieAlgebra_eq_bot_of_finite (S : CompactMatrixStructureGroup n)
    (hS : (S.group : Set (Matrix.unitaryGroup n ℂ)).Finite) :
    S.group.matrixLieAlgebra = ⊥ :=
  ClosedSubgroup.matrixLieAlgebra_eq_bot_of_finite hS

/-- A structure group with finite underlying subgroup has subsingleton (zero-dimensional) Lie
algebra `S.group.matrixLieAlgebra`. -/
theorem subsingleton_matrixLieAlgebra_of_finite (S : CompactMatrixStructureGroup n)
    (hS : (S.group : Set (Matrix.unitaryGroup n ℂ)).Finite) :
    Subsingleton S.group.matrixLieAlgebra := by
  refine ⟨fun X Y ↦ Subtype.ext ?_⟩
  have hbot := S.matrixLieAlgebra_eq_bot_of_finite hS
  have hx : (X : Matrix n n ℂ) ∈ (⊥ : LieSubalgebra ℝ (Matrix n n ℂ)) := hbot ▸ X.property
  have hy : (Y : Matrix n n ℂ) ∈ (⊥ : LieSubalgebra ℝ (Matrix n n ℂ)) := hbot ▸ Y.property
  rw [(LieSubalgebra.mem_bot _).1 hx, (LieSubalgebra.mem_bot _).1 hy]

end Finite

section TangentSpace

/-- The tangent space `g · 𝔤` of `S.group` at `g ∈ S.group`, viewed as a real subspace of
`Matrix n n ℂ`. -/
abbrev tangentSpace (g : S.group) : Submodule ℝ (Matrix n n ℂ) :=
  S.group.matrixTangentSpace g

/-- At every `g ∈ S.group`, the left and right translates of the Lie algebra coincide:
`g · 𝔤 = 𝔤 · g`. -/
theorem tangentSpace_eq_mulRight (g : S.group) :
    S.tangentSpace g =
      S.group.matrixLieAlgebra.toSubmodule.map (LinearMap.mulRight ℝ (g : Matrix n n ℂ)) :=
  S.group.matrixTangentSpace_eq_mulRight g

/-- Membership in `S.tangentSpace g` via left multiplication by `g`. -/
theorem mem_tangentSpace_iff_mulLeft (g : S.group) (V : Matrix n n ℂ) :
    V ∈ S.tangentSpace g ↔ ∃ X ∈ S.group.matrixLieAlgebra, (g : Matrix n n ℂ) * X = V :=
  S.group.mem_matrixTangentSpace_iff_mulLeft g V

/-- Membership in `S.tangentSpace g` via right multiplication by `g`. -/
theorem mem_tangentSpace_iff_mulRight (g : S.group) (V : Matrix n n ℂ) :
    V ∈ S.tangentSpace g ↔ ∃ X ∈ S.group.matrixLieAlgebra, X * (g : Matrix n n ℂ) = V :=
  S.group.mem_matrixTangentSpace_iff_mulRight g V

/-- A matrix `V` lies in `S.tangentSpace g` iff `gᴴ * V` lies in `S.group.matrixLieAlgebra`. -/
theorem mem_tangentSpace_iff_conjTranspose_mul (g : S.group) (V : Matrix n n ℂ) :
    V ∈ S.tangentSpace g ↔ (g : Matrix n n ℂ)ᴴ * V ∈ S.group.matrixLieAlgebra :=
  S.group.mem_matrixTangentSpace_iff_conjTranspose_mul g V

/-- A matrix `V` lies in `S.tangentSpace g` iff `V * gᴴ` lies in `S.group.matrixLieAlgebra`. -/
theorem mem_tangentSpace_iff_mul_conjTranspose (g : S.group) (V : Matrix n n ℂ) :
    V ∈ S.tangentSpace g ↔ V * (g : Matrix n n ℂ)ᴴ ∈ S.group.matrixLieAlgebra :=
  S.group.mem_matrixTangentSpace_iff_mul_conjTranspose g V

/-- The tangent space of `S` at the identity is `S.group.matrixLieAlgebra`. -/
theorem tangentSpace_one : S.tangentSpace 1 = S.group.matrixLieAlgebra.toSubmodule :=
  S.group.matrixTangentSpace_one

open scoped Manifold Matrix.Norms.Operator in
/-- At any `g ∈ S.group`, the range of the differential of the matrix inclusion
`S.group → Matrix n n ℂ` is the left translate `g · 𝔤 = S.tangentSpace g`. -/
theorem range_mvfderiv_matrixInclusion (g : S.group) :
    let _ := Matrix.linftyOpTopologicalSpace n n ℂ
    let E := (TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n ℂ))
      S.group.toGL).toSubmodule
    let _ : ChartedSpace E S.group.toGL := S.group.embeddedLieSubgroupData.chartedSpace
    (mvfderiv 𝓘(ℝ, E) (fun k : S.group.toGL ↦ ((k : GL n ℂ) : Matrix n n ℂ))
      (S.group.equivToGL g)).range = S.tangentSpace g :=
  S.group.range_mvfderiv_matrixInclusion g

open scoped Manifold Matrix.Norms.Operator in
/-- At any `g ∈ S.group`, the range of the differential of the matrix inclusion
`S.group → Matrix n n ℂ` is also the right translate `𝔤 · g`. -/
theorem range_mvfderiv_matrixInclusion_eq_mulRight (g : S.group) :
    let _ := Matrix.linftyOpTopologicalSpace n n ℂ
    let E := (TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix n n ℂ))
      S.group.toGL).toSubmodule
    let _ : ChartedSpace E S.group.toGL := S.group.embeddedLieSubgroupData.chartedSpace
    (mvfderiv 𝓘(ℝ, E) (fun k : S.group.toGL ↦ ((k : GL n ℂ) : Matrix n n ℂ))
      (S.group.equivToGL g)).range =
      S.group.matrixLieAlgebra.toSubmodule.map (LinearMap.mulRight ℝ (g : Matrix n n ℂ)) :=
  S.group.range_mvfderiv_matrixInclusion_eq_mulRight g

end TangentSpace

section Restrict

variable {H : ClosedSubgroup (Matrix.unitaryGroup n ℂ)}

/-- **Restriction to a closed subgroup** `H ≤ G`: the Lie algebra of `H` is a Lie subalgebra of
that of `G`, and the inner product restricts to it. -/
-- The type of `innerForm` depends on `group`, so its value can only be stated once `group` reduces.
@[expose]
def restrict (S : CompactMatrixStructureGroup n) (hH : H ≤ S.group) :
    CompactMatrixStructureGroup n where
  group := H
  innerForm := S.innerForm.compl₁₂
    (LieSubalgebra.inclusion (ClosedSubgroup.matrixLieAlgebra_mono hH)).toLinearMap
    (LieSubalgebra.inclusion (ClosedSubgroup.matrixLieAlgebra_mono hH)).toLinearMap
  isSymm_innerForm := ⟨fun X Y ↦ S.innerForm_comm _ _⟩
  posDef_innerForm := LinearMap.BilinForm.posDef_toQuadraticMap_compl₁₂ _ S.posDef_innerForm _
    (LieSubalgebra.inclusion_injective (ClosedSubgroup.matrixLieAlgebra_mono hH))
  isInvariantForm_innerForm := Representation.isInvariantForm_iff.mpr fun g X Y ↦ by
    have hAd (Z : H.matrixLieAlgebra) :
        LieSubalgebra.inclusion (ClosedSubgroup.matrixLieAlgebra_mono hH)
            (H.matrixAdjointRepresentation g Z) =
          S.group.matrixAdjointRepresentation ⟨g, hH g.property⟩
            (LieSubalgebra.inclusion (ClosedSubgroup.matrixLieAlgebra_mono hH) Z) :=
      Subtype.ext (by simp)
    simp only [LinearMap.compl₁₂_apply, LieHom.coe_toLinearMap, hAd,
      innerForm_matrixAdjointRepresentation]

@[simp]
theorem restrict_group (hH : H ≤ S.group) : (S.restrict hH).group = H :=
  (rfl)

/-- The inner product of the restriction is the inner product of the ambient Lie algebra. -/
@[simp]
theorem restrict_innerForm_apply (hH : H ≤ S.group) (X Y : H.matrixLieAlgebra) :
    (S.restrict hH).innerForm X Y =
      S.innerForm (LieSubalgebra.inclusion (ClosedSubgroup.matrixLieAlgebra_mono hH) X)
        (LieSubalgebra.inclusion (ClosedSubgroup.matrixLieAlgebra_mono hH) Y) :=
  (rfl)

end Restrict

section Reindex

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Transport a compact matrix structure group along a bijection of index types `e : n ≃ m`. -/
@[expose]
def reindex (S : CompactMatrixStructureGroup n) (e : n ≃ m) :
    CompactMatrixStructureGroup m where
  group := S.group.reindex e
  innerForm := S.innerForm.compl₁₂
    (S.group.matrixLieAlgebraReindexEquiv e).symm.toLinearEquiv.toLinearMap
    (S.group.matrixLieAlgebraReindexEquiv e).symm.toLinearEquiv.toLinearMap
  isSymm_innerForm := ⟨fun X Y ↦ S.innerForm_comm _ _⟩
  posDef_innerForm := LinearMap.BilinForm.posDef_toQuadraticMap_compl₁₂ _ S.posDef_innerForm _
    (S.group.matrixLieAlgebraReindexEquiv e).symm.toLinearEquiv.injective
  isInvariantForm_innerForm := Representation.isInvariantForm_iff.mpr fun g X Y ↦ by
    let u := (Matrix.UnitaryGroup.reindexEquiv e).symm g.val
    have hu : u ∈ S.group := (ClosedSubgroup.mem_reindex_iff e).mp g.property
    have hg : g = ⟨Matrix.UnitaryGroup.reindexEquiv e u,
        ClosedSubgroup.reindexEquiv_mem_reindex e hu⟩ :=
      Subtype.ext (by simp [u])
    rw [hg]
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv]
    rw [ClosedSubgroup.matrixLieAlgebraReindexEquiv_symm_matrixAdjointRepresentation e hu,
      ClosedSubgroup.matrixLieAlgebraReindexEquiv_symm_matrixAdjointRepresentation e hu,
      innerForm_matrixAdjointRepresentation]

@[simp]
theorem reindex_group (e : n ≃ m) : (S.reindex e).group = S.group.reindex e :=
  (rfl)

/-- The inner product on `(S.reindex e).group.matrixLieAlgebra` pulls back via inverse
reindexing. -/
@[simp]
theorem reindex_innerForm_apply (e : n ≃ m) (X Y : (S.group.reindex e).matrixLieAlgebra) :
    (S.reindex e).innerForm X Y =
      S.innerForm ((S.group.matrixLieAlgebraReindexEquiv e).symm X)
        ((S.group.matrixLieAlgebraReindexEquiv e).symm Y) :=
  (rfl)

/-- Reindexing preserves the inner product on `S.group.matrixLieAlgebra`. -/
theorem reindex_innerForm_map (e : n ≃ m) (X Y : S.group.matrixLieAlgebra) :
    (S.reindex e).innerForm (S.group.matrixLieAlgebraReindexEquiv e X)
      (S.group.matrixLieAlgebraReindexEquiv e Y) = S.innerForm X Y := by
  simp

end Reindex

section Prod

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **The block-diagonal product of structure groups**: the closed subgroup
`G₁ × G₂ = {diag(g₁, g₂)}` of `U(n ⊕ m)`, whose Lie algebra is `𝔤₁ × 𝔤₂`, with the orthogonal sum
`⟨X, Y⟩ = ⟨X₁, Y₁⟩₁ + ⟨X₂, Y₂⟩₂` of the inner products on the diagonal blocks. -/
-- The type of `innerForm` depends on `group`, so its value can only be stated once `group` reduces.
@[expose]
def prod (S₁ : CompactMatrixStructureGroup n) (S₂ : CompactMatrixStructureGroup m) :
    CompactMatrixStructureGroup (n ⊕ m) where
  group := S₁.group.fromBlocksProd S₂.group
  innerForm :=
    (S₁.innerForm.compl₁₂ (LinearMap.fst ℝ _ _) (LinearMap.fst ℝ _ _) +
        S₂.innerForm.compl₁₂ (LinearMap.snd ℝ _ _) (LinearMap.snd ℝ _ _)).compl₁₂
      (S₁.group.matrixLieAlgebraFromBlocksProdEquiv S₂.group).toLinearEquiv.toLinearMap
      (S₁.group.matrixLieAlgebraFromBlocksProdEquiv S₂.group).toLinearEquiv.toLinearMap
  isSymm_innerForm := ⟨fun X Y ↦ by
    simp only [LinearMap.compl₁₂_apply, LinearMap.add_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, S₁.innerForm_comm, S₂.innerForm_comm]⟩
  posDef_innerForm := by
    refine LinearMap.BilinForm.posDef_toQuadraticMap_compl₁₂ _ ?_ _
      (S₁.group.matrixLieAlgebraFromBlocksProdEquiv S₂.group).toLinearEquiv.injective
    -- The quadratic map of the orthogonal sum of the two forms is, by definition, the product
    -- `QuadraticMap.prod` of their quadratic maps.
    exact S₁.posDef_innerForm.prod S₂.posDef_innerForm
  isInvariantForm_innerForm := Representation.isInvariantForm_iff.mpr fun g X Y ↦ by
    obtain ⟨g₁, h₁, g₂, h₂, hg⟩ := ClosedSubgroup.mem_fromBlocksProd_iff.mp g.property
    have hg' : g = ⟨Matrix.UnitaryGroup.sum (g₁, g₂),
        ClosedSubgroup.sum_mem_fromBlocksProd h₁ h₂⟩ :=
      Subtype.ext (Subtype.ext (by simpa using hg))
    subst hg'
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv]
    rw [ClosedSubgroup.matrixLieAlgebraFromBlocksProdEquiv_matrixAdjointRepresentation h₁ h₂ X,
      ClosedSubgroup.matrixLieAlgebraFromBlocksProdEquiv_matrixAdjointRepresentation h₁ h₂ Y]
    simp only [LinearMap.add_apply, LinearMap.compl₁₂_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, innerForm_matrixAdjointRepresentation]

@[simp]
theorem prod_group (S₁ : CompactMatrixStructureGroup n) (S₂ : CompactMatrixStructureGroup m) :
    (S₁.prod S₂).group = S₁.group.fromBlocksProd S₂.group :=
  (rfl)

/-- The inner product of the product is the sum of the inner products of the diagonal blocks. -/
@[simp]
theorem prod_innerForm_apply (S₁ : CompactMatrixStructureGroup n)
    (S₂ : CompactMatrixStructureGroup m)
    (X Y : (S₁.group.fromBlocksProd S₂.group).matrixLieAlgebra) :
    (S₁.prod S₂).innerForm X Y =
      S₁.innerForm (S₁.group.matrixLieAlgebraFromBlocksProdEquiv S₂.group X).1
          (S₁.group.matrixLieAlgebraFromBlocksProdEquiv S₂.group Y).1 +
        S₂.innerForm (S₁.group.matrixLieAlgebraFromBlocksProdEquiv S₂.group X).2
          (S₁.group.matrixLieAlgebraFromBlocksProdEquiv S₂.group Y).2 :=
  (rfl)

end Prod

section BlockProd

/-- The block-diagonal product of structure groups on `Fin N₁` and `Fin N₂`, landing on
`Fin (N₁ + N₂)` via `finSumFinEquiv`. -/
@[expose]
def blockProd {N₁ N₂ : ℕ} (S₁ : CompactMatrixStructureGroup (Fin N₁))
    (S₂ : CompactMatrixStructureGroup (Fin N₂)) : CompactMatrixStructureGroup (Fin (N₁ + N₂)) :=
  (S₁.prod S₂).reindex finSumFinEquiv

@[simp]
theorem blockProd_group {N₁ N₂ : ℕ} (S₁ : CompactMatrixStructureGroup (Fin N₁))
    (S₂ : CompactMatrixStructureGroup (Fin N₂)) :
    (S₁.blockProd S₂).group = (S₁.group.fromBlocksProd S₂.group).reindex finSumFinEquiv :=
  (rfl)

/-- The canonical Lie-algebra isomorphism between `(S₁.blockProd S₂).group.matrixLieAlgebra` and
`S₁.group.matrixLieAlgebra × S₂.group.matrixLieAlgebra`. -/
def blockProdLieEquiv {N₁ N₂ : ℕ} (S₁ : CompactMatrixStructureGroup (Fin N₁))
    (S₂ : CompactMatrixStructureGroup (Fin N₂)) :
    ((S₁.group.fromBlocksProd S₂.group).reindex finSumFinEquiv).matrixLieAlgebra ≃ₗ⁅ℝ⁆
      S₁.group.matrixLieAlgebra × S₂.group.matrixLieAlgebra :=
  ((S₁.group.fromBlocksProd S₂.group).matrixLieAlgebraReindexEquiv finSumFinEquiv).symm.trans
    (S₁.group.matrixLieAlgebraFromBlocksProdEquiv S₂.group)

/-- The first component of `blockProdLieEquiv` is the upper-left block of the inverse-reindexed
matrix. -/
@[simp]
theorem coe_blockProdLieEquiv_fst_apply {N₁ N₂ : ℕ}
    (S₁ : CompactMatrixStructureGroup (Fin N₁)) (S₂ : CompactMatrixStructureGroup (Fin N₂))
    (X : ((S₁.group.fromBlocksProd S₂.group).reindex finSumFinEquiv).matrixLieAlgebra) :
    ((S₁.blockProdLieEquiv S₂ X).1 : Matrix (Fin N₁) (Fin N₁) ℂ) =
      (Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm
        (X : Matrix (Fin (N₁ + N₂)) (Fin (N₁ + N₂)) ℂ)).toBlocks₁₁ := by
  simp [blockProdLieEquiv]

/-- The second component of `blockProdLieEquiv` is the lower-right block of the inverse-reindexed
matrix. -/
@[simp]
theorem coe_blockProdLieEquiv_snd_apply {N₁ N₂ : ℕ}
    (S₁ : CompactMatrixStructureGroup (Fin N₁)) (S₂ : CompactMatrixStructureGroup (Fin N₂))
    (X : ((S₁.group.fromBlocksProd S₂.group).reindex finSumFinEquiv).matrixLieAlgebra) :
    ((S₁.blockProdLieEquiv S₂ X).2 : Matrix (Fin N₂) (Fin N₂) ℂ) =
      (Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm
        (X : Matrix (Fin (N₁ + N₂)) (Fin (N₁ + N₂)) ℂ)).toBlocks₂₂ := by
  simp [blockProdLieEquiv]

/-- The inverse of `blockProdLieEquiv` is the reindexed block-diagonal matrix `diag(X₁, X₂)`. -/
@[simp]
theorem coe_blockProdLieEquiv_symm_apply {N₁ N₂ : ℕ}
    (S₁ : CompactMatrixStructureGroup (Fin N₁)) (S₂ : CompactMatrixStructureGroup (Fin N₂))
    (p : S₁.group.matrixLieAlgebra × S₂.group.matrixLieAlgebra) :
    ((S₁.blockProdLieEquiv S₂).symm p : Matrix (Fin (N₁ + N₂)) (Fin (N₁ + N₂)) ℂ) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (p.1 : Matrix (Fin N₁) (Fin N₁) ℂ) 0 0
          (p.2 : Matrix (Fin N₂) (Fin N₂) ℂ)) := by
  simp [blockProdLieEquiv]

/-- The inner product of `blockProd` is the orthogonal direct sum of the inner products on the
diagonal blocks. -/
@[simp]
theorem blockProd_innerForm_apply {N₁ N₂ : ℕ}
    (S₁ : CompactMatrixStructureGroup (Fin N₁)) (S₂ : CompactMatrixStructureGroup (Fin N₂))
    (X Y : ((S₁.group.fromBlocksProd S₂.group).reindex finSumFinEquiv).matrixLieAlgebra) :
    (S₁.blockProd S₂).innerForm X Y =
      S₁.innerForm (S₁.blockProdLieEquiv S₂ X).1 (S₁.blockProdLieEquiv S₂ Y).1 +
        S₂.innerForm (S₁.blockProdLieEquiv S₂ X).2 (S₁.blockProdLieEquiv S₂ Y).2 :=
  (rfl)

end BlockProd

end CompactMatrixStructureGroup

end TauCeti
