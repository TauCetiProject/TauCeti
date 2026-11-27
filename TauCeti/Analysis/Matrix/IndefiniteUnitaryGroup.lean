/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.Analysis.Matrix.DotProduct
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup
public import TauCeti.Topology.Algebra.UnitaryGroup
public import TauCeti.Topology.Instances.Matrix
import TauCeti.Analysis.Matrix.UnitaryGroup.Basic
import TauCeti.LinearAlgebra.Matrix.DotProduct

/-!
# The indefinite unitary group `U(p, q)` over `ℝ` and `ℂ`

This file records the facts about the unitary group `Matrix.unitaryGroupOf A` of a Gram
matrix `A`, and about the indefinite unitary group `TauCeti.Matrix.indefiniteUnitaryGroup p q 𝕜`,
that use the topology or the order of `ℝ` and `ℂ`.

* Over `ℝ` or `ℂ` (any `RCLike` field) and for Hermitian `A`, a matrix lies in `unitaryGroupOf A`
  exactly when it preserves the values `⟨z, z⟩ = star z ⬝ᵥ A *ᵥ z` of the form on the diagonal. By
  polarization the diagonal values determine the form, so this does not depend on which slot of
  the form is taken conjugate-linear: for `U(p, q)`, the form
  `z ⬝ᵥ J *ᵥ star w = Σ_{i ∈ p} zᵢ star wᵢ - Σ_{j ∈ q} zⱼ star wⱼ`, linear in the first slot, has
  the same values on the diagonal and so the same isometries.
* Over `ℝ` or `ℂ`, the form `⟨z, z⟩` of `J = indefiniteDiagonal p q 𝕜` is the real number
  `Σ_{i ∈ p} ‖zᵢ‖² - Σ_{j ∈ q} ‖zⱼ‖²`.
* Over a Hausdorff topological ring with continuous star, `unitaryGroupOf A` is a closed subgroup
  of the general linear group, with the topology of units. For invertible `A` it is also a closed
  subset of the matrices, with the subspace topology, since its inverse `A⁻¹ * star g * A` is a
  continuous function of `g`; over `ℝ` or `ℂ` this makes `U(p, q)` locally compact and second
  countable.
* For a unitary Gram matrix `A` over `ℝ` or `ℂ`, such as `diag(1, …, 1, -1, …, -1)`, the inverse
  `A⁻¹ * star g * A` of `g ∈ unitaryGroupOf A` has the operator norm of `g`, since multiplying by
  a unitary matrix and taking adjoints preserve the operator norm. As `1 ≤ ‖g‖ * ‖g⁻¹‖`, every such
  `g` has operator norm at least `1` when the size is positive.
* The block-diagonal embedding of `U(p) × U(q)` in `U(p, q)` is continuous, so over `ℝ` or `ℂ`
  its image is compact, being the continuous image of a product of compact unitary groups.

## Main results

* `Matrix.mem_unitaryGroupOf_iff_forall_dotProduct_self`: membership in
  `unitaryGroupOf A`, for Hermitian `A`, as the preservation of the values `⟨z, z⟩`.
* `LieAlgebra.Orthogonal.star_dotProduct_indefiniteDiagonal_mulVec_self`: the values of the
  indefinite Hermitian form.
* `Matrix.norm_val_inv_of_mem_unitaryGroupOf`: for unitary `A`, `‖g⁻¹‖ = ‖g‖` in the operator
  norm.
* `Matrix.one_le_norm_val_of_mem_unitaryGroupOf`: for unitary `A`, `1 ≤ ‖g‖` in the operator norm.
* `Matrix.isClosed_unitaryGroupOf`: `unitaryGroupOf A` is closed in `GL n R`.
* `Matrix.unitaryGroupOf.isClosedEmbedding_val`: for invertible `A`, the coercion of
  `unitaryGroupOf A` to the matrices is a closed embedding.
* `TauCeti.Matrix.indefiniteUnitaryGroup.continuous_fromBlocksHom`: the block-diagonal embedding
  of `U(p) × U(q)` is continuous.
* `TauCeti.Matrix.indefiniteUnitaryGroup.isCompact_range_fromBlocksHom`: the block-diagonal
  subgroup `U(p) × U(q)` is compact.
* `TauCeti.Matrix.indefiniteUnitaryGroup.instLocallyCompactSpace` and
  `TauCeti.Matrix.indefiniteUnitaryGroup.instSecondCountableTopology`: over `ℝ` or `ℂ`, `U(p, q)`
  is locally compact and second countable.

## Provenance

`Matrix.norm_val_inv_of_mem_unitaryGroupOf` and `Matrix.one_le_norm_val_of_mem_unitaryGroupOf` are
adapted from `New.U.norm_inv` and `New.U.one_le_norm` (file
`src/Lib/General/LinearAlgebra/HermitianMatrices.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC); the source
treats complex Hermitian involutions `J`, and the generalisation to unitary Gram matrices over `ℝ`
or `ℂ` is new here.
-/

public section

open Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `unitaryGroupOf A` is a closed subgroup of `GL n R`: it is cut out by the continuous equation
`star g * A * g = A`. -/
theorem isClosed_unitaryGroupOf {R : Type*} [CommRing R] [StarRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [ContinuousStar R] [T2Space R] (A : Matrix n n R) :
    IsClosed (unitaryGroupOf A : Set (GL n R)) := by
  have h : (unitaryGroupOf A : Set (GL n R)) =
      {g : GL n R | star (g : Matrix n n R) * A * g = A} :=
    Set.ext fun _ => mem_unitaryGroupOf_iff
  rw [h]
  exact isClosed_eq (((Units.continuous_val.star).matrix_mul continuous_const).matrix_mul
    Units.continuous_val) continuous_const

/-- **`unitaryGroupOf A` is a closed subset of the matrices**, for invertible `A`: the coercion to
matrices is a closed embedding. The topology of `GL n R` is that of the pair `(g, g⁻¹)`, and on
`unitaryGroupOf A` the inverse `A⁻¹ * star g * A` is a continuous function of `g`; the image is
cut out by the continuous equation `star M * A * M = A`, every solution of which is invertible. -/
theorem unitaryGroupOf.isClosedEmbedding_val {R : Type*} [CommRing R] [StarRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [ContinuousStar R] [T2Space R] {A : Matrix n n R}
    (hA : IsUnit A) :
    Topology.IsClosedEmbedding fun g : unitaryGroupOf A => ((g : GL n R) : Matrix n n R) := by
  have hc : Continuous fun g : unitaryGroupOf A => ((g : GL n R) : Matrix n n R) :=
    Units.continuous_val.comp continuous_subtypeVal
  have hrange : Set.range (fun g : unitaryGroupOf A => ((g : GL n R) : Matrix n n R)) =
      {M | star M * A * M = A} :=
    Set.ext fun M => ⟨fun ⟨g, hg⟩ => hg ▸ mem_unitaryGroupOf_iff.mp g.property,
      fun hM => ⟨ofMatrix hA M hM, val_ofMatrix hA M hM⟩⟩
  refine ⟨⟨Topology.IsInducing.of_comp hc
      (g := fun M : Matrix n n R => (M, MulOpposite.op (A⁻¹ * star M * A)))
      (continuous_id.prodMk (MulOpposite.continuous_op.comp
        ((continuous_const.matrix_mul continuous_id.star).matrix_mul continuous_const))) ?_,
    fun g h hgh => unitaryGroupOf.ext hgh⟩, ?_⟩
  · -- The composite is `g ↦ (g, g⁻¹)`, the inducing map defining the topology of `GL n R`.
    convert Units.isInducing_embedProduct.comp Topology.IsInducing.subtypeVal using 1
    funext g
    simp [Units.embedProduct_apply, val_inv_of_mem_unitaryGroupOf hA g.property]
  · rw [hrange]
    exact isClosed_eq ((continuous_id.star.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const

/-- **Membership in `unitaryGroupOf A` by polarization.** Over `ℝ` or `ℂ` and for Hermitian `A`,
`g ∈ unitaryGroupOf A` exactly when `⟨g z, g z⟩ = ⟨z, z⟩` for every `z`, where
`⟨z, z⟩ = star z ⬝ᵥ A *ᵥ z`. -/
theorem mem_unitaryGroupOf_iff_forall_dotProduct_self {𝕜 : Type*} [RCLike 𝕜] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {g : GL n 𝕜} :
    g ∈ unitaryGroupOf A ↔ ∀ z : n → 𝕜,
      star ((g : Matrix n n 𝕜) *ᵥ z) ⬝ᵥ A *ᵥ (g *ᵥ z) = star z ⬝ᵥ A *ᵥ z := by
  refine ⟨fun h z => mem_unitaryGroupOf_iff_forall_dotProduct.mp h z z, fun h => ?_⟩
  set M : Matrix n n 𝕜 := (g : Matrix n n 𝕜)
  have hA' : (star M * A * M - A).IsHermitian := by
    refine IsHermitian.sub ?_ hA
    rw [star_eq_conjTranspose]
    exact isHermitian_conjTranspose_mul_mul M hA
  rw [mem_unitaryGroupOf_iff, ← sub_eq_zero, ← hA'.forall_star_dotProduct_mulVec_self_eq_zero_iff]
  intro z
  rw [sub_mulVec, dotProduct_sub, sub_eq_zero, ← h z, star_eq_conjTranspose,
    star_dotProduct_conjTranspose_mul_mul_mulVec]

section OperatorNorm

open scoped Matrix.Norms.L2Operator

variable {𝕜 : Type*} [RCLike 𝕜] {A : Matrix n n 𝕜}

/-- For a unitary Gram matrix `A`, an element `g` of `unitaryGroupOf A` and its inverse
`A⁻¹ * star g * A` have the same operator norm. -/
theorem norm_val_inv_of_mem_unitaryGroupOf (hA : A ∈ unitary (Matrix n n 𝕜)) {g : GL n 𝕜}
    (hg : g ∈ unitaryGroupOf A) :
    ‖((g⁻¹ : GL n 𝕜) : Matrix n n 𝕜)‖ = ‖(g : Matrix n n 𝕜)‖ := by
  rw [val_inv_of_mem_unitaryGroupOf (Unitary.isUnit_coe (U := ⟨A, hA⟩)) hg,
    inv_eq_left_inv (Unitary.star_mul_self_of_mem hA), CStarRing.norm_mul_mem_unitary _ hA,
    CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem hA), norm_star]

/-- For a unitary Gram matrix `A` of positive size, every element of `unitaryGroupOf A` has
operator norm at least `1`: `1 = ‖g * g⁻¹‖ ≤ ‖g‖ * ‖g⁻¹‖ = ‖g‖ ^ 2`. -/
theorem one_le_norm_val_of_mem_unitaryGroupOf [Nonempty n] (hA : A ∈ unitary (Matrix n n 𝕜))
    {g : GL n 𝕜} (hg : g ∈ unitaryGroupOf A) : 1 ≤ ‖(g : Matrix n n 𝕜)‖ := by
  have h : (1 : ℝ) ≤ ‖(g : Matrix n n 𝕜)‖ ^ 2 :=
    calc (1 : ℝ) = ‖((g * g⁻¹ : GL n 𝕜) : Matrix n n 𝕜)‖ := by simp
      _ ≤ ‖(g : Matrix n n 𝕜)‖ * ‖((g⁻¹ : GL n 𝕜) : Matrix n n 𝕜)‖ := by
        rw [Units.val_mul]
        exact norm_mul_le _ _
      _ = ‖(g : Matrix n n 𝕜)‖ ^ 2 := by rw [norm_val_inv_of_mem_unitaryGroupOf hA hg, sq]
  exact (one_le_sq_iff₀ (norm_nonneg _)).1 h

end OperatorNorm

end Matrix

namespace LieAlgebra.Orthogonal

/-- **The values of the indefinite Hermitian form.** Over `ℝ` or `ℂ`, the form
`⟨z, z⟩ = star z ⬝ᵥ J *ᵥ z` of `J = indefiniteDiagonal p q 𝕜` is the real number
`Σ_{i ∈ p} ‖zᵢ‖² - Σ_{j ∈ q} ‖zⱼ‖²`. -/
theorem star_dotProduct_indefiniteDiagonal_mulVec_self {p q 𝕜 : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q] [RCLike 𝕜] (z : p ⊕ q → 𝕜) :
    star z ⬝ᵥ indefiniteDiagonal p q 𝕜 *ᵥ z =
      ((∑ i, ‖z (Sum.inl i)‖ ^ 2 - ∑ j, ‖z (Sum.inr j)‖ ^ 2 : ℝ) : 𝕜) := by
  simp [dotProduct, Fintype.sum_sum_type, indefiniteDiagonal, mulVec_diagonal, RCLike.conj_mul,
    sub_eq_add_neg]

end LieAlgebra.Orthogonal

namespace TauCeti

namespace Matrix

namespace indefiniteUnitaryGroup

variable {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

/-- The block-diagonal embedding of `U(p) × U(q)` in `U(p, q)` is continuous. -/
theorem continuous_fromBlocksHom {R : Type*} [CommRing R] [StarRing R] [TopologicalSpace R]
    [ContinuousStar R] : Continuous (fromBlocksHom p q R) :=
  continuous_induced_rng.mpr <|
    (Unitary.continuous_toUnits.comp UnitaryGroup.continuous_sum).congr fun _ =>
      Units.ext <| by simp

/-- **The block-diagonal subgroup `U(p) × U(q)` of `U(p, q)` is compact** over `ℝ` or `ℂ`. -/
theorem isCompact_range_fromBlocksHom {𝕜 : Type*} [RCLike 𝕜] :
    IsCompact ((fromBlocksHom p q 𝕜).range : Set (indefiniteUnitaryGroup p q 𝕜)) := by
  rw [MonoidHom.coe_range]
  exact isCompact_range continuous_fromBlocksHom

/-- `U(p, q)` over `ℝ` or `ℂ` is locally compact, being a closed subset of the matrices
(`Matrix.unitaryGroupOf.isClosedEmbedding_val`). -/
instance instLocallyCompactSpace {𝕜 : Type*} [RCLike 𝕜] :
    LocallyCompactSpace (indefiniteUnitaryGroup p q 𝕜) :=
  (unitaryGroupOf.isClosedEmbedding_val
    LieAlgebra.Orthogonal.isUnit_indefiniteDiagonal).locallyCompactSpace

/-- `U(p, q)` over `ℝ` or `ℂ` is second countable, being a subspace of the matrices. -/
instance instSecondCountableTopology {𝕜 : Type*} [RCLike 𝕜] :
    SecondCountableTopology (indefiniteUnitaryGroup p q 𝕜) :=
  (unitaryGroupOf.isClosedEmbedding_val
    LieAlgebra.Orthogonal.isUnit_indefiniteDiagonal).isEmbedding.secondCountableTopology

end indefiniteUnitaryGroup

end Matrix

end TauCeti
