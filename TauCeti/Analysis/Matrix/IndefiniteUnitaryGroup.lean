/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.Analysis.Matrix.DotProduct
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup
public import TauCeti.Topology.Algebra.UnitaryGroup
import TauCeti.LinearAlgebra.Matrix.DotProduct

/-!
# The indefinite unitary group `U(p, q)` over `ℝ` and `ℂ`

This file records the facts about the unitary group `TauCeti.Matrix.unitaryGroupOf A` of a Gram
matrix `A`, and about the indefinite unitary group `TauCeti.Matrix.indefiniteUnitaryGroup p q 𝕜`,
that use the topology or the order of `ℝ` and `ℂ`.

* Over `ℝ` or `ℂ` (any `RCLike` field) and for Hermitian `A`, a matrix lies in `unitaryGroupOf A`
  exactly when it preserves the values `⟨z, z⟩ = star z ⬝ᵥ A *ᵥ z` of the form on the diagonal. By
  polarization the diagonal values determine the form, so this does not depend on which slot of
  the form is taken conjugate-linear: for `U(p, q)`, the form
  `z ⬝ᵥ J *ᵥ star w = Σ_{i ∈ p} zᵢ star wᵢ - Σ_{j ∈ q} zⱼ star wⱼ`, linear in the first slot, has
  the same values on the diagonal and so the same isometries.
* Over a Hausdorff topological ring with continuous star, `unitaryGroupOf A` is a closed subgroup
  of the general linear group, with the topology of units.
* The block-diagonal embedding of `U(p) × U(q)` in `U(p, q)` is continuous, so over `ℝ` or `ℂ`
  its image is compact, being the continuous image of a product of compact unitary groups.

## Main results

* `TauCeti.Matrix.mem_unitaryGroupOf_iff_forall_dotProduct_self`: membership in
  `unitaryGroupOf A`, for Hermitian `A`, as the preservation of the values `⟨z, z⟩`.
* `TauCeti.Matrix.isClosed_unitaryGroupOf`: `unitaryGroupOf A` is closed in `GL n R`.
* `TauCeti.Matrix.indefiniteUnitaryGroup.continuous_fromBlocksHom`: the block-diagonal embedding
  of `U(p) × U(q)` is continuous.
* `TauCeti.Matrix.indefiniteUnitaryGroup.isCompact_range_fromBlocksHom`: the block-diagonal
  subgroup `U(p) × U(q)` is compact.
-/

public section

open Matrix

namespace TauCeti

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

section Topology

variable {R : Type*} [CommRing R] [StarRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [ContinuousStar R]

omit [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
/-- `unitaryGroupOf A` is a closed subgroup of `GL n R`: it is cut out by the continuous equation
`star g * A * g = A`. -/
theorem isClosed_unitaryGroupOf [T2Space R] (A : Matrix n n R) :
    IsClosed (unitaryGroupOf A : Set (GL n R)) := by
  have h : (unitaryGroupOf A : Set (GL n R)) =
      {g : GL n R | star (g : Matrix n n R) * A * g = A} :=
    Set.ext fun _ => mem_unitaryGroupOf_iff
  rw [h]
  exact isClosed_eq (((Units.continuous_val.star).matrix_mul continuous_const).matrix_mul
    Units.continuous_val) continuous_const

omit [IsTopologicalRing R] [Fintype n] [DecidableEq n] in
/-- The block-diagonal embedding of `U(p) × U(q)` in `U(p, q)` is continuous. -/
theorem indefiniteUnitaryGroup.continuous_fromBlocksHom :
    Continuous (indefiniteUnitaryGroup.fromBlocksHom p q R) := by
  have hval : Continuous fun x : unitaryGroup p R × unitaryGroup q R =>
      ((indefiniteUnitaryGroup.fromBlocksHom p q R x : GL (p ⊕ q) R) :
        Matrix (p ⊕ q) (p ⊕ q) R) := by
    simp only [indefiniteUnitaryGroup.val_fromBlocksHom]
    exact (continuous_subtype_val.comp continuous_fst).matrix_fromBlocks continuous_const
      continuous_const (continuous_subtype_val.comp continuous_snd)
  refine continuous_induced_rng.mpr (Units.continuous_iff.mpr ⟨hval, ?_⟩)
  exact (hval.comp continuous_inv).congr fun x => by
    rw [Function.comp_apply, map_inv, Subgroup.coe_inv, Function.comp_apply]

end Topology

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

omit [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
/-- **Membership in `unitaryGroupOf A` by polarization.** Over `ℝ` or `ℂ` and for Hermitian `A`,
`g ∈ unitaryGroupOf A` exactly when `⟨g z, g z⟩ = ⟨z, z⟩` for every `z`, where
`⟨z, z⟩ = star z ⬝ᵥ A *ᵥ z`. -/
theorem mem_unitaryGroupOf_iff_forall_dotProduct_self {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {g : GL n 𝕜} :
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

namespace indefiniteUnitaryGroup

omit [Fintype n] [DecidableEq n] in
/-- **The block-diagonal subgroup `U(p) × U(q)` of `U(p, q)` is compact** over `ℝ` or `ℂ`. -/
theorem isCompact_range_fromBlocksHom :
    IsCompact ((fromBlocksHom p q 𝕜).range : Set (indefiniteUnitaryGroup p q 𝕜)) := by
  rw [MonoidHom.coe_range]
  exact isCompact_range continuous_fromBlocksHom

end indefiniteUnitaryGroup

end RCLike

end Matrix

end TauCeti
