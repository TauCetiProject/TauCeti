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

This file records the facts about the indefinite unitary group
`Matrix.indefiniteUnitaryGroup p q 𝕜` that use the topology or the order of `ℝ` and `ℂ`.

* Over `ℝ` or `ℂ` (any `RCLike` field), a matrix lies in `U(p, q)` exactly when it preserves the
  values `⟨z, z⟩ = star z ⬝ᵥ J *ᵥ z` of the Hermitian form on the diagonal. By polarization the
  diagonal values determine the form, so this does not depend on which slot of the form is taken
  conjugate-linear: the form `Σ zᵢ star wᵢ`, linear in the first slot, has the same values on the
  diagonal and so the same isometries.
* Over a Hausdorff topological ring with continuous star, `U(p, q)` is a closed subgroup of the
  general linear group, with the topology of units.
* The block-diagonal embedding of `U(p) × U(q)` in `U(p, q)` is continuous, so over `ℝ` or `ℂ`
  its image is compact, being the continuous image of a product of compact unitary groups.

## Main results

* `Matrix.mem_indefiniteUnitaryGroup_iff_forall_dotProduct_self`: membership in `U(p, q)` as the
  preservation of the values `⟨z, z⟩`.
* `Matrix.isClosed_indefiniteUnitaryGroup`: `U(p, q)` is closed in `GL (p ⊕ q) R`.
* `Matrix.indefiniteUnitaryGroup.continuous_fromBlocksHom`: the block-diagonal embedding of
  `U(p) × U(q)` is continuous.
* `Matrix.indefiniteUnitaryGroup.isCompact_range_fromBlocksHom`: the block-diagonal subgroup
  `U(p) × U(q)` is compact.
-/

public section

open LieAlgebra.Orthogonal

namespace Matrix

variable {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

section Topology

variable {R : Type*} [CommRing R] [StarRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [ContinuousStar R]

/-- `U(p, q)` is a closed subgroup of `GL (p ⊕ q) R`: it is cut out by the continuous equation
`star g * J * g = J`. -/
theorem isClosed_indefiniteUnitaryGroup [T2Space R] :
    IsClosed (indefiniteUnitaryGroup p q R : Set (GL (p ⊕ q) R)) := by
  have h : (indefiniteUnitaryGroup p q R : Set (GL (p ⊕ q) R)) =
      {g : GL (p ⊕ q) R | star (g : Matrix (p ⊕ q) (p ⊕ q) R) * indefiniteDiagonal p q R * g =
        indefiniteDiagonal p q R} :=
    Set.ext fun _ => mem_indefiniteUnitaryGroup_iff
  rw [h]
  exact isClosed_eq (((Units.continuous_val.star).matrix_mul continuous_const).matrix_mul
    Units.continuous_val) continuous_const

omit [IsTopologicalRing R] in
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

/-- **Membership in `U(p, q)` by polarization.** Over `ℝ` or `ℂ`, `g ∈ U(p, q)` exactly when
`⟨g z, g z⟩ = ⟨z, z⟩` for every `z`, where `⟨z, z⟩ = star z ⬝ᵥ J *ᵥ z`. -/
theorem mem_indefiniteUnitaryGroup_iff_forall_dotProduct_self {g : GL (p ⊕ q) 𝕜} :
    g ∈ indefiniteUnitaryGroup p q 𝕜 ↔ ∀ z : p ⊕ q → 𝕜,
      star ((g : Matrix (p ⊕ q) (p ⊕ q) 𝕜) *ᵥ z) ⬝ᵥ indefiniteDiagonal p q 𝕜 *ᵥ (g *ᵥ z) =
        star z ⬝ᵥ indefiniteDiagonal p q 𝕜 *ᵥ z := by
  refine ⟨fun h z => mem_indefiniteUnitaryGroup_iff_forall_dotProduct.mp h z z, fun h => ?_⟩
  set M : Matrix (p ⊕ q) (p ⊕ q) 𝕜 := (g : Matrix (p ⊕ q) (p ⊕ q) 𝕜)
  have hA : (star M * indefiniteDiagonal p q 𝕜 * M - indefiniteDiagonal p q 𝕜).IsHermitian := by
    refine IsHermitian.sub ?_ isHermitian_indefiniteDiagonal
    rw [star_eq_conjTranspose]
    exact isHermitian_conjTranspose_mul_mul M isHermitian_indefiniteDiagonal
  rw [mem_indefiniteUnitaryGroup_iff, ← sub_eq_zero,
    ← hA.forall_star_dotProduct_mulVec_self_eq_zero_iff]
  intro z
  rw [sub_mulVec, dotProduct_sub, sub_eq_zero, ← h z, star_eq_conjTranspose,
    star_dotProduct_conjTranspose_mul_mul_mulVec]

namespace indefiniteUnitaryGroup

/-- **The block-diagonal subgroup `U(p) × U(q)` of `U(p, q)` is compact** over `ℝ` or `ℂ`. -/
theorem isCompact_range_fromBlocksHom :
    IsCompact ((fromBlocksHom p q 𝕜).range : Set (indefiniteUnitaryGroup p q 𝕜)) := by
  rw [MonoidHom.coe_range]
  exact isCompact_range continuous_fromBlocksHom

end indefiniteUnitaryGroup

end RCLike

end Matrix
