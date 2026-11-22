/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.Star.Unitary
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.SpecialUnitary
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Block
public import TauCeti.Topology.Algebra.Star.Unitary
import TauCeti.Analysis.Matrix.UnitaryGroup.Basic

/-!
# The unitary and special unitary matrix groups are compact

For a finite index type `n` and `𝕜 = ℝ` or `ℂ` (any `RCLike` field), the unitary group
`Matrix.unitaryGroup n 𝕜` and the special unitary group `Matrix.specialUnitaryGroup n 𝕜` are
compact subsets of `Matrix n n 𝕜` in the entrywise topology, hence compact topological groups.

The argument is the classical one. A unitary matrix has unit rows, so all its entries lie in the
closed unit ball (Mathlib's `entry_norm_bound_of_unitary`); the unitary group is therefore contained
in the compact set of matrices with entries in that ball, and it is closed because it is cut out by
the equations `star A * A = 1` and `A * star A = 1`. The special unitary group adds the closed
condition `det A = 1`.

Mathlib already supplies the topological group structure on `unitary R` for a topological star
monoid `R` (`isClosed_unitary` and the `IsTopologicalGroup (unitary R)` instance), so for the
unitary group only compactness is new. The special unitary group is a different submonoid, carrying
its own `Group` instance in `Mathlib/LinearAlgebra/UnitaryGroup.lean`, so its `ContinuousInv` and
`IsTopologicalGroup` instances are recorded here too. Those instances and its closedness need no
`RCLike` hypothesis, and are stated over a topological commutative star ring instead; only
compactness is `RCLike`-specific. Hausdorffness is not proved here: it
is inherited from the ambient matrix topology whenever `𝕜` is Hausdorff.

Closedness is also recorded one level up, for `TauCeti.GLSpecialUnitary`, the same group seen as
a subgroup of the general linear group of units: its carrier is the preimage of the matrix special
unitary group under the continuous coercion `Units.val`.  That is the form in which the
closed-subgroup theorem consumes it.  Over `ℝ` or `ℂ`, compactness of the matrix unitary group
likewise passes to the unitary subgroup `unitarySubgroup (GL n 𝕜)`. For the same reason the
block-diagonal product `{diag(g₁, g₂)}` of two closed subgroups of `U(n)` and `U(m)` is a closed
subgroup of `U(n ⊕ m)`.

This is the setup the compact-group representation theory of `SU(2)` runs on; see
`TauCeti/RepresentationTheory/SU2/Basic.lean`.

## Main definitions

* `ClosedSubgroup.fromBlocksProd`: the block-diagonal product `{diag(g₁, g₂)} ≤ U(n ⊕ m)` of
  closed subgroups `G₁ ≤ U(n)` and `G₂ ≤ U(m)`, closed by compactness.

## Main results

* `TauCeti.Matrix.isClosed_specialUnitaryGroup`: the special unitary matrix group is closed.
* `TauCeti.Matrix.isCompact_unitaryGroup` and `TauCeti.Matrix.isCompact_specialUnitaryGroup`: the
  unitary and special unitary matrix groups over `ℝ` or `ℂ` are compact.
* `TauCeti.isClosed_GLSpecialUnitary`: the special unitary subgroup of the general linear group is
  closed.
* `Matrix.GeneralLinearGroup.isCompact_unitarySubgroup`: the unitary subgroup of the general linear
  group over `ℝ` or `ℂ` is compact.
* `Matrix.UnitaryGroup.continuous_toSpecialUnitaryAt`: rescaling a column of a unitary matrix to
  make it special unitary is continuous.
* `Matrix.UnitaryGroup.continuous_fromBlocksOne`,
  `Matrix.specialUnitaryGroup.continuous_fromBlocksOne`: the block embeddings `B ↦ diag(1_r, B)`
  of `U(m)` in `U(r + m)` and of `SU(m)` in `SU(r + m)` are continuous.
-/

public section

open Metric Set

namespace TauCeti

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n]

section CommRing

variable [CommRing 𝕜] [StarRing 𝕜]

variable [TopologicalSpace 𝕜] [ContinuousStar 𝕜]

instance : ContinuousInv (Matrix.specialUnitaryGroup n 𝕜) where
  continuous_inv := continuous_induced_rng.mpr continuous_subtypeVal.star

section TopologicalSemiring

variable [IsTopologicalSemiring 𝕜]

instance : IsTopologicalGroup (Matrix.specialUnitaryGroup n 𝕜) where

end TopologicalSemiring

variable [IsTopologicalRing 𝕜]

/-- The special unitary group of `n × n` matrices is a closed subset of `Matrix n n 𝕜`: it is cut
out of the closed unitary group by the closed condition `det A = 1`. -/
theorem isClosed_specialUnitaryGroup [T1Space 𝕜] :
    IsClosed (Matrix.specialUnitaryGroup n 𝕜 : Set (Matrix n n 𝕜)) := by
  have hinter : (Matrix.specialUnitaryGroup n 𝕜 : Set (Matrix n n 𝕜))
      = (Matrix.unitaryGroup n 𝕜 : Set (Matrix n n 𝕜)) ∩ {A | A.det = 1} := by
    ext A
    simpa using Matrix.mem_specialUnitaryGroup_iff
  rw [hinter]
  exact isClosed_unitary.inter
    (isClosed_singleton.preimage (Continuous.matrix_det continuous_id))

end CommRing

section RCLike

variable [RCLike 𝕜]

/-- The unitary group of `n × n` matrices over `ℝ` or `ℂ` is a compact subset of `Matrix n n 𝕜`. -/
theorem isCompact_unitaryGroup :
    IsCompact (Matrix.unitaryGroup n 𝕜 : Set (Matrix n n 𝕜)) := by
  have : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  exact ((isCompact_closedBall (0 : 𝕜) 1).matrix).of_isClosed_subset isClosed_unitary
    fun _ hA _ _ => mem_closedBall_zero_iff.mpr (entry_norm_bound_of_unitary hA _ _)

instance : CompactSpace (Matrix.unitaryGroup n 𝕜) :=
  isCompact_iff_compactSpace.mp isCompact_unitaryGroup

/-- The special unitary group of `n × n` matrices over `ℝ` or `ℂ` is a compact subset of
`Matrix n n 𝕜`. -/
theorem isCompact_specialUnitaryGroup :
    IsCompact (Matrix.specialUnitaryGroup n 𝕜 : Set (Matrix n n 𝕜)) :=
  isCompact_unitaryGroup.of_isClosed_subset isClosed_specialUnitaryGroup
    fun _ hA => Matrix.specialUnitaryGroup_le_unitaryGroup hA

instance : CompactSpace (Matrix.specialUnitaryGroup n 𝕜) :=
  isCompact_iff_compactSpace.mp isCompact_specialUnitaryGroup

end RCLike

end Matrix

section GeneralLinear

variable (n : Type*) [Fintype n] [DecidableEq n] (𝕜 : Type*) [CommRing 𝕜] [StarRing 𝕜]
  [TopologicalSpace 𝕜] [ContinuousStar 𝕜] [IsTopologicalRing 𝕜] [T1Space 𝕜]

/-- **The special unitary subgroup of the general linear group is closed.**  Its carrier is the
preimage of the closed matrix special unitary group under the continuous coercion of units.  This
is the hypothesis the closed-subgroup theorem needs in order to promote it to an embedded Lie
subgroup. -/
theorem isClosed_GLSpecialUnitary :
    IsClosed ((GLSpecialUnitary n 𝕜 : Subgroup (GL n 𝕜)) : Set (GL n 𝕜)) := by
  rw [GLSpecialUnitary.coe_eq_preimage]
  exact (Matrix.isClosed_specialUnitaryGroup (n := n) (𝕜 := 𝕜)).preimage Units.continuous_val

end GeneralLinear

end TauCeti

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [RCLike 𝕜]

/-- **The unitary subgroup of `GL n 𝕜` is compact** over `ℝ` or `ℂ`: the matrix unitary group is
compact. -/
theorem isCompact_unitarySubgroup :
    IsCompact ((unitarySubgroup (GL n 𝕜) : Subgroup (GL n 𝕜)) : Set (GL n 𝕜)) :=
  TauCeti.isCompact_unitarySubgroup_units_iff.mpr TauCeti.Matrix.isCompact_unitaryGroup

end Matrix.GeneralLinearGroup

namespace Matrix.UnitaryGroup

variable {𝕜 : Type*} [CommRing 𝕜] [StarRing 𝕜] [TopologicalSpace 𝕜] {r : ℕ}

/-- The block embedding `B ↦ diag(1_r, B)` of `U(m)` in `U(r + m)` is continuous. -/
theorem continuous_fromBlocksOne (m : ℕ) :
    Continuous (fromBlocksOne 𝕜 r m) := by
  refine continuous_induced_rng.2 ?_
  simp only [Function.comp_def, coe_fromBlocksOne]
  exact (continuous_const.matrix_fromBlocks continuous_const continuous_const
    continuous_subtypeVal).matrix_reindex _ _

/-- Multiplying the column `j` of a unitary matrix by the conjugate of its determinant,
`A ↦ toSpecialUnitaryAt j A`, is continuous. -/
theorem continuous_toSpecialUnitaryAt [IsTopologicalRing 𝕜] [ContinuousStar 𝕜] {n : Type*}
    [Fintype n] [DecidableEq n] (j : n) :
    Continuous (toSpecialUnitaryAt (R := 𝕜) j : unitaryGroup n 𝕜 → specialUnitaryGroup n 𝕜) := by
  refine continuous_induced_rng.2 ?_
  simp only [Function.comp_def, coe_toSpecialUnitaryAt]
  exact continuous_subtypeVal.matrix_mul (Continuous.matrix_diagonal
    (continuous_const.update j (continuous_subtypeVal.matrix_det.star)))

/-- Reindexing unitary matrices along a bijection `e : n ≃ m` is continuous. -/
theorem continuous_reindexEquiv {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (e : n ≃ m) :
    Continuous (reindexEquiv (R := 𝕜) e) := by
  refine continuous_induced_rng.2 ?_
  simp only [Function.comp_def, coe_reindexEquiv]
  exact continuous_subtypeVal.matrix_reindex e e

end Matrix.UnitaryGroup

namespace Matrix.specialUnitaryGroup

variable {𝕜 : Type*} [CommRing 𝕜] [StarRing 𝕜] [TopologicalSpace 𝕜] {r : ℕ}

/-- The block embedding `B ↦ diag(1_r, B)` of `SU(m)` in `SU(r + m)` is continuous. -/
theorem continuous_fromBlocksOne (m : ℕ) :
    Continuous (fromBlocksOne 𝕜 r m) := by
  refine continuous_induced_rng.2 ?_
  simp only [Function.comp_def, coe_fromBlocksOne]
  exact (continuous_const.matrix_fromBlocks continuous_const continuous_const
    continuous_subtypeVal).matrix_reindex _ _

end Matrix.specialUnitaryGroup

namespace ClosedSubgroup

section Unitary

variable (n 𝕜 : Type*) [Fintype n] [DecidableEq n] [CommRing 𝕜] [StarRing 𝕜]
  [TopologicalSpace 𝕜]

/-- The full unitary group `U(n)` as a closed subgroup of `Matrix.unitaryGroup n 𝕜`. -/
def unitary : ClosedSubgroup (Matrix.unitaryGroup n 𝕜) where
  toSubgroup := ⊤
  isClosed' := isClosed_univ

/-- Every unitary matrix belongs to `ClosedSubgroup.unitary n 𝕜`. -/
@[simp]
theorem mem_unitary (U : Matrix.unitaryGroup n 𝕜) : U ∈ unitary n 𝕜 :=
  trivial

end Unitary

section SpecialUnitary

variable (n 𝕜 : Type*) [Fintype n] [DecidableEq n] [CommRing 𝕜] [StarRing 𝕜]
  [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] [T1Space 𝕜]

/-- The special unitary group `SU(n)` as a closed subgroup of `Matrix.unitaryGroup n 𝕜`. -/
def specialUnitary : ClosedSubgroup (Matrix.unitaryGroup n 𝕜) where
  toSubgroup := Matrix.UnitaryGroup.specialUnitarySubgroup n 𝕜
  isClosed' := by
    -- Identify the `ClosedSubgroup` carrier with the underlying `Subgroup` carrier set.
    change IsClosed ((Matrix.UnitaryGroup.specialUnitarySubgroup n 𝕜 :
      Subgroup (Matrix.unitaryGroup n 𝕜)) : Set (Matrix.unitaryGroup n 𝕜))
    have hset : ((Matrix.UnitaryGroup.specialUnitarySubgroup n 𝕜 :
        Subgroup (Matrix.unitaryGroup n 𝕜)) : Set (Matrix.unitaryGroup n 𝕜)) =
        (fun U : Matrix.unitaryGroup n 𝕜 ↦ (U : Matrix n n 𝕜).det) ⁻¹' {1} := by
      ext U
      simp [Matrix.UnitaryGroup.mem_specialUnitarySubgroup_iff]
    rw [hset]
    exact isClosed_singleton.preimage continuous_subtypeVal.matrix_det

/-- Membership in `ClosedSubgroup.specialUnitary n 𝕜` is having determinant `1`. -/
@[simp]
theorem mem_specialUnitary_iff {U : Matrix.unitaryGroup n 𝕜} :
    U ∈ specialUnitary n 𝕜 ↔ (U : Matrix n n 𝕜).det = 1 :=
  Matrix.UnitaryGroup.mem_specialUnitarySubgroup_iff

end SpecialUnitary

variable {n m 𝕜 : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [RCLike 𝕜]

/-- Reindex a closed subgroup `G ≤ U(n)` along a bijection `e : n ≃ m` to obtain a closed
subgroup of `U(m)`. -/
def reindex (G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜)) (e : n ≃ m) :
    ClosedSubgroup (Matrix.unitaryGroup m 𝕜) where
  toSubgroup := (G : Subgroup _).map (Matrix.UnitaryGroup.reindexEquiv e).toMonoidHom
  isClosed' := by
    convert (G.isClosed'.isCompact.image
      (Matrix.UnitaryGroup.continuous_reindexEquiv e)).isClosed using 1
    ext g
    simp only [Subgroup.mem_carrier, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, Set.mem_image]

/-- Membership in `G.reindex e` reduces to membership of the inverse reindexing in `G`. -/
@[simp]
theorem mem_reindex_iff {G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜)} (e : n ≃ m)
    {V : Matrix.unitaryGroup m 𝕜} :
    V ∈ G.reindex e ↔ (Matrix.UnitaryGroup.reindexEquiv e).symm V ∈ G := by
  -- The underlying subgroup of `reindex` is, by definition, the image of `G` under `reindexEquiv`.
  change V ∈ (G : Subgroup _).map (Matrix.UnitaryGroup.reindexEquiv e).toMonoidHom ↔ _
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨U, hU, rfl⟩
    simp only [MulEquiv.symm_apply_apply]
    exact hU
  · intro hV
    exact ⟨(Matrix.UnitaryGroup.reindexEquiv e).symm V, hV, by simp⟩

/-- Reindexing an element of `G` along `e` lands in `G.reindex e`. -/
theorem reindexEquiv_mem_reindex {G : ClosedSubgroup (Matrix.unitaryGroup n 𝕜)} (e : n ≃ m)
    {U : Matrix.unitaryGroup n 𝕜} (hU : U ∈ G) :
    Matrix.UnitaryGroup.reindexEquiv e U ∈ G.reindex e := by
  simpa using hU

/-- The block-diagonal product `G₁ × G₂ ≤ U(n ⊕ m)` of closed subgroups `G₁ ≤ U(n)` and
`G₂ ≤ U(m)`: the matrices `diag(g₁, g₂)` with `g₁ ∈ G₁` and `g₂ ∈ G₂`. It is closed, being the
compact image of `G₁ × G₂` under the block-diagonal sum. -/
def fromBlocksProd (G₁ : ClosedSubgroup (Matrix.unitaryGroup n 𝕜))
    (G₂ : ClosedSubgroup (Matrix.unitaryGroup m 𝕜)) :
    ClosedSubgroup (Matrix.unitaryGroup (n ⊕ m) 𝕜) where
  toSubgroup := ((G₁ : Subgroup _).prod G₂).map Matrix.UnitaryGroup.sum
  isClosed' := by
    convert ((G₁.isClosed'.isCompact.prod G₂.isClosed'.isCompact).image
      Matrix.UnitaryGroup.continuous_sum).isClosed using 1
    ext g
    simp only [Subgroup.mem_carrier, Subgroup.mem_map, Subgroup.mem_prod, Set.mem_image,
      Set.mem_prod]

variable {G₁ : ClosedSubgroup (Matrix.unitaryGroup n 𝕜)}
  {G₂ : ClosedSubgroup (Matrix.unitaryGroup m 𝕜)}

/-- An element of `U(n ⊕ m)` lies in the block-diagonal product exactly when it is `diag(g₁, g₂)`
with `g₁ ∈ G₁` and `g₂ ∈ G₂`. -/
theorem mem_fromBlocksProd_iff {g : Matrix.unitaryGroup (n ⊕ m) 𝕜} :
    g ∈ G₁.fromBlocksProd G₂ ↔ ∃ g₁ ∈ G₁, ∃ g₂ ∈ G₂,
      (g : Matrix (n ⊕ m) (n ⊕ m) 𝕜) = Matrix.fromBlocks (g₁ : Matrix n n 𝕜) 0 0 g₂ := by
  -- The underlying subgroup of `fromBlocksProd` is, by definition, the image of `G₁ × G₂`.
  change g ∈ ((G₁ : Subgroup _).prod G₂).map Matrix.UnitaryGroup.sum ↔ _
  simp only [Subgroup.mem_map, Subgroup.mem_prod, Prod.exists]
  constructor
  · rintro ⟨g₁, g₂, ⟨h₁, h₂⟩, rfl⟩
    exact ⟨g₁, h₁, g₂, h₂, Matrix.UnitaryGroup.coe_sum _⟩
  · rintro ⟨g₁, h₁, g₂, h₂, hg⟩
    exact ⟨g₁, g₂, ⟨h₁, h₂⟩, Subtype.ext ((Matrix.UnitaryGroup.coe_sum _).trans hg.symm)⟩

/-- The block-diagonal sum `diag(g₁, g₂)` of `g₁ ∈ G₁` and `g₂ ∈ G₂` lies in the product. -/
theorem sum_mem_fromBlocksProd {g₁ : Matrix.unitaryGroup n 𝕜}
    {g₂ : Matrix.unitaryGroup m 𝕜} (h₁ : g₁ ∈ G₁) (h₂ : g₂ ∈ G₂) :
    Matrix.UnitaryGroup.sum (g₁, g₂) ∈ G₁.fromBlocksProd G₂ :=
  mem_fromBlocksProd_iff.mpr ⟨g₁, h₁, g₂, h₂, Matrix.UnitaryGroup.coe_sum _⟩

end ClosedSubgroup
