/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.SpecialUnitary
public import TauCeti.Topology.Algebra.Matrix.ProjectiveSpecialLinearGroup
public import TauCeti.Topology.Algebra.UnitaryGroup
import Mathlib.Topology.Maps.Strict.Group

/-!
# The projective special unitary group as a compact subgroup of `PSL(n, 𝕜)`

The inclusion `Matrix.specialUnitaryGroup.toSL` of the special unitary group into the special
linear group is continuous, and so is its composite `Matrix.specialUnitaryGroup.toPSL` with the
quotient map onto `PSL(n, α)`, for the subspace topologies of the matrix groups and the quotient
topology of `PSL(n, α)`.

Over `𝕜 = ℝ` or `ℂ` the special unitary group is compact
(`TauCeti.Matrix.isCompact_specialUnitaryGroup`) and `PSL(n, 𝕜)` is Hausdorff, since the center of
`SL(n, 𝕜)` is closed. Hence the projective special unitary group `PSU(n)`, the range of `toPSL`, is
a compact and closed subgroup of `PSL(n, 𝕜)`, and the continuous bijection from `SU(n)` modulo the
kernel of `toPSL` onto `PSU(n)` is a homeomorphism
(`Matrix.specialUnitaryGroup.quotientKerToPSLContinuousMulEquiv`). For `n = 2` that kernel is
`{1, -1}` (`Matrix.specialUnitaryGroup.mem_ker_toPSL_iff`), so `PSU(2) ≃ₜ* SU(2) ⧸ {±1}`; for
`𝕜 = ℂ` this is classically the group of rotations of the Riemann sphere, which is not proved here.

## Main declarations

* `Matrix.specialUnitaryGroup.continuous_toSL`, `Matrix.specialUnitaryGroup.continuous_toPSL`:
  the maps `SU(n) → SL(n)` and `SU(n) → PSL(n)` are continuous.
* `Matrix.specialUnitaryGroup.isCompact_range_toPSL`,
  `Matrix.specialUnitaryGroup.isClosed_range_toPSL`: `PSU(n)` is compact and closed in `PSL(n, 𝕜)`.
* `Matrix.specialUnitaryGroup.quotientKerToPSLContinuousMulEquiv`: the isomorphism of topological
  groups `SU(n) ⧸ ker toPSL ≃ₜ* PSU(n)`.
-/

public section

open scoped MatrixGroups

namespace Matrix.specialUnitaryGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

section TopologicalRing

variable {α : Type*} [CommRing α] [StarRing α] [TopologicalSpace α]

/-- The inclusion `SU(n) → SL(n)` is continuous: both carry the topology induced from the
matrices. -/
@[fun_prop]
theorem continuous_toSL : Continuous (toSL : specialUnitaryGroup n α →* SpecialLinearGroup n α) :=
  (Topology.IsInducing.subtypeVal (t := {A : Matrix n n α | A.det = 1})).continuous_iff.mpr <| by
    exact (continuous_subtype_val (p := (· ∈ specialUnitaryGroup n α))).congr fun A =>
      (coe_toSL A).symm

/-- The map `SU(n) → PSL(n)` is continuous for the quotient topology on `PSL(n)`. -/
@[fun_prop]
theorem continuous_toPSL :
    Continuous (toPSL : specialUnitaryGroup n α →* ProjectiveSpecialLinearGroup n α) :=
  (QuotientGroup.continuous_mk.comp continuous_toSL).congr fun A => (toPSL_apply A).symm

end TopologicalRing

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Over `ℝ` or `ℂ`, the projective special unitary group `PSU(n)` is a compact subset of
`PSL(n, 𝕜)`, as the continuous image of the compact group `SU(n)`. -/
theorem isCompact_range_toPSL :
    IsCompact ((toPSL : specialUnitaryGroup n 𝕜 →* _).range :
      Set (ProjectiveSpecialLinearGroup n 𝕜)) := by
  rw [MonoidHom.coe_range]
  exact isCompact_range continuous_toPSL

/-- Over `ℝ` or `ℂ`, the projective special unitary group `PSU(n)` is closed in the Hausdorff
group `PSL(n, 𝕜)`. -/
theorem isClosed_range_toPSL :
    IsClosed ((toPSL : specialUnitaryGroup n 𝕜 →* _).range :
      Set (ProjectiveSpecialLinearGroup n 𝕜)) :=
  isCompact_range_toPSL.isClosed

/-- **`PSU(n)` as a quotient of `SU(n)`.** Over `ℝ` or `ℂ`, `SU(n)` modulo the kernel of
`toPSL` is isomorphic as a topological group to the projective special unitary group `PSU(n)`,
the range of `toPSL` with the topology induced from `PSL(n, 𝕜)`: a continuous map from a
compact space to a Hausdorff space is closed, hence strict. For `n = 2` the kernel is `{1, -1}`
(`Matrix.specialUnitaryGroup.mem_ker_toPSL_iff`). -/
noncomputable def quotientKerToPSLContinuousMulEquiv :
    specialUnitaryGroup n 𝕜 ⧸ (toPSL : specialUnitaryGroup n 𝕜 →* _).ker ≃ₜ*
      (toPSL : specialUnitaryGroup n 𝕜 →* ProjectiveSpecialLinearGroup n 𝕜).range :=
  ContinuousMulEquiv.quotientKerEquivRange (f := toPSL)
    (continuous_toPSL.isClosedMap.isStrictMap continuous_toPSL)

@[simp]
theorem coe_quotientKerToPSLContinuousMulEquiv_mk (A : specialUnitaryGroup n 𝕜) :
    (quotientKerToPSLContinuousMulEquiv (A : specialUnitaryGroup n 𝕜 ⧸ _) :
      ProjectiveSpecialLinearGroup n 𝕜) = toPSL A := by
  rfl

end RCLike

end Matrix.specialUnitaryGroup
