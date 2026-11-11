/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Star.Unitary
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.SpecialUnitary
public import TauCeti.Topology.Algebra.Star.Unitary

import TauCeti.Topology.Algebra.Group.Units.ContinuousMulEquiv

/-!
# Topology and native carriers of unitary matrix groups

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
likewise passes to the unitary subgroup `unitarySubgroup (GL n 𝕜)`.

The continuous matrix-to-units inclusion also identifies `GLSpecialUnitary` with Mathlib's
special unitary group by a continuous multiplicative equivalence for the inherited topologies.
This homeomorphism transports the closed-subgroup charts to the native matrix carrier.

This is the setup the compact-group representation theory of `SU(2)` runs on; see
`TauCeti/RepresentationTheory/SU2/Basic.lean`.

## Main results

* `TauCeti.GLSpecialUnitary.toMulEquiv_specialUnitaryGroupContinuousMulEquiv`: the underlying
  algebraic equivalence is unchanged.
* `TauCeti.GLSpecialUnitary.coe_specialUnitaryGroupContinuousMulEquiv_symm`: the inverse
  matrix rule.

* `TauCeti.GLSpecialUnitary.continuous_ofSpecialUnitaryGroup`: continuity of the inclusion.
* `TauCeti.GLSpecialUnitary.specialUnitaryGroupContinuousMulEquiv`: the carrier homeomorphism.
* `TauCeti.GLSpecialUnitary.coe_specialUnitaryGroupContinuousMulEquiv`:
  its forward map is the canonical matrix-to-units inclusion.

* `TauCeti.Matrix.isClosed_specialUnitaryGroup`: the special unitary matrix group is closed.
* `TauCeti.Matrix.isCompact_unitaryGroup` and `TauCeti.Matrix.isCompact_specialUnitaryGroup`: the
  unitary and special unitary matrix groups over `ℝ` or `ℂ` are compact.
* `TauCeti.isClosed_GLSpecialUnitary`: the special unitary subgroup of the general linear group is
  closed.
* `Matrix.GeneralLinearGroup.isCompact_unitarySubgroup`: the unitary subgroup of the general linear
  group over `ℝ` or `ℂ` is compact.
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
  continuous_inv := continuous_induced_rng.mpr continuous_subtype_val.star

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

namespace TauCeti.GLSpecialUnitary

variable (n : Type*) [Fintype n] [DecidableEq n]
  (R : Type*) [CommRing R] [StarRing R] [TopologicalSpace R] [ContinuousStar R]

/-- The canonical matrix-to-units inclusion is continuous in both unit coordinates. -/
@[fun_prop]
theorem continuous_ofSpecialUnitaryGroup : Continuous (ofSpecialUnitaryGroup n R) :=
  Continuous.of_coeHom_comp (f := ofSpecialUnitaryGroup n R)
    (continuous_subtype_val.congr fun A ↦ (coe_ofSpecialUnitaryGroup n R A).symm)

/-- The canonical equivalence is a homeomorphism for the inherited topologies. -/
noncomputable def specialUnitaryGroupContinuousMulEquiv :
    Matrix.specialUnitaryGroup n R ≃ₜ* GLSpecialUnitary n R :=
  (mulEquivSpecialUnitaryGroup n R).symm.toContinuousMulEquivOfUnits
    (by simpa only [coe_mulEquivSpecialUnitaryGroup_symm_apply, coe_ofSpecialUnitaryGroup] using
      (Topology.IsEmbedding.subtypeVal (p := fun A ↦ A ∈ Matrix.specialUnitaryGroup n R)))

/-- The homeomorphism sends a special unitary matrix to its canonical unit. -/
@[simp]
theorem coe_specialUnitaryGroupContinuousMulEquiv (A : Matrix.specialUnitaryGroup n R) :
    (specialUnitaryGroupContinuousMulEquiv n R A : GL n R) = ofSpecialUnitaryGroup n R A := by
  rw [specialUnitaryGroupContinuousMulEquiv, MulEquiv.toContinuousMulEquivOfUnits_apply]
  exact coe_mulEquivSpecialUnitaryGroup_symm_apply n R A

/-- The inverse homeomorphism keeps the underlying matrix of each unit. -/
@[simp]
theorem coe_specialUnitaryGroupContinuousMulEquiv_symm (A : GLSpecialUnitary n R) :
    ((specialUnitaryGroupContinuousMulEquiv n R).symm A : Matrix n n R) =
      (A.val : Matrix n n R) := by
  rw [specialUnitaryGroupContinuousMulEquiv, MulEquiv.toContinuousMulEquivOfUnits_symm_apply,
    MulEquiv.symm_symm]
  exact coe_mulEquivSpecialUnitaryGroup n R A

/-- The homeomorphism retains the canonical algebraic equivalence. -/
@[simp]
theorem toMulEquiv_specialUnitaryGroupContinuousMulEquiv :
    (specialUnitaryGroupContinuousMulEquiv n R : Matrix.specialUnitaryGroup n R ≃*
      GLSpecialUnitary n R) = (mulEquivSpecialUnitaryGroup n R).symm := by
  rw [specialUnitaryGroupContinuousMulEquiv, MulEquiv.toMulEquiv_toContinuousMulEquivOfUnits]

end TauCeti.GLSpecialUnitary
