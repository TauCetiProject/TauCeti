/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Star.Unitary

/-!
# The unitary subgroup of the units is closed

Mathlib's `isClosed_unitary` says that the unitary elements of a topological star monoid `M` are
a closed subset of `M`.  This file transfers that to the group of units: `unitarySubgroup Mˣ`,
the unitary elements of `Mˣ` packaged as a subgroup, is closed in `Mˣ`.  Compactness transfers in
the same way: when `unitary M` is compact, so is `unitarySubgroup Mˣ`.

The transfer is immediate once Mathlib's `Units.unitary_eq` exhibits the subgroup as the
preimage of `unitary M` under `Units.val`, which is continuous.  No hypothesis beyond the ones
`isClosed_unitary` already needs is required.

This is the closedness hypothesis that the Lie algebra of a closed subgroup of `Mˣ` is computed
from; see `TauCeti/Geometry/Lie/Subgroup/Unitary.lean`.

## Main results

* `TauCeti.mem_unitary_units_iff`: a unit is unitary exactly when its underlying element is.
* `TauCeti.isClosed_unitarySubgroup_units`: the unitary subgroup of `Mˣ` is closed.
* `TauCeti.isCompact_unitarySubgroup_units`: the unitary subgroup of `Mˣ` is compact when
  `unitary M` is.
-/

public section

namespace TauCeti

/-- A unit of a star monoid is unitary exactly when its underlying element is unitary. -/
@[simp]
theorem mem_unitary_units_iff {M : Type*} [Monoid M] [StarMul M] {g : Mˣ} :
    g ∈ unitary Mˣ ↔ (g : M) ∈ unitary M := by
  rw [Units.unitary_eq, Submonoid.mem_comap, Units.coeHom_apply]

variable (M : Type*) [Monoid M] [StarMul M] [TopologicalSpace M] [T1Space M] [ContinuousStar M]
  [ContinuousMul M]

/-- **The unitary subgroup of the units of a topological star monoid is closed.**  It is the
preimage of the closed set `unitary M` under the continuous coercion `Units.val`. -/
theorem isClosed_unitarySubgroup_units :
    IsClosed ((unitarySubgroup Mˣ : Subgroup Mˣ) : Set Mˣ) := by
  have hpre : ((unitarySubgroup Mˣ : Subgroup Mˣ) : Set Mˣ) =
      Units.val ⁻¹' (unitary M : Set M) :=
    Set.ext fun _ => mem_unitary_units_iff
  rw [hpre]
  exact isClosed_unitary.preimage Units.continuous_val

/-- **The unitary subgroup of the units of a topological star monoid is compact when `unitary M`
is.**  It is the image of `unitary M` under the continuous map sending a unitary element to the
unit it defines. -/
theorem isCompact_unitarySubgroup_units {M : Type*} [Monoid M] [StarMul M] [TopologicalSpace M]
    [ContinuousStar M] (h : IsCompact (unitary M : Set M)) :
    IsCompact ((unitarySubgroup Mˣ : Subgroup Mˣ) : Set Mˣ) := by
  have : CompactSpace (unitary M) := isCompact_iff_compactSpace.mp h
  have hrange : ((unitarySubgroup Mˣ : Subgroup Mˣ) : Set Mˣ) =
      Set.range fun U : unitary M ↦ Unitary.toUnits U := by
    ext g
    refine ⟨fun hg ↦ ⟨⟨g, mem_unitary_units_iff.mp hg⟩, Units.ext rfl⟩, ?_⟩
    rintro ⟨U, rfl⟩
    exact mem_unitary_units_iff.mpr U.property
  rw [hrange]
  exact isCompact_range <| Units.continuous_iff.mpr
    ⟨continuous_subtype_val, continuous_subtype_val.star⟩

end TauCeti
