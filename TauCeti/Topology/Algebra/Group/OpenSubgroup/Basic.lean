/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Compactness.LocallyCompact
public import TauCeti.Topology.Algebra.Group.Basic

/-!
# Topological group structure and local compactness of open subgroups

Mathlib registers `IsTopologicalGroup` on `Subgroup G`, and `TauCeti.Topology.Algebra.Group.Basic`
registers `ContinuousMul` and `SeparatelyContinuousMul` on `Subgroup G`, but instance search does
not unfold `H : OpenSubgroup G` to `H.toSubgroup`. Moreover, an open subgroup of a locally compact
group is locally compact (`IsOpen.locallyCompactSpace`), and an open subgroup of a weakly locally
compact group with separately continuous multiplication is weakly locally compact
(`OpenSubgroup.isClosed`, `IsClosed.weaklyLocallyCompactSpace`).

Registering all five instances on `OpenSubgroup G` lets constructions requiring a locally compact
topological group — such as Haar measures, the modular character, or compactly supported peak
functions — apply directly to `H : OpenSubgroup G`.

## Main declarations

* `OpenSubgroup.continuousMul`, `OpenSubgroup.separatelyContinuousMul`,
  `OpenSubgroup.isTopologicalGroup` (and additive counterparts): subgroup continuity instances on
  `OpenSubgroup G`.
* `OpenSubgroup.locallyCompactSpace`, `OpenSubgroup.weaklyLocallyCompactSpace` (and additive
  counterparts): local compactness instances on `OpenSubgroup G`.
-/

public section

namespace OpenSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G]

@[to_additive]
instance continuousMul [ContinuousMul G] (H : OpenSubgroup G) : ContinuousMul H :=
  H.toSubgroup.continuousMul

@[to_additive]
instance separatelyContinuousMul [SeparatelyContinuousMul G] (H : OpenSubgroup G) :
    SeparatelyContinuousMul H :=
  H.toSubgroup.separatelyContinuousMul

@[to_additive]
instance isTopologicalGroup [IsTopologicalGroup G] (H : OpenSubgroup G) :
    IsTopologicalGroup H :=
  inferInstanceAs (IsTopologicalGroup H.toSubgroup)

/-- An open subgroup of a locally compact group is locally compact. -/
@[to_additive /-- An open subgroup of a locally compact additive group is locally compact. -/]
instance locallyCompactSpace [LocallyCompactSpace G] (H : OpenSubgroup G) :
    LocallyCompactSpace H :=
  H.isOpen.locallyCompactSpace

/-- An open subgroup of a weakly locally compact group with separately continuous multiplication is
weakly locally compact. -/
@[to_additive /-- An open subgroup of a weakly locally compact additive group with separately
continuous addition is weakly locally compact. -/]
instance weaklyLocallyCompactSpace [SeparatelyContinuousMul G] [WeaklyLocallyCompactSpace G]
    (H : OpenSubgroup G) : WeaklyLocallyCompactSpace H :=
  H.isClosed.weaklyLocallyCompactSpace

end OpenSubgroup
