/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Strict.Group
public import TauCeti.GroupTheory.Amenable.Basic

/-!
# Quotients and images of amenable topological groups

Amenability passes from a topological group `G` to its quotient `G ⧸ N` by every normal subgroup,
with the quotient topology, and to the range of every continuous homomorphism `φ : G →* H`, with
the subspace topology of `H`. In both cases the canonical map out of `G` is a surjective continuous
homomorphism, along which left-invariant means push forward (`TauCeti.Amenable.of_denseRange`).

The range of `φ` is also the image of `G ⧸ φ.ker` under the continuous surjective homomorphism
`QuotientGroup.rangeKerLift φ`, so amenability of `G ⧸ φ.ker` alone implies amenability of
`φ.range`. The quotient carries the quotient topology and the range the subspace topology, so the
first isomorphism theorem `QuotientGroup.quotientKerEquivRange φ` need not be a homeomorphism. It
is one exactly when `φ` is a strict map (Mathlib's `Topology.IsStrictMap`), for instance a
continuous homomorphism to a discrete group, and then the two groups are amenable together.

## Main results

* `TauCeti.Amenable.quotient`: the quotient of an amenable topological group by a normal subgroup
  is amenable.
* `TauCeti.Amenable.range_of_quotient_ker`: if `φ` is continuous and `G ⧸ φ.ker` is amenable,
  then `φ.range` is amenable.
* `TauCeti.Amenable.range`: the range of a continuous homomorphism out of an amenable topological
  group is amenable.
* `TauCeti.amenable_quotient_ker_iff_range`: for a strict homomorphism `φ`, the groups
  `G ⧸ φ.ker` and `φ.range` are amenable together.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Proposition G.2.2.
* A. Garrido, *An introduction to amenable groups*, Proposition 2.2.
-/

public section

open Topology

namespace TauCeti

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The quotient of an amenable topological group by a normal subgroup is amenable for the
quotient topology. -/
instance Amenable.quotient [Amenable G] (N : Subgroup G) [N.Normal] : Amenable (G ⧸ N) :=
  .of_denseRange ⟨QuotientGroup.mk' N, QuotientGroup.continuous_mk⟩
    (QuotientGroup.mk'_surjective N).denseRange

/-- If `φ : G →* H` is continuous and the quotient `G ⧸ φ.ker` is amenable, then the range of `φ`
is amenable for the subspace topology. -/
theorem Amenable.range_of_quotient_ker {φ : G →* H} (hφ : Continuous φ) [Amenable (G ⧸ φ.ker)] :
    Amenable φ.range := by
  -- `rangeKerLift φ` is defined as the lift of `φ.rangeRestrict` through the quotient map, so its
  -- composite with the quotient map is the corestriction of `φ` to its range.
  have h (g : G) : QuotientGroup.rangeKerLift φ g = φ.rangeRestrict g :=
    QuotientGroup.lift_mk _ _ _
  have hc : Continuous (QuotientGroup.rangeKerLift φ) := by
    rw [(QuotientGroup.isQuotientMap_mk φ.ker).continuous_iff]
    exact (hφ.subtype_mk _).congr fun g => (h g).symm
  exact .of_denseRange ⟨QuotientGroup.rangeKerLift φ, hc⟩
    (QuotientGroup.rangeKerLift_surjective φ).denseRange

/-- The range of a continuous homomorphism out of an amenable topological group is amenable for
the subspace topology. -/
theorem Amenable.range [Amenable G] {φ : G →* H} (hφ : Continuous φ) : Amenable φ.range :=
  .range_of_quotient_ker hφ

/-- For a strict homomorphism `φ : G →* H`, the quotient `G ⧸ φ.ker` with the quotient topology is
amenable exactly when the range of `φ` with the subspace topology is. -/
theorem amenable_quotient_ker_iff_range {φ : G →* H} (hφ : IsStrictMap φ) :
    Amenable (G ⧸ φ.ker) ↔ Amenable φ.range :=
  (ContinuousMulEquiv.quotientKerEquivRange hφ).amenable_iff

end TauCeti
