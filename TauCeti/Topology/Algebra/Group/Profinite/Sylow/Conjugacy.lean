/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Sylow.Containment

/-!
# Conjugacy of Sylow subgroups in profinite groups

Any two Sylow pro-`p` subgroups of a profinite group are conjugate. This is containment read
against maximality: a Sylow pro-`p` subgroup lies in a conjugate of any other by
`IsProP.exists_le_map_conj`, and a conjugate of a Sylow pro-`p` subgroup is again Sylow pro-`p`,
so `IsProPSylow.eq_of_le` upgrades that containment to an equality.

## Main results

* `IsProPSylow.exists_map_conj_eq`: any two Sylow pro-`p` subgroups are conjugate.
* `IsProPSylow.eq_of_normal`: a normal Sylow pro-`p` subgroup is unique.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.3.
-/

public section

namespace TauCeti

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
variable {P Q : Subgroup G}

namespace IsProPSylow

/-- Any two Sylow pro-`p` subgroups of a profinite group are conjugate. -/
theorem exists_map_conj_eq (hP : IsProPSylow p P) (hQ : IsProPSylow p Q) :
    ∃ g : G, P.map (MulAut.conj g).toMonoidHom = Q := by
  obtain ⟨g, hg⟩ := hQ.isProP.exists_le_map_conj hP
  exact ⟨g, (hQ.eq_of_le (hP.map_conj g).isProP hg).symm⟩

/-- A normal Sylow pro-`p` subgroup is the unique Sylow pro-`p` subgroup. -/
theorem eq_of_normal (p : ℕ) [Fact p.Prime] (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (P Q : Subgroup G)
    (hP : IsProPSylow p P) (hQ : IsProPSylow p Q) (hn : P.Normal) : P = Q := by
  obtain ⟨g, rfl⟩ := hP.exists_map_conj_eq hQ
  exact (@Subgroup.Normal.map_conj_eq G _ P hn g).symm

end IsProPSylow

end TauCeti
