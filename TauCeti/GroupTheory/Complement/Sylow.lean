/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Sylow
public import TauCeti.GroupTheory.Complement.Gaschutz

/-!
# Sylow detection of complements

Let `N` be a finite abelian normal `p`-subgroup of a group `G` and `P` a Sylow `p`-subgroup of
finite index. Then `N` has a complement in `G` if and only if it has a complement in `P`. The
forward direction intersects a complement with `P`, which contains `N` because `N` is a normal
`p`-subgroup (`IsPGroup.le_sylow_of_normal`). The backward direction is Gaschütz's splitting
theorem (`Subgroup.IsLocalComplement.exists_isComplement'_of_coprime_index`), since `[G : P]` is
prime to `p` (`Sylow.not_dvd_index`) and hence to `|N|`.

The complement inside `P` is given either as a local complement `K ≤ G` of `N` in `P`
(`IsPGroup.exists_isComplement'_iff_sylow`) or as a complement of `N.subgroupOf P` in the group
`P` (`IsPGroup.exists_isComplement'_iff_sylow_subgroupOf`). Both hold in particular for every
finite group `G`.

The theorem fails for non-abelian `N`: in the central product of `SL(2, 3)` and a cyclic group of
order `4`, the quaternion group `Q₈` is a normal `2`-subgroup with a complement in a Sylow
`2`-subgroup but none in the whole group (Sambale, Section 1).

## References

* W. Gaschütz, *Zur Erweiterungstheorie der endlichen Gruppen*, J. reine angew. Math. 190
  (1952), 93–107, 2. Reduktionssatz.
* B. Sambale, *On the converse of Gaschütz' complement theorem*, arXiv:2303.00254, Section 1.
-/

public section

open scoped IsMulCommutative

namespace IsPGroup

variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] {N : Subgroup G} [N.Normal]
  [IsMulCommutative N] [Finite N]

/-- **Sylow detection of complements** (Gaschütz). A finite abelian normal `p`-subgroup `N` of
`G` has a complement in `G` if and only if it has a local complement in a Sylow `p`-subgroup `P`
of finite index. -/
theorem exists_isComplement'_iff_sylow (hN : IsPGroup p N) (P : Sylow p G) [P.FiniteIndex] :
    (∃ D : Subgroup G, N.IsComplement' D) ↔ ∃ K : Subgroup G, N.IsLocalComplement K P := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hN
  refine Subgroup.exists_isComplement'_iff_exists_isLocalComplement_of_coprime_index
    (hN.le_sylow_of_normal P) ?_
  rw [hn]
  exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr P.not_dvd_index).symm.pow_right n

/-- **Sylow detection of complements** (Gaschütz), stated inside the Sylow subgroup. A finite
abelian normal `p`-subgroup `N` of `G` has a complement in `G` if and only if `N.subgroupOf P`
has a complement in the group `P`, for a Sylow `p`-subgroup `P` of finite index. -/
theorem exists_isComplement'_iff_sylow_subgroupOf (hN : IsPGroup p N) (P : Sylow p G)
    [P.FiniteIndex] :
    (∃ D : Subgroup G, N.IsComplement' D) ↔
      ∃ K : Subgroup P, (N.subgroupOf P).IsComplement' K :=
  (hN.exists_isComplement'_iff_sylow P).trans
    (Subgroup.exists_isLocalComplement_iff_exists_isComplement'_subgroupOf
      (hN.le_sylow_of_normal P))

end IsPGroup
