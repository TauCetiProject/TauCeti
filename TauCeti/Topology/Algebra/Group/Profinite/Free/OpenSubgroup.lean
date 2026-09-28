/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.OpenSubgroup
public import TauCeti.Topology.Algebra.Group.Profinite.Free.CohomologicalDimension
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Rank
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Serre
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.EulerCharacteristic.Basic

/-!
# Open subgroups of a free pro-`p` group: the Nielsen–Schreier theorem

An open subgroup `U` of index `m` in a free pro-`p` group `F` of finite rank `n ≥ 1` is free pro-`p`
of rank `d(U) = 1 + m * (n - 1)`. This is the pro-`p` Nielsen–Schreier theorem for open subgroups,
with the Schreier index formula for the rank. The rank formula shows that the Schreier bound
`TauCeti.topologicalGeneratorRankNat_le_of_openSubgroup` is an equality for free pro-`p` groups.

Closed subgroups that are not open are free pro-`p` of possibly infinite rank; that statement needs
free pro-`p` groups on a profinite space and is not made here.

## Main results

* `TauCeti.freeProP.topologicalGeneratorRankNat_add_index`: `d(U) + [F : U] = 1 + [F : U] * n`.
* `TauCeti.freeProP.topologicalGeneratorRankNat_openSubgroup`: `d(U) = 1 + [F : U] * (n - 1)` for
  `n ≥ 1`.
* `TauCeti.freeProP.cohomologicalDimensionAt_le_one_openSubgroup`: `cd_p U ≤ 1` for an open
  subgroup `U` of a free pro-`p` group, on any type of generators.
* `TauCeti.freeProP.nonempty_continuousMulEquiv_freeProP_openSubgroup`: an open subgroup `U` of a
  free pro-`p` group of finite rank is free pro-`p` of rank `d(U)`.
* `TauCeti.freeProP.nonempty_continuousMulEquiv_freeProP_openSubgroup_index`: **the pro-`p`
  Nielsen–Schreier theorem for open subgroups**, `U ≅ freeProP p Y` for every finite type `Y` with
  `Nat.card Y = 1 + [F : U] * (n - 1)`.

## References

* H. Koch, *Galois Theory of `p`-Extensions*, Example 6.3.
* J.-P. Serre, *Galois Cohomology*, Ch. I, §4.2.
* L. Ribes and P. Zalesskii, *Profinite Groups*, Thm. 3.6.2, for the transversal proof.
-/

public section

namespace TauCeti

universe u

namespace freeProP

variable {p : ℕ} {X : Type u}

/-! ### Cohomological dimension of an open subgroup -/

/-- **`cd_p U ≤ 1` for an open subgroup `U` of a free pro-`p` group**, on any type `X` of
generators and for `p ≠ 0`: `cd_p (freeProP p X) ≤ 1` passes to open subgroups. -/
theorem cohomologicalDimensionAt_le_one_openSubgroup (hp : p ≠ 0)
    (U : OpenSubgroup (freeProP p X)) : cohomologicalDimensionAt.{u} p U.toSubgroup ≤ 1 :=
  cohomologicalDimensionAt_le_one_of_openSubgroup hp (cohomologicalDimensionAt_le_one hp) U

/-! ### The rank of an open subgroup -/

variable [hp : Fact p.Prime] [Finite X]

/-- **The Schreier index formula for open subgroups, additive form.** For an open subgroup
`U` of the free pro-`p` group on a finite type `X`, `d(U) + [F : U] = 1 + [F : U] * #X`. -/
theorem topologicalGeneratorRankNat_add_index (U : OpenSubgroup (freeProP p X)) :
    topologicalGeneratorRankNat U.toSubgroup
        ((isTopologicallyFinitelyGenerated_freeProP p X).of_openSubgroup U) + U.toSubgroup.index =
      1 + U.toSubgroup.index * Nat.card X := by
  -- `H²(F, ℤ/p)` vanishes, so the two-term Euler formula applies to `F`; then use `d(F) = #X`.
  have h := (isProP_freeProP p X).topologicalGeneratorRankNat_add_index
    (isTopologicallyFinitelyGenerated_freeProP p X)
    (fun A _ _ _ _ _ _ hA _ ↦ subsingleton_H2_of_isPPrimaryTorsion
      (isPPrimaryTorsion_of_natCard_eq_pow (hA.trans (pow_one p).symm))) U
  rwa [topologicalGeneratorRankNat_freeProP] at h

/-- **The Schreier index formula for open subgroups.** For an open subgroup `U` of index
`m` in the free pro-`p` group on a nonempty finite type `X` of cardinality `n`,
`d(U) = 1 + m * (n - 1)`. -/
theorem topologicalGeneratorRankNat_openSubgroup [Nonempty X] (U : OpenSubgroup (freeProP p X)) :
    topologicalGeneratorRankNat U.toSubgroup
        ((isTopologicallyFinitelyGenerated_freeProP p X).of_openSubgroup U) =
      1 + U.toSubgroup.index * (Nat.card X - 1) := by
  have h := topologicalGeneratorRankNat_add_index U
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.card_pos (α := X)).ne'
  rw [hn, Nat.succ_sub_one]
  rw [hn, Nat.succ_eq_add_one, mul_add, mul_one] at h
  omega

/-! ### Freeness of an open subgroup -/

/-- **An open subgroup of a free pro-`p` group of finite rank is free pro-`p`, of rank `d(U)`.**
For an open subgroup `U` of the free pro-`p` group on a finite type `X`, `U` is topologically
isomorphic to the free pro-`p` group on any finite type `Y` with `Nat.card Y = d(U)`. -/
theorem nonempty_continuousMulEquiv_freeProP_openSubgroup (U : OpenSubgroup (freeProP p X))
    (Y : Type u) [Finite Y] (hY : Nat.card Y = topologicalGeneratorRankNat U.toSubgroup
      ((isTopologicallyFinitelyGenerated_freeProP p X).of_openSubgroup U)) :
    Nonempty (U.toSubgroup ≃ₜ* freeProP p Y) :=
  -- Serre's theorem: `U` is a topologically finitely generated pro-`p` group with `cd_p U ≤ 1`.
  have : CompactSpace U.toSubgroup := isCompact_iff_compactSpace.mp U.isClosed.isCompact
  IsProP.nonempty_continuousMulEquiv_freeProP_of_cohomologicalDimensionAt_le_one
    ((isProP_freeProP p X).subgroup U.toSubgroup) _
    (cohomologicalDimensionAt_le_one_openSubgroup hp.out.ne_zero U) Y hY

/-- **The pro-`p` Nielsen–Schreier theorem for open subgroups.** An open subgroup `U` of index `m`
in the free pro-`p` group on a nonempty finite type `X` of cardinality `n` is topologically
isomorphic to the free pro-`p` group on any finite type `Y` with `Nat.card Y = 1 + m * (n - 1)`. -/
theorem nonempty_continuousMulEquiv_freeProP_openSubgroup_index [Nonempty X]
    (U : OpenSubgroup (freeProP p X)) (Y : Type u) [Finite Y]
    (hY : Nat.card Y = 1 + U.toSubgroup.index * (Nat.card X - 1)) :
    Nonempty (U.toSubgroup ≃ₜ* freeProP p Y) :=
  nonempty_continuousMulEquiv_freeProP_openSubgroup U Y
    (hY.trans (topologicalGeneratorRankNat_openSubgroup U).symm)

end freeProP

end TauCeti
