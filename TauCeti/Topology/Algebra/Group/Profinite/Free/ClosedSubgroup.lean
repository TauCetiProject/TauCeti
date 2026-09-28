/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClosedSubgroup
public import TauCeti.Topology.Algebra.Group.Profinite.Free.CohomologicalDimension
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Pointed.Serre
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Subgroup

/-!
# Closed subgroups of a free pro-`p` group are free pro-`p`

This is the pro-`p` **Nielsen–Schreier theorem**: a closed subgroup `U` of a free pro-`p` group
`F = freeProP p X`, on any type `X` of generators, is free pro-`p` on a pointed profinite space.
More precisely `U` has a subset `s` converging to `1` such that the presentation
`F_p(insert 1 s, 1) → U` on `s` (`TauCeti.IsProP.presentation`) is a topological isomorphism;
in the language of Ribes–Zalesskii, `s` is a basis of `U` converging to `1`.

The proof is cohomological. A free pro-`p` group has `cd_p F ≤ 1`
(`TauCeti.freeProP.cohomologicalDimensionAt_le_one`), and `cd_p ≤ 1` passes to closed subgroups
by Shapiro's lemma in degree two (`TauCeti.cohomologicalDimensionAt_le_of_isClosed_of_le_one`),
so `cd_p U ≤ 1`; Serre's theorem at arbitrary rank
(`IsProP.exists_convergesToOne_continuousMulEquiv_presentation_of_cohomologicalDimensionAt_le_one`)
then identifies `U` with the free pro-`p` group on a pointed profinite space. The same argument
applies verbatim to a closed subgroup of any pro-`p` group with `cd_p ≤ 1`, and that is the form
proved first. Open subgroups of a free pro-`p` group of finite rank are the case of finite rank,
where the Schreier index formula for the rank is available
(`TauCeti.Topology.Algebra.Group.Profinite.Free.OpenSubgroup`).

## Main results

* `IsProP.exists_convergesToOne_continuousMulEquiv_of_cohomologicalDimensionAt_le_one_of_isClosed`:
  a closed subgroup of a pro-`p` group with `cd_p ≤ 1` is free pro-`p` on a pointed profinite
  space.
* `TauCeti.freeProP.cohomologicalDimensionAt_le_one_of_isClosed`: `cd_p U ≤ 1` for a closed
  subgroup `U` of a free pro-`p` group.
* `TauCeti.freeProP.exists_convergesToOne_continuousMulEquiv_of_isClosed`: **the pro-`p`
  Nielsen–Schreier theorem**, a closed subgroup of a free pro-`p` group is free pro-`p` on a
  pointed profinite space, with a basis converging to `1`.

## Implementation notes

The isomorphism `F_p(insert 1 s, 1) ≃ₜ* U` is recorded by its values on the generators, the
generator attached to a point of `insert 1 s` going to that point, rather than as the equation
`⇑e = ⇑(presentation s)` used by Serre's theorem for the ambient group. The presentation of `U` on
`s` needs `U` to be a profinite group, and the `CompactSpace U` instance that closedness supplies
is available inside a proof but not in the statement of a theorem about an arbitrary closed
subgroup. The two forms agree by `TauCeti.IsProP.presentation_of` and
`TauCeti.freeProCPointed.hom_ext`.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §4.2, Cor. 3 of Prop. 24.
* L. Ribes and P. Zalesskii, *Profinite Groups*, 2nd ed., Cor. 7.7.5.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. III, §5.
-/

public section

namespace TauCeti

universe u

variable {p : ℕ}

namespace IsProP

variable [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **A closed subgroup of a pro-`p` group with `cd_p ≤ 1` is free pro-`p` on a pointed profinite
space.** For `G` pro-`p` with `cd_p G ≤ 1` and `U ≤ G` closed, some subset `s` of `U` converging
to `1` has a topological isomorphism `F_p(insert 1 s, 1) ≃ₜ* U` sending the generator attached to
each point of `insert 1 s` to that point; by `TauCeti.freeProCPointed.hom_ext` it is the
presentation `TauCeti.IsProP.presentation` of `U` on `s`. -/
theorem exists_convergesToOne_continuousMulEquiv_of_cohomologicalDimensionAt_le_one_of_isClosed
    (hG : IsProP p G) (hcd : cohomologicalDimensionAt.{u} p G ≤ 1) {U : Subgroup G}
    (hU : IsClosed (U : Set G)) :
    ∃ s : Set U, ConvergesToOne s ∧ ∃ e : freeProPInsertOne p s ≃ₜ* U,
      ∀ x : ↥(insert (1 : U) s), e (freeProCPointed.of (finiteGroupClassP.{u} p) _ x) = x := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU.isCompact
  have hcdU : cohomologicalDimensionAt.{u} p U ≤ 1 := mod_cast
    cohomologicalDimensionAt_le_of_isClosed_of_le_one (by exact_mod_cast hcd) hU le_rfl
  have hU' : IsProP p U := hG.subgroup U
  obtain ⟨s, hs, e, he⟩ :=
    hU'.exists_convergesToOne_continuousMulEquiv_presentation_of_cohomologicalDimensionAt_le_one
      hcdU
  exact ⟨s, hs, e, fun x ↦ (congrFun he _).trans (presentation_of _ _ x)⟩

end IsProP

namespace freeProP

variable {X : Type u}

/-- **`cd_p U ≤ 1` for a closed subgroup `U` of a free pro-`p` group**, on any type `X` of
generators and for `p ≠ 0`: `cd_p (freeProP p X) ≤ 1` passes to closed subgroups. -/
theorem cohomologicalDimensionAt_le_one_of_isClosed (hp : p ≠ 0) {U : Subgroup (freeProP p X)}
    (hU : IsClosed (U : Set (freeProP p X))) : cohomologicalDimensionAt.{u} p U ≤ 1 :=
  mod_cast cohomologicalDimensionAt_le_of_isClosed_of_le_one
    (by exact_mod_cast cohomologicalDimensionAt_le_one hp) hU le_rfl

/-- **The pro-`p` Nielsen–Schreier theorem.** A closed subgroup `U` of the free pro-`p` group on
any type `X` is free pro-`p` on a pointed profinite space: some subset `s` of `U` converging to
`1` has a topological isomorphism `F_p(insert 1 s, 1) ≃ₜ* U` sending the generator attached to each
point of `insert 1 s` to that point, so that `s` is a basis of `U` converging to `1`. -/
theorem exists_convergesToOne_continuousMulEquiv_of_isClosed [Fact p.Prime]
    {U : Subgroup (freeProP p X)} (hU : IsClosed (U : Set (freeProP p X))) :
    ∃ s : Set U, ConvergesToOne s ∧ ∃ e : freeProPInsertOne p s ≃ₜ* U,
      ∀ x : ↥(insert (1 : U) s), e (freeProCPointed.of (finiteGroupClassP.{u} p) _ x) = x :=
  IsProP.exists_convergesToOne_continuousMulEquiv_of_cohomologicalDimensionAt_le_one_of_isClosed
    (isProP_freeProP p X) (cohomologicalDimensionAt_le_one (Fact.out : p.Prime).ne_zero) hU

end freeProP

end TauCeti
