/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Product
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Subgroup

/-!
# Inverse limits of pro-p groups

The class of pro-`p` groups is stable under inverse limits. Mathlib builds the limit of a
diagram of profinite groups as the subgroup `ProfiniteGrp.limitConePtAux` of the product of its
objects, so this is the composite of stability under products (`IsProP.pi`, which is why that
lemma may not assume a finite index type) with stability under subgroups (`IsProP.subgroup`).

Together with the covariant half of the API this gives the inverse-limit description of pro-`p`
groups: a profinite group is pro-`p` exactly when it is topologically isomorphic to a limit of
finite `p`-groups. One direction is the stability result, and the other realises a profinite
group as the limit of its own quotients by open normal subgroups, which are `p`-groups precisely
by the definition of `IsProP`.

## Main results

* `IsProP.limit`: an inverse limit of pro-`p` profinite groups is pro-`p`.
* `isProP_iff_exists_continuousMulEquiv_limit`: a profinite group is pro-`p` if and only if it is
  topologically isomorphic to an inverse limit of finite `p`-groups.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.2 and Proposition 2.2.1.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v

variable {p : ℕ}

/-- An inverse limit of pro-`p` profinite groups is pro-`p`: the limit is a subgroup of the
product of the objects of the diagram. -/
theorem IsProP.limit {J : Type v} [SmallCategory J] (F : J ⥤ ProfiniteGrp.{max v u})
    (hF : ∀ j, IsProP p (F.obj j)) : IsProP p (ProfiniteGrp.limit F) :=
  (IsProP.pi hF).subgroup (ProfiniteGrp.limitConePtAux F)

/-- A profinite group is pro-`p` exactly when it is topologically isomorphic to an inverse limit
of finite `p`-groups. The forward direction realises `G` as the limit of its own quotients by
open normal subgroups. -/
theorem isProP_iff_exists_continuousMulEquiv_limit {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] :
    IsProP p G ↔ ∃ (J : Type u) (_ : SmallCategory J) (F : J ⥤ FiniteGrp.{u}),
      (∀ j, IsPGroup p (F.obj j)) ∧
        Nonempty (G ≃ₜ* ProfiniteGrp.limit (F ⋙ forget₂ FiniteGrp ProfiniteGrp)) := by
  refine ⟨fun hG ↦ ⟨OpenNormalSubgroup (ProfiniteGrp.of G), inferInstance,
    ProfiniteGrp.toFiniteQuotientFunctor (ProfiniteGrp.of G), fun U ↦ isProP_iff.mp hG U,
    ⟨ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor (ProfiniteGrp.of G)⟩⟩, ?_⟩
  rintro ⟨J, _, F, hF, ⟨e⟩⟩
  refine (IsProP.limit _ fun j ↦ ?_).of_equiv e.symm
  exact IsPGroup.isProP (hF j)

end TauCeti
