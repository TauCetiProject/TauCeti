/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Principal
public import TauCeti.RepresentationTheory.GroupAlgebra.Brauer.Kernel
public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup.Basic

/-!
# Defect groups of the principal block

Let `R` be a commutative semiring of characteristic `p` and `G` a finite group. The Brauer
projection at a `p`-subgroup `P` preserves the augmentation of `P`-invariant elements
(`TauCeti.augmentation_brauerProjection`). Hence a central element `e` of nonzero augmentation
has `Br_S(e) ≠ 0` at every Sylow `p`-subgroup `S`, and its defect groups are exactly the Sylow
`p`-subgroups (`TauCeti.isDefectGroup_iff_sylow_of_augmentation_ne_zero`): a defect group `D` lies
in a Sylow subgroup `S` with `Br_S(e) ≠ 0`, so `D = S` by maximality. In particular the defect
groups of the principal block of `k[G]`, `k` a field of characteristic `p`, are the Sylow
`p`-subgroups (`TauCeti.isDefectGroup_principalBlockIdempotent_iff`; Webb, Corollary 12.4.7,
p. 242). The argument needs neither vertices nor the conjugacy of defect groups.

## Main results

* `TauCeti.isDefectGroup_iff_sylow_of_augmentation_ne_zero`: the defect groups of a central
  element of nonzero augmentation are the Sylow `p`-subgroups.
* `TauCeti.isDefectGroup_principalBlockIdempotent_iff`: the defect groups of the principal block
  are the Sylow `p`-subgroups.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Corollary 12.4.7, p. 242.
-/

public section

namespace TauCeti

open MonoidAlgebra

variable {R G : Type*} [CommSemiring R] [Group G] {p : ℕ} [Fact p.Prime] [CharP R p]

/-- **Defect groups of an element of nonzero augmentation.** In characteristic `p`, the defect
groups of a central element `e` of `R[G]` with nonzero augmentation are exactly the Sylow
`p`-subgroups of `G` (Webb, Corollary 12.4.7, p. 242, for the principal block). -/
theorem isDefectGroup_iff_sylow_of_augmentation_ne_zero [Finite G] {e : MonoidAlgebra R G}
    (he : e ∈ Subalgebra.center R (MonoidAlgebra R G)) (hε : augmentation R G e ≠ 0)
    {D : Subgroup G} : IsDefectGroup R p e D ↔ ∃ S : Sylow p G, D = S := by
  have hne (S : Sylow p G) : brauerProjection (S : Subgroup G) e ≠ 0 :=
    brauerProjection_ne_zero_of_augmentation_ne_zero S.isPGroup
      (center_le_conjInvariants _ he) hε
  refine ⟨fun hD => ?_, ?_⟩
  · obtain ⟨S, hS⟩ := hD.isPGroup.exists_le_sylow
    exact ⟨S, ((isDefectGroup_iff.1 hD).2.2 S S.isPGroup (hne S) hS).symm⟩
  · rintro ⟨S, rfl⟩
    exact isDefectGroup_iff.2 ⟨S.isPGroup, hne S, fun Q hQ _ hSQ =>
      (S.maximal_isPGroup.eq_of_le hQ hSQ).symm⟩

/-- **The defect groups of the principal block are the Sylow subgroups.** For a field `k` of
characteristic `p`, the defect groups of the principal block idempotent of `k[G]` are exactly the
Sylow `p`-subgroups of `G` (Webb, Corollary 12.4.7, p. 242). -/
theorem isDefectGroup_principalBlockIdempotent_iff {k : Type*} [Field k] [CharP k p] [Finite G]
    {D : Subgroup G} :
    IsDefectGroup k p (principalBlockIdempotent k G : MonoidAlgebra k G) D ↔
      ∃ S : Sylow p G, D = S :=
  isDefectGroup_iff_sylow_of_augmentation_ne_zero (principalBlockIdempotent k G).property
    (by rw [augmentation_principalBlockIdempotent]; exact one_ne_zero)

end TauCeti
