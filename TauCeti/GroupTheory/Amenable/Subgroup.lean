/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Basic
public import TauCeti.Topology.Algebra.Group.UCB.Subgroup

/-!
# Subgroups of amenable discrete groups

Every subgroup of an amenable discrete group is amenable. Choose a right transversal of
`H ≤ G`, extend functions on `H` constantly in the transversal coordinate, and apply a mean
on `G`. Equivariance of the extension makes the resulting mean left invariant.

`Mean.subgroup` records the mean for each choice of transversal, and `Mean.subgroup_apply`
gives its averaging formula. The construction preserves positivity and normalization. For a
normalized transversal it is a left inverse of pushforward along the subgroup inclusion,
because the equivariant map used in the construction is a retraction.

## References

* A. Garrido, *An introduction to amenable groups*, Proposition 2.2 (subgroups).
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Proposition G.2.2.
-/

public section

noncomputable section

open scoped BoundedContinuousFunction

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  {H : Subgroup G}

namespace Mean

/-- Average functions on a subgroup using a mean on the ambient discrete group and a right
transversal. -/
def subgroup (m : Mean G) (T : H.RightTransversal) : Mean H :=
  mk₀ (m.toPositiveLinearMap.toLinearMap ∘ₗ (UCB.extendSubgroup T).toLinearMap)
    (fun f hf => map_nonneg m (by simpa using (UCB.monotone_extendSubgroup T) hf)) (by simp)

/-- Subgroup averaging applies the original mean to the extension along a right transversal. -/
@[simp]
theorem subgroup_apply (m : Mean G) (T : H.RightTransversal) (f : UCB H) :
    m.subgroup T f = m (UCB.extendSubgroup T f) :=
  mk₀_apply _ _ _ f

/-- Subgroup averaging of point evaluation evaluates at the subgroup coordinate. -/
@[simp]
theorem subgroup_eval (T : H.RightTransversal) (x : G) :
    (eval G x).subgroup T = eval H (T.2.equiv x).1 := by
  ext f
  simp

/-- Extending a mean along the subgroup inclusion and then averaging back returns the
original mean, provided the transversal represents `H` by `1`. -/
@[simp]
theorem subgroup_map_subgroupSubtype (m : Mean H) (T : H.RightTransversal) (hT : 1 ∈ T.1) :
    (m.map (ContinuousMonoidHom.subgroupSubtype H)).subgroup T = m := by
  ext f
  simp [hT]

/-- Left invariance of an ambient mean implies left invariance of its subgroup mean. -/
theorem IsLeftInvariant.subgroup {m : Mean G} (hm : m.IsLeftInvariant) (T : H.RightTransversal) :
    (m.subgroup T).IsLeftInvariant := by
  rw [isLeftInvariant_iff]
  intro h f
  simp [UCB.extendSubgroup_leftTranslation, hm]

end Mean

/-- Every subgroup of an amenable discrete group is amenable, with its induced topology. -/
instance Amenable.subgroup [Amenable G] (H : Subgroup G) : Amenable H := by
  obtain ⟨m, hm⟩ := Amenable.exists_isLeftInvariant (G := G)
  obtain ⟨T, hT, _⟩ := H.exists_isComplement_right 1
  exact ⟨⟨m.subgroup ⟨T, hT⟩, hm.subgroup ⟨T, hT⟩⟩⟩

end TauCeti
