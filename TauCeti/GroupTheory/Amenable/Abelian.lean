/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Additive
public import TauCeti.GroupTheory.Amenable.Int
public import TauCeti.GroupTheory.NoncommPiCoprod

/-!
# Amenability of commutative groups

Every commutative topological group — additive or multiplicative — is amenable, with no hypothesis
on its rank, its torsion, or its topology.

For a finitely generated commutative additive subgroup `K`,
`AddGroup.fg_iff_exists_fin_int_hom_surjective` produces a surjective homomorphism
`(Fin n → ℤ) →+ K`. Giving `Fin n → ℤ` the discrete product topology, it is amenable by amenability
of `ℤ` (`TauCeti.AddAmenable.int`) and closure under products (`TauCeti.AddAmenable.pi`), and the
homomorphism is continuous into `K` for any additive group topology, so `K` is amenable by
`TauCeti.AddAmenable.of_denseRange`.

Every commutative topological group is then amenable because all of its finitely generated
subgroups are commutative and finitely generated (`TauCeti.AddAmenable.of_forall_fg`,
`TauCeti.Amenable.of_forall_fg`). Equipping an abstract commutative group with the discrete
topology yields Følner sets (`TauCeti.HasAddFoelnerSets.of_addCommGroup`,
`TauCeti.HasFoelnerSets.of_commGroup`).

## Main results

* `TauCeti.AddAmenable.of_addCommGroup`, `TauCeti.Amenable.of_commGroup`: every commutative
  topological group is amenable.
* `TauCeti.HasAddFoelnerSets.of_addCommGroup`, `TauCeti.HasFoelnerSets.of_commGroup`: every
  commutative group has Følner sets.

## References

* A. Garrido, *An introduction to amenable groups*, Proposition 2.3.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Proposition G.2.2 and
  Example G.5.4.
-/

public section

namespace TauCeti

/-- Every commutative additive topological group is amenable, whatever its additive group
topology. -/
instance (priority := 100) AddAmenable.of_addCommGroup {A : Type*} [AddCommGroup A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] : AddAmenable A :=
  .of_forall_fg fun K hK => by
    obtain ⟨n, φ, hφ⟩ := AddGroup.fg_iff_exists_fin_int_hom_surjective.1
      ((AddGroup.fg_iff_addSubgroup_fg K).2 hK)
    exact .of_denseRange ⟨φ, continuous_of_discreteTopology⟩ hφ.denseRange

/-- Every commutative topological group is amenable, whatever its group topology. -/
instance (priority := 100) Amenable.of_commGroup {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Amenable G :=
  .of_forall_fg fun K hK => by
    obtain ⟨n, φ, hφ⟩ := Group.fg_iff_exists_fin_multiplicative_int_hom_surjective.1
      ((Group.fg_iff_subgroup_fg K).2 hK)
    exact .of_denseRange ⟨φ, continuous_of_discreteTopology⟩ hφ.denseRange

/-- Every commutative additive group has Følner sets. -/
theorem HasAddFoelnerSets.of_addCommGroup {A : Type*} [AddCommGroup A] : HasAddFoelnerSets A := by
  let _ : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  exact AddAmenable.hasAddFoelnerSets

/-- Every commutative group has Følner sets. -/
@[to_additive existing]
theorem HasFoelnerSets.of_commGroup {G : Type*} [CommGroup G] : HasFoelnerSets G := by
  let _ : TopologicalSpace G := ⊥
  have : DiscreteTopology G := ⟨rfl⟩
  exact Amenable.hasFoelnerSets

end TauCeti
