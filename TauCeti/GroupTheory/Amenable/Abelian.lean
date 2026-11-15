/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Discrete
public import TauCeti.GroupTheory.Amenable.DirectedUnion
public import TauCeti.GroupTheory.Amenable.Int
public import TauCeti.GroupTheory.Amenable.Prod
public import TauCeti.GroupTheory.NoncommPiCoprod

/-!
# Amenability of commutative groups

Every commutative topological group — additive (`AddCommGroup`) or multiplicative (`CommGroup`) —
is amenable, with no hypothesis on its rank, its torsion or its topology.

A finitely generated commutative additive group `A` is a surjective homomorphic image of `Fin n → ℤ`
via `TauCeti.zmultiplesPiHom` (`AddGroup.fg_iff_exists_fin_addMonoidHom_surjective`). Equipping `ℤ`
with the discrete topology makes `Fin n → ℤ` a finite product of amenable discrete groups
(`TauCeti.AddAmenable.int`, `TauCeti.AddAmenable.pi`), so `A` is amenable for every additive group
topology by `TauCeti.AddAmenable.of_surjective`.

An arbitrary commutative additive group is exhausted by its finitely generated subgroups, each of
which is amenable by the finitely generated case, so `TauCeti.AddAmenable.of_forall_fg` proves
`TauCeti.AddAmenable.of_addCommGroup`. Transporting across `Additive` gives the multiplicative
counterpart `TauCeti.Amenable.of_commGroup`, alongside the finitely generated theorem
`TauCeti.Amenable.of_group_fg`.

## Main results

* `TauCeti.AddAmenable.of_addGroup_fg`, `TauCeti.Amenable.of_group_fg`: finitely generated
  commutative topological groups are amenable.
* `TauCeti.AddAmenable.of_addCommGroup`: every commutative additive topological group is amenable.
* `TauCeti.Amenable.of_commGroup`: every commutative topological group is amenable.

## References

* A. Garrido, *An introduction to amenable groups*, Proposition 2.3.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Proposition G.2.2 and
  Example G.5.4.
-/

public section

namespace TauCeti

/-- Every finitely generated commutative additive topological group is amenable: it is a surjective
homomorphic image of a finite product of copies of `ℤ`. -/
theorem AddAmenable.of_addGroup_fg {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [AddGroup.FG A] : AddAmenable A := by
  obtain ⟨n, φ, hφ⟩ := AddGroup.fg_iff_exists_fin_addMonoidHom_surjective.1 ‹_›
  let : TopologicalSpace ℤ := ⊥
  have : DiscreteTopology ℤ := ⟨rfl⟩
  exact .of_surjective φ hφ

/-- Every commutative additive topological group is amenable, whatever its additive group topology:
its finitely generated subgroups are amenable and exhaust the group. -/
instance (priority := 100) AddAmenable.of_addCommGroup {A : Type*} [AddCommGroup A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] : AddAmenable A :=
  .of_forall_fg fun K hK => by
    have : AddGroup.FG K := (AddGroup.fg_iff_addSubgroup_fg K).2 hK
    exact .of_addGroup_fg

/-- Every finitely generated commutative topological group is amenable: it is a surjective
homomorphic image of a finite product of copies of `Multiplicative ℤ`. -/
theorem Amenable.of_group_fg {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group.FG G] : Amenable G := by
  obtain ⟨n, φ, hφ⟩ := Group.fg_iff_exists_fin_monoidHom_surjective.1 ‹_›
  let : TopologicalSpace (Multiplicative ℤ) := ⊥
  have : DiscreteTopology (Multiplicative ℤ) := ⟨rfl⟩
  exact .of_surjective φ hφ

/-- Every commutative topological group is amenable, whatever its group topology. -/
instance (priority := 100) Amenable.of_commGroup {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Amenable G :=
  addAmenable_additive_iff.1 inferInstance

end TauCeti
