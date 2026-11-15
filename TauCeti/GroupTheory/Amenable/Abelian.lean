/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Additive
public import TauCeti.GroupTheory.Amenable.Int
public import TauCeti.GroupTheory.Finiteness

/-!
# Amenability of commutative groups

Every commutative topological group, additive or multiplicative, is amenable, with no hypothesis on
its rank, its torsion, or its topology.

First, a finitely generated commutative group is a surjective homomorphic image of a finite product
`Fin n → ℤ` (or `Fin n → Multiplicative ℤ`) equipped with the discrete topology
(`TauCeti.AddCommGroup.fg_iff_exists_fin_addMonoidHom_surjective` and
`TauCeti.CommGroup.fg_iff_exists_fin_monoidHom_surjective`). Since `ℤ` is amenable and finite
products and continuous homomorphic images preserve amenability, every finitely generated
commutative topological group is amenable (`TauCeti.AddAmenable.of_fg`, `TauCeti.Amenable.of_fg`).

Every commutative group is exhausted by its finitely generated subgroups, each carrying the
subspace topology, so `TauCeti.AddAmenable.of_forall_fg` and `TauCeti.Amenable.of_forall_fg` give
amenability of arbitrary commutative topological additive and multiplicative groups
(`TauCeti.AddAmenable.of_addCommGroup`, `TauCeti.Amenable.of_commGroup`).

## Main results

* `TauCeti.AddAmenable.of_fg`, `TauCeti.Amenable.of_fg`: finitely generated commutative topological
  additive and multiplicative groups are amenable.
* `TauCeti.AddAmenable.of_addCommGroup`, `TauCeti.Amenable.of_commGroup`: all commutative
  topological additive and multiplicative groups are amenable.

## References

* A. Garrido, *An introduction to amenable groups*, Proposition 2.3.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Proposition G.2.2 and
  Example G.5.4.
-/

public section

namespace TauCeti

/-- Every finitely generated commutative topological additive group is amenable: it is a surjective
homomorphic image of a finite discrete power `Fin n → ℤ`. -/
theorem AddAmenable.of_fg {A : Type*} [AddCommGroup A] [AddGroup.FG A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] : AddAmenable A := by
  obtain ⟨n, φ, hφ⟩ := AddCommGroup.fg_iff_exists_fin_addMonoidHom_surjective.1 ‹_›
  exact .of_denseRange ⟨φ, continuous_of_discreteTopology⟩ hφ.denseRange

/-- Every finitely generated commutative topological group is amenable: it is a surjective
homomorphic image of a finite discrete power `Fin n → Multiplicative ℤ`. -/
theorem Amenable.of_fg {G : Type*} [CommGroup G] [Group.FG G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Amenable G := by
  obtain ⟨n, φ, hφ⟩ := CommGroup.fg_iff_exists_fin_monoidHom_surjective.1 ‹_›
  exact .of_denseRange ⟨φ, continuous_of_discreteTopology⟩ hφ.denseRange

/-- Every commutative topological additive group is amenable, whatever its additive group
topology. -/
instance (priority := 100) AddAmenable.of_addCommGroup {A : Type*} [AddCommGroup A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] : AddAmenable A :=
  .of_forall_fg fun K hK => by
    have := (AddGroup.fg_iff_addSubgroup_fg K).2 hK
    exact .of_fg

/-- Every commutative topological group is amenable, whatever its group topology. -/
instance (priority := 100) Amenable.of_commGroup {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Amenable G :=
  .of_forall_fg fun K hK => by
    have := (Group.fg_iff_subgroup_fg K).2 hK
    exact .of_fg

end TauCeti
