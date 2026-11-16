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
import TauCeti.GroupTheory.Finiteness

/-!
# Amenability of commutative groups

Every commutative topological group — additive (`AddCommGroup`) or multiplicative (`CommGroup`) —
is amenable, with no hypothesis on its rank, its torsion or its topology.

A finitely generated commutative group `G` is a surjective homomorphic image of
`Fin n → Multiplicative ℤ` (`Group.fg_iff_exists_fin_monoidHom_surjective`), and additively a
finitely generated commutative additive group `A` is a surjective homomorphic image of `Fin n → ℤ`
(`AddGroup.fg_iff_exists_fin_addMonoidHom_surjective`). Equipping `Multiplicative ℤ` or `ℤ` with
the discrete topology makes the finite product amenable (`TauCeti.Amenable.multiplicative_int`,
`TauCeti.AddAmenable.int`, `TauCeti.Amenable.pi`, `TauCeti.AddAmenable.pi`), so the finitely
generated group is amenable for every group topology by `TauCeti.Amenable.of_surjective` /
`TauCeti.AddAmenable.of_surjective`.

An arbitrary commutative group is exhausted by its finitely generated subgroups, each of which is
amenable by the finitely generated case, so `TauCeti.Amenable.of_forall_fg` proves
`TauCeti.Amenable.of_commGroup` (and `@[to_additive]` gives `TauCeti.AddAmenable.of_addCommGroup`).

## Main results

* `TauCeti.Amenable.of_commGroup_of_fg`, `TauCeti.AddAmenable.of_addCommGroup_of_fg`: finitely
  generated commutative topological groups are amenable.
* `TauCeti.Amenable.of_commGroup`, `TauCeti.AddAmenable.of_addCommGroup`: every commutative
  topological group is amenable.

## References

* A. Garrido, *An introduction to amenable groups*, Proposition 2.3.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Proposition G.2.2 and
  Example G.5.4.
-/

public section

namespace TauCeti

/-- Every finitely generated commutative additive topological group is amenable: it is a surjective
homomorphic image of a finite product of copies of `ℤ`. -/
theorem AddAmenable.of_addCommGroup_of_fg {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [AddGroup.FG A] : AddAmenable A := by
  obtain ⟨n, φ, hφ⟩ := AddGroup.fg_iff_exists_fin_addMonoidHom_surjective.1 ‹_›
  let : TopologicalSpace ℤ := ⊥
  have : DiscreteTopology ℤ := ⟨rfl⟩
  exact .of_surjective φ hφ

/-- Every finitely generated commutative topological group is amenable: it is a surjective
homomorphic image of a finite product of copies of `Multiplicative ℤ`. -/
theorem Amenable.of_commGroup_of_fg {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group.FG G] : Amenable G := by
  obtain ⟨n, φ, hφ⟩ := Group.fg_iff_exists_fin_monoidHom_surjective.1 ‹_›
  let : TopologicalSpace (Multiplicative ℤ) := ⊥
  have : DiscreteTopology (Multiplicative ℤ) := ⟨rfl⟩
  exact .of_surjective φ hφ

attribute [to_additive existing] Amenable.of_commGroup_of_fg

/-- Every commutative topological group is amenable, whatever its group topology: its finitely
generated subgroups are amenable and exhaust the group. -/
@[to_additive
/-- Every commutative additive topological group is amenable, whatever its additive group topology:
its finitely generated subgroups are amenable and exhaust the group. -/]
instance (priority := 100) Amenable.of_commGroup {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Amenable G :=
  .of_forall_fg fun K hK => by
    have : Group.FG K := (Group.fg_iff_subgroup_fg K).2 hK
    exact .of_commGroup_of_fg

end TauCeti
