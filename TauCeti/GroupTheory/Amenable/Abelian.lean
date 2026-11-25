/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Int
import TauCeti.GroupTheory.Finiteness
import TauCeti.GroupTheory.NoncommPiCoprod

/-!
# Amenability of commutative groups

Every commutative topological group is amenable, in both additive (`AddCommGroup`) and
multiplicative (`CommGroup`) notation, with no hypothesis on rank, torsion, or topology.

First, for a finitely generated commutative group, choosing a finite generating tuple
`S : Fin n → A` (`AddGroup.fg_iff_exists_fin_generating_family` /
`Group.fg_iff_exists_fin_generating_family`) yields a surjective homomorphism
`TauCeti.zmultiplesPiHom S : (Fin n → ℤ) →+ A` or
`TauCeti.zpowersPiHom S : (Fin n → Multiplicative ℤ) →* G`
(`TauCeti.zmultiplesPiHom_surjective` / `TauCeti.zpowersPiHom_surjective`). Equipping the integers
with the discrete topology makes the finite power `Fin n → ℤ` a discrete amenable group by
amenability of `ℤ` and finite-product closure, so surjectivity passes amenability to `A` (or `G`)
for every compatible group topology.

Next, an arbitrary commutative topological group (in particular any discrete commutative group, with
no rank or torsion restriction) has amenable finitely generated subgroups by the first step, so the
directed-union criterion `TauCeti.AddAmenable.of_forall_fg` / `TauCeti.Amenable.of_forall_fg` proves
amenability in full generality. Specializing to the discrete topology `⊥` via the discrete Følner
characterization also yields counting-measure Følner sets for every abstract commutative group
(`TauCeti.HasAddFoelnerSets.of_addCommGroup` and `TauCeti.HasFoelnerSets.of_commGroup`).

## Main results

* `TauCeti.AddAmenable.of_addCommGroup_of_fg` and `TauCeti.Amenable.of_commGroup_of_fg`: finitely
  generated commutative topological groups are amenable.
* `TauCeti.AddAmenable.of_addCommGroup` and `TauCeti.Amenable.of_commGroup`: every commutative
  topological group (in particular every discrete commutative group) is amenable.
* `TauCeti.HasAddFoelnerSets.of_addCommGroup` and `TauCeti.HasFoelnerSets.of_commGroup`: every
  commutative group has counting-measure Følner sets.

## References

* A. Garrido, *An introduction to amenable groups*, Proposition 2.3 and Example 3.5.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Proposition G.2.2 and
  Example G.5.4.
-/

public section

namespace TauCeti

/-- A finitely generated additive commutative topological group is amenable, as a homomorphic image
of a finite discrete power `Fin n → ℤ`. -/
theorem AddAmenable.of_addCommGroup_of_fg {A : Type*} [AddCommGroup A] [AddGroup.FG A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] : AddAmenable A := by
  obtain ⟨n, S, hS⟩ := AddGroup.fg_iff_exists_fin_generating_family.1 ‹_›
  let : TopologicalSpace ℤ := ⊥
  let : DiscreteTopology ℤ := discreteTopology_bot ℤ
  exact .of_surjective (zmultiplesPiHom S fun _ _ => AddCommute.all _ _)
    ((zmultiplesPiHom_surjective S _).2 hS)

/-- A finitely generated commutative topological group is amenable, as a homomorphic image of a
finite discrete power `Fin n → Multiplicative ℤ`. -/
@[to_additive existing]
theorem Amenable.of_commGroup_of_fg {G : Type*} [CommGroup G] [Group.FG G]
    [TopologicalSpace G] [IsTopologicalGroup G] : Amenable G := by
  obtain ⟨n, S, hS⟩ := Group.fg_iff_exists_fin_generating_family.1 ‹_›
  let : TopologicalSpace (Multiplicative ℤ) := ⊥
  let : DiscreteTopology (Multiplicative ℤ) := discreteTopology_bot (Multiplicative ℤ)
  exact .of_surjective (zpowersPiHom S fun _ _ => Commute.all _ _)
    ((zpowersPiHom_surjective S _).2 hS)

/-- Every additive commutative topological group is amenable, with no rank, torsion, or topology
restriction, as the directed union of its finitely generated additive subgroups. -/
instance (priority := 100) AddAmenable.of_addCommGroup {A : Type*} [AddCommGroup A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] : AddAmenable A :=
  .of_forall_fg fun K hK => by
    have : AddGroup.FG K := (AddGroup.fg_iff_addSubgroup_fg K).2 hK
    exact .of_addCommGroup_of_fg

/-- Every commutative topological group is amenable, with no rank, torsion, or topology
restriction, as the directed union of its finitely generated subgroups. -/
@[to_additive existing]
instance (priority := 100) Amenable.of_commGroup {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Amenable G :=
  .of_forall_fg fun K hK => by
    have : Group.FG K := (Group.fg_iff_subgroup_fg K).2 hK
    exact .of_commGroup_of_fg

/-- Every additive commutative group has counting-measure Følner sets. -/
theorem HasAddFoelnerSets.of_addCommGroup (A : Type*) [AddCommGroup A] : HasAddFoelnerSets A := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := discreteTopology_bot A
  exact AddAmenable.hasAddFoelnerSets

/-- Every commutative group has counting-measure Følner sets. -/
@[to_additive existing]
theorem HasFoelnerSets.of_commGroup (G : Type*) [CommGroup G] : HasFoelnerSets G := by
  let : TopologicalSpace G := ⊥
  let : DiscreteTopology G := discreteTopology_bot G
  exact Amenable.hasFoelnerSets

end TauCeti
