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

Every commutative topological group — additive or multiplicative — is amenable, with no hypothesis
on its rank, its torsion, or its topology.

We work first in the additive setting (`TauCeti.AddAmenable.of_addCommGroup`). By
`TauCeti.AddAmenable.of_discrete`, it suffices to treat the discrete topology; by
`TauCeti.AddAmenable.of_forall_fg`, it suffices to show that every finitely generated additive
subgroup `K` is additively amenable. Choosing a finite generating family `S : Fin n → K`
(`AddGroup.fg_iff_exists_fin_generating_family`), the homomorphism
`TauCeti.zmultiplesPiHom S : (Fin n → ℤ) →+ K` sending the standard basis vectors to `S` is
surjective (`TauCeti.surjective_zmultiplesPiHom_iff`). Since `Fin n → ℤ` is additively amenable as a
finite product of copies of `ℤ`, closure under continuous homomorphisms with dense range gives
additive amenability of `K`.

The multiplicative counterpart `TauCeti.Amenable.of_commGroup` follows immediately via
`TauCeti.addAmenable_additive_iff`.

## Main results

* `TauCeti.AddAmenable.of_addCommGroup`: every commutative topological additive group is additively
  amenable.
* `TauCeti.Amenable.of_commGroup`: every commutative topological group is amenable.

## References

* A. Garrido, *An introduction to amenable groups*, Proposition 2.3.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Proposition G.2.2 and
  Example G.5.4.
-/

public section

namespace TauCeti

/-- Every commutative topological additive group is additively amenable, whatever its additive group
topology. -/
instance (priority := 100) AddAmenable.of_addCommGroup {A : Type*} [AddCommGroup A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] : AddAmenable A := by
  refine .of_discrete ?_
  let : TopologicalSpace A := ⊥
  have : DiscreteTopology A := discreteTopology_bot A
  refine .of_forall_fg fun K hK => ?_
  have hKfg : AddGroup.FG K := (AddGroup.fg_iff_addSubgroup_fg K).2 hK
  obtain ⟨n, S, hS⟩ := AddGroup.fg_iff_exists_fin_generating_family.1 hKfg
  let φ := zmultiplesPiHom S fun _ _ => .all _ _
  have hsurj : Function.Surjective φ := surjective_zmultiplesPiHom_iff.2 hS
  exact .of_denseRange ⟨φ, continuous_of_discreteTopology⟩ hsurj.denseRange

/-- Every commutative topological group is amenable, whatever its group topology. -/
instance (priority := 100) Amenable.of_commGroup {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Amenable G :=
  addAmenable_additive_iff.1 inferInstance

end TauCeti
