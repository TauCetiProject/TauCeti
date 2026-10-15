/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.ArtinMap
import TauCeti.GroupTheory.Transfer.Commutator

/-!
# The principal ideal theorem for a class formation

Let `V ◁ U` be a finite normal layer of a class formation, the extension `K/F` in field notation,
and let `U'` be the intermediate subgroup with `U'/V` the commutator subgroup of `U/V`, so that the
fixed field `E` of `U'` is the maximal abelian subextension of `K/F`. Then every element of the
ground level `A^U` becomes a norm from `A^V` in `A^{U'}`
(`TauCeti.ClassFieldTheory.ClassFormation.groundInclusion_mem_normSubgroup_of_range_eq_commutator`).

Inclusion of ground levels corresponds under the Artin maps to the transfer
`Gal(K/F)^{ab} → Gal(K/E)^{ab}` (`ClassFormation.artinMap_groundInclusion`), and the transfer of a
finite group into its commutator subgroup is trivial (Furtwängler's theorem,
`MonoidHom.transfer_commutator_eq_one`). For the idele-class formation of a number field `F`, with
`E` the Hilbert class field of `F` and `K` that of `E`, this is the idelic form of the principal
ideal theorem: every ideal of `F` becomes principal in its Hilbert class field.

## Main results

* `TauCeti.ClassFieldTheory.LayerRestriction.transferHom_eq_zero_of_range_eq_commutator`: the
  transfer to the commutator subgroup vanishes on abelianized Galois groups.
* `TauCeti.ClassFieldTheory.ClassFormation.groundInclusion_mem_normSubgroup_of_range_eq_commutator`:
  the principal ideal theorem for a class formation.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIII.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §7.
-/

public section

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- **The transfer into the commutator subgroup vanishes**: if the Galois group `U'/V` of the
restricted layer is the commutator subgroup of `U/V`, the transfer
`(U/V)^{ab} → (U'/V)^{ab}` is zero. -/
theorem LayerRestriction.transferHom_eq_zero_of_range_eq_commutator {small big : NormalLayer G}
    (T : LayerRestriction small big) (hT : T.galHom.range = commutator big.Gal) :
    T.transferHom = 0 := by
  have key (H : Subgroup big.Gal) (hH : H = commutator big.Gal) [H.FiniteIndex]
      (ϕ : H →* Abelianization small.Gal) : ϕ.transfer = 1 := by
    subst hH
    exact MonoidHom.transfer_commutator_eq_one ϕ
  refine AddMonoidHom.ext fun x ↦ ?_
  obtain ⟨x, rfl⟩ := Additive.ofMul.surjective x
  obtain ⟨y, rfl⟩ : ∃ y, Abelianization.of y = x := QuotientGroup.mk_surjective x
  rw [AddMonoidHom.zero_apply, transferHom_of, key _ hT,
    MonoidHom.one_apply, ofMul_one]

/-- **The principal ideal theorem for a class formation.** Let `V ◁ U` be a layer, `K/F` in field
notation, and restrict it to the ground subgroup `U'` whose image `U'/V` is the commutator subgroup
of `U/V`, the layer `K/E` over the maximal abelian subextension `E`. Then every element of the
ground level `A^U` is, in `A^{U'}`, a norm from `A^V`. -/
theorem ClassFormation.groundInclusion_mem_normSubgroup_of_range_eq_commutator {F : Formation G}
    (cf : ClassFormation F) {small big : NormalLayer G} (T : LayerRestriction small big)
    (hT : T.galHom.range = commutator big.Gal) (a : F.level big.ground) :
    T.groundInclusion F a ∈ small.normSubgroup F := by
  rw [← cf.artinMap_eq_zero_iff, cf.artinMap_groundInclusion,
    T.transferHom_eq_zero_of_range_eq_commutator hT, AddMonoidHom.zero_apply]

end TauCeti.ClassFieldTheory
