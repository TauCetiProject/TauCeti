/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Sporadic.Janko.One
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Sporadic.Janko.One.Index
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Janko.One.Simple

/-!
# Recognition and simplicity of the presented group of `J₁`

The classification list carries the first Janko group as the group `SporadicName.J1.Group`
defined by the transcribed ATLAS presentation

```text
⟨a, b | a², b³, (ab)⁷, (ab(abab⁻¹)³)⁵, (ab(abab⁻¹)⁶abab(ab⁻¹)²)²⟩
```

(`TauCeti.Sporadic.j1Presentation`). A finite list of relators does not by itself make a group
finite. Two checked certificates bound this one: the element `u = abab⁻¹` has order `19`
(`TauCeti.SporadicName.orderOf_wordValue_group_J1`), and the cyclic subgroup `⟨u⟩` has index at
most `9240` (`TauCeti.SporadicName.index_zpowers_wordValue_ababInv_group_J1_le`). By Lagrange's
theorem the presented group is finite, with at most `9240 * 19 = 175560` elements.

This is the order of the ATLAS permutation model `TauCeti.Sporadic.J1` (`TauCeti.Sporadic.card_J1`),
onto which the presentation maps. Comparing the two orders upgrades the canonical presentation
homomorphism `TauCeti.Sporadic.J1.presentationHom` to an explicit multiplicative equivalence with
that model, and proves that the presented group has exactly `175560` elements. Since the model is
simple (`TauCeti.Sporadic.isSimpleGroup_J1`), so is the presented group.

## Main results

* `TauCeti.SporadicName.finite_group_J1`: the presented group of `J₁` is finite.
* `TauCeti.Sporadic.J1.presentationEquiv`: recognition by the canonical presentation map.
* `TauCeti.SporadicName.natCard_group_J1`: the presented group has `175560` elements.
* `TauCeti.SporadicName.isSimpleGroup_group_J1`: the presented group is simple.

## References

* R. A. Wilson, R. A. Parker, and J. N. Bray, *ATLAS of Finite Group Representations*,
  version 3, `J₁`, section "Presentation",
  <https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/J1/>.
-/

public section

namespace TauCeti.SporadicName

open CosetEnumeration

/-- The order of the presented group of `J₁` is `19` times the index of `⟨abab⁻¹⟩`. -/
private theorem natCard_group_J1_eq_index_mul :
    Nat.card J1.Group = (Subgroup.zpowers (wordValue
      (PresentedGroup.of (rels := J1.presentation.relatorSet)) [0, 2, 0, 3])).index * 19 := by
  rw [← Subgroup.card_mul_index (Subgroup.zpowers _), Nat.card_zpowers,
    orderOf_wordValue_group_J1, mul_comm]

/-- **The presented group of `J₁` is finite.** -/
instance finite_group_J1 : Finite J1.Group :=
  Nat.finite_of_card_ne_zero <| natCard_group_J1_eq_index_mul ▸
    mul_ne_zero finiteIndex_zpowers_wordValue_ababInv_group_J1.index_ne_zero (by decide)

/-- The presented group of `J₁` has at most `175560 = 9240 * 19` elements. -/
private theorem natCard_group_J1_le : Nat.card J1.Group ≤ 175560 :=
  natCard_group_J1_eq_index_mul ▸
    Nat.mul_le_mul_right 19 index_zpowers_wordValue_ababInv_group_J1_le

end TauCeti.SporadicName

namespace TauCeti.Sporadic.J1

/-- The transcribed presentation of `J₁` is isomorphic to the ATLAS permutation model, via the
homomorphism sending its generators to `presentationImage`. -/
noncomputable def presentationEquiv : SporadicName.J1.Group ≃* Sporadic.J1 := by
  let f := (MulEquiv.subgroupCongr range_presentationHom).toMonoidHom.comp
    presentationHom.rangeRestrict
  have hf : Function.Surjective f :=
    (MulEquiv.subgroupCongr range_presentationHom).surjective.comp
      presentationHom.rangeRestrict_surjective
  exact MulEquiv.ofBijective f (hf.bijective_of_nat_card_le
    (by simpa only [card_J1] using SporadicName.natCard_group_J1_le))

/-- The underlying permutation of the recognition equivalence is the canonical presentation
homomorphism. -/
@[simp]
theorem coe_presentationEquiv (g : SporadicName.J1.Group) :
    (presentationEquiv g : Equiv.Perm (Fin 266)) = presentationHom g := (rfl)

end TauCeti.Sporadic.J1

namespace TauCeti.SporadicName

/-- The group defined by the transcribed presentation of `J₁` has exactly `175560` elements. -/
theorem natCard_group_J1 : Nat.card J1.Group = 175560 :=
  (Nat.card_congr Sporadic.J1.presentationEquiv.toEquiv).trans Sporadic.card_J1

/-- **The presented group of `J₁` is simple.** -/
instance isSimpleGroup_group_J1 : IsSimpleGroup J1.Group :=
  Sporadic.J1.presentationEquiv.isSimpleGroup

end TauCeti.SporadicName
