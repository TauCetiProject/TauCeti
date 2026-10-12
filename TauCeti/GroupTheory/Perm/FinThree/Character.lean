/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FiniteAbelian.CharacterOrthogonality
public import TauCeti.GroupTheory.Perm.AlternatingCharacter
public import TauCeti.GroupTheory.Perm.FinThree.Basic

/-!
# The linear characters of the symmetric group on three points

`Equiv.Perm (Fin 3)` is the symmetric group `S₃`, the smallest non-commutative group, and this
file records what that does to its linear characters, the homomorphisms `S₃ →* Mˣ` into the units
of a commutative monoid `M`. The commutator subgroup of `S₃` is the alternating subgroup `A₃` and
the abelianization has order two and exponent two
(`TauCeti.commutator_perm_fin_three_eq_alternatingGroup` and its companions in
`TauCeti.GroupTheory.Perm.FinThree.Basic`), so every linear character kills the
three-cycle, and once `M` has a primitive square root of unity there are exactly two linear
characters: the trivial character and a single nontrivial one.

The consequence the file exists for is that **column orthogonality fails on `S₃`**. For a finite
commutative group `G`, `CommGroup.sum_inv_mul_monoidHom_apply_eq_ite` says that the tagged sum
`∑ χ, (χ σ)⁻¹ * χ g` over the characters is `#G` when `g = σ` and `0` otherwise; it is what turns
the indicator of one Frobenius fibre into a sum over characters in the cyclotomic case of the
Chebotarev density theorem. On `S₃`, at the tag `σ = 1` and `g` the three-cycle, the sum is `2`
and not `0`: the linear characters of a non-commutative group do not separate its elements, and
the orthogonality formula cannot be applied to a Galois group that is not abelian. The general form
of the failure is `TauCeti.exists_sum_inv_mul_monoidHom_apply_ne_ite`; this file exhibits it on the
smallest example, with the offending value computed.

## Main results

* `MonoidHom.apply_finRotate_three`: every linear character of `S₃` kills the three-cycle.
* `TauCeti.card_monoidHom_perm_fin_three`: **`S₃` has exactly two linear characters** valued in a
  commutative monoid with a primitive square root of unity.
* `TauCeti.sum_monoidHom_apply_finRotate_three`: the character sum of `S₃` at the three-cycle is
  `2`.
* `TauCeti.sum_inv_mul_monoidHom_apply_finRotate_three_ne_ite`: **column orthogonality fails on
  `S₃`** at the tag `1` and the three-cycle.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Chapter 2, where the
  linear characters of `G` are identified with the characters of `G / G'`.
-/

public section

open Equiv

namespace TauCeti

section CommMonoid

variable {M : Type*} [CommMonoid M]

/-- **Every linear character of `S₃` kills the three-cycle.** The three-cycle is even, and every
homomorphism from a permutation group to a commutative monoid is trivial on the alternating
subgroup (`MonoidHom.alternatingGroup_le_ker`). -/
@[simp]
theorem _root_.MonoidHom.apply_finRotate_three (χ : Perm (Fin 3) →* M) : χ (finRotate 3) = 1 :=
  MonoidHom.mem_ker.mp <| χ.alternatingGroup_le_ker <| Perm.mem_alternatingGroup.mpr (by decide)

variable (M) [HasEnoughRootsOfUnity M 2]

/-- **`S₃` has exactly two linear characters** valued in a commutative monoid with a primitive
square root of unity: the trivial character and a single nontrivial one. Every linear character
factors through
the abelianization, which has order two by `TauCeti.card_abelianization_perm_fin_three`, and a
finite commutative group with enough roots of unity in `M` has as many characters as elements. -/
@[simp]
theorem card_monoidHom_perm_fin_three : Nat.card (Perm (Fin 3) →* Mˣ) = 2 := by
  have : HasEnoughRootsOfUnity M (Monoid.exponent (Abelianization (Perm (Fin 3)))) := by
    rw [exponent_abelianization_perm_fin_three]
    infer_instance
  rw [card_monoidHom_eq_card_abelianization, card_abelianization_perm_fin_three]

end CommMonoid

section Domain

variable (M : Type*) [CommRing M] [IsDomain M] [HasEnoughRootsOfUnity M 2]

/-- **The character sum of `S₃` at the three-cycle is `2`**: the three-cycle lies in the commutator
subgroup `A₃`, so by `TauCeti.sum_monoidHom_apply_eq_card_of_mem_commutator` the sum counts the
linear characters, of which there are two. -/
theorem sum_monoidHom_apply_finRotate_three :
    ∑ χ : Perm (Fin 3) →* Mˣ, (χ (finRotate 3) : M) = 2 := by
  have hrot : finRotate 3 ∈ commutator (Perm (Fin 3)) := by
    rw [commutator_perm_fin_three_eq_alternatingGroup]
    exact Perm.mem_alternatingGroup.mpr (by decide)
  rw [sum_monoidHom_apply_eq_card_of_mem_commutator hrot, card_monoidHom_perm_fin_three,
    Nat.cast_ofNat]

/-- **Column orthogonality fails on `S₃`.** At the tag `σ = 1` and the three-cycle `g`, the sum
`∑ χ, (χ σ)⁻¹ * χ g` over the linear characters of `S₃` is `2`, whereas the identity
`CommGroup.sum_inv_mul_monoidHom_apply_eq_ite` for finite commutative groups would return `0`,
since `g ≠ σ`. The linear characters of `S₃` do not separate its elements, so the orthogonality
formula does not extend to a Galois group that is not abelian. -/
theorem sum_inv_mul_monoidHom_apply_finRotate_three_ne_ite :
    ∑ χ : Perm (Fin 3) →* Mˣ, (((χ 1)⁻¹ : Mˣ) : M) * ((χ (finRotate 3) : Mˣ) : M) ≠
      if finRotate 3 = (1 : Perm (Fin 3)) then (Nat.card (Perm (Fin 3)) : M) else 0 := by
  -- a domain with a primitive square root of unity does not have characteristic two
  have h2 : (2 : M) ≠ 0 := by
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot M 2
    exact_mod_cast hζ.neZero'.out
  rw [ite_eq_right (by decide)]
  simpa only [map_one, inv_one, Units.val_one, one_mul, sum_monoidHom_apply_finRotate_three]
    using h2

end Domain

end TauCeti
