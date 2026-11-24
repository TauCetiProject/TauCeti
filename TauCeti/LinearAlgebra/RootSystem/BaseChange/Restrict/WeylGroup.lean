/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Restrict.Hom
public import TauCeti.LinearAlgebra.RootSystem.Weyl.ReflectionPerm
import TauCeti.LinearAlgebra.RootSystem.BaseChange.Balanced.WeylGroup

/-!
# Weyl group isomorphism under scalar restriction

For a balanced root pairing `P` taking pairing values in a subfield `K`, both `P.weylGroup` and
`(P.restrictScalars' K).weylGroup` act faithfully on root indices with identical reflection
permutations. This file identifies the two Weyl groups via a canonical group isomorphism.

## Main definitions

* `RootPairing.weylGroupRestrictScalars'Equiv`: the canonical group isomorphism
  `P.weylGroup ≃* (P.restrictScalars' K).weylGroup`.

## Main results

* `RootPairing.map_weylGroup_restrictScalars'Hom`: restriction of automorphisms maps
  `P.weylGroup` onto `(P.restrictScalars' K).weylGroup`.
* `RootPairing.weylGroupToPerm_weylGroupRestrictScalars'Equiv`,
  `RootPairing.weylGroupRestrictScalars'Equiv_ofIdx`, and
  `RootPairing.coe_weylGroupRestrictScalars'Equiv`: compatibility with the permutation
  representation, simple reflections, and `Equiv.restrictScalars'Hom`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
* M. Demazure, A. Grothendieck (eds.), *Schémas en groupes III* (SGA 3), Exposé XXI, §§1, 6.
-/

public section

open Function Set

namespace RootPairing

variable {ι L M N : Type*} [Field L] [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]
  (P : RootPairing ι L M N) (K : Type*) [Field K] [Algebra K L]
  [Module K M] [Module K N] [IsScalarTower K L M] [IsScalarTower K L N]
  [P.IsBalanced] [P.IsValuedIn K]

/-- Restriction of automorphisms maps `P.weylGroup` onto `(P.restrictScalars' K).weylGroup`. -/
@[simp]
theorem map_weylGroup_restrictScalars'Hom :
    P.weylGroup.map (Equiv.restrictScalars'Hom P K) = (P.restrictScalars' K).weylGroup := by
  have h : (Equiv.restrictScalars'Hom P K ∘ Equiv.reflection P) =
      Equiv.reflection (P.restrictScalars' K) :=
    funext fun i ↦ by
      rw [Function.comp_apply, Equiv.restrictScalars'Hom_apply, Equiv.restrictScalars'_reflection]
  rw [weylGroup, MonoidHom.map_closure, ← range_comp, h, weylGroup]

/-- **The Weyl group of `P` is canonically isomorphic to that of `P.restrictScalars' K`.** -/
noncomputable def weylGroupRestrictScalars'Equiv :
    P.weylGroup ≃* (P.restrictScalars' K).weylGroup :=
  P.weylGroupEquivOfReflectionPermEq (P.restrictScalars' K)
    (P.restrictScalars'_reflectionPerm K).symm
    P.weylGroupToPerm_injective_of_isBalanced (weylGroupToPerm_injective (P.restrictScalars' K))

/-- `RootPairing.weylGroupRestrictScalars'Equiv` commutes with the root-index permutation
representations. -/
theorem weylGroupToPerm_weylGroupRestrictScalars'Equiv (w : P.weylGroup) :
    (P.restrictScalars' K).weylGroupToPerm (P.weylGroupRestrictScalars'Equiv K w) =
      P.weylGroupToPerm w :=
  weylGroupToPerm_weylGroupEquivOfReflectionPermEq _ _ _ _ _ w

/-- `RootPairing.weylGroupRestrictScalars'Equiv` sends each indexed reflection to the reflection
with the same root index. -/
@[simp]
theorem weylGroupRestrictScalars'Equiv_ofIdx (i : ι) :
    P.weylGroupRestrictScalars'Equiv K (weylGroup.ofIdx P i) =
      weylGroup.ofIdx (P.restrictScalars' K) i :=
  weylGroupEquivOfReflectionPermEq_ofIdx _ _ _ _ _ i

/-- Coercing `RootPairing.weylGroupRestrictScalars'Equiv` to `(P.restrictScalars' K).Aut` agrees
with `RootPairing.Equiv.restrictScalars'Hom`. -/
@[simp]
theorem coe_weylGroupRestrictScalars'Equiv (w : P.weylGroup) :
    (P.weylGroupRestrictScalars'Equiv K w : (P.restrictScalars' K).Aut) =
      Equiv.restrictScalars'Hom P K w := by
  apply Equiv.indexHom_injective (P.restrictScalars' K)
  ext i
  simpa [Equiv.indexEquiv_restrictScalars'] using
    congrArg (fun p : _root_.Equiv.Perm ι ↦ p i)
      (P.weylGroupToPerm_weylGroupRestrictScalars'Equiv K w)

end RootPairing
