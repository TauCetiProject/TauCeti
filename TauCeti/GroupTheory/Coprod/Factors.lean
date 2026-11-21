/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.ULift
public import TauCeti.GroupTheory.CoprodI
import TauCeti.Algebra.Group.ULift

/-!
# The free product of two monoids as a free product of a family

Mathlib builds the free product `M ∗ N` of two monoids independently of the free product
`Monoid.CoprodI` of an indexed family. The free product of two monoids, possibly in different
universes, is the free product of the family of their `ULift`s indexed by `Bool`, by the
isomorphism matching the canonical inclusions. Through it, results about free products of families
apply to free products of two monoids. The same family indexes the two factors of an amalgamated
product `Monoid.PushoutI` of two monoids.

## Main definitions

* `Monoid.Coprod.Factors M N`: the family indexed by `Bool` with `ULift M` at `false` and
  `ULift N` at `true`, with its monoid structure, and its group structure when `M` and `N` are
  groups.
* `Monoid.Coprod.equivCoprodI`: the isomorphism `M ∗ N ≃* CoprodI (Factors M N)`.
-/

public section

universe u v

namespace Monoid.Coprod

variable (M : Type u) (N : Type v)

/-- The factors of `M ∗ N`, or of an amalgamated product of `M` and `N`, as a family indexed by
`Bool`, lifted to a common universe: `false` gives `M` and `true` gives `N`. -/
abbrev Factors : Bool → Type max u v
  | false => ULift.{v} M
  | true => ULift.{u} N

variable {M N}

/-- The monoid structures of `ULift M` and `ULift N` on the factors of `M ∗ N`. -/
instance instMonoidFactors [Monoid M] [Monoid N] : ∀ b, Monoid (Factors M N b)
  | false => inferInstanceAs (Monoid (ULift M))
  | true => inferInstanceAs (Monoid (ULift N))

-- The monoid structure is the one of `instMonoidFactors`, so that free products of the family
-- built from the monoid and from the group structure agree; the other operations are those of
-- `ULift M` and `ULift N`, so that at `false` and `true` this is their group structure.
/-- The group structures of `ULift M` and `ULift N` on the factors of the free product of two
groups. -/
instance instGroupFactors [Group M] [Group N] (b : Bool) : Group (Factors M N b) where
  toMonoid := instMonoidFactors b
  inv := Bool.rec (motive := fun b => Factors M N b → Factors M N b)
    (Inv.inv : ULift M → ULift M) (Inv.inv : ULift N → ULift N) b
  div := Bool.rec (motive := fun b => Factors M N b → Factors M N b → Factors M N b)
    (HDiv.hDiv : ULift M → ULift M → ULift M) (HDiv.hDiv : ULift N → ULift N → ULift N) b
  zpow := Bool.rec (motive := fun b => ℤ → Factors M N b → Factors M N b)
    (fun n (x : ULift M) => x ^ n) (fun n (x : ULift N) => x ^ n) b
  div_eq_mul_inv := by cases b <;> exact DivInvMonoid.div_eq_mul_inv
  zpow_zero' := by cases b <;> exact DivInvMonoid.zpow_zero'
  zpow_succ' := by cases b <;> exact DivInvMonoid.zpow_succ'
  zpow_neg' := by cases b <;> exact DivInvMonoid.zpow_neg'
  inv_mul_cancel := by cases b <;> exact inv_mul_cancel

variable [Monoid M] [Monoid N]

/-- The free product of two monoids is the free product of the family `Factors M N`: the inclusion
of `M` corresponds to that of `ULift M` at `false`, and the inclusion of `N` to that of `ULift N`
at `true`. -/
def equivCoprodI : M ∗ N ≃* CoprodI (Factors M N) :=
  (MulEquiv.coprodCongr MulEquiv.ulift.symm MulEquiv.ulift.symm).trans
    (CoprodI.boolEquivCoprod (Factors M N)).symm

@[simp]
theorem equivCoprodI_inl (m : M) :
    equivCoprodI (inl m : M ∗ N) = CoprodI.of (M := Factors M N) (i := false) (ULift.up m) := by
  simp [equivCoprodI]

@[simp]
theorem equivCoprodI_inr (n : N) :
    equivCoprodI (inr n : M ∗ N) = CoprodI.of (M := Factors M N) (i := true) (ULift.up n) := by
  simp [equivCoprodI]

-- The factor element is `no_index`: the discrimination tree would store the type
-- `Factors M N false` of `CoprodI.of (i := false)` unreduced, and the lemma would never fire.
@[simp]
theorem equivCoprodI_symm_of_false (x : ULift.{v} M) :
    equivCoprodI.symm (no_index (CoprodI.of (M := Factors M N) (i := false) x)) = inl x.down := by
  simp [equivCoprodI]

@[simp]
theorem equivCoprodI_symm_of_true (x : ULift.{u} N) :
    equivCoprodI.symm (no_index (CoprodI.of (M := Factors M N) (i := true) x)) = inr x.down := by
  simp [equivCoprodI]

end Monoid.Coprod
