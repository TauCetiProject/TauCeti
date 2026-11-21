/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.PushoutI
public import TauCeti.GroupTheory.PushoutI.Map

/-!
# Amalgamating a free product along its first factor

For a homomorphism `φ : H →* G` of monoids and a monoid `Q`, the amalgamated product
`G ∗_H (H ∗ Q)` of `G` and the free product `H ∗ Q`, along `φ` and the inclusion of the factor `H`,
is the free product `G ∗ Q`: the amalgamation identifies the factor `H` of `H ∗ Q` with its image
`φ(H)` in `G`, and the free factor `Q` is left untouched. Both monoids have the same universal
property, that of a pair of homomorphisms on `G` and on `Q`.

For a further homomorphism `ψ : Q →* G`, the amalgamated product `G ∗_H (H ∗ Q)` maps to the double
`G ∗_H G` of `G` along `φ` by the identity on `G` and by `φ` together with `ψ` on `H ∗ Q`. For
groups, this homomorphism is injective when `φ` together with `ψ` is an injective homomorphism
`H ∗ Q →* G`.

## Main definitions

* `Monoid.PushoutI.CoprodAmalgamFactor G H Q`: the factors `G` and `H ∗ Q`, as a family indexed
  by `Bool`.
* `Monoid.PushoutI.freeFactorMap φ`: the two homomorphisms from `H` that are amalgamated: `φ`
  into `G`, and the inclusion `inl` of the first factor into `H ∗ Q`.
* `Monoid.PushoutI.freeFactorEquiv φ`: the isomorphism `G ∗_H (H ∗ Q) ≃* G ∗ Q`.
* `Monoid.PushoutI.freeFactorToDouble φ ψ`: the homomorphism `G ∗_H (H ∗ Q) →* G ∗_H G`.

## Main results

* `Monoid.PushoutI.freeFactorToDouble_injective`: `freeFactorToDouble φ ψ` is injective when
  `Monoid.Coprod.lift φ ψ` is.

## References

* J.-P. Serre, *Trees*, Chapter I, §1.1 (amalgamated products and their universal property).
-/

public section

universe u

namespace Monoid.PushoutI

open Monoid.Coprod

variable {G H Q : Type u}

variable (G H Q) in
/-- The factors `G` and `H ∗ Q` of the amalgamated product `G ∗_H (H ∗ Q)`, as a family indexed by
`Bool`: `G` at `false` and `H ∗ Q` at `true`. -/
abbrev CoprodAmalgamFactor [MulOneClass H] [MulOneClass Q] (b : Bool) : Type u :=
  Bool.rec (motive := fun _ => Type u) G (H ∗ Q) b

/-- The monoid structures of `G` and `H ∗ Q` on the factors of `G ∗_H (H ∗ Q)`. -/
instance instMonoidCoprodAmalgamFactor [Monoid G] [Monoid H] [Monoid Q] (b : Bool) :
    Monoid (CoprodAmalgamFactor G H Q b) :=
  Bool.rec (motive := fun b => Monoid (CoprodAmalgamFactor G H Q b)) (inferInstanceAs (Monoid G))
    (inferInstanceAs (Monoid (H ∗ Q))) b

-- The monoid structure is the one of `instMonoidCoprodAmalgamFactor`, so that amalgamated products
-- of the family built from the monoid and from the group structure agree; the other operations are
-- those of `G` and `H ∗ Q`, so that at `false` and `true` this is their group structure.
/-- The group structures of `G` and `H ∗ Q` on the factors of `G ∗_H (H ∗ Q)`, for groups. -/
instance instGroupCoprodAmalgamFactor [Group G] [Group H] [Group Q] (b : Bool) :
    Group (CoprodAmalgamFactor G H Q b) where
  toMonoid := instMonoidCoprodAmalgamFactor b
  inv := Bool.rec (motive := fun b => CoprodAmalgamFactor G H Q b → CoprodAmalgamFactor G H Q b)
    (Inv.inv : G → G) (Inv.inv : H ∗ Q → H ∗ Q) b
  div := Bool.rec (motive := fun b => CoprodAmalgamFactor G H Q b → CoprodAmalgamFactor G H Q b →
      CoprodAmalgamFactor G H Q b)
    (HDiv.hDiv : G → G → G) (HDiv.hDiv : H ∗ Q → H ∗ Q → H ∗ Q) b
  zpow := Bool.rec (motive := fun b => ℤ → CoprodAmalgamFactor G H Q b →
      CoprodAmalgamFactor G H Q b)
    (fun n (x : G) => x ^ n) (fun n (x : H ∗ Q) => x ^ n) b
  div_eq_mul_inv := by cases b <;> exact DivInvMonoid.div_eq_mul_inv
  zpow_zero' := by cases b <;> exact DivInvMonoid.zpow_zero'
  zpow_succ' := by cases b <;> exact DivInvMonoid.zpow_succ'
  zpow_neg' := by cases b <;> exact DivInvMonoid.zpow_neg'
  inv_mul_cancel := by cases b <;> exact inv_mul_cancel

section Monoid

variable [Monoid G] [Monoid H] [Monoid Q]

/-- The two homomorphisms from `H` amalgamated in `G ∗_H (H ∗ Q)`: `φ` into `G` and the inclusion
`inl` of the first factor into `H ∗ Q`. -/
def freeFactorMap (φ : H →* G) : ∀ b, H →* CoprodAmalgamFactor G H Q b
  | false => φ
  | true => inl

@[simp]
theorem freeFactorMap_false (φ : H →* G) : freeFactorMap (Q := Q) φ false = φ :=
  (rfl)

@[simp]
theorem freeFactorMap_true (φ : H →* G) : freeFactorMap (Q := Q) φ true = inl :=
  (rfl)

-- The domain of `of true` is written `H ∗ Q`, the reduced form of `CoprodAmalgamFactor G H Q true`
-- under which `simp` looks the terms it rewrites up; the discrimination tree would otherwise store
-- it unreduced, and the lemma would never fire.
/-- The amalgamation identifies `h ∈ H` in the factor `H ∗ Q` with `φ h ∈ G`. -/
@[simp]
theorem of_true_inl_freeFactorMap (φ : H →* G) (h : H) :
    @DFunLike.coe (H ∗ Q →* PushoutI (freeFactorMap (Q := Q) φ)) (H ∗ Q) _ _
      (of (φ := freeFactorMap φ) true) (inl h) = of (φ := freeFactorMap φ) false (φ h) :=
  (of_apply_eq_base (freeFactorMap φ) true h).trans
    (of_apply_eq_base (freeFactorMap φ) false h).symm

/-- The homomorphisms from the factors of `G ∗_H (H ∗ Q)` to `G ∗ Q`: the inclusion of `G`, and
`φ` on `H` together with the inclusion of `Q`. -/
private def toCoprod (φ : H →* G) : ∀ b, CoprodAmalgamFactor G H Q b →* G ∗ Q
  | false => inl
  | true => Coprod.map φ (.id Q)

/-- **Amalgamating a free product along its first factor.** For `φ : H →* G`, the amalgamated
product `G ∗_H (H ∗ Q)` is the free product `G ∗ Q`: `g ∈ G` and `q ∈ Q` are sent to themselves,
and `h ∈ H` to `φ h`. -/
def freeFactorEquiv (φ : H →* G) : PushoutI (freeFactorMap (Q := Q) φ) ≃* G ∗ Q :=
  MonoidHom.toMulEquiv
    (lift (toCoprod φ) (inl.comp φ) fun b => by cases b <;> ext <;> simp [toCoprod])
    (Coprod.lift (of (φ := freeFactorMap φ) false) ((of (φ := freeFactorMap φ) true).comp inr))
    (hom_ext_nonempty fun b => by cases b <;> ext <;> simp [toCoprod])
    (by ext <;> simp [toCoprod])

variable (φ : H →* G)

-- The factor element is `no_index`: the discrimination tree would store the type
-- `CoprodAmalgamFactor G H Q false` of `of false` unreduced, and the lemma would never fire.
@[simp]
theorem freeFactorEquiv_of_false (g : G) :
    freeFactorEquiv (Q := Q) φ (no_index (of false g)) = inl g := by
  simp [freeFactorEquiv, toCoprod]

@[simp]
theorem freeFactorEquiv_of_true (x : H ∗ Q) :
    freeFactorEquiv φ (no_index (of (φ := freeFactorMap φ) true x)) = Coprod.map φ (.id Q) x := by
  simp [freeFactorEquiv, toCoprod]

@[simp]
theorem freeFactorEquiv_base (h : H) :
    freeFactorEquiv (Q := Q) φ (base (freeFactorMap φ) h) = inl (φ h) := by
  simp [freeFactorEquiv]

@[simp]
theorem freeFactorEquiv_symm_inl (g : G) :
    (freeFactorEquiv (Q := Q) φ).symm (inl g) = of false g := by
  simp [freeFactorEquiv]

@[simp]
theorem freeFactorEquiv_symm_inr (q : Q) :
    (freeFactorEquiv φ).symm (inr q) = of (φ := freeFactorMap φ) true (inr q) := by
  simp [freeFactorEquiv]

/-- The homomorphisms from the factors `G` and `H ∗ Q` of `G ∗_H (H ∗ Q)` to `G`: the identity, and
`φ` together with `ψ`. -/
private def toDoubleFactor (ψ : Q →* G) : ∀ b, CoprodAmalgamFactor G H Q b →* G
  | false => .id G
  | true => Coprod.lift φ ψ

/-- The homomorphism `G ∗_H (H ∗ Q) →* G ∗_H G` to the double of `G` along `φ` that is the identity
from `G` to the first copy of `G`, and `φ` together with `ψ : Q →* G` from `H ∗ Q` to the second
copy. -/
def freeFactorToDouble (ψ : Q →* G) :
    PushoutI (freeFactorMap (Q := Q) φ) →* PushoutI fun _ : Bool => φ :=
  map (toDoubleFactor φ ψ) (.id H) fun b => by cases b <;> ext <;> simp [toDoubleFactor]

variable (ψ : Q →* G)

-- The factor elements are `no_index`, as in `freeFactorEquiv_of_false`.
@[simp]
theorem freeFactorToDouble_of_false (g : G) :
    freeFactorToDouble φ ψ (no_index (of false g)) = of false g :=
  map_of ..

@[simp]
theorem freeFactorToDouble_of_true (x : H ∗ Q) :
    freeFactorToDouble φ ψ (no_index (of (φ := freeFactorMap φ) true x)) =
      of true (Coprod.lift φ ψ x) :=
  map_of ..

@[simp]
theorem freeFactorToDouble_base (h : H) :
    freeFactorToDouble φ ψ (base (freeFactorMap φ) h) = base _ h :=
  map_base ..

end Monoid

/-- The homomorphism `G ∗_H (H ∗ Q) →* G ∗_H G` is injective when `φ` together with `ψ` is an
injective homomorphism `H ∗ Q →* G`. -/
theorem freeFactorToDouble_injective [Group G] [Group H] [Group Q] {φ : H →* G} {ψ : Q →* G}
    (hφψ : Function.Injective (Coprod.lift φ ψ)) : Function.Injective (freeFactorToDouble φ ψ) := by
  have hφ : Function.Injective φ := fun a b hab => inl_injective (hφψ (by simpa using hab))
  refine map_injective _ (fun _ => hφ) Function.injective_id fun b g hg => ?_
  cases b
  · simpa [toDoubleFactor] using hg
  · -- An element of `H ∗ Q` mapped into `φ(H)` lies in the first factor.
    obtain ⟨h, hh⟩ := hg
    exact ⟨h, hφψ (by simpa [toDoubleFactor] using hh)⟩

end Monoid.PushoutI
