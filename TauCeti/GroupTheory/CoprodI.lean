/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.CoprodI
public import Mathlib.GroupTheory.Coprod.Basic

/-!
# Isomorphisms of free products of monoids

A family of isomorphisms `M i ≃* N i` induces an isomorphism `CoprodI M ≃* CoprodI N` of the free
products, acting on each factor by the given isomorphism.  This is the indexed counterpart of
Mathlib's `MulEquiv.coprodCongr` for the free product of two monoids.  It is used to rewrite a
free product of fundamental groups one factor at a time, for instance to recognise the
fundamental group of a wedge of circles as a free group.

The free product of a family of two monoids indexed by `Bool` is the binary free product
`Monoid.Coprod` of its two members, by the isomorphism matching the canonical inclusions.

The free product of an empty family is trivial, and so is a free product of trivial monoids. The
free product of a family indexed by a type with a unique element is that single monoid.

## Main declarations

* `MulEquiv.coprodICongr`: the isomorphism of free products induced by a family of isomorphisms.
* `Monoid.CoprodI.boolEquivCoprod`: `CoprodI M ≃* Coprod (M false) (M true)` for a family `M`
  indexed by `Bool`.
* `Monoid.CoprodI.instUniqueOfIsEmpty`: the free product of an empty family is trivial.
* `Monoid.CoprodI.instSubsingleton`: the free product of a family of trivial monoids is trivial.
* `MulEquiv.coprodIUnique`: the free product of a family indexed by a type with a unique element
  is isomorphic to the monoid at the single index.
-/

public section

open Monoid

namespace Monoid.CoprodI

variable {ι : Type*} (M : ι → Type*) [∀ i, Monoid (M i)]

/-- The free product of an empty family of monoids is trivial. -/
instance instUniqueOfIsEmpty [IsEmpty ι] : Unique (CoprodI M) where
  default := 1
  uniq x := DFunLike.congr_fun (ext_hom (.id _) 1 isEmptyElim) x

/-- The free product of a family of trivial monoids is trivial. -/
instance instSubsingleton [∀ i, Subsingleton (M i)] : Subsingleton (CoprodI M) :=
  subsingleton_of_forall_eq 1 fun x ↦ by
    simpa using DFunLike.congr_fun (ext_hom (.id (CoprodI M)) 1 fun _ ↦ Subsingleton.elim _ _) x

end Monoid.CoprodI

namespace MulEquiv

variable {ι : Type*} {M N : ι → Type*} [∀ i, Monoid (M i)] [∀ i, Monoid (N i)]

/-- A family of isomorphisms of monoids `M i ≃* N i` induces an isomorphism of their free
products, acting on the `i`-th factor by the `i`-th isomorphism. -/
def coprodICongr (e : ∀ i, M i ≃* N i) : CoprodI M ≃* CoprodI N :=
  MonoidHom.toMulEquiv (CoprodI.lift fun i => CoprodI.of.comp (e i).toMonoidHom)
    (CoprodI.lift fun i => CoprodI.of.comp (e i).symm.toMonoidHom)
    (by ext; simp) (by ext; simp)

@[simp]
theorem coprodICongr_apply_of (e : ∀ i, M i ≃* N i) {i : ι} (m : M i) :
    coprodICongr e (CoprodI.of m) = CoprodI.of (e i m) :=
  CoprodI.lift_of _ _

@[simp]
theorem coprodICongr_symm (e : ∀ i, M i ≃* N i) :
    (coprodICongr e).symm = coprodICongr fun i => (e i).symm :=
  (rfl)

variable (M) [Unique ι]

/-- The free product of a family of monoids indexed by a type with a unique element is
isomorphic to the monoid at the single index. -/
def coprodIUnique : CoprodI M ≃* M default :=
  MonoidHom.toMulEquiv (CoprodI.lift <| Pi.mulSingle default (.id _)) CoprodI.of
    (CoprodI.ext_hom _ _ fun i => by obtain rfl := Unique.eq_default i; ext; simp)
    (by ext; simp)

@[simp]
theorem coprodIUnique_apply_of (m : M default) : coprodIUnique M (CoprodI.of m) = m := by
  simp [coprodIUnique]

@[simp]
theorem coprodIUnique_symm_apply (m : M default) : (coprodIUnique M).symm m = CoprodI.of m :=
  (rfl)

end MulEquiv

namespace Monoid.CoprodI

variable (M : Bool → Type*) [∀ i, Monoid (M i)]

/-- The free product of a family of monoids indexed by `Bool` is the free product of its two
members: the inclusion of `M false` corresponds to `Monoid.Coprod.inl` and that of `M true` to
`Monoid.Coprod.inr`. -/
def boolEquivCoprod : CoprodI M ≃* Coprod (M false) (M true) :=
  MonoidHom.toMulEquiv
    (lift fun
      | false => Coprod.inl
      | true => Coprod.inr)
    (Coprod.lift (of (i := false)) (of (i := true)))
    (by ext i x; cases i <;> simp) (by ext <;> simp)

variable {M}

@[simp]
theorem boolEquivCoprod_of_false (x : M false) : boolEquivCoprod M (of x) = Coprod.inl x :=
  lift_of _ _

@[simp]
theorem boolEquivCoprod_of_true (x : M true) : boolEquivCoprod M (of x) = Coprod.inr x :=
  lift_of _ _

@[simp]
theorem boolEquivCoprod_symm_inl (x : M false) : (boolEquivCoprod M).symm (Coprod.inl x) = of x :=
  Coprod.lift_apply_inl (of (i := false)) (of (i := true)) x

@[simp]
theorem boolEquivCoprod_symm_inr (x : M true) : (boolEquivCoprod M).symm (Coprod.inr x) = of x :=
  Coprod.lift_apply_inr (of (i := false)) (of (i := true)) x

end Monoid.CoprodI
