/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Concrete
public import TauCeti.CategoryTheory.Sites.Descent.IsomTorsor

/-!
# Isomorphisms of a banded pseudofunctor as `A(U)`-sets

Let `b` be an `A`-banding of a pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` and `x y` objects of
the fibre over `U`. The action `AbelianBanding.act` of `A(U)` on the isomorphisms `x ≅ y` is a
multiplicative action (`AbelianBanding.isomMulAction`), so `x ≅ y` is an object of the category
of `A(U)`-sets (`AbelianBanding.fibreAction`), and postcomposition with `q : y ≅ z` is an
isomorphism of `A(U)`-sets (`AbelianBanding.postcomposeActionIso`), functorial in `q`. The
`A(U)`-set `x ≅ y` may be empty. These are the fibre actions on which the functor from
band-preserving transformations to `A(U)`-sets is built (Olsson, Definition 31.1, Remark 31.2,
Lemma 31.3 and Remark 31.5).

## Main declarations

In the namespace `CategoryTheory.Pseudofunctor.AbelianBanding`:

* `isomMulAction`: the action of `Multiplicative A(U)` on `x ≅ y`.
* `fibreAction`: `x ≅ y` as an object of `Action (Type _) (Multiplicative A(U))`, with
  `fibreAction_ρ_apply` and `isEmpty_fibreAction_V`.
* `postcomposeActionIso`: postcomposition with `q : y ≅ z`, with `postcomposeActionIso_hom_hom`,
  `postcomposeActionIso_inv_hom`, `postcomposeActionIso_refl`, `postcomposeActionIso_trans`.

## References

* [Martin Olsson, *Stacks* (lecture notes, notes by A. Geraschenko et al.)](https://stacky.net/files/written/Stacks/Stacks.pdf),
  Definition 31.1, Remark 31.2, Lemma 31.3 and Remark 31.5
-/

public section

universe w v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.AbelianBanding

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {J : GrothendieckTopology C} {A : Sheaf J AddCommGrpCat.{w}} (b : F.AbelianBanding J A)
  {U : C}

variable (x y : F.obj (.mk (op U)))

/-- The action of `A(U)` on the isomorphisms `x ≅ y`: `a • p = act p a`, the composite of `p` with
the band automorphism of `a` at `y`. -/
@[reducible]
def isomMulAction : MulAction (Multiplicative (A.obj.obj (op U))) (x ≅ y) where
  smul a p := b.act p a
  one_smul := b.act_one
  mul_smul a c p := b.act_mul p a c

/-- **The `A(U)`-set of isomorphisms `x ≅ y`**, an object of the category of `A(U)`-sets. -/
abbrev fibreAction : Action (Type v') (Multiplicative (A.obj.obj (op U))) :=
  letI := b.isomMulAction x y
  Action.ofMulAction _ (x ≅ y)

theorem fibreAction_V : (b.fibreAction x y).V = (x ≅ y) :=
  (rfl)

variable {x y}

/-- A coefficient `a` acts on `p : x ≅ y` by `act p a`, that is, `p` followed by the band
automorphism of `a` at `y`. -/
@[simp]
theorem fibreAction_ρ_apply (a : Multiplicative (A.obj.obj (op U)))
    (p : (b.fibreAction x y).V) :
    (b.fibreAction x y).ρ a p = b.act (show x ≅ y from p) a :=
  (rfl)

/-- If there is no isomorphism `x ≅ y`, the `A(U)`-set `fibreAction` is empty. -/
theorem isEmpty_fibreAction_V (h : IsEmpty (x ≅ y)) : IsEmpty (b.fibreAction x y).V :=
  h

variable {z : F.obj (.mk (op U))}

/-- **Postcomposition** with `q : y ≅ z` as an isomorphism of `A(U)`-sets
`fibreAction x y ≅ fibreAction x z`. -/
def postcomposeActionIso (q : y ≅ z) : b.fibreAction x y ≅ b.fibreAction x z :=
  Action.mkIso
    (Equiv.toIso
      { toFun p := (show x ≅ y from p) ≪≫ q
        invFun p := (show x ≅ z from p) ≪≫ q.symm
        left_inv p := by
          change ((show x ≅ y from p) ≪≫ q) ≪≫ q.symm = p
          rw [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
        right_inv p := by
          change ((show x ≅ z from p) ≪≫ q.symm) ≪≫ q = p
          rw [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl] }) fun a ↦ by
    ext p
    exact b.act_trans (show x ≅ y from p) q a

/-- The forward map of `postcomposeActionIso q` sends `p` to `p ≪≫ q`. -/
theorem postcomposeActionIso_hom_hom (q : y ≅ z) (p : (b.fibreAction x y).V) :
    (b.postcomposeActionIso q).hom.hom p = (show x ≅ y from p) ≪≫ q :=
  (rfl)

/-- The inverse map of `postcomposeActionIso q` sends `p` to `p ≪≫ q.symm`. -/
theorem postcomposeActionIso_inv_hom (q : y ≅ z) (p : (b.fibreAction x z).V) :
    (b.postcomposeActionIso q).inv.hom p = (show x ≅ z from p) ≪≫ q.symm :=
  (rfl)

/-- Postcomposition with the identity is the identity. -/
theorem postcomposeActionIso_refl :
    b.postcomposeActionIso (Iso.refl y) = Iso.refl (b.fibreAction x y) := by
  ext p
  exact Iso.trans_refl (show x ≅ y from p)

/-- Postcomposition with `q ≪≫ r` is postcomposition with `q` followed by postcomposition with
`r`. -/
theorem postcomposeActionIso_trans {w : F.obj (.mk (op U))} (q : y ≅ z) (r : z ≅ w) :
    b.postcomposeActionIso (q ≪≫ r) =
      b.postcomposeActionIso (x := x) q ≪≫ b.postcomposeActionIso r := by
  ext p
  exact (Iso.trans_assoc (show x ≅ y from p) q r).symm

end CategoryTheory.Pseudofunctor.AbelianBanding
