/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Concrete
public import TauCeti.CategoryTheory.Sites.Descent.IsomTorsor.Basic

/-!
# Isomorphisms of a banded pseudofunctor as `A(U)`-sets

Let `b` be an `A`-banding of a pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` and `x y` objects of
the fibre over `U`. The action `AbelianBanding.act` of `A(U)` on the isomorphisms `x ≅ y` is a
multiplicative action (`AbelianBanding.isomMulAction`), so `x ≅ y` is an object of the category
of `A(U)`-sets (`AbelianBanding.fiberAction`), and postcomposition with `q : y ≅ z` is an
isomorphism of `A(U)`-sets (`AbelianBanding.postcomposeActionIso`), functorial in `q`; so is
precomposition with the inverse of `e : x ≅ w` (`AbelianBanding.precomposeActionIso`). The
`A(U)`-set `x ≅ y` may be empty. These fibre actions are the input for a functor from
band-preserving transformations to `A(U)`-sets (Olsson, Definition 31.1, Remark 31.2, Lemma 31.3
and Remark 31.5).

## Main declarations

In the namespace `CategoryTheory.Pseudofunctor.AbelianBanding`:

* `fiberAction`: `x ≅ y` as an object of `Action (Type _) (Multiplicative A(U))`, with
  `fiberAction_ρ_apply` and `isEmpty_fiberAction_V`.
* `postcomposeActionIso`: postcomposition with `q : y ≅ z`, with `postcomposeActionIso_hom_hom`,
  `postcomposeActionIso_inv_hom`, `postcomposeActionIso_refl`, `postcomposeActionIso_trans`,
  `postcomposeActionIso_symm`.
* `precomposeActionIso`: precomposition with the inverse of `e : x ≅ w`, with
  `precomposeActionIso_hom_hom`, `precomposeActionIso_inv_hom`, `precomposeActionIso_refl`,
  `precomposeActionIso_trans`.

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

/-- **The `A(U)`-set of isomorphisms `x ≅ y`**, an object of the category of `A(U)`-sets. Its
carrier is definitionally `x ≅ y` (see `fiberAction_V`), so an isomorphism `p : x ≅ y` can be used
as an element of it, possibly after a `change` or an explicit type ascription. -/
abbrev fiberAction : Action (Type v') (Multiplicative (A.obj.obj (op U))) :=
  letI := b.isomMulAction x y
  Action.ofMulAction _ (x ≅ y)

theorem fiberAction_V : (b.fiberAction x y).V = (x ≅ y) :=
  (rfl)

variable {x y}

/-- A coefficient `a` acts on `p : x ≅ y` by `act p a`, that is, `p` followed by the band
automorphism of `a` at `y`. The element `p` is taken in the carrier `(b.fiberAction x y).V`, the
form produced by `ext`; for `p : x ≅ y`, simp instead rewrites the action to `a • p`, which
`isomMulAction_smul` identifies with `act p a`. -/
@[simp]
theorem fiberAction_ρ_apply (a : Multiplicative (A.obj.obj (op U))) (p : (b.fiberAction x y).V) :
    (b.fiberAction x y).ρ a p = b.act p a :=
  b.isomMulAction_smul a p

/-- If there is no isomorphism `x ≅ y`, the `A(U)`-set `fiberAction` is empty. -/
theorem isEmpty_fiberAction_V (h : IsEmpty (x ≅ y)) : IsEmpty (b.fiberAction x y).V :=
  h

variable {z : F.obj (.mk (op U))}

/-- **Postcomposition** with `q : y ≅ z` as an isomorphism of `A(U)`-sets
`fiberAction x y ≅ fiberAction x z`: the bijection `Iso.isoCongrRight q`, which commutes with the
action by `AbelianBanding.act_trans`. -/
def postcomposeActionIso (q : y ≅ z) : b.fiberAction x y ≅ b.fiberAction x z :=
  Action.mkIso (Equiv.toIso (Iso.isoCongrRight (X := x) q)) fun a ↦ by
    ext (p : x ≅ y)
    -- The carrier of `fiberAction` is `x ≅ y` only after unfolding `Action.ofMulAction`, which
    -- simp does not do, so the Mathlib simp lemmas for `Equiv.toIso` and `Iso.isoCongr` do not
    -- fire. `change` states the goal on isomorphisms, by unfolding `isoCongrRight q p` to
    -- `(Iso.refl x).symm ≪≫ (p ≪≫ q)`, and simp closes it with `act_trans`.
    change (Iso.refl x).symm ≪≫ (b.act p a ≪≫ q) = b.act ((Iso.refl x).symm ≪≫ (p ≪≫ q)) a
    simp

/-- The forward map of `postcomposeActionIso q` sends `p` to `p ≪≫ q`. -/
@[simp]
theorem postcomposeActionIso_hom_hom (q : y ≅ z) (p : x ≅ y) :
    (b.postcomposeActionIso q).hom.hom p = p ≪≫ q := by
  -- The forward map unfolds to `Iso.isoCongrRight q`; see the comment in `postcomposeActionIso`.
  change (Iso.refl x).symm ≪≫ (p ≪≫ q) = p ≪≫ q
  simp

/-- The inverse map of `postcomposeActionIso q` sends `p` to `p ≪≫ q.symm`. -/
@[simp]
theorem postcomposeActionIso_inv_hom (q : y ≅ z) (p : x ≅ z) :
    (b.postcomposeActionIso q).inv.hom p = p ≪≫ q.symm := by
  -- The inverse map unfolds to `(Iso.isoCongrRight q).symm`; see the comment in
  -- `postcomposeActionIso`.
  change Iso.refl x ≪≫ (p ≪≫ q.symm) = p ≪≫ q.symm
  simp

/-- Postcomposition with the identity is the identity. -/
@[simp]
theorem postcomposeActionIso_refl :
    b.postcomposeActionIso (Iso.refl y) = Iso.refl (b.fiberAction x y) := by
  ext p
  -- `p` lies in the carrier `(b.fiberAction x y).V`, which simp does not identify with `x ≅ y`,
  -- so the lemmas about `p` are instantiated at `p` explicitly.
  simp [b.postcomposeActionIso_hom_hom _ p, Iso.trans_refl p]

/-- Postcomposition with `q ≪≫ r` is postcomposition with `q` followed by postcomposition with
`r`. -/
@[simp]
theorem postcomposeActionIso_trans {w : F.obj (.mk (op U))} (q : y ≅ z) (r : z ≅ w) :
    b.postcomposeActionIso (q ≪≫ r) =
      b.postcomposeActionIso (x := x) q ≪≫ b.postcomposeActionIso r := by
  ext p
  -- As in `postcomposeActionIso_refl`, the lemma about the carrier element `p` is instantiated
  -- explicitly; what remains is associativity of composition.
  simp only [TypeCat.Fun.toFun_apply, Iso.trans_hom, Action.comp_hom, comp_apply,
    b.postcomposeActionIso_hom_hom _ p, postcomposeActionIso_hom_hom]
  exact (Iso.trans_assoc p q r).symm

/-- Postcomposition with `q.symm` is the inverse of postcomposition with `q`. -/
theorem postcomposeActionIso_symm (q : y ≅ z) :
    b.postcomposeActionIso (x := x) q.symm = (b.postcomposeActionIso q).symm := by
  ext p
  exact (b.postcomposeActionIso_hom_hom _ p).trans (b.postcomposeActionIso_inv_hom _ p).symm

variable {w : F.obj (.mk (op U))}

/-- **Precomposition** with the inverse of `e : x ≅ w` as an isomorphism of `A(U)`-sets
`fiberAction x y ≅ fiberAction w y`: the bijection `Iso.isoCongrLeft e`, which commutes with the
action by `AbelianBanding.trans_act`. -/
def precomposeActionIso (e : x ≅ w) : b.fiberAction x y ≅ b.fiberAction w y :=
  Action.mkIso (Equiv.toIso (Iso.isoCongrLeft (Y := y) e)) fun a ↦ by
    ext (p : x ≅ y)
    -- As in `postcomposeActionIso`, `change` states the goal on isomorphisms, by unfolding
    -- `isoCongrLeft e p` to `e.symm ≪≫ (p ≪≫ Iso.refl y)`.
    change e.symm ≪≫ (b.act p a ≪≫ Iso.refl y) = b.act (e.symm ≪≫ (p ≪≫ Iso.refl y)) a
    simp

/-- The forward map of `precomposeActionIso e` sends `p` to `e.symm ≪≫ p`. -/
@[simp]
theorem precomposeActionIso_hom_hom (e : x ≅ w) (p : x ≅ y) :
    (b.precomposeActionIso e).hom.hom p = e.symm ≪≫ p := by
  -- The forward map unfolds to `Iso.isoCongrLeft e`; see the comment in `postcomposeActionIso`.
  change e.symm ≪≫ (p ≪≫ Iso.refl y) = e.symm ≪≫ p
  simp

/-- The inverse map of `precomposeActionIso e` sends `p` to `e ≪≫ p`. -/
@[simp]
theorem precomposeActionIso_inv_hom (e : x ≅ w) (p : w ≅ y) :
    (b.precomposeActionIso e).inv.hom p = e ≪≫ p := by
  -- The inverse map unfolds to `(Iso.isoCongrLeft e).symm`; see the comment in
  -- `postcomposeActionIso`.
  change e ≪≫ (p ≪≫ (Iso.refl y).symm) = e ≪≫ p
  simp

/-- Precomposition with the identity is the identity. -/
@[simp]
theorem precomposeActionIso_refl :
    b.precomposeActionIso (y := y) (Iso.refl x) = Iso.refl (b.fiberAction x y) := by
  ext p
  -- As in `postcomposeActionIso_refl`, the lemma about the carrier element `p` is instantiated
  -- explicitly.
  simp [b.precomposeActionIso_hom_hom _ p, Iso.refl_trans p]

/-- Precomposition with the inverse of `e ≪≫ f` is precomposition with the inverse of `e`
followed by precomposition with the inverse of `f`. -/
@[simp]
theorem precomposeActionIso_trans {v : F.obj (.mk (op U))} (e : x ≅ w) (f : w ≅ v) :
    b.precomposeActionIso (y := y) (e ≪≫ f) =
      b.precomposeActionIso e ≪≫ b.precomposeActionIso f := by
  ext p
  simp only [TypeCat.Fun.toFun_apply, Iso.trans_hom, Action.comp_hom, comp_apply,
    b.precomposeActionIso_hom_hom _ p, precomposeActionIso_hom_hom, Iso.trans_symm]
  exact Iso.trans_assoc f.symm e.symm p

end CategoryTheory.Pseudofunctor.AbelianBanding
