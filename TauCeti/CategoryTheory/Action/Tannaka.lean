/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.CategoryTheory.Whiskering

/-!
# Tannaka duality for `G`-sets

A monoid `G` can be read off from the category `Action (Type u) G` of `G`-sets together with the
forgetful functor `Action.forget (Type u) G` to types: the monoid of natural endomorphisms of that
functor is `G` itself, and for a group `G` its automorphism group is `G`.

The proof is the usual one. A natural endomorphism `η` is determined by its value `s` at the
identity of the left regular `G`-set `Action.leftRegular G`, because for every `G`-set `A` and
every point `x` of `A` the orbit map `a ↦ a • x` is a map of `G`-sets out of the left regular one,
and naturality against it forces `η` to act as `x ↦ s • x`.

The last statement below transports the group form along an equivalence: a functor `C ⥤ Type u`
that factors as an equivalence onto `G`-sets followed by the forgetful functor has automorphism
group `G`. This is the form the classification of covering spaces consumes, with `C` the covering
spaces of a based space and `G` its fundamental group.

No finiteness enters, so this is not Mathlib's `CategoryTheory.PreGaloisCategory` picture: there a
fibre functor takes values in `FintypeCat` and `CategoryTheory.PreGaloisCategory.IsFundamentalGroup`
asks for a *compact* topological group, which for a discrete `G` means a finite one.

## Main declarations

* `TauCeti.toEndForgetAction`: the monoid map sending `g : G` to the natural endomorphism of the
  forgetful functor acting by `g`, with `TauCeti.toEndForgetAction_app_apply` computing it.
* `TauCeti.leftRegularHom`: the orbit map of a point of a `G`-set, as a map of `G`-sets out of the
  left regular `G`-set.
* `TauCeti.end_forgetAction_app_apply`: a natural endomorphism of the forgetful functor acts on
  every `G`-set by the element of `G` it produces at the identity of the left regular `G`-set.
* `TauCeti.endForgetActionMulEquiv`: **Tannaka duality for `G`-sets**: `G` is the monoid of
  natural endomorphisms of the forgetful functor.
* `TauCeti.toAutForgetAction` and `TauCeti.autForgetActionMulEquiv`: the group form, for `G` a
  group.
* `TauCeti.endCompForgetActionMulEquiv` and `TauCeti.autCompForgetActionMulEquiv`: both forms
  transported along an equivalence `C ⥤ Action (Type u) G`.

## References

The argument is the standard Tannaka reconstruction of a group from its permutation
representations; see for instance Lenstra, *Galois theory for schemes*, Section 3, where the same
naturality-against-orbit-maps computation identifies the automorphism group of a fibre functor.
Mathlib's `Mathlib/RepresentationTheory/Tannaka.lean` proves the *linear* analogue for finite
groups, a different statement sharing no proof with this one.
-/

public section
noncomputable section

open CategoryTheory

universe u

namespace TauCeti

section Monoid

variable (G : Type u) [Monoid G]

/-- Acting by `g : G` on every `G`-set is a natural endomorphism of the forgetful functor from
`G`-sets to types; this is the resulting monoid map `G →* End (Action.forget (Type u) G)`. -/
def toEndForgetAction : G →* End (Action.forget (Type u) G) where
  toFun g := { app A := A.ρ g, naturality _ _ f := (f.comm g).symm }
  map_one' := NatTrans.ext (funext fun A => map_one A.ρ)
  map_mul' g h := NatTrans.ext (funext fun A => map_mul A.ρ g h)

variable {G}

@[simp]
theorem toEndForgetAction_app_apply (g : G) (A : Action (Type u) G) (x : ToType A) :
    (toEndForgetAction G g).app A x = g • x :=
  by
    change A.ρ g x = g • x
    rfl

@[simp]
theorem toEndForgetAction_app_leftRegular_one (g : G) :
    (toEndForgetAction G g).app (Action.leftRegular G) (1 : G) = g :=
  mul_one g

/-- The orbit map `a ↦ a • x` of a point `x` of a `G`-set `A`, as a map of `G`-sets from the left
regular `G`-set to `A`. -/
def leftRegularHom {A : Action (Type u) G} (x : ToType A) :
    Action.leftRegular G ⟶ A where
  hom := ↾(fun a : G => a • x)
  comm g := by ext a; exact mul_smul g a x

@[simp]
theorem leftRegularHom_hom_apply {A : Action (Type u) G} (x : ToType A) (a : G) :
    (leftRegularHom x).hom a = a • x :=
  by
    change a • x = a • x
    rfl

/-- A natural endomorphism of the forgetful functor from `G`-sets to types acts on every `G`-set
as the element of `G` it produces at the identity of the left regular `G`-set: naturality against
the orbit map `TauCeti.leftRegularHom` leaves it no other choice. -/
theorem end_forgetAction_app_apply (η : End (Action.forget (Type u) G)) {s : G}
    (hs : η.app (Action.leftRegular G) (1 : G) = s) (A : Action (Type u) G) (x : ToType A) :
    η.app A x = s • x := by
  subst hs
  calc η.app A x = η.app A ((1 : G) • x) := by rw [one_smul]
    _ = _ := NatTrans.naturality_apply η (leftRegularHom x) (1 : G)

variable (G)

theorem toEndForgetAction_bijective : Function.Bijective (toEndForgetAction G) := by
  refine ⟨fun g h hgh => ?_, fun η => ⟨η.app (Action.leftRegular G) (1 : G), ?_⟩⟩
  · rw [← toEndForgetAction_app_leftRegular_one g, ← toEndForgetAction_app_leftRegular_one h, hgh]
  · refine NatTrans.ext (funext fun A => ?_)
    ext x
    exact (end_forgetAction_app_apply η rfl A x).symm

/-- **Tannaka duality for `G`-sets.** A monoid `G` is the monoid of natural endomorphisms of the
forgetful functor from `G`-sets to types. -/
def endForgetActionMulEquiv : G ≃* End (Action.forget (Type u) G) :=
  MulEquiv.ofBijective (toEndForgetAction G) (toEndForgetAction_bijective G)

variable {G}

@[simp]
theorem endForgetActionMulEquiv_apply (g : G) :
    endForgetActionMulEquiv G g = toEndForgetAction G g :=
  (rfl)

/-- The inverse Tannaka equivalence is characterized by evaluation at the identity of the left
regular `G`-set. -/
@[simp]
theorem endForgetActionMulEquiv_symm_apply_eq (η : End (Action.forget (Type u) G)) (g : G) :
    (endForgetActionMulEquiv G).symm η = g ↔
      η.app (Action.leftRegular G) (1 : G) = g := by
  rw [MulEquiv.symm_apply_eq]
  constructor
  · intro h
    rw [h, endForgetActionMulEquiv_apply, toEndForgetAction_app_leftRegular_one]
  · intro h
    rw [endForgetActionMulEquiv_apply]
    refine NatTrans.ext (funext fun A => ?_)
    ext x
    change η.app A x = A.ρ g x
    exact end_forgetAction_app_apply η h A x

variable (G)

/-- Tannaka duality transported along an equivalence: if a functor `e` from a category `C` to
`G`-sets is an equivalence, then `G` is the monoid of natural endomorphisms of the composite
functor `C ⥤ Type u`. -/
def endCompForgetActionMulEquiv {C : Type*} [Category C] (e : C ⥤ Action (Type u) G)
    [e.IsEquivalence] : G ≃* End (e ⋙ Action.forget (Type u) G) :=
  (endForgetActionMulEquiv G).trans
    ((Functor.FullyFaithful.ofFullyFaithful
      ((Functor.whiskeringLeft C (Action (Type u) G) (Type u)).obj e)).mulEquivEnd _)

variable {G}

/-- The value of a transported natural endomorphism on a point of a fibre.

This is not a `simp` lemma: `simp` rewrites the composite `(e ⋙ Action.forget (Type u) G).obj p`
appearing in the type of `x` to `(Action.forget (Type u) G).obj (e.obj p)`, so the left-hand side
here is not in `simp`-normal form. -/
theorem endCompForgetActionMulEquiv_app_apply {C : Type*} [Category C]
    (e : C ⥤ Action (Type u) G) [e.IsEquivalence] (g : G) (p : C) (x : ToType (e.obj p)) :
    (endCompForgetActionMulEquiv G e g).app p x = g • x :=
  by
    change (endForgetActionMulEquiv G g).app (e.obj p) x = g • x
    rw [endForgetActionMulEquiv_apply, toEndForgetAction_app_apply]

end Monoid

section Group

variable (G : Type u) [Group G]

/-- Acting by `g : G` on every `G`-set is a natural *automorphism* of the forgetful functor from
`G`-sets to types, with inverse the action of `g⁻¹`. -/
def toAutForgetAction : G →* Aut (Action.forget (Type u) G) where
  toFun g :=
    { hom := toEndForgetAction G g
      inv := toEndForgetAction G g⁻¹
      hom_inv_id := by
        rw [← End.mul_def, ← map_mul, inv_mul_cancel, map_one, End.one_def]
      inv_hom_id := by
        rw [← End.mul_def, ← map_mul, mul_inv_cancel, map_one, End.one_def] }
  map_one' := Aut.ext (map_one (toEndForgetAction G))
  map_mul' g h := Aut.ext (map_mul (toEndForgetAction G) g h)

variable {G}

@[simp]
theorem toAutForgetAction_hom (g : G) :
    (toAutForgetAction G g).hom = toEndForgetAction G g :=
  by
    change toEndForgetAction G g = toEndForgetAction G g
    rfl

variable (G)

/-- **Tannaka duality for `G`-sets**, group form: a group `G` is the automorphism group of the
forgetful functor from `G`-sets to types. -/
def autForgetActionMulEquiv : G ≃* Aut (Action.forget (Type u) G) :=
  MulEquiv.ofBijective (toAutForgetAction G) <| by
    refine ⟨fun g h hgh => (toEndForgetAction_bijective G).1 ?_,
      fun η => ((toEndForgetAction_bijective G).2 η.hom).imp fun g hg => Aut.ext hg⟩
    rw [← toAutForgetAction_hom g, ← toAutForgetAction_hom h, hgh]

variable {G}

@[simp]
theorem autForgetActionMulEquiv_hom_app_apply (g : G) (A : Action (Type u) G) (x : ToType A) :
    (autForgetActionMulEquiv G g).hom.app A x = g • x :=
  by
    change (toEndForgetAction G g).app A x = g • x
    exact toEndForgetAction_app_apply g A x

/-- The inverse Tannaka equivalence is characterized by evaluating the forward natural
transformation at the identity of the left regular `G`-set. -/
@[simp]
theorem autForgetActionMulEquiv_symm_apply_eq (η : Aut (Action.forget (Type u) G)) (g : G) :
    (autForgetActionMulEquiv G).symm η = g ↔
      η.hom.app (Action.leftRegular G) (1 : G) = g := by
  rw [MulEquiv.symm_apply_eq]
  constructor
  · intro h
    rw [h]
    change g • (1 : G) = g
    exact mul_one g
  · intro h
    refine Aut.ext (NatTrans.ext (funext fun A => ?_))
    ext x
    change η.hom.app A x = A.ρ g x
    exact end_forgetAction_app_apply η.hom h A x

/-- The inverse of the automorphism associated to `g` acts by `g⁻¹`. -/
@[simp]
theorem autForgetActionMulEquiv_inv_app_apply (g : G) (A : Action (Type u) G) (x : ToType A) :
    (autForgetActionMulEquiv G g).inv.app A x = g⁻¹ • x := by
  change ((autForgetActionMulEquiv G g)⁻¹).hom.app A x = _
  rw [← map_inv]
  exact autForgetActionMulEquiv_hom_app_apply g⁻¹ A x

variable (G)

/-- Tannaka duality transported along an equivalence: if a functor `e` from a category `C` to
`G`-sets is an equivalence, then `G` is the automorphism group of the composite `C ⥤ Type u`. -/
def autCompForgetActionMulEquiv {C : Type*} [Category C] (e : C ⥤ Action (Type u) G)
    [e.IsEquivalence] : G ≃* Aut (e ⋙ Action.forget (Type u) G) :=
  (autForgetActionMulEquiv G).trans
    ((Functor.FullyFaithful.ofFullyFaithful
      ((Functor.whiskeringLeft C (Action (Type u) G) (Type u)).obj e)).autMulEquivOfFullyFaithful _)

variable {G}

/-- The value of a transported natural automorphism on a point of a fibre; not a `simp` lemma, for
the reason given at `TauCeti.endCompForgetActionMulEquiv_app_apply`. -/
theorem autCompForgetActionMulEquiv_hom_app_apply {C : Type*} [Category C]
    (e : C ⥤ Action (Type u) G) [e.IsEquivalence] (g : G) (p : C) (x : ToType (e.obj p)) :
    (autCompForgetActionMulEquiv G e g).hom.app p x = g • x :=
  by
    change (autForgetActionMulEquiv G g).hom.app (e.obj p) x = g • x
    exact autForgetActionMulEquiv_hom_app_apply g (e.obj p) x

/-- The inverse of a transported natural automorphism acts by `g⁻¹` on every fibre. -/
@[simp]
theorem autCompForgetActionMulEquiv_inv_app_apply {C : Type*} [Category C]
    (e : C ⥤ Action (Type u) G) [e.IsEquivalence] (g : G) (p : C) (x : ToType (e.obj p)) :
    (autCompForgetActionMulEquiv G e g).inv.app p x = g⁻¹ • x := by
  change ((autCompForgetActionMulEquiv G e g)⁻¹).hom.app p x = _
  rw [← map_inv]
  exact autCompForgetActionMulEquiv_hom_app_apply e g⁻¹ p x

end Group

end TauCeti
