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
functor is `G` itself, so its automorphism group is the unit group `Gˣ`, which for a group `G` is
`G` again.

The proof is the usual one. A natural endomorphism `η` is determined by its value `s` at the
identity of the left regular `G`-set `Action.leftRegular G`, because for every `G`-set `A` and
every point `x` of `A` the orbit map `a ↦ a • x` is a map of `G`-sets out of the left regular one,
and naturality against it forces `η` to act as `x ↦ s • x`.

The last statements below transport this along an equivalence: a functor `C ⥤ Type u` that factors
as an equivalence onto `G`-sets followed by the forgetful functor has endomorphism monoid `G` and
automorphism group `Gˣ`. This is the form the classification of covering spaces consumes, with `C`
the covering spaces of a based space and `G` its fundamental group.

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
* `TauCeti.unitsAutForgetActionMulEquiv`: the automorphism form, over a monoid: the automorphism
  group of the forgetful functor is `Gˣ`.
* `TauCeti.autForgetActionMulEquiv`: its specialisation to a group `G`, where the automorphism
  group is `G` itself.
* `TauCeti.endCompForgetActionMulEquiv`, `TauCeti.unitsAutCompForgetActionMulEquiv` and
  `TauCeti.autCompForgetActionMulEquiv`: all three forms transported along an equivalence
  `C ⥤ Action (Type u) G`.

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
    -- Unfold the unexposed constructor once to establish its public computation rule.
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
    -- Unfold the unexposed constructor once to establish its public computation rule.
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

/-- Acting by the elements of `G` exhausts the natural endomorphisms of the forgetful functor, and
does so without repetition: evaluation at the identity of the left regular `G`-set inverts
`TauCeti.toEndForgetAction`, by `TauCeti.end_forgetAction_app_apply`. -/
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
    exact (end_forgetAction_app_apply η h A x).trans
      (toEndForgetAction_app_apply g A x).symm

variable (G)

/-- **Tannaka duality for `G`-sets**, automorphism form: the automorphism group of the forgetful
functor from `G`-sets to types is the group of units of the monoid `G`.

An automorphism is an invertible endomorphism, so this is the endomorphism form
`TauCeti.endForgetActionMulEquiv` on units. -/
def unitsAutForgetActionMulEquiv : Gˣ ≃* Aut (Action.forget (Type u) G) :=
  (Units.mapEquiv (endForgetActionMulEquiv G)).trans (Aut.unitsEndEquivAut _)

variable {G}

@[simp]
theorem unitsAutForgetActionMulEquiv_hom_app_apply (g : Gˣ) (A : Action (Type u) G)
    (x : ToType A) :
    (unitsAutForgetActionMulEquiv G g).hom.app A x = (g : G) • x := by
  -- `Aut.unitsEndEquivAut` keeps the underlying endomorphism as the `hom` projection.
  change (endForgetActionMulEquiv G (g : G)).app A x = _
  rw [endForgetActionMulEquiv_apply, toEndForgetAction_app_apply]

@[simp]
theorem unitsAutForgetActionMulEquiv_inv_app_apply (g : Gˣ) (A : Action (Type u) G)
    (x : ToType A) :
    (unitsAutForgetActionMulEquiv G g).inv.app A x = ((g⁻¹ : Gˣ) : G) • x := by
  -- `Aut.unitsEndEquivAut` keeps the endomorphism of the inverse unit as the `inv` projection.
  change (endForgetActionMulEquiv G ((g⁻¹ : Gˣ) : G)).app A x = _
  rw [endForgetActionMulEquiv_apply, toEndForgetAction_app_apply]

/-- The inverse of the automorphism form of Tannaka duality is characterized by evaluating the
forward natural transformation at the identity of the left regular `G`-set. -/
@[simp]
theorem unitsAutForgetActionMulEquiv_symm_apply_eq (η : Aut (Action.forget (Type u) G)) (g : Gˣ) :
    (unitsAutForgetActionMulEquiv G).symm η = g ↔
      η.hom.app (Action.leftRegular G) (1 : G) = (g : G) := by
  rw [MulEquiv.symm_apply_eq]
  constructor
  · intro h
    rw [h]
    -- The left regular scalar action is definitionally multiplication.
    change (g : G) * 1 = (g : G)
    exact mul_one (g : G)
  · intro h
    refine Aut.ext (NatTrans.ext (funext fun A => ?_))
    ext x
    exact (end_forgetAction_app_apply η.hom h A x).trans
      (unitsAutForgetActionMulEquiv_hom_app_apply g A x).symm

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
    -- Unfold the unexposed transport once; its value is then governed by the public base rule.
    change (endForgetActionMulEquiv G g).app (e.obj p) x = g • x
    rw [endForgetActionMulEquiv_apply, toEndForgetAction_app_apply]

variable (G)

/-- The automorphism form of Tannaka duality, transported along an equivalence: if a functor `e`
from a category `C` to `G`-sets is an equivalence, then `Gˣ` is the automorphism group of the
composite `C ⥤ Type u`. -/
def unitsAutCompForgetActionMulEquiv {C : Type*} [Category C] (e : C ⥤ Action (Type u) G)
    [e.IsEquivalence] : Gˣ ≃* Aut (e ⋙ Action.forget (Type u) G) :=
  (Units.mapEquiv (endCompForgetActionMulEquiv G e)).trans (Aut.unitsEndEquivAut _)

variable {G}

/-- The value of a transported natural automorphism on a point of a fibre; not a `simp` lemma, for
the reason given at `TauCeti.endCompForgetActionMulEquiv_app_apply`. -/
theorem unitsAutCompForgetActionMulEquiv_hom_app_apply {C : Type*} [Category C]
    (e : C ⥤ Action (Type u) G) [e.IsEquivalence] (g : Gˣ) (p : C) (x : ToType (e.obj p)) :
    (unitsAutCompForgetActionMulEquiv G e g).hom.app p x = (g : G) • x :=
  by
    -- `Aut.unitsEndEquivAut` keeps the underlying endomorphism as the `hom` projection.
    change (endCompForgetActionMulEquiv G e (g : G)).app p x = _
    exact endCompForgetActionMulEquiv_app_apply e (g : G) p x

/-- The inverse of a transported natural automorphism acts by the inverse unit on every fibre; not
a `simp` lemma, for the reason given at `TauCeti.endCompForgetActionMulEquiv_app_apply`. -/
theorem unitsAutCompForgetActionMulEquiv_inv_app_apply {C : Type*} [Category C]
    (e : C ⥤ Action (Type u) G) [e.IsEquivalence] (g : Gˣ) (p : C) (x : ToType (e.obj p)) :
    (unitsAutCompForgetActionMulEquiv G e g).inv.app p x = ((g⁻¹ : Gˣ) : G) • x :=
  by
    -- `Aut.unitsEndEquivAut` keeps the endomorphism of the inverse unit as the `inv` projection.
    change (endCompForgetActionMulEquiv G e ((g⁻¹ : Gˣ) : G)).app p x = _
    exact endCompForgetActionMulEquiv_app_apply e ((g⁻¹ : Gˣ) : G) p x

end Monoid

section Group

variable (G : Type u) [Group G]

/-- **Tannaka duality for `G`-sets**, group form: a group `G` is the automorphism group of the
forgetful functor from `G`-sets to types. This is the monoid form
`TauCeti.unitsAutForgetActionMulEquiv` read through the identification `toUnits` of a group with
its group of units. -/
def autForgetActionMulEquiv : G ≃* Aut (Action.forget (Type u) G) :=
  toUnits.trans (unitsAutForgetActionMulEquiv G)

variable {G}

/-- The group form of Tannaka duality is the monoid form at the unit attached to `g`. -/
theorem autForgetActionMulEquiv_apply (g : G) :
    autForgetActionMulEquiv G g = unitsAutForgetActionMulEquiv G (toUnits g) :=
  (rfl)

@[simp]
theorem autForgetActionMulEquiv_hom_app_apply (g : G) (A : Action (Type u) G) (x : ToType A) :
    (autForgetActionMulEquiv G g).hom.app A x = g • x := by
  rw [autForgetActionMulEquiv_apply, unitsAutForgetActionMulEquiv_hom_app_apply,
    val_toUnits_apply]

/-- The inverse of the automorphism associated to `g` acts by `g⁻¹`. -/
@[simp]
theorem autForgetActionMulEquiv_inv_app_apply (g : G) (A : Action (Type u) G) (x : ToType A) :
    (autForgetActionMulEquiv G g).inv.app A x = g⁻¹ • x := by
  rw [autForgetActionMulEquiv_apply, unitsAutForgetActionMulEquiv_inv_app_apply, ← map_inv,
    val_toUnits_apply]

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
    -- The left regular scalar action is definitionally multiplication.
    change g * 1 = g
    exact mul_one g
  · intro h
    refine Aut.ext (NatTrans.ext (funext fun A => ?_))
    ext x
    exact (end_forgetAction_app_apply η.hom h A x).trans
      (autForgetActionMulEquiv_hom_app_apply g A x).symm

variable (G)

/-- Tannaka duality transported along an equivalence: if a functor `e` from a category `C` to
`G`-sets is an equivalence, then the group `G` is the automorphism group of the composite
`C ⥤ Type u`. -/
def autCompForgetActionMulEquiv {C : Type*} [Category C] (e : C ⥤ Action (Type u) G)
    [e.IsEquivalence] : G ≃* Aut (e ⋙ Action.forget (Type u) G) :=
  toUnits.trans (unitsAutCompForgetActionMulEquiv G e)

variable {G}

/-- The transported group form of Tannaka duality is the transported monoid form at the unit
attached to `g`. -/
theorem autCompForgetActionMulEquiv_apply {C : Type*} [Category C] (e : C ⥤ Action (Type u) G)
    [e.IsEquivalence] (g : G) :
    autCompForgetActionMulEquiv G e g = unitsAutCompForgetActionMulEquiv G e (toUnits g) :=
  (rfl)

/-- The value of a transported natural automorphism on a point of a fibre; not a `simp` lemma, for
the reason given at `TauCeti.endCompForgetActionMulEquiv_app_apply`. -/
theorem autCompForgetActionMulEquiv_hom_app_apply {C : Type*} [Category C]
    (e : C ⥤ Action (Type u) G) [e.IsEquivalence] (g : G) (p : C) (x : ToType (e.obj p)) :
    (autCompForgetActionMulEquiv G e g).hom.app p x = g • x := by
  rw [autCompForgetActionMulEquiv_apply, unitsAutCompForgetActionMulEquiv_hom_app_apply,
    val_toUnits_apply]

/-- The inverse of a transported natural automorphism acts by `g⁻¹` on every fibre; not a `simp`
lemma, for the reason given at `TauCeti.endCompForgetActionMulEquiv_app_apply`. -/
theorem autCompForgetActionMulEquiv_inv_app_apply {C : Type*} [Category C]
    (e : C ⥤ Action (Type u) G) [e.IsEquivalence] (g : G) (p : C) (x : ToType (e.obj p)) :
    (autCompForgetActionMulEquiv G e g).inv.app p x = g⁻¹ • x := by
  rw [autCompForgetActionMulEquiv_apply, unitsAutCompForgetActionMulEquiv_inv_app_apply,
    ← map_inv, val_toUnits_apply]

end Group

end TauCeti
