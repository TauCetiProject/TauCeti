/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
public import Mathlib.CategoryTheory.Center.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import TauCeti.CategoryTheory.Endomorphism

/-!
# Intrinsic central sections of a fibred category

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a pseudofunctor and `U` an object of `C`. The group
`ZF(U)` of **intrinsic central sections** over `U` (`IntrinsicBandSections F U`) consists of the
families `z = (z(V, f))`, indexed by the arrows `f : V ⟶ U`, of units `z(V, f)` of the categorical
centre `CatCenter (F V)` (invertible natural endomorphisms of the identity of the fibre over `V`),
that are compatible with pullback: for every `g : W ⟶ V` and every object `x` over `V`,
`F(g)(z(V, f)_x) = z(W, g ≫ f)_{F(g) x}`. These are pullback-compatible families of central
automorphisms of the fibres, defined without choosing objects; when `F` is a gerbe they give the
sections over `U` of the centre of its band (Stacks, Lemma 8.11.8 (06NY), the varying-`U` step).

`ZF(U)` is a subgroup of the product of the unit groups, with pointwise operations, and it is
commutative because each categorical centre is. Restriction along `f : V ⟶ U` reindexes a
section by composition with `f`; it is a group homomorphism `ZF(U) →* ZF(V)`, the identity for
`f = 𝟙` and compatible with composition.

## Main definitions

* `CategoryTheory.Pseudofunctor.IntrinsicBandSections F U`: the group `ZF(U)`.
* `CategoryTheory.Pseudofunctor.IntrinsicBandSections.ofCompatible`: the section with given
  compatible components.
* `CategoryTheory.Pseudofunctor.IntrinsicBandSections.restrict`: restriction `ZF(U) →* ZF(V)`
  along `f : V ⟶ U`.

## Main results

* `IntrinsicBandSections.map_app`: a section commutes with every pullback functor on every
  object.
* `IntrinsicBandSections.ext`: sections with the same component automorphisms are equal.
* `IntrinsicBandSections.mul_comm` and the `CommGroup` instance: `ZF(U)` is commutative.
* `IntrinsicBandSections.subsingleton_of_subsingleton_end`: when every object of every fibre has
  only the identity endomorphism (for instance thin fibres), the group of central sections is
  trivial.
* `IntrinsicBandSections.restrict_id` and `IntrinsicBandSections.restrict_comp`: restriction along
  the identity is the identity, and restriction is compatible with composition.

## References

* [The Stacks Project, Lemma 8.11.8 (06NY)](https://stacks.math.columbia.edu/tag/06NY)
-/

public section

universe v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor

variable {C : Type u} [Category.{v} C] (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})

/-- A family of units `z(V, f)` of the categorical centres of the fibres, indexed by the arrows
`f : V ⟶ U`, is **compatible with pullback** when `F(g)(z(V, f)_x) = z(W, g ≫ f)_{F(g) x}` for
every `g : W ⟶ V` and every object `x` over `V`. -/
def IsPullbackCompatible {U : C} (z : ∀ (V : C) (_ : V ⟶ U), (CatCenter (F.obj (.mk (op V))))ˣ) :
    Prop :=
  ∀ ⦃V W : C⦄ (f : V ⟶ U) (g : W ⟶ V) (x : F.obj (.mk (op V))),
    (F.map g.op.toLoc).toFunctor.map ((z V f).val.app x) =
      (z W (g ≫ f)).val.app ((F.map g.op.toLoc).toFunctor.obj x)

/-- The **intrinsic central sections** of `F` over `U`: the families of units `z(V, f)` of the
categorical centres `CatCenter (F V)`, for `f : V ⟶ U`, compatible with pullback
(`CategoryTheory.Pseudofunctor.IsPullbackCompatible`). -/
def IntrinsicBandSections (U : C) :
    Subgroup (∀ (V : C) (_ : V ⟶ U), (CatCenter (F.obj (.mk (op V))))ˣ) where
  carrier := {z | F.IsPullbackCompatible z}
  one_mem' := by
    intro V W f g x
    simp only [Pi.one_apply, Units.val_one, CatCenter.app_one, Functor.map_id]
  mul_mem' := by
    intro a b ha hb V W f g x
    simp only [Pi.mul_apply, Units.val_mul, CatCenter.mul_app, Functor.map_comp, ha f g x,
      hb f g x]
  inv_mem' := by
    intro a ha V W f g x
    simp only [Pi.inv_apply, NatTrans.inv_val_app, Functor.map_inv, ha f g x]

variable {F}

/-- Unfolding of `CategoryTheory.Pseudofunctor.IsPullbackCompatible`. -/
theorem isPullbackCompatible_iff {U : C}
    (z : ∀ (V : C) (_ : V ⟶ U), (CatCenter (F.obj (.mk (op V))))ˣ) :
    F.IsPullbackCompatible z ↔ ∀ ⦃V W : C⦄ (f : V ⟶ U) (g : W ⟶ V) (x : F.obj (.mk (op V))),
      (F.map g.op.toLoc).toFunctor.map ((z V f).val.app x) =
        (z W (g ≫ f)).val.app ((F.map g.op.toLoc).toFunctor.obj x) :=
  Iff.rfl

namespace IntrinsicBandSections

variable {U : C}

theorem mem_iff (z : ∀ (V : C) (_ : V ⟶ U), (CatCenter (F.obj (.mk (op V))))ˣ) :
    z ∈ IntrinsicBandSections F U ↔ F.IsPullbackCompatible z :=
  Iff.rfl

/-- **Compatibility with pullback.** The component of a section at `g ≫ f` is the pullback along
`g` of its component at `f`. -/
theorem map_app (s : IntrinsicBandSections F U) {V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (x : F.obj (.mk (op V))) :
    (F.map g.op.toLoc).toFunctor.map ((s.val V f).val.app x) =
      (s.val W (g ≫ f)).val.app ((F.map g.op.toLoc).toFunctor.obj x) :=
  s.property f g x

/-- The section with components `z(V, f)`, given their compatibility with pullback. -/
def ofCompatible (z : ∀ (V : C) (_ : V ⟶ U), (CatCenter (F.obj (.mk (op V))))ˣ)
    (hz : F.IsPullbackCompatible z) : IntrinsicBandSections F U :=
  ⟨z, hz⟩

@[simp]
theorem val_ofCompatible (z : ∀ (V : C) (_ : V ⟶ U), (CatCenter (F.obj (.mk (op V))))ˣ)
    (hz : F.IsPullbackCompatible z) (V : C) (f : V ⟶ U) :
    (ofCompatible z hz).val V f = z V f :=
  (rfl)

@[simp]
theorem val_one (V : C) (f : V ⟶ U) : (1 : IntrinsicBandSections F U).val V f = 1 :=
  rfl

@[simp]
theorem val_mul (s t : IntrinsicBandSections F U) (V : C) (f : V ⟶ U) :
    (s * t).val V f = s.val V f * t.val V f :=
  rfl

@[simp]
theorem val_inv (s : IntrinsicBandSections F U) (V : C) (f : V ⟶ U) :
    s⁻¹.val V f = (s.val V f)⁻¹ :=
  rfl

/-- **Extensionality**: two sections with the same component automorphism at
every arrow `f : V ⟶ U` and every object `x` over `V` are equal. -/
@[ext]
theorem ext {s t : IntrinsicBandSections F U}
    (h : ∀ (V : C) (f : V ⟶ U) (x : F.obj (.mk (op V))),
      (s.val V f).val.app x = (t.val V f).val.app x) :
    s = t :=
  Subtype.ext <| funext fun V ↦ funext fun f ↦ Units.ext <| CatCenter.ext _ _ (h V f)

/-- **Commutativity**: the intrinsic central sections commute, because the
categorical centre of each fibre is commutative. No commutativity of the automorphism groups of
`F` is needed. -/
protected theorem mul_comm (s t : IntrinsicBandSections F U) : s * t = t * s := by
  ext V f x
  simp only [val_mul, Units.val_mul]
  congr 1
  exact Std.Commutative.comm _ _

instance : CommGroup (IntrinsicBandSections F U) where
  mul_comm := IntrinsicBandSections.mul_comm

/-- **Restriction** along `f : V ⟶ U`: `(r_f s)(W, a) = s(W, a ≫ f)`. -/
def restrict {V : C} (f : V ⟶ U) : IntrinsicBandSections F U →* IntrinsicBandSections F V where
  toFun s := ofCompatible (fun W a ↦ s.val W (a ≫ f)) fun W T a g x ↦ by
    simp only [map_app, Category.assoc]
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem val_restrict {V : C} (f : V ⟶ U) (s : IntrinsicBandSections F U) (W : C) (a : W ⟶ V) :
    (restrict f s).val W a = s.val W (a ≫ f) :=
  (rfl)

/-- Restriction along the identity is the identity. -/
@[simp]
theorem restrict_id (s : IntrinsicBandSections F U) : restrict (𝟙 U) s = s := by
  ext W a x
  rw [val_restrict, Category.comp_id]

/-- Restriction is compatible with composition: `r_g (r_f s) = r_{g ≫ f} s`. -/
@[simp]
theorem restrict_comp {V W : C} (f : V ⟶ U) (g : W ⟶ V) (s : IntrinsicBandSections F U) :
    restrict g (restrict f s) = restrict (g ≫ f) s := by
  ext T a x
  rw [val_restrict, val_restrict, val_restrict, Category.assoc]

/-- If every object of every fibre has only the identity endomorphism, for instance when the
fibres are thin, the only intrinsic central section is the identity. -/
theorem subsingleton_of_subsingleton_end
    (h : ∀ (V : C) (x : F.obj (.mk (op V))), Subsingleton (x ⟶ x)) :
    Subsingleton (IntrinsicBandSections F U) :=
  ⟨fun _ _ ↦ ext fun V _ x ↦ (h V x).elim _ _⟩

end IntrinsicBandSections

end CategoryTheory.Pseudofunctor
