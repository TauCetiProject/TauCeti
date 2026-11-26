/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandCenter
public import TauCeti.CategoryTheory.Sites.Descent.Banding

/-!
# Central sections from an abelian banding

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a pseudofunctor whose fibres are groupoids (for instance a
gerbe) and `b` an `A`-banding of `F` by a sheaf of abelian groups `A`
(`CategoryTheory.Pseudofunctor.AbelianBanding`): group isomorphisms `b(U, x) : A(U) ≃* Aut x`,
compatible with pullback and with conjugation along isomorphisms.

Since every fibre arrow is invertible, the conjugation equation says that the band automorphisms
`b(U, x)(a)` are natural in `x` (`AbelianBanding.naturality_mulEquiv_hom`). So for a coefficient
`a ∈ A(U)` they form a unit `z_b(U)(a)` of the categorical centre of the fibre over `U`
(`AbelianBanding.coefficientCenter`), a group homomorphism in `a`, whose components are pulled
back to those of the restricted coefficient (`AbelianBanding.map_coefficientCenter_app`).

Taking at every arrow `f : V ⟶ U` the unit `z_b(V)(a|_V)` gives an intrinsic central section
`c_b(U)(a) ∈ ZF(U)` (`AbelianBanding.centerFromBanding`): a group homomorphism `A(U) →* ZF(U)`,
compatible with restriction, with evaluation `ev_(f, x)(c_b(U)(a)) = b(V, x)(a|_V)`, and
characterized by these evaluations. Distinct bandings give distinct sections. This is the
comparison map from the coefficient sheaf of a banding to the intrinsic band in the varying-base
step of the Stacks Project, Lemma 8.11.8 (06NY).

## Main definitions

In the namespace `CategoryTheory.Pseudofunctor.AbelianBanding`:

* `coefficientCenter`: the homomorphism `z_b(U) : A(U) →* (CatCenter (F U))ˣ`.
* `centerFromBanding`: the homomorphism `c_b(U) : A(U) →* ZF(U)`.

## Main results

* `naturality_mulEquiv_hom`: band automorphisms are natural in the object.
* `coefficientCenter_app`, `unitsEndEval_coefficientCenter`, `map_coefficientCenter_app`.
* `evaluation_centerFromBanding`: `ev_(f, x)(c_b(U)(a)) = b(V, x)(a|_V)`.
* `restrict_centerFromBanding`: `r_f(c_b(U)(a)) = c_b(V)(a|_V)`.
* `eq_centerFromBanding`: a section with these evaluations is `c_b(U)(a)`.
* `centerFromBanding_ne`: bandings differing at one coefficient give different sections.

## References

* [The Stacks Project, Lemma 8.11.8 (06NY)](https://stacks.math.columbia.edu/tag/06NY)
-/

public section

universe w v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.AbelianBanding

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {J : GrothendieckTopology C} {A : Sheaf J AddCommGrpCat.{w}} (b : F.AbelianBanding J A)
  (hF : ∀ U : C, IsGroupoid (F.obj (.mk (op U))))

include hF in
/-- **Band automorphisms are natural** when the fibres are groupoids: for every fibre arrow
`f : x ⟶ y`, `f ≫ b(U, y)(a) = b(U, x)(a) ≫ f`. -/
@[reassoc]
theorem naturality_mulEquiv_hom {U : C} {x y : F.obj (.mk (op U))} (f : x ⟶ y)
    (a : Multiplicative (A.obj.obj (op U))) :
    f ≫ (b.mulEquiv U y a).asIso.hom = (b.mulEquiv U x a).asIso.hom ≫ f := by
  have := hF U
  exact (b.mulEquiv_hom_comp (asIso f) a).symm

/-- The **central unit of a coefficient** `a ∈ A(U)`: the invertible natural endomorphism of the
identity of the fibre over `U` with component `b(U, x)(a)` at `x`, as a group homomorphism
`z_b(U) : A(U) →* (CatCenter (F U))ˣ`. -/
noncomputable def coefficientCenter (U : C) :
    Multiplicative (A.obj.obj (op U)) →* (CatCenter (F.obj (.mk (op U))))ˣ where
  toFun a := (Aut.unitsEndEquivAut (𝟭 _)).symm
    (.of (NatIso.ofComponents (fun x ↦ (b.mulEquiv U x a).asIso)
      fun f ↦ b.naturality_mulEquiv_hom hF f a))
  map_one' := by
    rw [MulEquiv.symm_apply_eq, map_one]
    refine Aut.ext (Iso.ext (NatTrans.ext (funext fun x ↦ ?_)))
    simp only [NatIso.ofComponents_hom_app, map_one, Aut.one_asIso, Iso.refl_hom, NatTrans.id_app,
      Functor.id_obj]
  map_mul' a a' := by
    rw [← map_mul, MulEquiv.apply_eq_iff_eq]
    refine Aut.ext (Iso.ext (NatTrans.ext (funext fun x ↦ ?_)))
    simp only [NatIso.ofComponents_hom_app, map_mul, Aut.mul_asIso, Iso.trans_hom,
      NatTrans.comp_app]

/-- The component of the central unit of `a` at `x` is the band automorphism `b(U, x)(a)`. -/
@[simp]
theorem coefficientCenter_app (U : C) (a : Multiplicative (A.obj.obj (op U)))
    (x : F.obj (.mk (op U))) :
    (b.coefficientCenter hF U a).val.app x = (b.mulEquiv U x a).asIso.hom :=
  (rfl)

/-- Evaluating the central unit of `a` at `x` gives the band automorphism `b(U, x)(a)`. -/
theorem unitsEndEval_coefficientCenter (U : C) (a : Multiplicative (A.obj.obj (op U)))
    (x : F.obj (.mk (op U))) :
    NatTrans.unitsEndEval (𝟭 _) x (b.coefficientCenter hF U a) = b.mulEquiv U x a :=
  Aut.ext (Iso.ext (by
    rw [NatTrans.unitsEndEval_asIso_hom]
    -- `CatCenter.app` is Mathlib's abbreviation for `asHom.app`
    exact b.coefficientCenter_app hF U a x))

/-- **Restriction of central units.** Pulling the central unit of `a` back along `f : V ⟶ U` at
`x` gives the central unit of the restriction `a|_V` at `F(f) x`. -/
theorem map_coefficientCenter_app {U V : C} (f : V ⟶ U) (a : Multiplicative (A.obj.obj (op U)))
    (x : F.obj (.mk (op U))) :
    (F.map f.op.toLoc).toFunctor.map ((b.coefficientCenter hF U a).val.app x) =
      (b.coefficientCenter hF V (.ofAdd (A.obj.map f.op a.toAdd))).val.app
        ((F.map f.op.toLoc).toFunctor.obj x) := by
  rw [coefficientCenter_app, coefficientCenter_app, map_mulEquiv_hom]

/-- The **central section of a coefficient** `a ∈ A(U)`: the intrinsic central section whose
component at `f : V ⟶ U` is the central unit of the restriction `a|_V`, as a group homomorphism
`c_b(U) : A(U) →* ZF(U)`. -/
noncomputable def centerFromBanding (U : C) :
    Multiplicative (A.obj.obj (op U)) →* IntrinsicBandSections F U where
  toFun a := IntrinsicBandSections.ofCompatible
    (fun V f ↦ b.coefficientCenter hF V (.ofAdd (A.obj.map f.op a.toAdd)))
    ((F.isPullbackCompatible_iff _).mpr fun V W f g x ↦ by simp)
  map_one' := IntrinsicBandSections.ext fun V f x ↦ by
    simp only [IntrinsicBandSections.val_ofCompatible, toAdd_one, map_zero, ofAdd_zero, map_one,
      IntrinsicBandSections.val_one]
  map_mul' a a' := IntrinsicBandSections.ext fun V f x ↦ by
    simp only [IntrinsicBandSections.val_ofCompatible, toAdd_mul, map_add, ofAdd_add, map_mul,
      IntrinsicBandSections.val_mul]

/-- The component of `c_b(U)(a)` at `f : V ⟶ U` is the central unit of `a|_V`. -/
@[simp]
theorem val_centerFromBanding (U : C) (a : Multiplicative (A.obj.obj (op U))) (V : C)
    (f : V ⟶ U) :
    (b.centerFromBanding hF U a).val V f =
      b.coefficientCenter hF V (.ofAdd (A.obj.map f.op a.toAdd)) :=
  IntrinsicBandSections.val_ofCompatible _ _ V f

/-- **Evaluation of the central section of a coefficient**: `ev_(f, x)(c_b(U)(a)) = b(V, x)(a|_V)`
for every `f : V ⟶ U` and every `x` over `V`. -/
@[simp]
theorem evaluation_centerFromBanding {U V : C} (f : V ⟶ U) (x : F.obj (.mk (op V)))
    (a : Multiplicative (A.obj.obj (op U))) :
    IntrinsicBandSections.evaluation f x (b.centerFromBanding hF U a) =
      b.mulEquiv V x (.ofAdd (A.obj.map f.op a.toAdd)) :=
  Aut.ext (Iso.ext (by
    rw [IntrinsicBandSections.evaluation_asIso_hom, val_centerFromBanding,
      coefficientCenter_app]))

/-- **Restriction of the central section of a coefficient**: `r_f(c_b(U)(a)) = c_b(V)(a|_V)`. -/
@[simp]
theorem restrict_centerFromBanding {U V : C} (f : V ⟶ U) (a : Multiplicative (A.obj.obj (op U))) :
    IntrinsicBandSections.restrict f (b.centerFromBanding hF U a) =
      b.centerFromBanding hF V (.ofAdd (A.obj.map f.op a.toAdd)) :=
  IntrinsicBandSections.ext fun W g x ↦ by simp

/-- **Characterization by evaluations.** A central section over `U` whose evaluation at every
`f : V ⟶ U` and every `x` over `V` is `b(V, x)(a|_V)` is `c_b(U)(a)`. -/
theorem eq_centerFromBanding {U : C} (a : Multiplicative (A.obj.obj (op U)))
    (s : IntrinsicBandSections F U)
    (hs : ∀ (V : C) (f : V ⟶ U) (x : F.obj (.mk (op V))),
      IntrinsicBandSections.evaluation f x s = b.mulEquiv V x (.ofAdd (A.obj.map f.op a.toAdd))) :
    s = b.centerFromBanding hF U a :=
  IntrinsicBandSections.ext_evaluation fun V f x ↦ by
    rw [hs, evaluation_centerFromBanding]

/-- **Distinct bandings give distinct sections**: if two bandings differ on a coefficient `a` at
one object `x` over `U`, then their central sections of `a` differ. -/
theorem centerFromBanding_ne {b' : F.AbelianBanding J A} {U : C} {x : F.obj (.mk (op U))}
    {a : Multiplicative (A.obj.obj (op U))} (hne : b.mulEquiv U x a ≠ b'.mulEquiv U x a) :
    b.centerFromBanding hF U a ≠ b'.centerFromBanding hF U a := by
  intro h
  apply hne
  have := congrArg (IntrinsicBandSections.evaluation (𝟙 U) x) h
  simpa using this

end CategoryTheory.Pseudofunctor.AbelianBanding
