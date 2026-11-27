/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandCenter.SheafIso

/-!
# Checks for the coefficient sheaf of a banding as the intrinsic band

For a gerbe `F` with an `A`-banding `b`:

* the presheaf comparison sends the zero coefficient to the zero section; its inverse undoes it on
  both sides; its inverse commutes with restriction along any arrow; a nonzero coefficient has a
  nonzero image, so the comparison is not the zero transformation;
* the sheaf comparison, read back in `U ↦ Additive ZF(U)`, is the coefficient transformation and
  its inverse; its two composites are identities;
* any sheaf isomorphism with the evaluations `b(V, x)(a|_V)` is the comparison;
* two bandings that differ at one coefficient and one object give different comparisons, so a
  different coefficient identification is not identified with the comparison.
-/

public section

namespace TauCeti.Examples.BandCenterSheafIso

open CategoryTheory CategoryTheory.Pseudofunctor Opposite Bicategory
open IntrinsicBandSections AbelianBanding

universe v u v' u'

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {J : GrothendieckTopology C} [F.IsGerbe J] {A : Sheaf J AddCommGrpCat.{max u v u' v'}}
  (b : F.AbelianBanding J A) (U : Cᵒᵖ)

/-- The forward component sends the zero coefficient to the zero central section. -/
example : b.centerFromBandingPresheafIso.hom.app U 0 = 0 :=
  map_zero _

/-- The inverse component applied to the forward image of `a` returns `a`. -/
example (a : A.obj.obj U) :
    b.centerFromBandingPresheafIso.inv.app U (b.centerFromBandingPresheafIso.hom.app U a) = a :=
  b.centerFromBandingPresheafIso.hom_inv_id_app_apply U a

/-- The forward component applied to the inverse of a central section `z` returns `z`. -/
example (z : (IntrinsicBandSections.presheaf F).obj U) :
    b.centerFromBandingPresheafIso.hom.app U (b.centerFromBandingPresheafIso.inv.app U z) = z :=
  b.centerFromBandingPresheafIso.inv_hom_id_app_apply U z

/-- The inverse commutes with restriction along any arrow `f : V ⟶ U`. -/
example {V : C} (f : V ⟶ U.unop) (z : (IntrinsicBandSections.presheaf F).obj U) :
    A.obj.map f.op (b.centerFromBandingPresheafIso.inv.app U z) =
      b.centerFromBandingPresheafIso.inv.app (op V)
        (Additive.ofMul (restrict f (Additive.toMul z))) :=
  b.map_centerFromBandingPresheafIso_inv_app f.op z

/-- A nonzero coefficient has a nonzero image: the comparison is not the zero transformation. -/
example (a : A.obj.obj U) (ha : a ≠ 0) : b.centerFromBandingPresheafIso.hom.app U a ≠ 0 := by
  intro h
  have := b.centerFromBandingPresheafIso.hom_inv_id_app_apply U a
  rw [h, map_zero] at this
  exact ha this.symm

variable (S : Sheaf J AddCommGrpCat.{max u v u' v'}) (h : S.obj = IntrinsicBandSections.presheaf F)

/-- Read back in `U ↦ Additive ZF(U)`, the forward sheaf map is the coefficient transformation. -/
example : (b.centerFromBandingSheafIso S h).hom.hom ≫ eqToHom h = b.centerFromBandingPresheaf :=
  b.centerFromBandingSheafIso_hom_transport S h

/-- Read from `U ↦ Additive ZF(U)`, the inverse sheaf map is the inverse presheaf map. -/
example :
    eqToHom h.symm ≫ (b.centerFromBandingSheafIso S h).inv.hom =
      b.centerFromBandingPresheafIso.inv :=
  b.centerFromBandingSheafIso_inv_transport S h

/-- The forward sheaf map followed by its inverse is the identity of `A`, and the inverse followed
by the forward map is the identity of `S`. -/
example :
    (b.centerFromBandingSheafIso S h).hom ≫ (b.centerFromBandingSheafIso S h).inv = 𝟙 A ∧
      (b.centerFromBandingSheafIso S h).inv ≫ (b.centerFromBandingSheafIso S h).hom = 𝟙 S :=
  ⟨Iso.hom_inv_id _, Iso.inv_hom_id _⟩

/-- A sheaf isomorphism `A ≅ ZF` with the evaluations `b(V, x)(a|_V)` is the comparison. -/
example (e : A ≅ IntrinsicBandSections.sheaf F J)
    (he : ∀ (U V : C) (f : V ⟶ U) (x : F.obj (.mk (op V))) (a : A.obj.obj (op U)),
      IntrinsicBandSections.evaluation f x (Additive.toMul (e.hom.hom.app (op U) a)) =
        b.mulEquiv V x (.ofAdd (A.obj.map f.op a))) :
    e = b.bandCenterIso :=
  b.bandCenterIso_unique e he

/-- Two bandings that differ at one coefficient and one object give different comparisons. -/
example (b' : F.AbelianBanding J A) {U : C} {x : F.obj (.mk (op U))}
    {a : Multiplicative (A.obj.obj (op U))} (hne : b.mulEquiv U x a ≠ b'.mulEquiv U x a) :
    b.bandCenterIso ≠ b'.bandCenterIso := by
  intro e
  have := congrArg (fun i : A ≅ IntrinsicBandSections.sheaf F J ↦ i.hom.hom.app (op U) a.toAdd) e
  simp only [bandCenterIso_hom] at this
  exact b.centerFromBanding_ne hne (congrArg Additive.toMul this)

end TauCeti.Examples.BandCenterSheafIso
