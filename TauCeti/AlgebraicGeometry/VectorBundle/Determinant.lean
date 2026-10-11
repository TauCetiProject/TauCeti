/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.ExteriorPower
public import TauCeti.AlgebraicGeometry.VectorBundle.FixedRank

/-!
# The determinant of a vector bundle of fixed rank

If `E` is a finite locally free sheaf on a scheme `X` of constant rank `r`, its top exterior power
`det E = ⋀ʳ E` has rank `r.choose r = 1` at every point, so it is an invertible sheaf. This file
packages the top exterior power as the determinant functor
`FiniteLocallyFreeSheaf.determinant X r : FixedRank X r ⥤ InvertibleSheaf X`, and computes it in
the basic cases: the determinant of the free sheaf of rank `r` is the trivial line bundle, the
determinant of a sheaf of constant rank one is the sheaf itself, and every sheaf of rank zero has
trivial determinant.

## Main declarations

* `FiniteLocallyFreeSheaf.determinant X r`: the determinant `E ↦ ⋀ʳ E` of finite locally free
  sheaves of constant rank `r`, with values in invertible sheaves;
* `FiniteLocallyFreeSheaf.determinantFreeIso`: the determinant of the free sheaf of rank `r` is
  the trivial invertible sheaf;
* `FiniteLocallyFreeSheaf.determinantOneIso`: on sheaves of constant rank one, the determinant is
  naturally the sheaf itself, as a finite locally free sheaf;
* `FiniteLocallyFreeSheaf.determinantZeroIso`: in rank zero, the determinant is naturally the
  trivial invertible sheaf.

## References

* [R. Hartshorne, *Algebraic Geometry*][hartshorne1977], Chapter II, Exercise 5.16
-/

public section

open CategoryTheory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

namespace FiniteLocallyFreeSheaf

variable (X : Scheme.{u})

/-- The determinant of finite locally free sheaves of constant rank `r` on `X`: the top exterior
power `E ↦ ⋀ʳ E` of the underlying `𝒪_X`-modules, which has rank `r.choose r = 1` everywhere and
so is an invertible sheaf. -/
def determinant (r : ℕ) : FixedRank X r ⥤ InvertibleSheaf X :=
  (SheafOfModules.isInvertible X).lift
    (FixedRank.toFiniteLocallyFree X r ⋙ (Scheme.Modules.isFiniteLocallyFree X).ι ⋙
      SheafOfModules.exteriorPower X.sheaf r)
    fun E ↦ exteriorPower_obj_obj r E.obj ▸
      (isInvertible_iff_forall_rank_eq_one ((exteriorPower X r).obj E.obj)).mpr fun x ↦ by
        rw [rank_exteriorPower_apply, FixedRank.rank_apply, Nat.choose_self]

variable {X}

/-- The underlying sheaf of the determinant of a sheaf `E` of constant rank `r` is the `r`-th
exterior power of the underlying `𝒪_X`-module of `E`. -/
@[simp]
theorem determinant_obj_obj {r : ℕ} (E : FixedRank X r) :
    ((determinant X r).obj E).obj = (SheafOfModules.exteriorPower X.sheaf r).obj E.obj.obj :=
  (rfl)

/-- The determinant acts on a morphism of sheaves of constant rank `r` by the `r`-th exterior
power of the underlying morphism of `𝒪_X`-modules. -/
@[simp]
theorem determinant_map_hom {r : ℕ} {E F : FixedRank X r} (φ : E ⟶ F) :
    ((determinant X r).map φ).hom =
      eqToHom (determinant_obj_obj E) ≫ (SheafOfModules.exteriorPower X.sheaf r).map φ.hom.hom ≫
        eqToHom (determinant_obj_obj F).symm :=
  -- Both `eqToHom`s are identities, since `determinant` is a lift of the exterior power; they only
  -- record `determinant_obj_obj`, which is not a syntactic equality outside this file.
  ((Category.id_comp _).trans (Category.comp_id _)).symm

variable (X) in
/-- The determinant of the free sheaf of rank `r` is the trivial invertible sheaf: the top
exterior power of the free sheaf on `Fin r` is free on its single `r`-element subset. -/
def determinantFreeIso (r : ℕ) :
    (determinant X r).obj (FixedRank.free X r) ≅ InvertibleSheaf.trivial X :=
  -- `Fin r` has exactly one `r`-element subset, so the free sheaf on these subsets is the free
  -- sheaf on one generator.
  have h := Nat.card_eq_one_iff_unique.mp (by
    rw [Set.powersetCard.card, Nat.card_ulift, Nat.card_eq_fintype_card, Fintype.card_fin,
      Nat.choose_self] : Nat.card (Set.powersetCard (ULift.{u} (Fin r)) r) = 1)
  have := h.1
  ObjectProperty.isoMk _ (eqToIso (by rw [determinant_obj_obj, FixedRank.free_obj, free_obj]) ≪≫
    SheafOfModules.exteriorPowerFreeIso (R := X.sheaf) (ULift.{u} (Fin r)) r ≪≫
    (SheafOfModules.freeFunctor (R := X.ringCatSheaf)).mapIso
      (equivOfSubsingletonOfSubsingleton (fun _ ↦ PUnit.unit) fun _ ↦ h.2.some).toIso ≪≫
    eqToIso (InvertibleSheaf.trivial_obj X).symm)

/-- On underlying sheaves, `determinantFreeIso` is the identification
`⋀ʳ (free (Fin r)) ≅ free (Set.powersetCard (Fin r) r)` of `exteriorPowerFreeIso`, followed by the
map of free sheaves collapsing the single `r`-element subset of `Fin r` to a point. -/
theorem determinantFreeIso_hom_hom (r : ℕ) :
    (determinantFreeIso X r).hom.hom =
      eqToHom (by rw [determinant_obj_obj, FixedRank.free_obj, free_obj]) ≫
        (SheafOfModules.exteriorPowerFreeIso (R := X.sheaf) (ULift.{u} (Fin r)) r).hom ≫
        SheafOfModules.freeMap (R := X.ringCatSheaf) (fun _ ↦ PUnit.unit) ≫
        eqToHom (InvertibleSheaf.trivial_obj X).symm := by
  -- The free-sheaf part of `determinantFreeIso` is `freeFunctor` applied to the collapsing map,
  -- which `freeFunctor_map` identifies with `freeMap`.
  unfold determinantFreeIso
  exact congrArg (fun g ↦ _ ≫ _ ≫ g ≫ _) (SheafOfModules.freeFunctor_map _)

variable (X) in
/-- The determinant of a finite locally free sheaf of constant rank one is naturally the sheaf
itself: `⋀¹ E ≅ E`. -/
def determinantOneIso :
    determinant X 1 ⋙ InvertibleSheaf.toFiniteLocallyFree X ≅ FixedRank.toFiniteLocallyFree X 1 :=
  NatIso.ofComponents
    (fun E ↦ ObjectProperty.isoMk _ ((SheafOfModules.exteriorPowerOneIso X.sheaf).app E.obj.obj))
    (fun f ↦ by
      -- `determinant` is a lift of the exterior power, so on underlying morphisms this is the
      -- naturality of `exteriorPowerOneIso`.
      ext1
      exact (SheafOfModules.exteriorPowerOneIso X.sheaf).hom.naturality f.hom.hom)

/-- On underlying sheaves, the components of `determinantOneIso` are those of
`SheafOfModules.exteriorPowerOneIso`. -/
@[simp]
theorem determinantOneIso_hom_app_hom (E : FixedRank X 1) :
    ((determinantOneIso X).hom.app E).hom =
      eqToHom (determinant_obj_obj E) ≫
        (SheafOfModules.exteriorPowerOneIso X.sheaf).hom.app E.obj.obj :=
  (Category.id_comp _).symm

variable (X) in
/-- In rank zero the determinant is naturally the trivial invertible sheaf: `⋀⁰ E ≅ 𝒪_X`. -/
def determinantZeroIso :
    determinant X 0 ≅ (Functor.const _).obj (InvertibleSheaf.trivial X) :=
  NatIso.ofComponents
    (fun E ↦ ObjectProperty.isoMk _
      ((SheafOfModules.exteriorPowerZeroIso X.sheaf).app E.obj.obj ≪≫
        (TauCeti.SheafOfModules.freePUnitIsoUnit X.ringCatSheaf).symm ≪≫
        eqToIso (InvertibleSheaf.trivial_obj X).symm))
    (fun f ↦ by
      -- As for `determinantOneIso`, this is the naturality of `exteriorPowerZeroIso`; the
      -- constant functor acts on morphisms by identities.
      ext1
      exact ((SheafOfModules.exteriorPowerZeroIso X.sheaf).hom.naturality_assoc f.hom.hom _).trans
        (Category.comp_id _).symm)

/-- On underlying sheaves, the components of `determinantZeroIso` are those of
`SheafOfModules.exteriorPowerZeroIso`, followed by the identification of the structure sheaf with
the free sheaf on one generator. -/
@[simp]
theorem determinantZeroIso_hom_app_hom (E : FixedRank X 0) :
    ((determinantZeroIso X).hom.app E).hom =
      eqToHom (determinant_obj_obj E) ≫
        (SheafOfModules.exteriorPowerZeroIso X.sheaf).hom.app E.obj.obj ≫
        (TauCeti.SheafOfModules.freePUnitIsoUnit X.ringCatSheaf).inv ≫
        eqToHom (InvertibleSheaf.trivial_obj X).symm :=
  (Category.id_comp _).symm

end FiniteLocallyFreeSheaf

end

end AlgebraicGeometry

end TauCeti
