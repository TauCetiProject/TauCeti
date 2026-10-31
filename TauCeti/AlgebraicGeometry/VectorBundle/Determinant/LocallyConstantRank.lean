/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Core
public import TauCeti.AlgebraicGeometry.VectorBundle.Determinant.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.ExteriorPower.LocallyConstantRank

/-!
# The determinant of a vector bundle of locally constant rank

The rank of a finite locally free sheaf `E` on a scheme `X` is only locally constant: on a
disconnected scheme it may differ between components. Its determinant `det E` is the invertible
sheaf which over each open set `X_n = {x | rank E x = n}` is the top exterior power `⋀ⁿ E`.

It is the exterior power of `E` in the locally constant degree `rank E`
(`FiniteLocallyFreeSheaf.locallyConstantExteriorPower`), which has rank
`(rank E).choose (rank E) = 1` everywhere, so it is an invertible sheaf
`FiniteLocallyFreeSheaf.det E`. An isomorphism `E ≅ F` preserves the rank, so the determinant is a
functor `FiniteLocallyFreeSheaf.determinantCore X` on the core of the category of finite locally
free sheaves. On sheaves of constant rank `r` it agrees with the fixed-rank determinant
`FiniteLocallyFreeSheaf.determinant X r` (`FiniteLocallyFreeSheaf.detIsoDeterminant`).

## Main declarations

* `FiniteLocallyFreeSheaf.det`: the determinant `⋀^{rank E} E` of a finite locally free sheaf, an
  invertible sheaf;
* `FiniteLocallyFreeSheaf.determinantCore X`: the determinant as a functor on the core of the
  category of finite locally free sheaves;
* `FiniteLocallyFreeSheaf.detIsoDeterminant`: in constant rank `r`, `det E` is the fixed-rank
  determinant `⋀ʳ E`.

## References

* [R. Hartshorne, *Algebraic Geometry*][hartshorne1977], Chapter II, Exercise 5.16
* F. Knudsen and D. Mumford, *The projectivity of the moduli space of stable curves I:
  Preliminaries on det and Div*, Math. Scand. 39 (1976), Chapter I
-/

public section

open CategoryTheory

universe u

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry Scheme.Modules

noncomputable section

variable {X : Scheme.{u}}

namespace FiniteLocallyFreeSheaf

/-- The **determinant** `det E = ⋀^{rank E} E` of a finite locally free sheaf `E`: over each open
set where `E` has rank `n` it is the top exterior power `⋀ⁿ E`. It has rank `(rank E).choose
(rank E) = 1` everywhere, so it is an invertible sheaf. -/
def det (E : FiniteLocallyFreeSheaf X) : InvertibleSheaf X :=
  ⟨(AlgebraicGeometry.locallyConstantExteriorPower E.rank).obj E.obj,
    locallyConstantExteriorPower_obj_obj E.rank E ▸
      (isInvertible_iff_forall_rank_eq_one ((locallyConstantExteriorPower X E.rank).obj E)).2
        fun x ↦ by simp⟩

/-- The underlying sheaf of `det E` is `⋀^{rank E}` of the underlying `𝒪_X`-module of `E`. -/
@[simp]
lemma det_obj (E : FiniteLocallyFreeSheaf X) :
    (det E).obj = (AlgebraicGeometry.locallyConstantExteriorPower E.rank).obj E.obj :=
  (rfl)

/-- `⋀^r` of an identity, followed by the transport along `r = r`, is the identity. -/
private lemma locallyConstantExteriorPower_map_id_comp_eqToHom {r : LocallyConstant X ℕ}
    (h : r = r) (M : X.Modules) :
    (AlgebraicGeometry.locallyConstantExteriorPower r).map (𝟙 M) ≫
        eqToHom (congrArg (fun r ↦ (AlgebraicGeometry.locallyConstantExteriorPower r).obj M) h) =
      𝟙 _ := by
  simp

/-- `⋀^r` of a composite, followed by transport along `r = r''`, is the composite of the
transported maps along `r = r'` and `r' = r''`. -/
private lemma locallyConstantExteriorPower_map_comp_comp_eqToHom
    {r r' r'' : LocallyConstant X ℕ} (h : r = r') (h' : r' = r'') (h'' : r = r'')
    {M N P : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ P) :
    (AlgebraicGeometry.locallyConstantExteriorPower r).map (φ ≫ ψ) ≫
        eqToHom (congrArg (fun r ↦ (AlgebraicGeometry.locallyConstantExteriorPower r).obj P) h'') =
      ((AlgebraicGeometry.locallyConstantExteriorPower r).map φ ≫
          eqToHom (congrArg (fun r ↦ (AlgebraicGeometry.locallyConstantExteriorPower r).obj N) h)) ≫
        (AlgebraicGeometry.locallyConstantExteriorPower r').map ψ ≫
          eqToHom
            (congrArg (fun r ↦ (AlgebraicGeometry.locallyConstantExteriorPower r).obj P) h') := by
  subst h h'
  simp

variable (X) in
/-- The determinant is functorial on the core of the category of finite locally free sheaves:
an isomorphism `E ≅ F` preserves the rank and induces the isomorphism
`⋀^{rank E} E ≅ ⋀^{rank E} F = ⋀^{rank F} F` of determinants. -/
def determinantCore : Core (FiniteLocallyFreeSheaf X) ⥤ InvertibleSheaf X where
  obj E := det E.of
  map {E F} e := ObjectProperty.homMk <|
    (AlgebraicGeometry.locallyConstantExteriorPower E.of.rank).map e.iso.hom.hom ≫
      eqToHom (congrArg (fun r ↦ (AlgebraicGeometry.locallyConstantExteriorPower r).obj F.of.obj)
        (rank_eq_of_iso ((Scheme.Modules.isFiniteLocallyFree X).ι.mapIso e.iso)))
  map_id E := by
    ext1
    simp only [ObjectProperty.homMk_hom, coreCategory_id_iso, Iso.refl_hom,
      ObjectProperty.FullSubcategory.id_hom]
    exact locallyConstantExteriorPower_map_id_comp_eqToHom rfl _
  map_comp {E F G} e f := by
    ext1
    simp only [ObjectProperty.homMk_hom, coreCategory_comp_iso, Iso.trans_hom,
      ObjectProperty.FullSubcategory.comp_hom]
    exact locallyConstantExteriorPower_map_comp_comp_eqToHom
      (rank_eq_of_iso ((Scheme.Modules.isFiniteLocallyFree X).ι.mapIso e.iso))
      (rank_eq_of_iso ((Scheme.Modules.isFiniteLocallyFree X).ι.mapIso f.iso))
      (rank_eq_of_iso ((Scheme.Modules.isFiniteLocallyFree X).ι.mapIso (e ≫ f).iso)) _ _

/-- The determinant of an object of the core is `det` of the underlying finite locally free
sheaf. -/
@[simp]
lemma determinantCore_obj (E : Core (FiniteLocallyFreeSheaf X)) :
    (determinantCore X).obj E = det E.of :=
  (rfl)

/-- The determinant acts on an isomorphism `E ≅ F` through `⋀^{rank E}`, followed by the
identification `⋀^{rank E} F = ⋀^{rank F} F` given by `rank E = rank F`. -/
@[simp]
lemma determinantCore_map_hom {E F : Core (FiniteLocallyFreeSheaf X)} (e : E ⟶ F) :
    ((determinantCore X).map e).hom =
      eqToHom (by rw [determinantCore_obj, det_obj]) ≫
        (AlgebraicGeometry.locallyConstantExteriorPower E.of.rank).map e.iso.hom.hom ≫
        eqToHom (congrArg (fun r ↦ (AlgebraicGeometry.locallyConstantExteriorPower r).obj F.of.obj)
          (rank_eq_of_iso ((Scheme.Modules.isFiniteLocallyFree X).ι.mapIso e.iso))) ≫
        eqToHom (by rw [determinantCore_obj, det_obj]) :=
  -- The outer `eqToHom`s are identities; they only record `determinantCore_obj` and `det_obj`,
  -- which are not syntactic equalities outside this file.
  ((Category.id_comp _).trans (congrArg _ (Category.comp_id _))).symm

/-- On a sheaf `E` of constant rank `r`, the determinant `det E` is the fixed-rank determinant
`⋀ʳ E`. -/
def detIsoDeterminant {r : ℕ} (E : FixedRank X r) : det E.obj ≅ (determinant X r).obj E :=
  ObjectProperty.isoMk _ <| eqToIso (det_obj E.obj) ≪≫
    (AlgebraicGeometry.locallyConstantExteriorPowerIso E.obj.rank (FixedRank.rank_apply E)).app
      E.obj.obj ≪≫ eqToIso (determinant_obj_obj E).symm

/-- On underlying sheaves, `detIsoDeterminant` is `locallyConstantExteriorPowerIso`. -/
lemma detIsoDeterminant_hom_hom {r : ℕ} (E : FixedRank X r) :
    (detIsoDeterminant E).hom.hom =
      eqToHom (det_obj E.obj) ≫
        (AlgebraicGeometry.locallyConstantExteriorPowerIso E.obj.rank
          (FixedRank.rank_apply E)).hom.app E.obj.obj ≫
        eqToHom (determinant_obj_obj E).symm :=
  (rfl)

end FiniteLocallyFreeSheaf

end

end TauCeti.AlgebraicGeometry
