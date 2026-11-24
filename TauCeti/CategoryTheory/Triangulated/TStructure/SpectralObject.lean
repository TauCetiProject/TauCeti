/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
public import Mathlib.Algebra.Homology.SpectralObject.HasSpectralSequence
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import TauCeti.Algebra.Homology.SpectralObject.Abutment

/-!
# The spectral sequence of a homological functor on a t-structure

Let `t` be a t-structure on a triangulated category `C`, let `X` be an object of `C` and let
`H : C ⥤ A` be a homological functor to an abelian category, with its shift sequence
`n ↦ H.shift n`, `(H.shift n).obj Y ≅ H.obj (Y⟦n⟧)` (`H.isoShift n`). The truncations of `X`
form Mathlib's spectral object `t.spectralObject X` in `C`, and applying `H` gives the spectral
object `(t.spectralObject X).mapHomologicalFunctor H` in `A`, whose value `H^n(a ≤ b)` is
`(H.shift n).obj (τ_{≥a} τ_{<b} X)` (`mapHomologicalFunctor_spectralObject_H_obj_mk₁`). Its
abutment is `H^n(⊥ ≤ ⊤) ≅ (H.shift n).obj X` (`abutmentMapHomologicalFunctorSpectralObjectIso`),
because `τ_{≥⊥} τ_{<⊤}` is the identity, and the objects of the first page of its `E₂` spectral
sequence are the values `(H.shift (p + q)).obj (τ_{≥q} τ_{<q+1} X)` of `H` on the `t`-cohomology
objects of `X`. For the canonical t-structure on a derived category this is the hypercohomology
spectral sequence `E₂^{p,q} = Hᵖ(Hᵠ(X)) ⇒ H^{p+q}(X)` (see
`TauCeti.Algebra.Homology.DerivedCategory.SpectralObject`); applied to the derived pushforward
`X = Rf_* F` of a sheaf and to the represented functor `Hom(Z, -)` with `Z` the constant sheaf
`ℤ` placed in degree `0`, which computes global sections, it gives the Leray spectral sequence.

The spectral object is first quadrant in the sense of Mathlib's `IsFirstQuadrant`
(`isFirstQuadrant_mapHomologicalFunctor_spectralObject`) as soon as `X` is `≥ 0` and `H` vanishes
on the objects `≥ 1`: then `τ_{<b} X = 0` for `b ≤ 0`, and
`(H.shift n).obj (τ_{≥a} Y) ≅ H.obj ((τ_{≥a} Y)⟦n⟧)` vanishes for `n < a`
(`isZero_shift_obj_of_isGE`, which more generally allows `H` vanishing on the objects `≥ b` and
`n + b ≤ a`). The filtration of its abutment is then finite in each degree, with
`F_q H^n = 0` for `q ≤ 0` and `F_q H^n = H^n` for `q > n` (Tau Ceti's
`CategoryTheory.Abelian.SpectralObject.isZero_abutmentFiltration` and
`CategoryTheory.Abelian.SpectralObject.isIso_abutmentFiltrationι`), and the pages stabilize to
its graded pieces (`CategoryTheory.Abelian.SpectralObject.spectralSequencePageXIsoEInfty`). The
vanishing condition holds for the represented functor `H = Hom(Z, -)` when `Z` is `≤ 0`, since
`Hom(Z, -)` vanishes on the objects `≥ q` when `Z` is `≤ p` for some `p < q`
(`isZero_preadditiveCoyoneda_obj_of_isLE_of_isGE`), and the spectral object is then first
quadrant by an instance.

## Main results

* `CategoryTheory.Triangulated.TStructure.isZero_shift_obj_of_isGE`: a functor vanishing on the
  objects `≥ b` has `H.shift n` vanishing on the objects `≥ a` for `n + b ≤ a`.
* `CategoryTheory.Triangulated.TStructure.isFirstQuadrant_mapHomologicalFunctor_spectralObject`:
  the spectral object of `X ≥ 0` under a homological functor vanishing on the objects `≥ 1` is
  first quadrant.
* `CategoryTheory.Triangulated.TStructure.abutmentMapHomologicalFunctorSpectralObjectIso`: its
  abutment is `(H.shift n).obj X`.

## References

* J.-L. Verdier, *Des catégories dérivées des catégories abéliennes*, Astérisque 239 (1996), II.4.
* [The Stacks Project, Section 21.14](https://stacks.math.columbia.edu/tag/072X), for the Leray
  spectral sequence.
-/

public section

namespace CategoryTheory.Triangulated.TStructure

open Limits

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] (t : TStructure C)

/-- If a functor `H` with a shift sequence vanishes on the objects `≥ b` of a t-structure, its
shift `H.shift n` vanishes on the objects `≥ a` for `n + b ≤ a`. -/
lemma isZero_shift_obj_of_isGE {A : Type*} [Category* A] (H : C ⥤ A) [H.ShiftSequence ℤ] {b : ℤ}
    (hH : ∀ Y : C, t.IsGE Y b → IsZero (H.obj Y)) (Y : C) {n a : ℤ} (hna : n + b ≤ a)
    [t.IsGE Y a] : IsZero ((H.shift n).obj Y) :=
  have := t.isGE_of_ge Y (n + b) a
  (hH _ (t.isGE_shift Y (n + b) n b)).of_iso ((H.isoShift n).app Y).symm

/-- The functor `Hom(Z, -)` vanishes on the objects `≥ q` when `Z` is `≤ p` for some `p < q`. -/
lemma isZero_preadditiveCoyoneda_obj_of_isLE_of_isGE (Z Y : C) {p q : ℤ} (hpq : p < q)
    [t.IsLE Z p] [t.IsGE Y q] : IsZero ((preadditiveCoyoneda.obj (Opposite.op Z)).obj Y) :=
  have : Subsingleton (Z ⟶ Y) := ⟨fun f g ↦ (t.zero f p q).trans (t.zero g p q).symm⟩
  @AddCommGrpCat.isZero_of_subsingleton _ this

variable [IsTriangulated C] {A : Type*} [Category* A] [Abelian A] (H : C ⥤ A) [H.IsHomological]
  [H.ShiftSequence ℤ]

/-- The value `H^n(i ≤ j)` of the spectral object of the truncations of `X` under `H` is
`(H.shift n).obj (τ_{≥i} τ_{<j} X)`. -/
lemma mapHomologicalFunctor_spectralObject_H_obj_mk₁ (X : C) (n : ℤ) {i j : EInt} (hij : i ≤ j) :
    (((t.spectralObject X).mapHomologicalFunctor H).H n).obj
        (ComposableArrows.mk₁ (homOfLE hij)) =
      (H.shift n).obj ((t.eTruncGE.obj i).obj ((t.eTruncLT.obj j).obj X)) := by
  simp only [SpectralObject.mapHomologicalFunctor_H, spectralObject_ω₁, Functor.comp_obj,
    evaluation_obj_obj, ω₁_obj, ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj]

/-- The component at `i ≤ j` of the morphism of spectral objects induced by `f : X ⟶ X'` under
`H` is the value of `H.shift n` on the map `τ_{≥i} τ_{<j} X ⟶ τ_{≥i} τ_{<j} X'` induced by `f`. -/
lemma mapHomologicalFunctorFunctor_map_spectralObjectFunctor_map_hom_app_mk₁ {X X' : C}
    (f : X ⟶ X') (n : ℤ) {i j : EInt} (hij : i ≤ j) :
    (((SpectralObject.mapHomologicalFunctorFunctor H EInt).map
        (t.spectralObjectFunctor.map f)).hom n).app (ComposableArrows.mk₁ (homOfLE hij)) =
      (H.shift n).map ((t.eTruncGE.obj i).map ((t.eTruncLT.obj j).map f)) := by
  simp only [SpectralObject.mapHomologicalFunctorFunctor_map_hom, spectralObjectFunctor_map_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, evaluation_map_app, ω₁_obj, Functor.comp_map,
    ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj]

/-- For integer bounds `a ≤ b`, the value `H^n(a ≤ b)` of the spectral object of the truncations
of `X` under `H` is `(H.shift n).obj (τ_{≥a} τ_{<b} X)`, for the truncation functors
`t.truncGE a` and `t.truncLT b`. -/
lemma mapHomologicalFunctor_spectralObject_H_obj_mk₁_coe (X : C) (n : ℤ) {a b : ℤ}
    (hab : (a : EInt) ≤ b) :
    (((t.spectralObject X).mapHomologicalFunctor H).H n).obj
        (ComposableArrows.mk₁ (homOfLE hab)) =
      (H.shift n).obj ((t.truncGE a).obj ((t.truncLT b).obj X)) := by
  rw [mapHomologicalFunctor_spectralObject_H_obj_mk₁, eTruncGE_obj_coe, eTruncLT_obj_coe]

/-- For integer bounds `a ≤ b`, the component at `a ≤ b` of the morphism of spectral objects
induced by `f : X ⟶ X'` under `H` is, through the identifications
`mapHomologicalFunctor_spectralObject_H_obj_mk₁_coe` of its source and target, the value of
`H.shift n` on the map `τ_{≥a} τ_{<b} X ⟶ τ_{≥a} τ_{<b} X'` induced by `f`. -/
@[reassoc]
lemma mapHomologicalFunctorFunctor_map_spectralObjectFunctor_map_hom_app_mk₁_comp_eqToHom
    {X X' : C} (f : X ⟶ X') (n : ℤ) {a b : ℤ} (hab : (a : EInt) ≤ b) :
    (((SpectralObject.mapHomologicalFunctorFunctor H EInt).map
        (t.spectralObjectFunctor.map f)).hom n).app (ComposableArrows.mk₁ (homOfLE hab)) ≫
        eqToHom (t.mapHomologicalFunctor_spectralObject_H_obj_mk₁_coe H X' n hab) =
      eqToHom (t.mapHomologicalFunctor_spectralObject_H_obj_mk₁_coe H X n hab) ≫
        (H.shift n).map ((t.truncGE a).map ((t.truncLT b).map f)) := by
  rw [mapHomologicalFunctorFunctor_map_spectralObjectFunctor_map_hom_app_mk₁,
    Functor.congr_hom (t.eTruncGE_obj_coe a), Functor.congr_hom (t.eTruncLT_obj_coe b)]
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- The spectral object of the truncations of an object `X ≥ 0` under a homological functor
vanishing on the objects `≥ 1` is first quadrant. -/
lemma isFirstQuadrant_mapHomologicalFunctor_spectralObject
    (hH : ∀ Y : C, t.IsGE Y 1 → IsZero (H.obj Y)) (X : C) [t.IsGE X 0] :
    ((t.spectralObject X).mapHomologicalFunctor H).IsFirstQuadrant where
  isZero₁ i j hij hj n := by
    rw [mapHomologicalFunctor_spectralObject_H_obj_mk₁]
    exact (H.shift n).map_isZero
      ((t.eTruncGE.obj i).map_isZero (t.isZero_eTruncLT_obj_obj X 0 j hj))
  isZero₂ i j hij n hi := by
    rw [mapHomologicalFunctor_spectralObject_H_obj_mk₁]
    induction i using WithBotTop.rec with
    | bot => simp at hi
    | coe a =>
      have : t.IsGE ((t.eTruncGE.obj a).obj ((t.eTruncLT.obj j).obj X)) a :=
        t.isGE_eTruncGE_obj_obj a a le_rfl _
      exact t.isZero_shift_obj_of_isGE H hH ((t.eTruncGE.obj a).obj ((t.eTruncLT.obj j).obj X))
        (by simp at hi; lia : n + 1 ≤ a)
    | top =>
      rw [eTruncGE_obj_top]
      exact (H.shift n).map_isZero (Functor.zero_obj _)

/-- The spectral object of the truncations of an object `X ≥ 0` under the functor `Hom(Z, -)`,
for `Z ≤ 0`, is first quadrant. -/
instance (Z X : C) [t.IsLE Z 0] [t.IsGE X 0] :
    ((t.spectralObject X).mapHomologicalFunctor
      (preadditiveCoyoneda.obj (Opposite.op Z))).IsFirstQuadrant :=
  t.isFirstQuadrant_mapHomologicalFunctor_spectralObject _
    (fun Y (_ : t.IsGE Y 1) ↦ t.isZero_preadditiveCoyoneda_obj_of_isLE_of_isGE Z Y zero_lt_one) X

/-- The abutment `H^n(⊥ ≤ ⊤)` of the spectral object of the truncations of `X` under a
homological functor `H` is `(H.shift n).obj X`: the truncations `τ_{<⊤}` and `τ_{≥⊥}` are the
identity (`eTruncLT_obj_top`, `eTruncGE_obj_bot`). -/
noncomputable def abutmentMapHomologicalFunctorSpectralObjectIso (X : C) (n : ℤ) :
    ((t.spectralObject X).mapHomologicalFunctor H).abutment n ≅ (H.shift n).obj X :=
  eqToIso (by
    rw [Abelian.SpectralObject.abutment, mapHomologicalFunctor_spectralObject_H_obj_mk₁,
      eTruncLT_obj_top, eTruncGE_obj_bot, Functor.id_obj, Functor.id_obj])

/-- The abutment identification is natural in `X`: the component at `⊥ ≤ ⊤` of the morphism
of spectral objects induced by `f : X ⟶ X'` corresponds to `(H.shift n).map f`. -/
@[reassoc]
lemma abutmentMapHomologicalFunctorSpectralObjectIso_hom_naturality {X X' : C}
    (f : X ⟶ X') (n : ℤ) :
    (((SpectralObject.mapHomologicalFunctorFunctor H EInt).map
        (t.spectralObjectFunctor.map f)).hom n).app
        (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) ≫
        (t.abutmentMapHomologicalFunctorSpectralObjectIso H X' n).hom =
      (t.abutmentMapHomologicalFunctorSpectralObjectIso H X n).hom ≫ (H.shift n).map f := by
  dsimp only [abutmentMapHomologicalFunctorSpectralObjectIso, eqToIso.hom]
  rw [mapHomologicalFunctorFunctor_map_spectralObjectFunctor_map_hom_app_mk₁,
    Functor.congr_hom t.eTruncGE_obj_bot, Functor.congr_hom t.eTruncLT_obj_top]
  simp only [Functor.id_map, eqToHom_refl, Category.comp_id, Category.id_comp]
  exact Category.comp_id _

end CategoryTheory.Triangulated.TStructure
