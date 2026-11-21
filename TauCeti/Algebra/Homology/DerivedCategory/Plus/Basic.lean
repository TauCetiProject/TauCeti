/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import TauCeti.Algebra.Homology.CochainComplex.Plus

/-!
# Basic localization, homology, single-functor, and cone properties on `DerivedCategory.Plus`

This file records basic properties of Mathlib's localization functor
`DerivedCategory.Plus.Q : CochainComplex.Plus C ⥤ DerivedCategory.Plus C` and cohomology functors
`DerivedCategory.Plus.homologyFunctor C n` for an abelian category `C`:

* `TauCeti.DerivedCategory.Plus.homologyFunctorFactors`: `Q ⋙ homologyFunctor C n` identifies
  with cochain-complex cohomology `HomologicalComplex.homologyFunctor`.
* `TauCeti.DerivedCategory.Plus.Q_map_eq_of_homotopy`: homotopic morphisms of bounded-below
  cochain complexes induce the same morphism in `DerivedCategory.Plus C`.
* `TauCeti.DerivedCategory.Plus.isIso_Q_map_of_quasiIso` and `isIso_Q_map_iff_quasiIso`: a
  morphism in `CochainComplex.Plus C` becomes an isomorphism under `Q` if and only if its
  underlying chain map is a quasi-isomorphism.
* `TauCeti.DerivedCategory.Plus.singleFunctorIsoCompQ`: the single functor
  `DerivedCategory.Plus.singleFunctor C n` factors through
  `TauCeti.CochainComplex.Plus.singleFunctor C n` and `Q`.
* `TauCeti.DerivedCategory.Plus.mappingConeTriangle_distinguished`: the image under `Q` of a
  bounded-below mapping cone triangle is distinguished.

## References

* Mathlib's `Mathlib/Algebra/Homology/DerivedCategory/Basic.lean` and
  `Mathlib/Algebra/Homology/DerivedCategory/Plus.lean`, whose unbounded and bounded-below
  localization conventions are followed here.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Pretriangulated

universe w v u

namespace TauCeti.DerivedCategory.Plus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

variable (C) in
/-- The cohomology of `DerivedCategory.Plus.Q.obj K` is naturally isomorphic to the cohomology of
the underlying bounded-below cochain complex `K.obj`. -/
def homologyFunctorFactors (n : ℤ) :
    _root_.DerivedCategory.Plus.Q ⋙ _root_.DerivedCategory.Plus.homologyFunctor C n ≅
      _root_.CochainComplex.Plus.ι C ⋙
        HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n :=
  NatIso.ofComponents
    (fun K ↦ (_root_.DerivedCategory.homologyFunctorFactors C n).app K.obj)
    (fun f ↦ (_root_.DerivedCategory.homologyFunctorFactors C n).hom.naturality f.hom)

@[reassoc]
lemma homologyFunctorFactors_hom_naturality {K L : _root_.CochainComplex.Plus C} (f : K ⟶ L)
    (n : ℤ) :
    (_root_.DerivedCategory.Plus.homologyFunctor C n).map (_root_.DerivedCategory.Plus.Q.map f) ≫
        (homologyFunctorFactors C n).hom.app L =
      (homologyFunctorFactors C n).hom.app K ≫ HomologicalComplex.homologyMap f.hom n :=
  (homologyFunctorFactors C n).hom.naturality f

@[simp]
lemma homologyFunctorFactors_hom_app (K : _root_.CochainComplex.Plus C) (n : ℤ) :
    (homologyFunctorFactors C n).hom.app K =
      (_root_.DerivedCategory.homologyFunctorFactors C n).hom.app K.obj :=
  (rfl)

@[simp]
lemma homologyFunctorFactors_inv_app (K : _root_.CochainComplex.Plus C) (n : ℤ) :
    (homologyFunctorFactors C n).inv.app K =
      (_root_.DerivedCategory.homologyFunctorFactors C n).inv.app K.obj :=
  (rfl)

/-- Homotopic morphisms of bounded-below cochain complexes induce the same morphism in
`DerivedCategory.Plus C`. -/
lemma Q_map_eq_of_homotopy {K L : _root_.CochainComplex.Plus C} {f g : K ⟶ L}
    (h : Homotopy f.hom g.hom) :
    _root_.DerivedCategory.Plus.Q.map f = _root_.DerivedCategory.Plus.Q.map g := by
  apply _root_.DerivedCategory.Plus.ι.map_injective
  rw [← cancel_mono ((_root_.DerivedCategory.Plus.QCompιIso C).hom.app L)]
  have hf := (_root_.DerivedCategory.Plus.QCompιIso C).hom.naturality f
  have hg := (_root_.DerivedCategory.Plus.QCompιIso C).hom.naturality g
  dsimp at hf hg ⊢
  rw [hf, hg, _root_.DerivedCategory.Q_map_eq_of_homotopy C h]

/-- A quasi-isomorphism in `CochainComplex.Plus C` becomes an isomorphism in
`DerivedCategory.Plus C`. -/
instance isIso_Q_map_of_quasiIso {K L : _root_.CochainComplex.Plus C} (f : K ⟶ L)
    [QuasiIso f.hom] :
    IsIso (_root_.DerivedCategory.Plus.Q.map f) :=
  Localization.inverts _root_.DerivedCategory.Plus.Q (_root_.CochainComplex.Plus.quasiIso C) f
    ((_root_.CochainComplex.Plus.quasiIso_iff C f).2 inferInstance)

/-- A morphism in `CochainComplex.Plus C` becomes an isomorphism in `DerivedCategory.Plus C`
if and only if its underlying chain map is a quasi-isomorphism. -/
lemma isIso_Q_map_iff_quasiIso {K L : _root_.CochainComplex.Plus C} (f : K ⟶ L) :
    IsIso (_root_.DerivedCategory.Plus.Q.map f) ↔ QuasiIso f.hom := by
  rw [← isIso_iff_of_reflects_iso _ _root_.DerivedCategory.Plus.ι,
    ← Functor.comp_map,
    NatIso.isIso_map_iff (_root_.DerivedCategory.Plus.QCompιIso C) f]
  exact _root_.DerivedCategory.isIso_Q_map_iff_quasiIso C f.hom

variable (C) in
/-- The single functor `DerivedCategory.Plus.singleFunctor C n` factors through
`TauCeti.CochainComplex.Plus.singleFunctor C n` and `DerivedCategory.Plus.Q`. -/
def singleFunctorIsoCompQ (n : ℤ) :
    _root_.DerivedCategory.Plus.singleFunctor C n ≅
      TauCeti.CochainComplex.Plus.singleFunctor C n ⋙ _root_.DerivedCategory.Plus.Q :=
  ((_root_.DerivedCategory.TStructure.t (C := C)).plus.fullyFaithfulι.whiskeringRight _).preimageIso
    (_root_.DerivedCategory.Plus.singleFunctorιIso C n ≪≫
      _root_.DerivedCategory.singleFunctorIsoCompQ C n ≪≫
      isoWhiskerRight (TauCeti.CochainComplex.Plus.singleFunctorCompιIso C n).symm
        _root_.DerivedCategory.Q ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (TauCeti.CochainComplex.Plus.singleFunctor C n)
        (_root_.DerivedCategory.Plus.QCompιIso C).symm ≪≫
      (Functor.associator _ _ _).symm)

/-- Characterizing identity for `singleFunctorIsoCompQ` after whiskering with
`DerivedCategory.Plus.ι`. -/
@[reassoc]
lemma whiskerRight_singleFunctorIsoCompQ_hom_ι (n : ℤ) :
    whiskerRight (singleFunctorIsoCompQ C n).hom _root_.DerivedCategory.Plus.ι =
      (_root_.DerivedCategory.Plus.singleFunctorιIso C n).hom ≫
        (_root_.DerivedCategory.singleFunctorIsoCompQ C n).hom ≫
        whiskerRight (TauCeti.CochainComplex.Plus.singleFunctorCompιIso C n).inv
          _root_.DerivedCategory.Q ≫
        (Functor.associator _ _ _).hom ≫
        whiskerLeft (TauCeti.CochainComplex.Plus.singleFunctor C n)
          (_root_.DerivedCategory.Plus.QCompιIso C).inv ≫
        (Functor.associator _ _ _).inv :=
  ((_root_.DerivedCategory.TStructure.t (C := C)).plus.fullyFaithfulι.whiskeringRight
    _).map_preimage _

/-- Component characterization of `singleFunctorIsoCompQ` after applying
`DerivedCategory.Plus.ι`. -/
@[reassoc]
lemma ι_map_singleFunctorIsoCompQ_hom_app (n : ℤ) (X : C) :
    _root_.DerivedCategory.Plus.ι.map ((singleFunctorIsoCompQ C n).hom.app X) =
      (_root_.DerivedCategory.Plus.singleFunctorιIso C n).hom.app X ≫
        (_root_.DerivedCategory.singleFunctorIsoCompQ C n).hom.app X ≫
        (_root_.DerivedCategory.Plus.QCompιIso C).inv.app
          ((TauCeti.CochainComplex.Plus.singleFunctor C n).obj X) := by
  have h := NatTrans.congr_app (whiskerRight_singleFunctorIsoCompQ_hom_ι (C := C) n) X
  simp only [Functor.whiskerRight_app, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Category.comp_id, Category.id_comp] at h
  have h1 : _root_.DerivedCategory.Q.map
        ((TauCeti.CochainComplex.Plus.singleFunctorCompιIso C n).inv.app X) ≫
        (_root_.DerivedCategory.Plus.QCompιIso C).inv.app
          ((TauCeti.CochainComplex.Plus.singleFunctor C n).obj X) =
      (_root_.DerivedCategory.Plus.QCompιIso C).inv.app
        ((TauCeti.CochainComplex.Plus.singleFunctor C n).obj X) := by
    rw [TauCeti.CochainComplex.Plus.singleFunctorCompιIso_inv_app,
      _root_.DerivedCategory.Q.map_id, Category.id_comp]
  rw [h1] at h
  exact h

/-- The image of a mapping cone triangle in `CochainComplex.Plus C` under `DerivedCategory.Plus.Q`
is distinguished. -/
lemma mappingConeTriangle_distinguished {K L : _root_.CochainComplex.Plus C} (f : K ⟶ L) :
    _root_.DerivedCategory.Plus.Q.mapTriangle.obj
        (_root_.CochainComplex.Plus.mappingConeTriangle f) ∈
      distTriang (_root_.DerivedCategory.Plus C) := by
  rw [← _root_.DerivedCategory.Plus.ι.map_distinguished_iff]
  refine isomorphic_distinguished _
    (_root_.DerivedCategory.mappingCone_triangle_distinguished f.hom) _ ?_
  exact (Functor.mapTriangleCompIso _root_.DerivedCategory.Plus.Q
      _root_.DerivedCategory.Plus.ι).symm.app _ ≪≫
    (Functor.mapTriangleIso (_root_.DerivedCategory.Plus.QCompιIso C)).app _ ≪≫
    (Functor.mapTriangleCompIso (_root_.CochainComplex.Plus.ι C)
      _root_.DerivedCategory.Q).app _ ≪≫
    _root_.DerivedCategory.Q.mapTriangle.mapIso
      (_root_.CochainComplex.Plus.mappingConeTriangleιIso f)

end TauCeti.DerivedCategory.Plus
