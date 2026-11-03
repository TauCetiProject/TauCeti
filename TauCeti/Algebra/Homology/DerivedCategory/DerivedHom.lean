/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import TauCeti.Algebra.Homology.DerivedCategory.KInjective
public import TauCeti.Algebra.Homology.LinearHomComplex.Cohomology
public import TauCeti.Algebra.Homology.LinearHomComplex.Homotopy

/-!
# The derived Hom complex of unbounded complexes

Let `C` be an `R`-linear abelian category in which every cochain complex, with no boundedness
assumption, has a K-injective replacement. The derived Hom complex
`TauCeti.derivedHom R C : D(C)ᵒᵖ ⥤ D(C) ⥤ D(R)` sends `L` and `M` to the `R`-linear Hom complex
`CochainComplex.linearHomComplex R I J` between their K-injective replacements `I` and `J`,
viewed in the derived category of `R`-modules. It is functorial in both variables because the
replacement functor `TauCeti.kInjectiveReplacement` is, and because the linear Hom complex
descends to homotopy categories (`TauCeti.linearHomComplexHomotopyFunctor`).

Its cohomology computes morphisms in the derived category: for every integer `n` the
`n`-th cohomology of `RHom(L, M)` is the `R`-module of morphisms `L ⟶ M⟦n⟧` in `D(C)`
(`TauCeti.derivedHomHomologyLinearEquiv`), naturally in `L` and in `M`. No boundedness of `L` or
`M` is assumed. The main example is `C = ModuleCat A` for a commutative ring `A` and `R = A`:
module categories have K-injective resolutions (`TauCeti.Algebra.Homology.ModuleCat.KInjective`),
and `derivedHom A (ModuleCat A)` is then the derived Hom `RHom_A(L, M)` in `D(A)`.

## Main definitions

* `TauCeti.derivedHom`: the derived Hom bifunctor.
* `TauCeti.derivedHomHomologyLinearEquiv`: the identification of `Hⁿ RHom(L, M)` with
  `L ⟶ M⟦n⟧`.

## Main results

* `TauCeti.derivedHomHomologyLinearEquiv_naturality_left` and
  `TauCeti.derivedHomHomologyLinearEquiv_naturality_right`: the identification is natural in
  both variables.

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154.
* [Stacks Project, Tag 0A5W](https://stacks.math.columbia.edu/tag/0A5W) and
  [Stacks Project, Tag 0A65](https://stacks.math.columbia.edu/tag/0A65).
-/

public section

noncomputable section

open CategoryTheory DerivedCategory CochainComplex.HomComplex Opposite

namespace TauCeti

universe t w' w v u

variable (R : Type w) [Ring R] (C : Type u) [Category.{v} C] [Abelian C] [Linear R C]
  [HasKInjectiveResolutions C] [HasDerivedCategory.{t} C]
  [HasDerivedCategory.{w'} (ModuleCat.{v} R)]

/-- The derived Hom complex `RHom(L, M)` of objects `L` and `M` of the derived category of `C`,
an object of the derived category of `R`-modules. It is the `R`-linear Hom complex between the
K-injective replacements of `L` and `M`. -/
-- Expose the composite so that its values on objects and morphisms have computed types.
@[expose]
def derivedHom :
    (DerivedCategory C)ᵒᵖ ⥤ DerivedCategory C ⥤ DerivedCategory (ModuleCat.{v} R) :=
  (kInjectiveReplacement C).op ⋙ linearHomComplexHomotopyFunctor R C ⋙
    (Functor.whiskeringLeft _ _ _).obj (kInjectiveReplacement C) ⋙
      (Functor.whiskeringRight _ _ _).obj Qh

variable {C}

/-- The derived Hom complex is the linear Hom complex between the K-injective replacements. -/
lemma derivedHom_obj_obj (L M : DerivedCategory C) :
    ((derivedHom R C).obj (op L)).obj M =
      Qh.obj ((HomotopyCategory.quotient _ _).obj (CochainComplex.linearHomComplex R
        ((kInjectiveReplacement C).obj L).as ((kInjectiveReplacement C).obj M).as)) :=
  (rfl)

/-- The derived Hom complex acts on morphisms of its second variable by postcomposition with the
induced map of K-injective replacements. -/
lemma derivedHom_obj_map (L : DerivedCategory C) {M M' : DerivedCategory C} (g : M ⟶ M') :
    ((derivedHom R C).obj (op L)).map g =
      Qh.map (((linearHomComplexHomotopyFunctor R C).obj
        (op ((kInjectiveReplacement C).obj L))).map ((kInjectiveReplacement C).map g)) :=
  (rfl)

/-- The derived Hom complex acts on morphisms of its first variable by precomposition with the
induced map of K-injective replacements. -/
lemma derivedHom_map_app {L L' : DerivedCategory C} (f : L' ⟶ L) (M : DerivedCategory C) :
    ((derivedHom R C).map f.op).app M =
      Qh.map (((linearHomComplexHomotopyFunctor R C).map
        ((kInjectiveReplacement C).map f).op).app ((kInjectiveReplacement C).obj M)) :=
  (rfl)

/-- The cohomology of the derived Hom complex, identified with the cohomology of the Hom complex
of the K-injective replacements. The identification is the identity; stating its type lets the
composite below be assembled from equivalences whose types match syntactically. -/
private def homologyDerivedHomIso (L M : DerivedCategory C) (n : ℤ) :
    (homologyFunctor (ModuleCat.{v} R) n).obj (((derivedHom R C).obj (op L)).obj M) ≅
      (homologyFunctor (ModuleCat.{v} R) n).obj (Qh.obj ((HomotopyCategory.quotient _ _).obj
        (CochainComplex.linearHomComplex R
          ((kInjectiveReplacement C).obj L).as ((kInjectiveReplacement C).obj M).as))) :=
  Iso.refl _

/-- The shift of the K-injective replacement of `M` represents `M⟦n⟧`. -/
private def shiftKInjectiveReplacementIso (M : DerivedCategory C) (n : ℤ) :
    Qh.obj ((HomotopyCategory.quotient C _).obj (((kInjectiveReplacement C).obj M).as⟦n⟧)) ≅
      M⟦n⟧ :=
  Qh.mapIso (((HomotopyCategory.quotient C _).commShiftIso n).app _) ≪≫
    (Qh.commShiftIso n).app _ ≪≫
      (shiftFunctor _ n).mapIso ((asIso (kInjectiveReplacementAdjunction C).counit).app M)

private lemma shiftKInjectiveReplacementIso_naturality {M M' : DerivedCategory C} (g : M ⟶ M')
    (g' : ((kInjectiveReplacement C).obj M).as ⟶ ((kInjectiveReplacement C).obj M').as)
    (hg' : (HomotopyCategory.quotient C _).map g' = (kInjectiveReplacement C).map g) (n : ℤ) :
    Qh.map ((HomotopyCategory.quotient C _).map (g'⟦n⟧')) ≫
        (shiftKInjectiveReplacementIso M' n).hom =
      (shiftKInjectiveReplacementIso M n).hom ≫ g⟦n⟧' := by
  have h : Qh.map ((HomotopyCategory.quotient C _).map g') ≫
      (kInjectiveReplacementAdjunction C).counit.app M' =
        (kInjectiveReplacementAdjunction C).counit.app M ≫ g := by
    rw [hg']
    exact (kInjectiveReplacementAdjunction C).counit.naturality g
  rw [shiftKInjectiveReplacementIso, shiftKInjectiveReplacementIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  rw [← Qh.map_comp_assoc, Functor.commShiftIso_hom_naturality, Qh.map_comp_assoc,
    Functor.commShiftIso_hom_naturality_assoc]
  congr 2
  exact ((shiftFunctor _ n).map_comp _ _).symm.trans
    ((congrArg (shiftFunctor _ n).map h).trans ((shiftFunctor _ n).map_comp _ _))

private lemma counit_inv_naturality {L L' : DerivedCategory C} (f : L' ⟶ L)
    (f' : ((kInjectiveReplacement C).obj L').as ⟶ ((kInjectiveReplacement C).obj L).as)
    (hf' : (HomotopyCategory.quotient C _).map f' = (kInjectiveReplacement C).map f) :
    ((asIso (kInjectiveReplacementAdjunction C).counit).app L').inv ≫
        Qh.map ((HomotopyCategory.quotient C _).map f') =
      f ≫ ((asIso (kInjectiveReplacementAdjunction C).counit).app L).inv := by
  rw [hf']
  exact ((asIso (kInjectiveReplacementAdjunction C).counit).inv.naturality f).symm

/-- The `n`-th cohomology of the derived Hom complex `RHom(L, M)` is the `R`-module of morphisms
`L ⟶ M⟦n⟧` in the derived category. -/
def derivedHomHomologyLinearEquiv (L M : DerivedCategory C) (n : ℤ) :
    (homologyFunctor (ModuleCat.{v} R) n).obj (((derivedHom R C).obj (op L)).obj M) ≃ₗ[R]
      (L ⟶ M⟦n⟧) :=
  (homologyDerivedHomIso R L M n ≪≫ (Functor.isoWhiskerLeft _ (homologyFunctorFactorsh _ n) ≪≫
    HomotopyCategory.homologyFunctorFactors _ _ n).app _).toLinearEquiv ≪≫ₗ
    linearHomComplexHomologyLinearEquiv R ((kInjectiveReplacement C).obj L).as
      ((kInjectiveReplacement C).obj M).as n ≪≫ₗ
    LinearEquiv.ofBijective (Qh.mapLinearMap R)
      (CochainComplex.IsKInjective.Qh_map_bijective _ _) ≪≫ₗ
    Linear.homCongr R ((asIso (kInjectiveReplacementAdjunction C).counit).app L)
      (shiftKInjectiveReplacementIso M n)

/-- The identification of the cohomology of `RHom(L, M)` with morphisms `L ⟶ M⟦n⟧` is natural in
`M`: a morphism `g : M ⟶ M'` acts by composition with `g⟦n⟧`. -/
theorem derivedHomHomologyLinearEquiv_naturality_right (L : DerivedCategory C)
    {M M' : DerivedCategory C} (g : M ⟶ M') (n : ℤ)
    (z : (homologyFunctor (ModuleCat.{v} R) n).obj (((derivedHom R C).obj (op L)).obj M)) :
    derivedHomHomologyLinearEquiv R L M' n
        (((homologyFunctor _ n).map (((derivedHom R C).obj (op L)).map g)).hom z) =
      derivedHomHomologyLinearEquiv R L M n z ≫ g⟦n⟧' := by
  obtain ⟨g', hg'⟩ : ∃ g' : ((kInjectiveReplacement C).obj M).as ⟶
      ((kInjectiveReplacement C).obj M').as,
        (HomotopyCategory.quotient C _).map g' = (kInjectiveReplacement C).map g :=
    (HomotopyCategory.quotient C _).map_surjective _
  have hmap : ((derivedHom R C).obj (op L)).map g = Qh.map ((HomotopyCategory.quotient _ _).map
      (linearHomComplexPostcomp R ((kInjectiveReplacement C).obj L).as g')) := by
    rw [derivedHom_obj_map, ← hg']
    rfl
  let I := ((kInjectiveReplacement C).obj L).as
  let J := ((kInjectiveReplacement C).obj M).as
  let J' := ((kInjectiveReplacement C).obj M').as
  let Φ := linearHomComplexPostcomp R I g'
  let e := Functor.isoWhiskerLeft (HomotopyCategory.quotient _ _)
    (homologyFunctorFactorsh (ModuleCat.{v} R) n) ≪≫ HomotopyCategory.homologyFunctorFactors _ _ n
  let w := (e.hom.app (CochainComplex.linearHomComplex R I J)).hom z
  have hz : (e.hom.app (CochainComplex.linearHomComplex R I J')).hom
      (((homologyFunctor _ n).map (Qh.map ((HomotopyCategory.quotient _ _).map Φ))).hom z) =
        (HomologicalComplex.homologyMap Φ n).hom w :=
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (e.hom.naturality Φ)) z
  have hcomp (a : (HomotopyCategory.quotient C _).obj I ⟶
      (HomotopyCategory.quotient C _).obj (J⟦n⟧)) :
      (((asIso (kInjectiveReplacementAdjunction C).counit).app L).inv ≫
        Qh.map (a ≫ (HomotopyCategory.quotient C _).map (g'⟦n⟧'))) ≫
          (shiftKInjectiveReplacementIso M' n).hom =
      ((((asIso (kInjectiveReplacementAdjunction C).counit).app L).inv ≫ Qh.map a) ≫
        (shiftKInjectiveReplacementIso M n).hom) ≫ g⟦n⟧' := by
    -- The objects `(kInjectiveReplacement C).obj M).as` defeat `rw`, so the associativity
    -- steps are given as terms.
    calc _ = ((asIso (kInjectiveReplacementAdjunction C).counit).app L).inv ≫ Qh.map a ≫
          Qh.map ((HomotopyCategory.quotient C _).map (g'⟦n⟧')) ≫
            (shiftKInjectiveReplacementIso M' n).hom :=
          (Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
            ((congrArg (· ≫ _) (Qh.map_comp _ _)).trans (Category.assoc _ _ _)))
      _ = _ := (congrArg (fun t ↦ _ ≫ Qh.map a ≫ t)
            (shiftKInjectiveReplacementIso_naturality g g' hg' n)).trans
          ((Category.assoc _ _ _).trans (Category.assoc _ _ _)).symm
  rw [derivedHomHomologyLinearEquiv, derivedHomHomologyLinearEquiv, hmap]
  exact (congrArg (fun t ↦ (((asIso (kInjectiveReplacementAdjunction C).counit).app L).inv ≫
    Qh.map (linearHomComplexHomologyLinearEquiv R I J' n t)) ≫
      (shiftKInjectiveReplacementIso M' n).hom) hz).trans
    ((congrArg (fun t ↦ (((asIso (kInjectiveReplacementAdjunction C).counit).app L).inv ≫
      Qh.map t) ≫ (shiftKInjectiveReplacementIso M' n).hom)
        (linearHomComplexHomologyLinearEquiv_homologyMap_postcomp R g' w)).trans
      (hcomp _))

/-- The identification of the cohomology of `RHom(L, M)` with morphisms `L ⟶ M⟦n⟧` is natural in
`L`: a morphism `f : L' ⟶ L` acts by precomposition with `f`. -/
theorem derivedHomHomologyLinearEquiv_naturality_left {L L' : DerivedCategory C} (f : L' ⟶ L)
    (M : DerivedCategory C) (n : ℤ)
    (z : (homologyFunctor (ModuleCat.{v} R) n).obj (((derivedHom R C).obj (op L)).obj M)) :
    derivedHomHomologyLinearEquiv R L' M n
        (((homologyFunctor _ n).map (((derivedHom R C).map f.op).app M)).hom z) =
      f ≫ derivedHomHomologyLinearEquiv R L M n z := by
  obtain ⟨f', hf'⟩ : ∃ f' : ((kInjectiveReplacement C).obj L').as ⟶
      ((kInjectiveReplacement C).obj L).as,
        (HomotopyCategory.quotient C _).map f' = (kInjectiveReplacement C).map f :=
    (HomotopyCategory.quotient C _).map_surjective _
  have hmap : ((derivedHom R C).map f.op).app M = Qh.map ((HomotopyCategory.quotient _ _).map
      (linearHomComplexPrecomp R f' ((kInjectiveReplacement C).obj M).as)) := by
    rw [derivedHom_map_app, ← hf']
    rfl
  let I := ((kInjectiveReplacement C).obj L).as
  let I' := ((kInjectiveReplacement C).obj L').as
  let J := ((kInjectiveReplacement C).obj M).as
  let Φ := linearHomComplexPrecomp R f' J
  let e := Functor.isoWhiskerLeft (HomotopyCategory.quotient _ _)
    (homologyFunctorFactorsh (ModuleCat.{v} R) n) ≪≫ HomotopyCategory.homologyFunctorFactors _ _ n
  let w := (e.hom.app (CochainComplex.linearHomComplex R I J)).hom z
  have hz : (e.hom.app (CochainComplex.linearHomComplex R I' J)).hom
      (((homologyFunctor _ n).map (Qh.map ((HomotopyCategory.quotient _ _).map Φ))).hom z) =
        (HomologicalComplex.homologyMap Φ n).hom w :=
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (e.hom.naturality Φ)) z
  have hcomp (a : (HomotopyCategory.quotient C _).obj I ⟶
      (HomotopyCategory.quotient C _).obj (J⟦n⟧)) :
      (((asIso (kInjectiveReplacementAdjunction C).counit).app L').inv ≫
        Qh.map ((HomotopyCategory.quotient C _).map f' ≫ a)) ≫
          (shiftKInjectiveReplacementIso M n).hom =
      f ≫ (((asIso (kInjectiveReplacementAdjunction C).counit).app L).inv ≫ Qh.map a) ≫
        (shiftKInjectiveReplacementIso M n).hom :=
    -- The objects `(kInjectiveReplacement C).obj L).as` defeat `rw`, so the associativity
    -- steps are given as terms.
    (congrArg (fun t ↦ (_ ≫ t) ≫ _) (Qh.map_comp _ _)).trans
      ((congrArg (· ≫ _) ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ Qh.map a) (counit_inv_naturality f f' hf')))).trans
          ((congrArg (· ≫ _) (Category.assoc _ _ _)).trans (Category.assoc _ _ _)))
  rw [derivedHomHomologyLinearEquiv, derivedHomHomologyLinearEquiv, hmap]
  exact (congrArg (fun t ↦ (((asIso (kInjectiveReplacementAdjunction C).counit).app L').inv ≫
    Qh.map (linearHomComplexHomologyLinearEquiv R I' J n t)) ≫
      (shiftKInjectiveReplacementIso M n).hom) hz).trans
    ((congrArg (fun t ↦ (((asIso (kInjectiveReplacementAdjunction C).counit).app L').inv ≫
      Qh.map t) ≫ (shiftKInjectiveReplacementIso M n).hom)
        (linearHomComplexHomologyLinearEquiv_homologyMap_precomp R f' w)).trans
      (hcomp _))

end TauCeti
