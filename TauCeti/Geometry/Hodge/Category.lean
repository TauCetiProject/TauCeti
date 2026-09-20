/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Mixed.Category
public import TauCeti.Geometry.Hodge.Polarization

/-!
# The category of polarizable rational Hodge structures

This file bundles polarizable pure Hodge structures of a fixed weight whose integral, rational,
and complex models live in one universe. Morphisms are rational linear maps whose
complexifications preserve the Hodge filtration. Thus the polarization is a property of an object,
not chosen data, and morphisms are ordinary Hodge morphisms rather than isometries.

The resulting category is preadditive and `ℚ`-linear. Its rational realization is a faithful
`ℚ`-linear functor to `ModuleCat ℚ`, and its complex realization is a `ℚ`-linear functor to
`ModuleCat ℂ`. This is the intended categorical setting for the future semisimplicity theorem,
in which Hodge projectors will split rational Hodge substructures as objects of this category.

The implementation specializes the existing mixed-Hodge category: a pure object is sent to
`MixedHodgeStructure.ofPure`, and its morphisms and categorical structure are inherited from
`MixedHodgeStructureCat`.

## Main declarations

* `TauCeti.Hodge.PolarizableHodgeStructureCat`: polarizable rational Hodge structures of a fixed
  weight.
* `TauCeti.Hodge.PolarizableHodgeStructureCat.Hom`: ordinary rational Hodge morphisms.
* `TauCeti.Hodge.PolarizableHodgeStructureCat.mixed`: the faithful realization as mixed Hodge
  structures.
* `TauCeti.Hodge.PolarizableHodgeStructureCat.rational`: the faithful rational realization.
* `TauCeti.Hodge.PolarizableHodgeStructureCat.complex`: the complex realization.

## References

The formal construction specializes `TauCeti.Geometry.Hodge.Mixed.Category`, in particular
`TauCeti.Hodge.MixedHodgeStructureCat`. For the mathematics, see Voisin, *Hodge Theory and Complex
Algebraic Geometry I*, §7.1.2, and Peters--Steenbrink, *Mixed Hodge Structures*, §2.
-/

public section

namespace TauCeti.Hodge

open CategoryTheory
open scoped ModuleCat.Algebra

universe u

/-- The category of finite-dimensional polarizable rational Hodge structures of weight `n`, with
integral, rational, and complex models in `Type u`.

The integral model is a finitely generated free lattice and determines the conjugation on the
complexification. The rational model is the carrier on which morphisms are defined. Polarizability
is retained only as a property, so no particular polarizing form is part of an object. -/
structure PolarizableHodgeStructureCat (n : ℤ) where
  /-- The integral lattice underlying the Hodge structure. -/
  intCarrier : Type u
  /-- The rational vector space underlying the Hodge structure. -/
  ratCarrier : Type u
  /-- The complex vector space underlying the Hodge structure. -/
  complexCarrier : Type u
  /-- The additive group structure on the integral lattice. -/
  [intAddCommGroup : AddCommGroup intCarrier]
  /-- The integral lattice is free. -/
  [intFree : Module.Free ℤ intCarrier]
  /-- The integral lattice is finitely generated. -/
  [intFinite : Module.Finite ℤ intCarrier]
  /-- The additive group structure on the rational carrier. -/
  [ratAddCommGroup : AddCommGroup ratCarrier]
  /-- The rational module structure. -/
  [ratModule : Module ℚ ratCarrier]
  /-- The rational carrier is finite-dimensional. -/
  [ratFinite : Module.Finite ℚ ratCarrier]
  /-- The additive group structure on the complex carrier. -/
  [complexAddCommGroup : AddCommGroup complexCarrier]
  /-- The complex module structure. -/
  [complexModule : Module ℂ complexCarrier]
  /-- The structure map from the integral lattice to the rational model. -/
  toRat : intCarrier →ₗ[ℤ] ratCarrier
  /-- The structure map from the integral lattice to the complex model. -/
  toComplex : intCarrier →ₗ[ℤ] complexCarrier
  /-- The rational model is a base change of the integral lattice. -/
  isBaseChangeRat : IsBaseChange ℚ toRat
  /-- The complex model is a base change of the integral lattice. -/
  isBaseChangeComplex : IsBaseChange ℂ toComplex
  /-- The pure Hodge structure on the complexification. -/
  hs : HodgeStructure isBaseChangeComplex n
  /-- The Hodge structure admits a polarization. -/
  isPolarizable : IsPolarizable isBaseChangeComplex hs

namespace PolarizableHodgeStructureCat

attribute [instance] PolarizableHodgeStructureCat.intAddCommGroup
  PolarizableHodgeStructureCat.intFree PolarizableHodgeStructureCat.intFinite
  PolarizableHodgeStructureCat.ratAddCommGroup PolarizableHodgeStructureCat.ratModule
  PolarizableHodgeStructureCat.ratFinite PolarizableHodgeStructureCat.complexAddCommGroup
  PolarizableHodgeStructureCat.complexModule

variable {n : ℤ}

/-- Bundle a finite-dimensional polarizable rational Hodge structure as an object. -/
abbrev of {Vℤ Vℚ Vℂ : Type u} [AddCommGroup Vℤ] [Module.Free ℤ Vℤ] [Module.Finite ℤ Vℤ]
    [AddCommGroup Vℚ] [Module ℚ Vℚ] [Module.Finite ℚ Vℚ] [AddCommGroup Vℂ] [Module ℂ Vℂ]
    {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}
    (hℚ : IsBaseChange ℚ ιℚ) (hℂ : IsBaseChange ℂ ιℂ)
    (hs : HodgeStructure hℂ n) (hpol : IsPolarizable hℂ hs) :
    PolarizableHodgeStructureCat.{u} n :=
  ⟨Vℤ, Vℚ, Vℂ, ιℚ, ιℂ, hℚ, hℂ, hs, hpol⟩

/-- The rational vector space underlying a polarizable rational Hodge structure. -/
abbrev rat (X : PolarizableHodgeStructureCat.{u} n) : ModuleCat.{u} ℚ :=
  ModuleCat.of ℚ X.ratCarrier

/-- The complex vector space underlying a polarizable rational Hodge structure. -/
abbrev complexSpace (X : PolarizableHodgeStructureCat.{u} n) : ModuleCat.{u} ℂ :=
  ModuleCat.of ℂ X.complexCarrier

/-- A polarizable pure Hodge structure regarded as a mixed Hodge structure concentrated in its
weight. -/
noncomputable abbrev asMixed (X : PolarizableHodgeStructureCat.{u} n) :
    MixedHodgeStructureCat.{u} :=
  MixedHodgeStructureCat.of X.isBaseChangeRat X.isBaseChangeComplex
    (MixedHodgeStructure.ofPure X.isBaseChangeRat X.isBaseChangeComplex X.hs)

/-- An ordinary morphism of polarizable rational Hodge structures, implemented as a morphism of
the corresponding pure mixed Hodge structures. The concentrated weight condition is automatic. -/
abbrev Hom (X Y : PolarizableHodgeStructureCat.{u} n) :=
  MixedHodgeStructure.Hom X.asMixed.hs Y.asMixed.hs

namespace Hom

variable {X Y : PolarizableHodgeStructureCat.{u} n}

/-- Construct a morphism from a rational linear map whose complexification preserves the Hodge
filtration. Preservation of the concentrated weight filtration is automatic. -/
noncomputable def mk (f : X.ratCarrier →ₗ[ℚ] Y.ratCarrier)
    (hf : ∀ p x, x ∈ X.hs.F p →
      rationalMapToComplex X.isBaseChangeRat X.isBaseChangeComplex
        Y.isBaseChangeRat Y.isBaseChangeComplex f x ∈ Y.hs.F p) : Hom X Y where
  toRatLinearMap := f
  map_mem_WQ := by
    intro k x hx
    by_cases hk : n ≤ k
    · rw [MixedHodgeStructure.ofPure_WQ, concentratedWeightFiltration_of_le hk]
      exact Submodule.mem_top
    · rw [MixedHodgeStructure.ofPure_WQ,
        concentratedWeightFiltration_of_lt (lt_of_not_ge hk)] at hx
      subst x
      simpa only [map_zero, MixedHodgeStructure.ofPure_WQ] using
        (concentratedWeightFiltration Y.ratCarrier n k).zero_mem
  map_mem_F := by
    simpa only [MixedHodgeStructure.ofPure_F] using hf

/-- The constructor retains the supplied rational linear map. -/
@[simp]
theorem mk_toRatLinearMap (f : X.ratCarrier →ₗ[ℚ] Y.ratCarrier) (hf) :
    (mk f hf).toRatLinearMap = f :=
  by rw [mk]

/-- A rational Hodge morphism is a morphism of the underlying pure Hodge structures on the
complexifications. -/
theorem isMorphism (f : Hom X Y) : HodgeStructureOn.IsMorphism X.hs Y.hs f.toLinearMap where
  commutes_conj x := by
    simpa only [latticeConjugation_toEquiv_apply] using f.commutes_conj x
  map_F_le := by
    simpa only [MixedHodgeStructure.ofPure_F] using f.map_F_le

end Hom

noncomputable instance : Category.{u} (PolarizableHodgeStructureCat.{u} n) where
  Hom := Hom
  id X := MixedHodgeStructure.Hom.id X.asMixed.hs
  comp f g := g.comp f

/-- Two categorical morphisms agree if their rational maps agree. -/
@[ext]
theorem hom_ext {X Y : PolarizableHodgeStructureCat.{u} n} {f g : X ⟶ Y}
    (h : f.toRatLinearMap = g.toRatLinearMap) : f = g :=
  MixedHodgeStructure.Hom.ext (LinearMap.congr_fun h)

/-- The categorical identity has the identity rational linear map. -/
@[simp]
theorem id_toRatLinearMap (X : PolarizableHodgeStructureCat.{u} n) :
    (MixedHodgeStructure.Hom.toRatLinearMap (𝟙 X)) = LinearMap.id :=
  MixedHodgeStructure.Hom.id_toRatLinearMap

/-- Categorical composition is composition of the underlying rational linear maps. -/
@[simp]
theorem comp_toRatLinearMap {X Y Z : PolarizableHodgeStructureCat.{u} n}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toRatLinearMap = g.toRatLinearMap ∘ₗ f.toRatLinearMap :=
  MixedHodgeStructure.Hom.comp_toRatLinearMap g f

/-- The identity morphism has the identity complex linear map. -/
@[simp]
theorem id_toLinearMap (X : PolarizableHodgeStructureCat.{u} n) :
    MixedHodgeStructure.Hom.toLinearMap (𝟙 X) = LinearMap.id :=
  MixedHodgeStructureCat.id_toLinearMap X.asMixed

/-- Composition of categorical morphisms is composition of their complex linear maps. -/
@[simp]
theorem comp_toLinearMap {X Y Z : PolarizableHodgeStructureCat.{u} n}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    MixedHodgeStructure.Hom.toLinearMap (f ≫ g) = g.toLinearMap ∘ₗ f.toLinearMap :=
  MixedHodgeStructureCat.comp_toLinearMap f g

noncomputable instance : Preadditive (PolarizableHodgeStructureCat.{u} n) where
  homGroup X Y := inferInstanceAs (AddCommGroup (Hom X Y))
  add_comp _ _ _ f g h := MixedHodgeStructure.Hom.comp_add h f g
  comp_add _ _ _ f g h := MixedHodgeStructure.Hom.add_comp g h f

noncomputable instance : Linear ℚ (PolarizableHodgeStructureCat.{u} n) where
  homModule X Y := inferInstanceAs (Module ℚ (Hom X Y))
  smul_comp _ _ _ q f g := MixedHodgeStructure.Hom.comp_smul g q f
  comp_smul _ _ _ f q g := MixedHodgeStructure.Hom.smul_comp q g f

/-- Regard a polarizable pure Hodge structure as a mixed Hodge structure concentrated in its
weight. -/
noncomputable def mixed :
    PolarizableHodgeStructureCat.{u} n ⥤ MixedHodgeStructureCat.{u} where
  obj X := X.asMixed
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The mixed realization sends an object to its concentrated mixed Hodge structure. -/
@[simp]
theorem mixed_obj (X : PolarizableHodgeStructureCat.{u} n) : mixed.obj X = X.asMixed := by
  rw [mixed]

noncomputable instance : (mixed (n := n)).Faithful where
  map_injective {_ _} _ _ h := h

noncomputable instance : (mixed (n := n)).Additive where
  map_add := by intros; rfl

noncomputable instance : (mixed (n := n)).Linear ℚ where
  map_smul := by intros; rfl

/-- The rational realization, induced from the rational realization of mixed Hodge structures. -/
noncomputable def rational : PolarizableHodgeStructureCat.{u} n ⥤ ModuleCat.{u} ℚ :=
  mixed ⋙ MixedHodgeStructureCat.rational

/-- The rational realization sends an object to its rational vector space. -/
@[simp]
theorem rational_obj (X : PolarizableHodgeStructureCat.{u} n) : rational.obj X = X.rat :=
  by rw [rational, Functor.comp_obj, mixed_obj, MixedHodgeStructureCat.rational_obj]

/-- The rational realization sends a morphism to its underlying rational linear map, up to the
object equalities in `rational_obj`. -/
@[simp]
theorem rational_map_hom {X Y : PolarizableHodgeStructureCat.{u} n} (f : X ⟶ Y) :
    HEq (rational.map f).hom f.toRatLinearMap := by
  rw [rational, Functor.comp_map]
  exact HEq.rfl

/-- The morphism formula for the rational realization, with its source and target transported
along `rational_obj`. -/
@[simp]
theorem rational_map {X Y : PolarizableHodgeStructureCat.{u} n} (f : X ⟶ Y) :
    rational.map f = eqToHom (rational_obj X) ≫ ModuleCat.ofHom f.toRatLinearMap ≫
      eqToHom (rational_obj Y).symm :=
  (conj_eqToHom_iff_heq _ _ (rational_obj X) (rational_obj Y)).2 HEq.rfl

noncomputable instance : (rational (n := n)).Faithful := by
  change (mixed ⋙ MixedHodgeStructureCat.rational).Faithful
  infer_instance

noncomputable instance : (rational (n := n)).Additive := by
  change (mixed ⋙ MixedHodgeStructureCat.rational).Additive
  infer_instance

noncomputable instance : (rational (n := n)).Linear ℚ := by
  change (mixed ⋙ MixedHodgeStructureCat.rational).Linear ℚ
  infer_instance

/-- The complex realization, induced from the complex realization of mixed Hodge structures. -/
noncomputable def complex : PolarizableHodgeStructureCat.{u} n ⥤ ModuleCat.{u} ℂ :=
  mixed ⋙ MixedHodgeStructureCat.complex

/-- The complex realization sends an object to its complex vector space. -/
@[simp]
theorem complex_obj (X : PolarizableHodgeStructureCat.{u} n) :
    complex.obj X = X.complexSpace :=
  by rw [complex, Functor.comp_obj, mixed_obj, MixedHodgeStructureCat.complex_obj]

/-- The complex realization sends a morphism to its derived complex linear map, up to the object
equalities in `complex_obj`. -/
@[simp]
theorem complex_map_hom {X Y : PolarizableHodgeStructureCat.{u} n} (f : X ⟶ Y) :
    HEq (complex.map f).hom f.toLinearMap := by
  rw [complex, Functor.comp_map]
  exact HEq.rfl

/-- The morphism formula for the complex realization, with its source and target transported
along `complex_obj`. -/
@[simp]
theorem complex_map {X Y : PolarizableHodgeStructureCat.{u} n} (f : X ⟶ Y) :
    complex.map f = eqToHom (complex_obj X) ≫ ModuleCat.ofHom f.toLinearMap ≫
      eqToHom (complex_obj Y).symm :=
  (conj_eqToHom_iff_heq _ _ (complex_obj X) (complex_obj Y)).2 HEq.rfl

noncomputable instance : (complex (n := n)).Additive := by
  change (mixed ⋙ MixedHodgeStructureCat.complex).Additive
  infer_instance

/-- The complex realization is rational-linear through the inclusion `ℚ → ℂ`. -/
noncomputable instance : (complex (n := n)).Linear ℚ := by
  change (mixed ⋙ MixedHodgeStructureCat.complex).Linear ℚ
  infer_instance

end PolarizableHodgeStructureCat

end TauCeti.Hodge
