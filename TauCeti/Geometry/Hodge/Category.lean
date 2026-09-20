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
`ModuleCat ℂ`. This category is the setting for formulating semisimplicity and splitting Hodge
projectors on rational Hodge substructures.

The implementation specializes the existing mixed-Hodge category: a pure object is sent to
`MixedHodgeStructure.ofPure`, and its morphisms and categorical structure are inherited from
`MixedHodgeStructureCat`.

## Main declarations

* `TauCeti.Hodge.PolarizableHodgeStructureCat`: polarizable rational Hodge structures of a fixed
  weight.
* `TauCeti.Hodge.PolarizableHodgeStructureCat.Hom`: ordinary rational Hodge morphisms.
* `TauCeti.Hodge.PolarizableHodgeStructureCat.mixed`: the fully faithful realization as mixed
  Hodge structures.
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

noncomputable instance : Category.{u} (PolarizableHodgeStructureCat.{u} n) :=
  inferInstanceAs <| Category (InducedCategory MixedHodgeStructureCat.{u} (asMixed (n := n)))

/-- An ordinary morphism of polarizable rational Hodge structures, implemented as a morphism of
the corresponding pure mixed Hodge structures. The concentrated weight condition is automatic. -/
abbrev Hom (X Y : PolarizableHodgeStructureCat.{u} n) : Type u :=
  X ⟶ Y

variable {X Y : PolarizableHodgeStructureCat.{u} n}

/-- A morphism of polarizable Hodge structures acts through its complexification. -/
noncomputable instance : CoeFun (Hom X Y) fun _ ↦ X.complexCarrier → Y.complexCarrier :=
  ⟨fun f ↦ f.hom.toLinearMap⟩

namespace Hom

/-- Construct a morphism from a rational linear map whose complexification preserves the Hodge
filtration. Preservation of the concentrated weight filtration is automatic. -/
noncomputable def mk (f : X.ratCarrier →ₗ[ℚ] Y.ratCarrier)
    (hf : ∀ p x, x ∈ X.hs.F p →
      rationalMapToComplex X.isBaseChangeRat X.isBaseChangeComplex
        Y.isBaseChangeRat Y.isBaseChangeComplex f x ∈ Y.hs.F p) : Hom X Y :=
  InducedCategory.homMk {
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
      simpa only [MixedHodgeStructure.ofPure_F] using hf }

/-- The constructor retains the supplied rational linear map. -/
@[simp]
theorem mk_toRatLinearMap (f : X.ratCarrier →ₗ[ℚ] Y.ratCarrier) (hf) :
    (mk f hf).hom.toRatLinearMap = f :=
  by simp [mk]

/-- Construct a morphism from a rational linear map whose complexification is a morphism of
the underlying pure Hodge structures. -/
noncomputable def ofIsMorphism (f : X.ratCarrier →ₗ[ℚ] Y.ratCarrier)
    (hf : HodgeStructureOn.IsMorphism X.hs Y.hs
      (rationalMapToComplex X.isBaseChangeRat X.isBaseChangeComplex
        Y.isBaseChangeRat Y.isBaseChangeComplex f)) : Hom X Y :=
  mk f fun p x hx ↦ hf.map_F_le p ⟨x, hx, rfl⟩

/-- The constructor from an unbundled Hodge morphism retains the supplied rational linear map. -/
@[simp]
theorem ofIsMorphism_toRatLinearMap (f : X.ratCarrier →ₗ[ℚ] Y.ratCarrier) (hf) :
    (ofIsMorphism f hf).hom.toRatLinearMap = f :=
  by simp [ofIsMorphism]

/-- A rational Hodge morphism is a morphism of the underlying pure Hodge structures on the
complexifications. -/
theorem isMorphism (f : Hom X Y) : HodgeStructureOn.IsMorphism X.hs Y.hs f.hom.toLinearMap where
  commutes_conj x := by
    simpa only [latticeConjugation_toEquiv_apply] using f.hom.commutes_conj x
  map_F_le := by
    simpa only [MixedHodgeStructure.ofPure_F] using f.hom.map_F_le

end Hom

/-- Two categorical morphisms agree if their rational maps agree. -/
@[ext]
theorem Hom.ext {X Y : PolarizableHodgeStructureCat.{u} n} {f g : X ⟶ Y}
    (h : f.hom.toRatLinearMap = g.hom.toRatLinearMap) : f = g :=
  InducedCategory.hom_ext (MixedHodgeStructure.Hom.ext (LinearMap.congr_fun h))

/-- The categorical identity has the identity rational linear map. -/
@[simp]
theorem id_toRatLinearMap (X : PolarizableHodgeStructureCat.{u} n) :
    (𝟙 X : X ⟶ X).hom.toRatLinearMap = LinearMap.id :=
  MixedHodgeStructureCat.id_toRatLinearMap X.asMixed

/-- Categorical composition is composition of the underlying rational linear maps. -/
@[simp]
theorem comp_toRatLinearMap {X Y Z : PolarizableHodgeStructureCat.{u} n}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom.toRatLinearMap = g.hom.toRatLinearMap ∘ₗ f.hom.toRatLinearMap :=
  MixedHodgeStructureCat.comp_toRatLinearMap f.hom g.hom

/-- The identity morphism has the identity complex linear map. -/
@[simp]
theorem id_toLinearMap (X : PolarizableHodgeStructureCat.{u} n) :
    (𝟙 X : X ⟶ X).hom.toLinearMap = LinearMap.id :=
  MixedHodgeStructureCat.id_toLinearMap X.asMixed

/-- Composition of categorical morphisms is composition of their complex linear maps. -/
@[simp]
theorem comp_toLinearMap {X Y Z : PolarizableHodgeStructureCat.{u} n}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom.toLinearMap = g.hom.toLinearMap ∘ₗ f.hom.toLinearMap :=
  MixedHodgeStructureCat.comp_toLinearMap f.hom g.hom

noncomputable instance : Preadditive (PolarizableHodgeStructureCat.{u} n) :=
  inferInstanceAs <| Preadditive (InducedCategory MixedHodgeStructureCat.{u} (asMixed (n := n)))

noncomputable instance : Linear ℚ (PolarizableHodgeStructureCat.{u} n) :=
  inferInstanceAs <| Linear ℚ (InducedCategory MixedHodgeStructureCat.{u} (asMixed (n := n)))

/-- The zero morphism has the zero rational linear map underneath. -/
@[simp]
theorem zero_toRatLinearMap {X Y : PolarizableHodgeStructureCat.{u} n} :
    (0 : X ⟶ Y).hom.toRatLinearMap = 0 :=
  MixedHodgeStructure.Hom.zero_toRatLinearMap

/-- Addition of morphisms is addition of their underlying rational linear maps. -/
@[simp]
theorem add_toRatLinearMap {X Y : PolarizableHodgeStructureCat.{u} n} (f g : X ⟶ Y) :
    (f + g).hom.toRatLinearMap = f.hom.toRatLinearMap + g.hom.toRatLinearMap :=
  MixedHodgeStructure.Hom.add_toRatLinearMap f.hom g.hom

/-- Rational scalar multiplication passes to the underlying rational linear map. -/
@[simp]
theorem smul_toRatLinearMap {X Y : PolarizableHodgeStructureCat.{u} n} (q : ℚ) (f : X ⟶ Y) :
    (q • f).hom.toRatLinearMap = q • f.hom.toRatLinearMap :=
  MixedHodgeStructure.Hom.smul_toRatLinearMap q f.hom

/-- The zero morphism has the zero complex linear map underneath. -/
@[simp]
theorem zero_toLinearMap {X Y : PolarizableHodgeStructureCat.{u} n} :
    (0 : X ⟶ Y).hom.toLinearMap = 0 := by
  ext x
  exact MixedHodgeStructure.Hom.zero_apply x

/-- Addition of morphisms is addition of their underlying complex linear maps. -/
@[simp]
theorem add_toLinearMap {X Y : PolarizableHodgeStructureCat.{u} n} (f g : X ⟶ Y) :
    (f + g).hom.toLinearMap = f.hom.toLinearMap + g.hom.toLinearMap := by
  ext x
  exact MixedHodgeStructure.Hom.add_apply f.hom g.hom x

/-- Rational scalar multiplication passes to the underlying complex linear map. -/
@[simp]
theorem smul_toLinearMap {X Y : PolarizableHodgeStructureCat.{u} n} (q : ℚ) (f : X ⟶ Y) :
    (q • f).hom.toLinearMap = (q : ℂ) • f.hom.toLinearMap := by
  ext x
  exact MixedHodgeStructure.Hom.smul_apply q f.hom x

/-- Regard a polarizable pure Hodge structure as a mixed Hodge structure concentrated in its
weight. -/
noncomputable def mixed :
    PolarizableHodgeStructureCat.{u} n ⥤ MixedHodgeStructureCat.{u} :=
  inducedFunctor (asMixed (n := n))

/-- The mixed realization sends an object to its concentrated mixed Hodge structure. -/
@[simp]
theorem mixed_obj (X : PolarizableHodgeStructureCat.{u} n) : mixed.obj X = X.asMixed :=
  by rw [mixed, inducedFunctor_obj]

/-- The mixed realization sends a morphism to its underlying mixed-Hodge morphism, up to the
object equalities in `mixed_obj`. -/
theorem mixed_map_hom {X Y : PolarizableHodgeStructureCat.{u} n} (f : X ⟶ Y) :
    HEq (mixed.map f) f.hom := by
  rw [mixed]
  exact HEq.rfl

/-- The morphism formula for the mixed realization, with its source and target transported along
`mixed_obj`. -/
@[simp]
theorem mixed_map {X Y : PolarizableHodgeStructureCat.{u} n} (f : X ⟶ Y) :
    mixed.map f = eqToHom (mixed_obj X) ≫ f.hom ≫ eqToHom (mixed_obj Y).symm :=
  (conj_eqToHom_iff_heq _ _ (mixed_obj X) (mixed_obj Y)).2 HEq.rfl

noncomputable instance : (mixed (n := n)).Full :=
  inferInstanceAs (inducedFunctor (asMixed (n := n))).Full

noncomputable instance : (mixed (n := n)).Faithful :=
  inferInstanceAs (inducedFunctor (asMixed (n := n))).Faithful

noncomputable instance : (mixed (n := n)).Additive :=
  inferInstanceAs (inducedFunctor (asMixed (n := n))).Additive

noncomputable instance : (mixed (n := n)).Linear ℚ :=
  inferInstanceAs ((inducedFunctor (asMixed (n := n))).Linear ℚ)

/-- The rational realization, induced from the rational realization of mixed Hodge structures. -/
noncomputable def rational : PolarizableHodgeStructureCat.{u} n ⥤ ModuleCat.{u} ℚ :=
  mixed ⋙ MixedHodgeStructureCat.rational

/-- The rational realization sends an object to its rational vector space. -/
@[simp]
theorem rational_obj (X : PolarizableHodgeStructureCat.{u} n) : rational.obj X = X.rat :=
  by rw [rational, Functor.comp_obj, mixed_obj, MixedHodgeStructureCat.rational_obj]

/-- The rational realization sends a morphism to its underlying rational linear map, up to the
object equalities in `rational_obj`. -/
theorem rational_map_hom {X Y : PolarizableHodgeStructureCat.{u} n} (f : X ⟶ Y) :
    HEq (rational.map f).hom f.hom.toRatLinearMap := by
  rw [rational, Functor.comp_map]
  exact HEq.rfl

/-- The morphism formula for the rational realization, with its source and target transported
along `rational_obj`. -/
@[simp]
theorem rational_map {X Y : PolarizableHodgeStructureCat.{u} n} (f : X ⟶ Y) :
    rational.map f = eqToHom (rational_obj X) ≫ ModuleCat.ofHom f.hom.toRatLinearMap ≫
      eqToHom (rational_obj Y).symm :=
  (conj_eqToHom_iff_heq _ _ (rational_obj X) (rational_obj Y)).2 HEq.rfl

noncomputable instance : (rational (n := n)).Faithful :=
  inferInstanceAs ((mixed ⋙ MixedHodgeStructureCat.rational).Faithful)

noncomputable instance : (rational (n := n)).Additive :=
  inferInstanceAs ((mixed ⋙ MixedHodgeStructureCat.rational).Additive)

noncomputable instance : (rational (n := n)).Linear ℚ :=
  inferInstanceAs ((mixed ⋙ MixedHodgeStructureCat.rational).Linear ℚ)

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
theorem complex_map_hom {X Y : PolarizableHodgeStructureCat.{u} n} (f : X ⟶ Y) :
    HEq (complex.map f).hom f.hom.toLinearMap := by
  rw [complex, Functor.comp_map]
  exact HEq.rfl

/-- The morphism formula for the complex realization, with its source and target transported
along `complex_obj`. -/
@[simp]
theorem complex_map {X Y : PolarizableHodgeStructureCat.{u} n} (f : X ⟶ Y) :
    complex.map f = eqToHom (complex_obj X) ≫ ModuleCat.ofHom f.hom.toLinearMap ≫
      eqToHom (complex_obj Y).symm :=
  (conj_eqToHom_iff_heq _ _ (complex_obj X) (complex_obj Y)).2 HEq.rfl

noncomputable instance : (complex (n := n)).Additive :=
  inferInstanceAs ((mixed ⋙ MixedHodgeStructureCat.complex).Additive)

/-- The complex realization is rational-linear through the inclusion `ℚ → ℂ`. -/
noncomputable instance : (complex (n := n)).Linear ℚ :=
  inferInstanceAs ((mixed ⋙ MixedHodgeStructureCat.complex).Linear ℚ)

end PolarizableHodgeStructureCat

end TauCeti.Hodge
