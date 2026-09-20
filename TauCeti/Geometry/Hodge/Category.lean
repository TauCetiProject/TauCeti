/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import TauCeti.Geometry.Hodge.Morphism
public import TauCeti.Geometry.Hodge.Polarization

/-!
# The category of polarizable rational Hodge structures

This file bundles polarizable pure Hodge structures of a fixed weight whose rational and complex
models live in one universe. Morphisms are rational linear maps whose complexifications preserve
the Hodge filtration. Thus the polarization is a property of an object, not chosen data, and
morphisms are ordinary Hodge morphisms rather than isometries.

The resulting category is preadditive and `ℚ`-linear. Its rational realization is a faithful
`ℚ`-linear functor to `ModuleCat ℚ`, and its complex realization is a `ℚ`-linear functor to
`ModuleCat ℂ`. This is the categorical setting for semisimplicity: Hodge projectors split rational
Hodge substructures as objects of this category.

## Main declarations

* `TauCeti.Hodge.PolarizableHodgeStructureCat`: polarizable rational Hodge structures of a fixed
  weight.
* `TauCeti.Hodge.PolarizableHodgeStructureCat.Hom`: ordinary rational Hodge morphisms.
* `TauCeti.Hodge.PolarizableHodgeStructureCat.rational`: the faithful rational realization.
* `TauCeti.Hodge.PolarizableHodgeStructureCat.complex`: the complex realization.

## References

Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.1.2; Peters--Steenbrink,
*Mixed Hodge Structures*, §2.
-/

public section

namespace TauCeti.Hodge

open CategoryTheory
open scoped ModuleCat.Algebra

universe u

/-- The category of finite-dimensional polarizable rational Hodge structures of weight `n`, with
integral, rational, and complex models in `Type u`.

The integral model determines the conjugation on the complexification. The rational model is the
carrier on which morphisms are defined. Polarizability is retained only as a property, so no
particular polarizing form is part of an object. -/
structure PolarizableHodgeStructureCat (n : ℤ) where
  /-- The integral carrier underlying the Hodge structure. -/
  intCarrier : Type u
  /-- The rational vector space underlying the Hodge structure. -/
  ratCarrier : Type u
  /-- The complex vector space underlying the Hodge structure. -/
  complexCarrier : Type u
  /-- The additive group structure on the integral carrier. -/
  [intAddCommGroup : AddCommGroup intCarrier]
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
  /-- The structure map from the integral carrier to the rational model. -/
  toRat : intCarrier →ₗ[ℤ] ratCarrier
  /-- The structure map from the integral carrier to the complex model. -/
  toComplex : intCarrier →ₗ[ℤ] complexCarrier
  /-- The rational model is a base change of the integral carrier. -/
  isBaseChangeRat : IsBaseChange ℚ toRat
  /-- The complex model is a base change of the integral carrier. -/
  isBaseChangeComplex : IsBaseChange ℂ toComplex
  /-- The pure Hodge structure on the complexification. -/
  hs : HodgeStructure isBaseChangeComplex n
  /-- The Hodge structure admits a polarization. -/
  isPolarizable : IsPolarizable isBaseChangeComplex hs

namespace PolarizableHodgeStructureCat

attribute [instance] PolarizableHodgeStructureCat.intAddCommGroup
  PolarizableHodgeStructureCat.ratAddCommGroup PolarizableHodgeStructureCat.ratModule
  PolarizableHodgeStructureCat.ratFinite PolarizableHodgeStructureCat.complexAddCommGroup
  PolarizableHodgeStructureCat.complexModule

variable {n : ℤ}

/-- Bundle a finite-dimensional polarizable rational Hodge structure as an object. -/
abbrev of {Vℤ Vℚ Vℂ : Type u} [AddCommGroup Vℤ] [AddCommGroup Vℚ] [Module ℚ Vℚ]
    [Module.Finite ℚ Vℚ] [AddCommGroup Vℂ] [Module ℂ Vℂ]
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

/-- An ordinary morphism of polarizable rational Hodge structures: a rational linear map whose
complexification preserves the Hodge filtration. No compatibility with chosen polarizations is
required. -/
structure Hom (X Y : PolarizableHodgeStructureCat.{u} n) where
  /-- The rational linear map underlying the Hodge morphism. -/
  toRatLinearMap : X.ratCarrier →ₗ[ℚ] Y.ratCarrier
  /-- The complexification preserves each step of the Hodge filtration. -/
  map_mem_F : ∀ p x, x ∈ X.hs.F p →
    rationalMapToComplex X.isBaseChangeRat X.isBaseChangeComplex
      Y.isBaseChangeRat Y.isBaseChangeComplex toRatLinearMap x ∈ Y.hs.F p

namespace Hom

variable {X Y Z : PolarizableHodgeStructureCat.{u} n}

/-- The complex-linear map induced by a rational Hodge morphism. -/
noncomputable def toLinearMap (f : Hom X Y) : X.complexCarrier →ₗ[ℂ] Y.complexCarrier :=
  rationalMapToComplex X.isBaseChangeRat X.isBaseChangeComplex
    Y.isBaseChangeRat Y.isBaseChangeComplex f.toRatLinearMap

/-- A rational Hodge morphism acts on complex vectors through its complexification. -/
noncomputable instance : CoeFun (Hom X Y) fun _ ↦ X.complexCarrier → Y.complexCarrier :=
  ⟨fun f ↦ f.toLinearMap⟩

/-- The complex action of a rational Hodge morphism is the complexification of its rational map. -/
theorem toLinearMap_def (f : Hom X Y) :
    f.toLinearMap = rationalMapToComplex X.isBaseChangeRat X.isBaseChangeComplex
      Y.isBaseChangeRat Y.isBaseChangeComplex f.toRatLinearMap :=
  (rfl)

/-- A rational Hodge morphism acts on a pure tensor through its rational map. -/
@[simp]
theorem apply_rationalToComplexLinearEquiv_tmul (f : Hom X Y) (z : ℂ) (x : X.ratCarrier) :
    f (rationalToComplexLinearEquiv X.isBaseChangeRat X.isBaseChangeComplex (z ⊗ₜ[ℚ] x)) =
      rationalToComplexLinearEquiv Y.isBaseChangeRat Y.isBaseChangeComplex
        (z ⊗ₜ[ℚ] f.toRatLinearMap x) :=
  rationalMapToComplex_rationalToComplexLinearEquiv_tmul X.isBaseChangeRat X.isBaseChangeComplex
    Y.isBaseChangeRat Y.isBaseChangeComplex f.toRatLinearMap z x

/-- Two rational Hodge morphisms are equal when their rational linear maps agree. -/
@[ext]
theorem ext {f g : Hom X Y} (h : f.toRatLinearMap = g.toRatLinearMap) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      cases h
      rfl

/-- The complex action of a rational Hodge morphism commutes with lattice-induced conjugation. -/
@[simp]
theorem commutes_conj (f : Hom X Y) (x : X.complexCarrier) :
    f (latticeConj X.isBaseChangeComplex x) = latticeConj Y.isBaseChangeComplex (f x) :=
  rationalMapToComplex_commutes_conj X.isBaseChangeRat X.isBaseChangeComplex
    Y.isBaseChangeRat Y.isBaseChangeComplex f.toRatLinearMap x

/-- A rational Hodge morphism preserves each step of the Hodge filtration. -/
theorem map_F_le (f : Hom X Y) (p : ℤ) : (X.hs.F p).map f.toLinearMap ≤ Y.hs.F p := by
  rintro _ ⟨x, hx, rfl⟩
  exact f.map_mem_F p x hx

/-- A rational Hodge morphism is a morphism of the underlying pure Hodge structures on the
complexifications. -/
theorem isMorphism (f : Hom X Y) : HodgeStructureOn.IsMorphism X.hs Y.hs f.toLinearMap where
  commutes_conj x := by
    simpa only [latticeConjugation_toEquiv_apply] using f.commutes_conj x
  map_F_le := f.map_F_le

/-- The identity rational Hodge morphism. -/
noncomputable def id (X : PolarizableHodgeStructureCat.{u} n) : Hom X X where
  toRatLinearMap := LinearMap.id
  map_mem_F := by simp

/-- The identity morphism has the identity rational linear map. -/
@[simp]
theorem id_toRatLinearMap (X : PolarizableHodgeStructureCat.{u} n) :
    (id X).toRatLinearMap = LinearMap.id :=
  by rw [id]

/-- The identity rational Hodge morphism acts as the identity on complex vectors. -/
@[simp]
theorem id_apply (X : PolarizableHodgeStructureCat.{u} n) (x : X.complexCarrier) : id X x = x := by
  simp [toLinearMap_def]

/-- Composition of rational Hodge morphisms. -/
noncomputable def comp (g : Hom Y Z) (f : Hom X Y) : Hom X Z where
  toRatLinearMap := g.toRatLinearMap ∘ₗ f.toRatLinearMap
  map_mem_F := by
    intro p x hx
    rw [rationalMapToComplex_comp X.isBaseChangeRat X.isBaseChangeComplex
      Y.isBaseChangeRat Y.isBaseChangeComplex Z.isBaseChangeRat Z.isBaseChangeComplex]
    exact g.map_mem_F p _ (f.map_mem_F p x hx)

/-- Composition is composition of the underlying rational linear maps. -/
@[simp]
theorem comp_toRatLinearMap (g : Hom Y Z) (f : Hom X Y) :
    (g.comp f).toRatLinearMap = g.toRatLinearMap ∘ₗ f.toRatLinearMap :=
  by rw [comp]

/-- Composition is pointwise composition on complex vectors. -/
@[simp]
theorem comp_apply (g : Hom Y Z) (f : Hom X Y) (x : X.complexCarrier) :
    g.comp f x = g (f x) := by
  exact LinearMap.congr_fun
    (rationalMapToComplex_comp X.isBaseChangeRat X.isBaseChangeComplex
      Y.isBaseChangeRat Y.isBaseChangeComplex Z.isBaseChangeRat Z.isBaseChangeComplex
      f.toRatLinearMap g.toRatLinearMap) x

/-- The zero rational Hodge morphism. -/
noncomputable instance instZero : Zero (Hom X Y) where
  zero := ⟨0, by simp⟩

/-- Addition of rational Hodge morphisms. -/
noncomputable instance instAdd : Add (Hom X Y) where
  add f g :=
    { toRatLinearMap := f.toRatLinearMap + g.toRatLinearMap
      map_mem_F := by
        intro p x hx
        rw [rationalMapToComplex_add, LinearMap.add_apply]
        exact (Y.hs.F p).add_mem (f.map_mem_F p x hx) (g.map_mem_F p x hx) }

/-- Negation of rational Hodge morphisms. -/
noncomputable instance instNeg : Neg (Hom X Y) where
  neg f :=
    { toRatLinearMap := -f.toRatLinearMap
      map_mem_F := by
        intro p x hx
        rw [rationalMapToComplex_neg, LinearMap.neg_apply]
        exact (Y.hs.F p).neg_mem (f.map_mem_F p x hx) }

/-- Subtraction of rational Hodge morphisms. -/
noncomputable instance instSub : Sub (Hom X Y) where
  sub f g :=
    { toRatLinearMap := f.toRatLinearMap - g.toRatLinearMap
      map_mem_F := by
        intro p x hx
        rw [rationalMapToComplex_sub, LinearMap.sub_apply]
        exact (Y.hs.F p).sub_mem (f.map_mem_F p x hx) (g.map_mem_F p x hx) }

/-- Natural-number multiples of rational Hodge morphisms. -/
noncomputable instance instSMulNat : SMul ℕ (Hom X Y) where
  smul k f :=
    { toRatLinearMap := k • f.toRatLinearMap
      map_mem_F := by
        intro p x hx
        rw [rationalMapToComplex_nsmul, LinearMap.smul_apply]
        exact nsmul_mem (f.map_mem_F p x hx) k }

/-- Integer multiples of rational Hodge morphisms. -/
noncomputable instance instSMulInt : SMul ℤ (Hom X Y) where
  smul k f :=
    { toRatLinearMap := k • f.toRatLinearMap
      map_mem_F := by
        intro p x hx
        rw [rationalMapToComplex_zsmul, LinearMap.smul_apply]
        exact zsmul_mem (f.map_mem_F p x hx) k }

/-- Rational multiples of rational Hodge morphisms. -/
noncomputable instance instSMulRat : SMul ℚ (Hom X Y) where
  smul q f :=
    { toRatLinearMap := q • f.toRatLinearMap
      map_mem_F := by
        intro p x hx
        rw [rationalMapToComplex_smul, LinearMap.smul_apply]
        exact Submodule.smul_mem _ (q : ℂ) (f.map_mem_F p x hx) }

/-- Rational Hodge morphisms form an additive commutative group. -/
noncomputable instance : AddCommGroup (Hom X Y) :=
  Function.Injective.addCommGroup (fun f : Hom X Y ↦ f.toRatLinearMap)
    (fun _ _ h ↦ ext h) rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- Rational Hodge morphisms form a rational vector space. -/
noncomputable instance : Module ℚ (Hom X Y) :=
  Function.Injective.module ℚ
    { toFun := fun f : Hom X Y ↦ f.toRatLinearMap
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
    (fun _ _ h ↦ ext h) (fun _ _ ↦ rfl)

/-- The zero morphism has the zero rational linear map underneath. -/
@[simp]
theorem zero_toRatLinearMap : (0 : Hom X Y).toRatLinearMap = 0 := rfl

/-- Addition of morphisms is addition of their underlying rational maps. -/
@[simp]
theorem add_toRatLinearMap (f g : Hom X Y) :
    (f + g).toRatLinearMap = f.toRatLinearMap + g.toRatLinearMap := rfl

/-- Negation of morphisms is negation of their underlying rational maps. -/
@[simp]
theorem neg_toRatLinearMap (f : Hom X Y) : (-f).toRatLinearMap = -f.toRatLinearMap := rfl

/-- Subtraction of morphisms is subtraction of their underlying rational maps. -/
@[simp]
theorem sub_toRatLinearMap (f g : Hom X Y) :
    (f - g).toRatLinearMap = f.toRatLinearMap - g.toRatLinearMap := rfl

/-- Natural-number multiples pass to the underlying rational maps. -/
@[simp]
theorem nsmul_toRatLinearMap (k : ℕ) (f : Hom X Y) :
    (k • f).toRatLinearMap = k • f.toRatLinearMap := rfl

/-- Integer multiples pass to the underlying rational maps. -/
@[simp]
theorem zsmul_toRatLinearMap (k : ℤ) (f : Hom X Y) :
    (k • f).toRatLinearMap = k • f.toRatLinearMap := rfl

/-- Rational multiples pass to the underlying rational maps. -/
@[simp]
theorem smul_toRatLinearMap (q : ℚ) (f : Hom X Y) :
    (q • f).toRatLinearMap = q • f.toRatLinearMap := rfl

/-- The zero morphism acts by zero on complex vectors. -/
@[simp]
theorem zero_apply (x : X.complexCarrier) : (0 : Hom X Y) x = 0 := by
  simp [toLinearMap_def]

/-- Addition of morphisms is pointwise addition on complex vectors. -/
@[simp]
theorem add_apply (f g : Hom X Y) (x : X.complexCarrier) : (f + g) x = f x + g x := by
  simp [toLinearMap_def]

/-- Negation of morphisms is pointwise negation on complex vectors. -/
@[simp]
theorem neg_apply (f : Hom X Y) (x : X.complexCarrier) : (-f) x = -f x := by
  simp [toLinearMap_def]

/-- Subtraction of morphisms is pointwise subtraction on complex vectors. -/
@[simp]
theorem sub_apply (f g : Hom X Y) (x : X.complexCarrier) : (f - g) x = f x - g x := by
  simp [toLinearMap_def]

/-- Rational scalar multiplication acts pointwise on complex vectors through `ℚ → ℂ`. -/
@[simp]
theorem smul_apply (q : ℚ) (f : Hom X Y) (x : X.complexCarrier) :
    (q • f) x = (q : ℂ) • f x := by
  simp [toLinearMap_def]

/-- Composition is additive in its outer morphism. -/
@[simp]
theorem add_comp (g h : Hom Y Z) (f : Hom X Y) :
    (g + h).comp f = g.comp f + h.comp f := by
  ext
  rfl

/-- Composition is additive in its inner morphism. -/
@[simp]
theorem comp_add (g : Hom Y Z) (f h : Hom X Y) :
    g.comp (f + h) = g.comp f + g.comp h := by
  ext x
  exact g.toRatLinearMap.map_add (f.toRatLinearMap x) (h.toRatLinearMap x)

/-- A rational scalar in the outer morphism can be pulled out of a composition. -/
@[simp]
theorem smul_comp (q : ℚ) (g : Hom Y Z) (f : Hom X Y) :
    (q • g).comp f = q • g.comp f := by
  ext
  rfl

/-- A rational scalar in the inner morphism can be pulled out of a composition. -/
@[simp]
theorem comp_smul (g : Hom Y Z) (q : ℚ) (f : Hom X Y) :
    g.comp (q • f) = q • g.comp f := by
  ext x
  exact g.toRatLinearMap.map_smul q (f.toRatLinearMap x)

end Hom

noncomputable instance : Category.{u} (PolarizableHodgeStructureCat.{u} n) where
  Hom := Hom
  id := Hom.id
  comp f g := g.comp f

/-- Two categorical morphisms agree if their rational maps agree. -/
@[ext]
theorem hom_ext {X Y : PolarizableHodgeStructureCat.{u} n} {f g : X ⟶ Y}
    (h : f.toRatLinearMap = g.toRatLinearMap) : f = g :=
  Hom.ext h

/-- The categorical identity has the identity rational linear map. -/
@[simp]
theorem id_toRatLinearMap (X : PolarizableHodgeStructureCat.{u} n) :
    (𝟙 X : X ⟶ X).toRatLinearMap = LinearMap.id :=
  Hom.id_toRatLinearMap X

/-- Categorical composition is composition of the underlying rational linear maps. -/
@[simp]
theorem comp_toRatLinearMap {X Y Z : PolarizableHodgeStructureCat.{u} n}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toRatLinearMap = g.toRatLinearMap ∘ₗ f.toRatLinearMap :=
  Hom.comp_toRatLinearMap g f

/-- The identity morphism has the identity complex linear map. -/
@[simp]
theorem id_toLinearMap (X : PolarizableHodgeStructureCat.{u} n) :
    Hom.toLinearMap (𝟙 X) = LinearMap.id := by
  simp [Hom.toLinearMap]

/-- Composition of categorical morphisms is composition of their complex linear maps. -/
@[simp]
theorem comp_toLinearMap {X Y Z : PolarizableHodgeStructureCat.{u} n}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Hom.toLinearMap (f ≫ g) = Hom.toLinearMap g ∘ₗ Hom.toLinearMap f := by
  apply LinearMap.ext
  exact Hom.comp_apply g f

noncomputable instance : Preadditive (PolarizableHodgeStructureCat.{u} n) where
  homGroup X Y := inferInstanceAs (AddCommGroup (Hom X Y))
  add_comp _ _ _ f g h := Hom.comp_add h f g
  comp_add _ _ _ f g h := Hom.add_comp g h f

noncomputable instance : Linear ℚ (PolarizableHodgeStructureCat.{u} n) where
  homModule X Y := inferInstanceAs (Module ℚ (Hom X Y))
  smul_comp _ _ _ q f g := Hom.comp_smul g q f
  comp_smul _ _ _ f q g := Hom.smul_comp q g f

/-- The rational realization of a polarizable rational Hodge structure and its morphisms. -/
@[expose]
noncomputable def rational : PolarizableHodgeStructureCat.{u} n ⥤ ModuleCat.{u} ℚ where
  obj X := X.rat
  map f := ModuleCat.ofHom f.toRatLinearMap
  map_id X := by
    apply ModuleCat.hom_ext
    exact id_toRatLinearMap X
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact comp_toRatLinearMap f g

/-- The rational realization sends an object to its rational vector space. -/
@[simp]
theorem rational_obj (X : PolarizableHodgeStructureCat.{u} n) : rational.obj X = X.rat := rfl

/-- The rational realization sends a morphism to its underlying rational linear map. -/
@[simp]
theorem rational_map_hom {X Y : PolarizableHodgeStructureCat.{u} n} (f : X ⟶ Y) :
    (rational.map f).hom = f.toRatLinearMap := rfl

noncomputable instance : (rational (n := n)).Faithful where
  map_injective {_ _} _ _ h := hom_ext (congrArg ModuleCat.Hom.hom h)

noncomputable instance : (rational (n := n)).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    exact Hom.add_toRatLinearMap f g

noncomputable instance : (rational (n := n)).Linear ℚ where
  map_smul := by
    intro X Y f q
    apply ModuleCat.hom_ext
    exact Hom.smul_toRatLinearMap q f

/-- The complex realization of a polarizable rational Hodge structure and the complexifications
of its morphisms. -/
@[expose]
noncomputable def complex : PolarizableHodgeStructureCat.{u} n ⥤ ModuleCat.{u} ℂ where
  obj X := X.complexSpace
  map f := ModuleCat.ofHom f.toLinearMap
  map_id X := by
    apply ModuleCat.hom_ext
    exact id_toLinearMap X
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact comp_toLinearMap f g

/-- The complex realization sends an object to its complex vector space. -/
@[simp]
theorem complex_obj (X : PolarizableHodgeStructureCat.{u} n) :
    complex.obj X = X.complexSpace := rfl

/-- The complex realization sends a morphism to its derived complex linear map. -/
@[simp]
theorem complex_map_hom {X Y : PolarizableHodgeStructureCat.{u} n} (f : X ⟶ Y) :
    (complex.map f).hom = f.toLinearMap := rfl

noncomputable instance : (complex (n := n)).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    exact rationalMapToComplex_add X.isBaseChangeRat X.isBaseChangeComplex
      Y.isBaseChangeRat Y.isBaseChangeComplex f.toRatLinearMap g.toRatLinearMap

/-- The complex realization is rational-linear through the inclusion `ℚ → ℂ`. -/
noncomputable instance : (complex (n := n)).Linear ℚ where
  map_smul := by
    intro X Y f q
    apply ModuleCat.hom_ext
    exact rationalMapToComplex_smul X.isBaseChangeRat X.isBaseChangeComplex
      Y.isBaseChangeRat Y.isBaseChangeComplex q f.toRatLinearMap

end PolarizableHodgeStructureCat

end TauCeti.Hodge
