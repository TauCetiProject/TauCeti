/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.Basic

/-!
# Homomorphisms of abelian varieties

This file supplies the morphism part of the basic abelian-variety API. A homomorphism of abelian
varieties over `K` is a morphism over `Spec K` preserving the unit and multiplication of the
underlying group schemes. Such morphisms form a category, inherited from Mathlib's category of
group objects.

The bundled `AbelianVariety.Hom` is the type required by the Jacobian's universal property: the
factorization from the Jacobian to another abelian variety must preserve the group law, rather than
being only a morphism of the underlying schemes. The characteristic lemmas expose preservation of
the unit, multiplication, and inverse, as well as the underlying morphism of schemes.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer E, "Abelian variety = smooth,
proper, geometrically connected group scheme over `k`; basic API", and prepares Layer F's unique
"homomorphism of abelian varieties". No external mathematics is vendored; the implementation
reuses Mathlib's `Grp` category and its `IsMonHom` API for group objects in a cartesian monoidal
category.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace AbelianVariety

variable {K : Type u} [Field K]

noncomputable section

/-- A homomorphism of abelian varieties over `K`: a morphism over `Spec K` preserving the group
law. Preservation of inverses follows from preservation of the unit and multiplication. -/
@[ext]
structure Hom (A B : AbelianVariety K) where
  /-- The underlying morphism of group schemes over `Spec K`. -/
  hom : A.toOver ⟶ B.toOver
  [isMonHom_hom : IsMonHom hom]

attribute [instance] Hom.isMonHom_hom

/-- Construct a homomorphism of abelian varieties from a morphism over `Spec K` and proofs that it
preserves the unit and multiplication. -/
def Hom.mk' {A B : AbelianVariety K} (f : A.toOver ⟶ B.toOver)
    (one_f : η[A.toOver] ≫ f = η[B.toOver] := by cat_disch)
    (mul_f : μ[A.toOver] ≫ f = (f ⊗ₘ f) ≫ μ[B.toOver] := by cat_disch) : A.Hom B :=
  haveI : IsMonHom f := ⟨one_f, mul_f⟩
  ⟨f⟩

/-- The identity homomorphism of an abelian variety. -/
@[expose]
noncomputable def Hom.id (A : AbelianVariety K) : A.Hom A :=
  ⟨𝟙 A.toOver⟩

/-- Composition of homomorphisms of abelian varieties. -/
@[expose]
noncomputable def Hom.comp {A B C : AbelianVariety K} (f : A.Hom B) (g : B.Hom C) : A.Hom C :=
  ⟨f.hom ≫ g.hom⟩

/-- Abelian varieties over a fixed field form a category with group-scheme homomorphisms. -/
noncomputable instance : Category (AbelianVariety K) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[simp]
lemma id_hom (A : AbelianVariety K) : (CategoryStruct.id A : A.Hom A).hom = 𝟙 A.toOver :=
  rfl

@[simp, reassoc]
lemma comp_hom {A B C : AbelianVariety K} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

/-- A homomorphism of abelian varieties preserves the unit section. -/
@[reassoc (attr := simp)]
lemma Hom.one_hom {A B : AbelianVariety K} (f : A ⟶ B) :
    η[A.toOver] ≫ f.hom = η[B.toOver] :=
  IsMonHom.one_hom f.hom

/-- A homomorphism of abelian varieties preserves multiplication. -/
@[reassoc (attr := simp)]
lemma Hom.mul_hom {A B : AbelianVariety K} (f : A ⟶ B) :
    μ[A.toOver] ≫ f.hom = (f.hom ⊗ₘ f.hom) ≫ μ[B.toOver] :=
  IsMonHom.mul_hom f.hom

/-- A homomorphism of abelian varieties preserves inverses. -/
@[reassoc (attr := simp)]
lemma Hom.inv_hom {A B : AbelianVariety K} (f : A ⟶ B) :
    ι[A.toOver] ≫ f.hom = f.hom ≫ ι[B.toOver] :=
  GrpObj.inv_hom f.hom

/-- The underlying morphism between the schemes of two abelian varieties. -/
abbrev Hom.toSchemeHom {A B : AbelianVariety K} (f : A ⟶ B) : A.toScheme ⟶ B.toScheme :=
  f.hom.left

@[simp]
lemma Hom.toSchemeHom_id (A : AbelianVariety K) :
    Hom.toSchemeHom (𝟙 A) = 𝟙 A.toScheme :=
  rfl

@[simp, reassoc]
lemma Hom.toSchemeHom_comp {A B C : AbelianVariety K} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).toSchemeHom = f.toSchemeHom ≫ g.toSchemeHom :=
  rfl

/-- The underlying scheme morphism of an abelian-variety homomorphism commutes with the structure
morphisms to `Spec K`. -/
@[reassoc (attr := simp)]
lemma Hom.toSchemeHom_comp_hom {A B : AbelianVariety K} (f : A ⟶ B) :
    f.toSchemeHom ≫ B.toOver.hom = A.toOver.hom :=
  f.hom.w

/-- Two homomorphisms of abelian varieties are equal when their underlying scheme morphisms are
equal. -/
lemma Hom.ext_toSchemeHom {A B : AbelianVariety K} {f g : A ⟶ B}
    (h : f.toSchemeHom = g.toSchemeHom) : f = g := by
  apply Hom.ext
  exact Over.OverMorphism.ext h

end

end AbelianVariety

end AlgebraicGeometry

end TauCeti
