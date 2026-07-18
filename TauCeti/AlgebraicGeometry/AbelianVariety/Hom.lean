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

/-- The group object over `Spec K` underlying an abelian variety. -/
@[expose]
def toGrp (A : AbelianVariety K) : Grp (Over (Spec (.of K))) :=
  ⟨A.toOver⟩

/-- Abelian varieties over a fixed field form a category with group-scheme homomorphisms. -/
noncomputable instance : Category (AbelianVariety K) :=
  inferInstanceAs (Category (InducedCategory _ toGrp))

/-- Construct a homomorphism of abelian varieties from a morphism over `Spec K` and proofs that it
preserves the unit and multiplication. -/
def Hom.mk' {A B : AbelianVariety K} (f : A.toOver ⟶ B.toOver)
    (one_f : η[A.toOver] ≫ f = η[B.toOver] := by cat_disch)
    (mul_f : μ[A.toOver] ≫ f = (f ⊗ₘ f) ≫ μ[B.toOver] := by cat_disch) : A ⟶ B :=
  InducedCategory.homMk (Grp.homMk'' f one_f mul_f)

/-- The underlying morphism of group schemes over `Spec K`. -/
abbrev Hom.toOverHom {A B : AbelianVariety K} (f : A ⟶ B) : A.toOver ⟶ B.toOver :=
  f.hom.hom.hom

@[simp]
lemma id_hom (A : AbelianVariety K) : Hom.toOverHom (CategoryStruct.id A) = 𝟙 A.toOver :=
  Grp.id_hom_hom _

@[simp, reassoc]
lemma comp_hom {A B C : AbelianVariety K} (f : A ⟶ B) (g : B ⟶ C) :
    Hom.toOverHom (f ≫ g) = Hom.toOverHom f ≫ Hom.toOverHom g :=
  Grp.comp_hom_hom _ _

/-- A homomorphism of abelian varieties preserves the unit section. -/
@[reassoc]
lemma Hom.one_hom {A B : AbelianVariety K} (f : A ⟶ B) :
    η[A.toOver] ≫ Hom.toOverHom f = η[B.toOver] :=
  IsMonHom.one_hom f.hom.hom.hom

/-- A homomorphism of abelian varieties preserves multiplication. -/
@[reassoc]
lemma Hom.mul_hom {A B : AbelianVariety K} (f : A ⟶ B) :
    μ[A.toOver] ≫ Hom.toOverHom f =
      (Hom.toOverHom f ⊗ₘ Hom.toOverHom f) ≫ μ[B.toOver] :=
  IsMonHom.mul_hom f.hom.hom.hom

/-- A homomorphism of abelian varieties preserves inverses. -/
@[reassoc]
lemma Hom.inv_hom {A B : AbelianVariety K} (f : A ⟶ B) :
    ι[A.toOver] ≫ Hom.toOverHom f = Hom.toOverHom f ≫ ι[B.toOver] :=
  GrpObj.inv_hom f.hom.hom.hom

/-- The underlying morphism between the schemes of two abelian varieties. -/
abbrev Hom.toSchemeHom {A B : AbelianVariety K} (f : A ⟶ B) : A.toScheme ⟶ B.toScheme :=
  (Hom.toOverHom f).left

@[simp]
lemma Hom.toSchemeHom_id (A : AbelianVariety K) :
    Hom.toSchemeHom (𝟙 A) = 𝟙 A.toScheme :=
  rfl

@[simp, reassoc]
lemma Hom.toSchemeHom_comp {A B C : AbelianVariety K} (f : A ⟶ B) (g : B ⟶ C) :
    Hom.toSchemeHom (f ≫ g) = Hom.toSchemeHom f ≫ Hom.toSchemeHom g :=
  rfl

/-- The underlying scheme morphism of an abelian-variety homomorphism commutes with the structure
morphisms to `Spec K`. -/
@[reassoc]
lemma Hom.toSchemeHom_comp_hom {A B : AbelianVariety K} (f : A ⟶ B) :
    Hom.toSchemeHom f ≫ B.toOver.hom = A.toOver.hom :=
  (Hom.toOverHom f).w

/-- Two homomorphisms of abelian varieties are equal when their underlying scheme morphisms are
equal. -/
lemma Hom.ext_toSchemeHom {A B : AbelianVariety K} {f g : A ⟶ B}
    (h : Hom.toSchemeHom f = Hom.toSchemeHom g) : f = g := by
  apply InducedCategory.hom_ext
  apply Grp.hom_ext
  exact Over.OverMorphism.ext h

end

end AbelianVariety

end AlgebraicGeometry

end TauCeti
