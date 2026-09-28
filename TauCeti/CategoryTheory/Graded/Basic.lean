/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import TauCeti.Algebra.Module.GradedModule.Internal

/-!
# Graded linear categories

A *graded linear quiver* over a commutative ring `R` is a small category whose hom sets are
`R`-modules carrying a `ℤ`-grading, such that composition is `R`-bilinear and takes a morphism of
degree `n` followed by one of degree `m` to a morphism of degree `n + m`, and such that the
identity of an object is a morphism of degree zero.  It is the linear graded object on which the
higher theories of this library are built: a differential graded category is a graded linear
quiver together with a differential raising the degree of each hom module by one, and an
`A∞` category is a graded linear quiver together with operations of degree `2 - n` in
arity `n` and their `Stasheff` relations.

The grading is *internal*: the morphisms of degree `n` are the submodule
`(grading X Y).piece n` of `X ⟶ Y`, and the submodule family is an internal direct sum, so every
morphism is a finite, uniquely determined sum of morphisms of definite degrees, the degree-`n`
component of a morphism being `DirectSum.decompose` of the grading, as in
`TauCeti.InternalGrading`.  Only three kinds
of data are postulated beyond the category laws, namely the grading of each hom module, the
homogeneity of composition, and the degree of the identity.  Associativity and the unit laws are
inherited from the underlying category, and the graded operations of this file are the
restrictions of composition and of the identity to the homogeneous submodules, so no law has to
be verified twice.  Each hom module is graded over `R` and composition is bilinear, so a graded
linear category is in particular a `CategoryTheory.Linear` and a `CategoryTheory.Preadditive`
category, and `grHom X Y n` is an `R`-module.

The degree bookkeeping is carried by `grHomReindex`, which records a homogeneous morphism at any
other degree without touching the underlying morphism, so that the associativity and unit laws of
graded composition below are stated without any equation between degrees appearing in a type.

## Main definitions

* `TauCeti.GradedLinearCategory`: a category with internal `ℤ`-graded hom modules, bilinear
composition homogeneous for the grading, and a degree-zero identity.
* `TauCeti.GradedLinearCategory.grHom`: the morphisms `X ⟶ Y` of a fixed degree.
* `TauCeti.GradedLinearCategory.grHomReindex`: a homogeneous morphism recorded at another degree.
* `TauCeti.GradedLinearCategory.grComp`: composition of morphisms of prescribed degrees.
* `TauCeti.GradedLinearCategory.grId`: the identity of an object, of degree zero.

## Main results

* `TauCeti.GradedLinearCategory.grComp_apply`: the underlying morphism of a graded composite is the
composite of the underlying morphisms, and `grComp` is `R`-linear in each argument.
* `TauCeti.GradedLinearCategory.grComp_assoc`: associativity of graded composition.
* `TauCeti.GradedLinearCategory.grComp_id` and `TauCeti.GradedLinearCategory.grComp_grId`: the
graded unit laws.
* `TauCeti.GradedLinearCategory.eq_zero_of_mem_piece_of_ne`: a nonzero morphism is homogeneous of
at most one degree, so a degree together with its homogeneous submodule determines a morphism.

## References

* E. Getzler and J. D. Jones, *A-infinity algebras and the cyclic bar complex*, *Illinois Journal of
Mathematics* 34 (1990), 256-283, Section 1: `ℤ`-graded objects, homogeneous elements, and the
degree bookkeeping of a graded higher theory.
* B. Keller, *Introduction to A-infinity algebras and modules*, *Homology, Homotopy and
Applications* 3 (2001), 1-35, Section 3.1: the sign conventions of a graded category.
* V. Drinfeld, *DG quotients of DG categories*, *Journal of Algebra* 272 (2004), 643-691,
Section 2: a differential graded category as a graded linear category with a differential.
-/

public section

open CategoryTheory
open scoped Category

namespace TauCeti

universe u v

/-- A **graded linear category** over a commutative ring `R`: a small category whose hom sets are
`R`-modules with an internal `ℤ`-grading, whose composition is `R`-bilinear and maps a morphism of
degree `n` followed by a morphism of degree `m` to a morphism of degree `n + m`, and whose
identity is a morphism of degree zero.

The hom module `X ⟶ Y` is an `R`-module by `CategoryTheory.Linear`, the grading of that module is
`grading X Y`, and its morphisms of degree `n` form the submodule `grHom X Y n`.

The base ring is a commutative ring, as for the differential graded categories of `TauCeti`: the
graded composition below is bundled as a bilinear `R`-linear map, and `LinearMap.mk₂` is available
over a commutative ring only. -/
class GradedLinearCategory (R : Type v) [CommRing R] (C : Type u)
    extends Category.{v} C, Preadditive C, Linear R C where
  /-- The internal `ℤ`-grading of the hom module `X ⟶ Y`. -/
  grading : (X Y : C) → InternalGrading R (X ⟶ Y)
  /-- The composite of morphisms of degrees `n` and `m` is a morphism of degree `n + m`. -/
  comp_grade : ∀ {X Y Z : C} (n m : ℤ) {f : X ⟶ Y} {g : Y ⟶ Z},
      f ∈ (grading X Y).piece n → g ∈ (grading Y Z).piece m →
        f ≫ g ∈ (grading X Z).piece (n + m)
  /-- The identity of `X` is homogeneous of degree zero. -/
  id_grade : ∀ (X : C), (𝟙 X : X ⟶ X) ∈ (grading X X).piece 0

namespace GradedLinearCategory

variable (R : Type v) [CommRing R] {C : Type u} [GradedLinearCategory R C] {X Y Z : C}

/-- The morphisms `X ⟶ Y` of cohomological degree `n`, as the `R`-module
`(grading X Y).piece n`. -/
abbrev grHom (R : Type v) [CommRing R] {C : Type u} [GradedLinearCategory R C]
    (X Y : C) (n : ℤ) : Type v := ↥((grading X Y).piece n : Submodule R (X ⟶ Y))

/-- Record a morphism of degree `n` as a morphism of degree `k`, along an equation `h : n = k` of
degrees.  The underlying morphism is unchanged. -/
def grHomReindex {X Y : C} {n k : ℤ} (h : n = k) (f : grHom R X Y n) : grHom R X Y k :=
  ⟨f, by rw [← h]; exact f.property⟩

/-- Reindexing a homogeneous morphism does not change the underlying morphism. -/
@[simp, grind =]
theorem val_grHomReindex (h : n = k) (f : grHom R X Y n) :
    (grHomReindex (R := R) (C := C) h f).1 = f.1 := by
  rw [grHomReindex]

/-- The composite of a morphism of degree `n` and a morphism of degree `m` is a morphism of degree
`n + m` whose underlying morphism is the composite of the underlying morphisms. -/
private def grCompFn {X Y Z : C} (n m : ℤ) (f : grHom R X Y n)
    (g : grHom R Y Z m) : grHom R X Z (n + m) :=
  ⟨(f : X ⟶ Y) ≫ (g : Y ⟶ Z), by grind [comp_grade]⟩

/-- **Composition of morphisms of prescribed degrees**: `grComp R n m f g` is the `R`-linear map
sending morphisms `f` and `g` of degrees `n` and `m` to a morphism of degree `n + m` whose
underlying morphism is the composite of the underlying morphisms. -/
def grComp {X Y Z : C} (n m : ℤ) :
    grHom R X Y n →ₗ[R] grHom R Y Z m →ₗ[R] grHom R X Z (n + m) :=
  LinearMap.mk₂' (M := grHom R X Y n) (N := grHom R Y Z m) (Pₗ := grHom R X Z (n + m))
    R R (grCompFn R n m)
    (by intro f f' g; rw [grCompFn]; exact Subtype.ext (Preadditive.add_comp X Y Z f.1 f'.1 g.1))
    (by intro c f g; rw [grCompFn]; exact Subtype.ext (Linear.smul_comp X Y Z c f.1 g.1))
    (by intro f g g'; rw [grCompFn]; exact Subtype.ext (Preadditive.comp_add X Y Z f.1 g.1 g'.1))
    (by intro c f g; rw [grCompFn]; exact Subtype.ext (Linear.comp_smul X Y Z f.1 c g.1))

/-- The underlying morphism of a graded composite is the composite of the underlying morphisms.

The composite is stated with the `CategoryStruct.comp` application made explicit: the two graded
morphisms are carried by submodules of the hom modules, and the `≫` notation cannot then recover
the category structure of `C` from the `GradedLinearCategory` instance. -/
@[simp, grind =]
theorem grComp_apply (f : grHom R X Y n) (g : grHom R Y Z m) :
    (grComp R n m f g).1 = @CategoryStruct.comp C _ X Y Z f.1 g.1 := by
  rw [grComp]
  rfl

/-- The identity of `X` is a morphism of degree zero. -/
def grId (X : C) : grHom R X X 0 := ⟨𝟙 X, id_grade X⟩

/-- The identity of degree zero is the identity morphism. -/
@[simp, grind =]
theorem val_grId (X : C) : (grId R X).1 = 𝟙 X := by rw [grId]

/-- Composing a morphism with the identity of its target gives that morphism back, so the graded
unit law holds at the degree `n + 0 = n`. -/
theorem grComp_id (f : grHom R X Y n) :
    grHomReindex (R := R) (C := C) (add_zero n) (grComp R n 0 f (grId R Y)) = f := by
  refine Subtype.ext ?_
  simp only [val_grHomReindex, grComp_apply, val_grId]
  exact Category.comp_id f.1

/-- Composing the identity of the source with a morphism gives that morphism back, so the graded
unit law holds at the degree `0 + n = n`. -/
theorem grComp_grId (f : grHom R X Y n) :
    grHomReindex (R := R) (C := C) (zero_add n) (grComp R 0 n (grId R X) f) = f := by
  refine Subtype.ext ?_
  simp only [val_grHomReindex, grComp_apply, val_grId]
  exact Category.id_comp f.1

/-- **Associativity of graded composition**: the two ways of composing morphisms of degrees `n`,
`m` and `l` agree, once the degree of the composite is recorded at the common value
`n + m + l`. -/
theorem grComp_assoc (f : grHom R X Y n) (g : grHom R Y Z m) (h : grHom R Z W l) :
    grHomReindex (R := R) (C := C) ((add_assoc n m l).symm)
      (grComp R n (m + l) f (grComp R m l g h)) = grComp R (n + m) l (grComp R n m f g) h := by
  refine Subtype.ext ?_
  simp only [val_grHomReindex, grComp_apply]
  exact (Category.assoc f.1 g.1 h.1).symm

/-- A morphism which is homogeneous of two distinct degrees is zero.  Equivalently, a nonzero
morphism is homogeneous of at most one degree. -/
theorem eq_zero_of_mem_piece_of_ne (R : Type v) [CommRing R] {C : Type u}
    [GradedLinearCategory R C] {X Y : C} {n m : ℤ} {f : X ⟶ Y} (hne : n ≠ m)
    (hn : f ∈ (grading X Y).piece n) (hm : f ∈ (grading X Y).piece m) : f = 0 := by
  let A := (grading (R := R) X Y).piece
  have h : DirectSum.IsInternal A := (grading (R := R) X Y).isInternal
  have happ : (⟨f, hn⟩ : A n) = 0 := by
    rw [← h.ofBijective_coeLinearMap_of_mem hn,
      ← h.ofBijective_coeLinearMap_of_mem_ne (i := m) (j := n) hne.symm hm]
  exact congrArg (fun x : A n => (x : X ⟶ Y)) happ

end GradedLinearCategory

end TauCeti
