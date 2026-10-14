/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.CategoryTheory.GradedObject.Braiding
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Basic

/-!
# Nonnegatively graded quasicoherent algebras

A nonnegatively graded algebra on a scheme `X` is a commutative monoid object in the symmetric
monoidal category of `ℕ`-graded `𝒪_X`-modules. Requiring every homogeneous component to be
quasicoherent gives the category `GradedQuasicoherentAlgebra X`. Its morphisms are genuine graded
algebra morphisms, since they are morphisms of commutative monoid objects in graded modules.

The functor `GradedQuasicoherentAlgebra.degree` extracts any homogeneous component as a
quasicoherent sheaf. In particular, `degreeOne` is the coefficient object from which freely
generated graded algebras and their associated linear schemes are recovered.

## Main declarations

* `TauCeti.AlgebraicGeometry.isGradedQuasicoherentAlgebra`: componentwise quasicoherence for a
  commutative algebra object in nonnegatively graded modules;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra`: the full category cut out by that
  property;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.toGradedModules`: the underlying graded
  module functor;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.degree`: extraction of a homogeneous
  component as a quasicoherent sheaf;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.degreeOne`: the degree-one functor.
-/

public section

open CategoryTheory MonoidalCategory MonObj

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable (X : Scheme.{u})

/-- A commutative algebra object in nonnegatively graded `𝒪_X`-modules is graded
quasicoherent when each of its homogeneous components is a quasicoherent `𝒪_X`-module. -/
def isGradedQuasicoherentAlgebra :
    ObjectProperty (CommMon (GradedObject ℕ X.Modules)) :=
  fun A ↦ ∀ n, (A.X n).IsQuasicoherent

/-- The category of commutative nonnegatively graded quasicoherent `𝒪_X`-algebras. Its morphisms
are morphisms of commutative monoid objects in graded modules, hence preserve the unit,
multiplication, and degree. -/
abbrev GradedQuasicoherentAlgebra : Type _ :=
  (isGradedQuasicoherentAlgebra X).FullSubcategory

namespace GradedQuasicoherentAlgebra

variable {X}

/-- Every homogeneous component of a graded quasicoherent algebra is quasicoherent. -/
instance (A : GradedQuasicoherentAlgebra X) (n : ℕ) : (A.obj.X n).IsQuasicoherent :=
  A.property n

/-- The faithful functor forgetting the algebra structure while retaining the grading. The
definition is exposed so that the underlying graded objects reduce in the types of its
characteristic equations. -/
@[expose]
def toGradedModules :
    GradedQuasicoherentAlgebra X ⥤ GradedObject ℕ X.Modules :=
  (isGradedQuasicoherentAlgebra X).ι ⋙ CommMon.forget _

instance : (toGradedModules (X := X)).Faithful :=
  inferInstanceAs ((isGradedQuasicoherentAlgebra X).ι ⋙ CommMon.forget _).Faithful

/-- Forgetting a graded quasicoherent algebra gives its underlying graded module. -/
@[simp]
theorem toGradedModules_obj (A : GradedQuasicoherentAlgebra X) :
    (toGradedModules (X := X)).obj A = A.obj.X :=
  rfl

/-- Forgetting a graded algebra morphism gives its underlying morphism of graded modules. -/
@[simp]
theorem toGradedModules_map {A B : GradedQuasicoherentAlgebra X} (f : A ⟶ B) :
    (toGradedModules (X := X)).map f = f.hom.hom.hom :=
  rfl

/-- Two morphisms of graded quasicoherent algebras agree when they agree in every degree. -/
@[ext]
theorem hom_ext {A B : GradedQuasicoherentAlgebra X} (f g : A ⟶ B)
    (h : ∀ n, f.hom.hom.hom n = g.hom.hom.hom n) : f = g := by
  apply ObjectProperty.hom_ext
  apply CommMon.hom_ext
  exact GradedObject.hom_ext _ _ h

/-- Extract the degree-`n` component of a graded quasicoherent algebra as a quasicoherent sheaf.
On morphisms this is the degree-`n` component of the underlying graded algebra morphism. The
definition is exposed so that the component objects and maps reduce in the types of its
characteristic equations. -/
@[expose]
def degree (n : ℕ) : GradedQuasicoherentAlgebra X ⥤ QuasicoherentSheaf X where
  obj A := ⟨A.obj.X n, inferInstance⟩
  map f := ⟨f.hom.hom.hom n⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The underlying module of the degree-`n` component is the corresponding component of the
underlying graded module. -/
@[simp]
theorem degree_obj_obj (A : GradedQuasicoherentAlgebra X) (n : ℕ) :
    ((degree (X := X) n).obj A).obj = A.obj.X n :=
  rfl

/-- The degree functor acts on a graded algebra morphism by its component in that degree. -/
@[simp]
theorem degree_map_hom {A B : GradedQuasicoherentAlgebra X} (f : A ⟶ B) (n : ℕ) :
    ((degree (X := X) n).map f).hom = f.hom.hom.hom n :=
  rfl

/-- Extract the degree-one component of a graded quasicoherent algebra. This is the component
that generates a free graded algebra and therefore the coefficient sheaf of a linear scheme. -/
abbrev degreeOne : GradedQuasicoherentAlgebra X ⥤ QuasicoherentSheaf X :=
  degree (X := X) 1

/-- Multiplication of homogeneous elements of degrees `i` and `j`, as a morphism from the tensor
product of the corresponding quasicoherent modules to degree `i + j`. -/
def mul (A : GradedQuasicoherentAlgebra X) (i j : ℕ) :
    A.obj.X i ⊗ A.obj.X j ⟶ A.obj.X (i + j) :=
  GradedObject.Monoidal.ιTensorObj A.obj.X A.obj.X i j (i + j) rfl ≫ μ[A.obj.X] (i + j)

/-- A graded algebra morphism commutes with multiplication on every pair of homogeneous
components. -/
@[reassoc]
theorem map_mul {A B : GradedQuasicoherentAlgebra X} (f : A ⟶ B) (i j : ℕ) :
    (f.hom.hom.hom i ⊗ₘ f.hom.hom.hom j) ≫ B.mul i j =
      A.mul i j ≫ f.hom.hom.hom (i + j) := by
  let φ : A.obj.X ⟶ B.obj.X := f.hom.hom.hom
  have hφ : IsMonHom φ := by
    dsimp only [φ]
    exact f.hom.hom.isMonHom_hom
  let _ : IsMonHom φ := hφ
  have hmul := congrFun (IsMonHom.mul_hom φ) (i + j)
  -- The successive full-subcategory and internal-monoid forgetful maps leave the graded object
  -- definitionally unchanged, but tactic transparency does not identify their displayed types.
  change μ[A.obj.X] (i + j) ≫ φ (i + j) =
    GradedObject.Monoidal.tensorHom φ φ (i + j) ≫ μ[B.obj.X] (i + j) at hmul
  change (φ i ⊗ₘ φ j) ≫
      GradedObject.Monoidal.ιTensorObj B.obj.X B.obj.X i j (i + j) rfl ≫ μ[B.obj.X] (i + j) =
    (GradedObject.Monoidal.ιTensorObj A.obj.X A.obj.X i j (i + j) rfl ≫ μ[A.obj.X] (i + j)) ≫
      φ (i + j)
  rw [← Category.assoc,
    ← GradedObject.Monoidal.ι_tensorHom φ φ i j (i + j) rfl,
    Category.assoc, ← hmul]
  rw [Category.assoc]

/-- The unit of a graded quasicoherent algebra, regarded as a morphism from the structure sheaf
to its degree-zero component. -/
def one (A : GradedQuasicoherentAlgebra X) : 𝟙_ X.Modules ⟶ A.obj.X 0 :=
  (GradedObject.Monoidal.tensorUnit₀ (C := X.Modules)).inv ≫ η[A.obj.X] 0

/-- A graded algebra morphism preserves the unit in degree zero. -/
@[reassoc, simp]
theorem one_map {A B : GradedQuasicoherentAlgebra X} (f : A ⟶ B) :
    A.one ≫ f.hom.hom.hom 0 = B.one := by
  let φ : A.obj.X ⟶ B.obj.X := f.hom.hom.hom
  have hφ : IsMonHom φ := by
    dsimp only [φ]
    exact f.hom.hom.isMonHom_hom
  let _ : IsMonHom φ := hφ
  have hone := congrFun (IsMonHom.one_hom φ) 0
  -- As for `map_mul`, state the component equation after removing the displayed `toMon` wrapper.
  change η[A.obj.X] 0 ≫ φ 0 = η[B.obj.X] 0 at hone
  change ((GradedObject.Monoidal.tensorUnit₀ (C := X.Modules)).inv ≫ η[A.obj.X] 0) ≫
      φ 0 = (GradedObject.Monoidal.tensorUnit₀ (C := X.Modules)).inv ≫ η[B.obj.X] 0
  rw [Category.assoc, hone]

end GradedQuasicoherentAlgebra

end


end AlgebraicGeometry

end TauCeti
