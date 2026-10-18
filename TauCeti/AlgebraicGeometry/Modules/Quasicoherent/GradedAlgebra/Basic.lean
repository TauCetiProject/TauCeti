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
public import TauCeti.CategoryTheory.GradedObject.MonObj

/-!
# Nonnegatively graded quasicoherent algebras

A nonnegatively graded algebra on a scheme `X` is a commutative monoid object in the symmetric
monoidal category of `ℕ`-graded `𝒪_X`-modules. Requiring every homogeneous component to be
quasicoherent gives the category `GradedQuasicoherentAlgebra X`. Its morphisms are genuine graded
algebra morphisms, since they are morphisms of commutative monoid objects in graded modules.

The functor `GradedQuasicoherentAlgebra.degree` extracts any homogeneous component as a
quasicoherent sheaf. In particular, `degreeOne` is the coefficient object from which freely
generated graded algebras and their associated linear schemes are recovered.

Conversely, `GradedQuasicoherentAlgebra.ofHomogeneous` builds a graded quasicoherent algebra from
its homogeneous components, unit and homogeneous multiplications, and
`GradedQuasicoherentAlgebra.homMk` builds morphisms from componentwise maps. These are the
constructors through which graded algebras that are described degree by degree, such as
symmetric algebras of quasicoherent sheaves, enter this category.

## Main declarations

* `TauCeti.AlgebraicGeometry.isGradedQuasicoherentAlgebra`: componentwise quasicoherence for a
  commutative algebra object in nonnegatively graded modules;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra`: the full category cut out by that
  property;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.toGradedModules`: the underlying graded
  module functor;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.degree`: extraction of a homogeneous
  component as a quasicoherent sheaf;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.degreeOne`: the degree-one functor;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.ofHomogeneous`: conversely, the graded
  quasicoherent algebra with given quasicoherent components, unit and homogeneous
  multiplications satisfying these laws;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.homMk`: the morphism of graded
  quasicoherent algebras given by componentwise maps preserving the unit and the homogeneous
  multiplications.
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

variable {X} in
/-- A commutative algebra object in graded modules is graded quasicoherent exactly when each of
its homogeneous components is quasicoherent. -/
theorem isGradedQuasicoherentAlgebra_iff (A : CommMon (GradedObject ℕ X.Modules)) :
    isGradedQuasicoherentAlgebra X A ↔ ∀ n, (A.X n).IsQuasicoherent :=
  Iff.rfl

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

/-- The faithful functor forgetting the algebra structure while retaining the grading. -/
def toGradedModules :
    GradedQuasicoherentAlgebra X ⥤ GradedObject ℕ X.Modules :=
  (isGradedQuasicoherentAlgebra X).ι ⋙ CommMon.forget _

instance : (toGradedModules (X := X)).Faithful :=
  inferInstanceAs ((isGradedQuasicoherentAlgebra X).ι ⋙ CommMon.forget _).Faithful

/-- Forgetting a graded quasicoherent algebra gives its underlying graded module. -/
@[simp]
theorem toGradedModules_obj (A : GradedQuasicoherentAlgebra X) :
    (toGradedModules (X := X)).obj A = A.obj.X :=
  (rfl)

/-- Forgetting a graded algebra morphism gives its underlying morphism of graded modules. -/
@[simp]
theorem toGradedModules_map {A B : GradedQuasicoherentAlgebra X} (f : A ⟶ B) :
    (toGradedModules (X := X)).map f =
      eqToHom (toGradedModules_obj A) ≫ f.hom.hom.hom ≫ eqToHom (toGradedModules_obj B).symm := by
  cases toGradedModules_obj A
  cases toGradedModules_obj B
  -- The functor is not exposed, so its action on morphisms is identified with the underlying
  -- graded morphism only after the object equations are eliminated.
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- Two morphisms of graded quasicoherent algebras agree when they agree in every degree. -/
@[ext]
theorem hom_ext {A B : GradedQuasicoherentAlgebra X} (f g : A ⟶ B)
    (h : ∀ n, f.hom.hom.hom n = g.hom.hom.hom n) : f = g := by
  apply ObjectProperty.hom_ext
  apply CommMon.hom_ext
  exact GradedObject.hom_ext _ _ h

/-- Extract the degree-`n` component of a graded quasicoherent algebra as a quasicoherent sheaf.
On morphisms this is the degree-`n` component of the underlying graded algebra morphism. -/
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
  (rfl)

/-- The degree functor acts on a graded algebra morphism by its component in that degree. -/
@[simp]
theorem degree_map_hom {A B : GradedQuasicoherentAlgebra X} (f : A ⟶ B) (n : ℕ) :
    ((degree (X := X) n).map f).hom =
      eqToHom (degree_obj_obj A n) ≫ f.hom.hom.hom n ≫ eqToHom (degree_obj_obj B n).symm := by
  cases degree_obj_obj A n
  cases degree_obj_obj B n
  -- As for `toGradedModules_map`, eliminate the object equations before the identity laws.
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- Extract the degree-one component of a graded quasicoherent algebra. This is the component
that generates a free graded algebra and therefore the coefficient sheaf of a linear scheme. -/
abbrev degreeOne : GradedQuasicoherentAlgebra X ⥤ QuasicoherentSheaf X :=
  degree (X := X) 1

section Homogeneous

variable (M : ℕ → X.Modules) [∀ n, (M n).IsQuasicoherent] (one : 𝟙_ X.Modules ⟶ M 0)
  (mul : ∀ i j, M i ⊗ M j ⟶ M (i + j))
  (one_mul : ∀ n, (one ▷ M n) ≫ mul 0 n = (λ_ (M n)).hom ≫ eqToHom (congrArg M (zero_add n).symm))
  (mul_one : ∀ n, (M n ◁ one) ≫ mul n 0 = (ρ_ (M n)).hom ≫ eqToHom (congrArg M (add_zero n).symm))
  (mul_assoc : ∀ i j k, (mul i j ▷ M k) ≫ mul (i + j) k =
    (α_ _ _ _).hom ≫ (M i ◁ mul j k) ≫ mul i (j + k) ≫
      eqToHom (congrArg M (add_assoc i j k).symm))
  (mul_comm : ∀ i j, (β_ (M i) (M j)).hom ≫ mul j i =
    mul i j ≫ eqToHom (congrArg M (add_comm i j)))

/-- The graded quasicoherent algebra with quasicoherent homogeneous components `M n`, unit
`one : 𝒪_X ⟶ M 0` and homogeneous multiplications `mul i j : M i ⊗ M j ⟶ M (i + j)`, which are
required to be unital, associative and commutative up to the identifications of degrees. -/
def ofHomogeneous : GradedQuasicoherentAlgebra X :=
  letI := GradedObject.monObjOfHomogeneous M one mul one_mul mul_one mul_assoc
  haveI := GradedObject.isCommMonObj_monObjOfHomogeneous M one mul one_mul mul_one mul_assoc
    mul_comm
  ⟨CommMon.mk M, (isGradedQuasicoherentAlgebra_iff _).2 inferInstance⟩

/-- The underlying graded module of `ofHomogeneous` is the given family of components. -/
@[simp]
theorem ofHomogeneous_obj_X :
    (ofHomogeneous M one mul one_mul mul_one mul_assoc mul_comm).obj.X = M :=
  (rfl)

/-- The homogeneous multiplication of `ofHomogeneous` is the given one, up to the
identification `ofHomogeneous_obj_X` of its components with `M`. -/
@[simp]
theorem mul_ofHomogeneous (i j : ℕ) :
    (ofHomogeneous M one mul one_mul mul_one mul_assoc mul_comm).obj.toMon.mul i j =
      eqToHom (by rw [CommMon.toMon_X, ofHomogeneous_obj_X]) ≫ mul i j ≫
        eqToHom (congrFun (ofHomogeneous_obj_X M one mul one_mul mul_one mul_assoc mul_comm)
          (i + j)).symm :=
  (GradedObject.Monoidal.ιTensorObj_mulOfHomogeneous M mul i j (i + j) rfl).trans
    (Category.comp_id _)

/-- The unit of `ofHomogeneous` is the given one, up to the identification
`ofHomogeneous_obj_X` of its degree-zero component with `M 0`. -/
@[simp]
theorem one_ofHomogeneous :
    (ofHomogeneous M one mul one_mul mul_one mul_assoc mul_comm).obj.toMon.one =
      one ≫ eqToHom (congrFun (ofHomogeneous_obj_X M one mul one_mul mul_one mul_assoc mul_comm)
        0).symm :=
  (congrArg (GradedObject.Monoidal.tensorUnit₀.inv ≫ ·)
    (GradedObject.Monoidal.oneOfDegreeZero_zero M one)).trans (Iso.inv_hom_id_assoc _ _)

end Homogeneous

/-- A family of morphisms between the homogeneous components of two graded quasicoherent
algebras which preserves the unit and the homogeneous multiplications is a morphism of graded
quasicoherent algebras. -/
def homMk {A B : GradedQuasicoherentAlgebra X} (f : ∀ n, A.obj.X n ⟶ B.obj.X n)
    (one_f : A.obj.toMon.one ≫ f 0 = B.obj.toMon.one)
    (mul_f : ∀ i j, (f i ⊗ₘ f j) ≫ B.obj.toMon.mul i j = A.obj.toMon.mul i j ≫ f (i + j)) :
    A ⟶ B :=
  have hf := GradedObject.isMonHom_of_homogeneous (X := A.obj.X) (Y := B.obj.X) f
    (by
      rw [← cancel_epi (GradedObject.Monoidal.tensorUnit₀ (C := X.Modules)).inv]
      exact (Category.assoc _ _ _).symm.trans one_f)
    (fun i j ↦ (Category.assoc _ _ _).symm.trans (mul_f i j).symm)
  ObjectProperty.homMk (CommMon.homMk (Mon.Hom.mk' (M := A.obj.toMon) (N := B.obj.toMon) f
    hf.one_hom hf.mul_hom))

/-- The components of `homMk f` are the given morphisms. -/
@[simp]
theorem homMk_hom_hom_hom {A B : GradedQuasicoherentAlgebra X} (f : ∀ n, A.obj.X n ⟶ B.obj.X n)
    (one_f : A.obj.toMon.one ≫ f 0 = B.obj.toMon.one)
    (mul_f : ∀ i j, (f i ⊗ₘ f j) ≫ B.obj.toMon.mul i j = A.obj.toMon.mul i j ≫ f (i + j)) :
    (homMk f one_f mul_f).hom.hom.hom = f :=
  (rfl)

end GradedQuasicoherentAlgebra

end


end AlgebraicGeometry

end TauCeti
