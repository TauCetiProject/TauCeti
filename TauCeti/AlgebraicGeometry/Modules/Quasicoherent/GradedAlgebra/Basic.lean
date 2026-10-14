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
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.degreeOne`: the degree-one functor;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.mul` and
  `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.one`: homogeneous multiplication and the
  unit, with their associativity, commutativity, and unit laws.
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

/-- Multiplication through the summand of degree `n = i + j` is homogeneous multiplication
followed by the transport along `i + j = n`. -/
private theorem ιTensorObj_mul (A : GradedQuasicoherentAlgebra X) {i j n : ℕ} (h : i + j = n) :
    GradedObject.Monoidal.ιTensorObj A.obj.X A.obj.X i j n h ≫ μ[A.obj.X] n =
      A.mul i j ≫ eqToHom (congrArg A.obj.X h) := by
  subst h
  rw [eqToHom_refl, Category.comp_id]
  rfl

/-- Homogeneous multiplication is associative, up to the transport identifying the degrees
`i + (j + k)` and `i + j + k`. -/
@[reassoc]
theorem mul_assoc (A : GradedQuasicoherentAlgebra X) (i j k : ℕ) :
    (A.mul i j ▷ A.obj.X k) ≫ A.mul (i + j) k =
      (α_ _ _ _).hom ≫ (A.obj.X i ◁ A.mul j k) ≫ A.mul i (j + k) ≫
        eqToHom (congrArg A.obj.X (add_assoc i j k).symm) := by
  have h := congrArg (GradedObject.Monoidal.ιTensorObj₃' A.obj.X A.obj.X A.obj.X i j k _ rfl ≫ ·)
    (congrFun (MonObj.mul_assoc A.obj.X) (i + j + k))
  -- The components of the monoidal structure maps of graded objects are displayed through the
  -- instance, while the summand-inclusion lemmas are stated for the underlying constructions.
  change GradedObject.Monoidal.ιTensorObj₃' A.obj.X A.obj.X A.obj.X i j k _ rfl ≫
      GradedObject.Monoidal.tensorHom μ[A.obj.X] (𝟙 A.obj.X) (i + j + k) ≫ μ[A.obj.X] (i + j + k) =
    GradedObject.Monoidal.ιTensorObj₃' A.obj.X A.obj.X A.obj.X i j k _ rfl ≫
      (GradedObject.Monoidal.associator A.obj.X A.obj.X A.obj.X).hom (i + j + k) ≫
      GradedObject.Monoidal.tensorHom (𝟙 A.obj.X) μ[A.obj.X] (i + j + k) ≫
        μ[A.obj.X] (i + j + k) at h
  rw [GradedObject.Monoidal.ιTensorObj₃'_associator_hom_assoc,
    GradedObject.Monoidal.ιTensorObj₃_eq_assoc _ _ _ i j k _ _ (j + k) rfl,
    GradedObject.Monoidal.ι_tensorHom_assoc, ιTensorObj_mul,
    GradedObject.Monoidal.ιTensorObj₃'_eq_assoc _ _ _ i j k _ _ (i + j) rfl,
    GradedObject.Monoidal.ι_tensorHom_assoc] at h
  simpa only [mul, GradedObject.categoryOfGradedObjects_id, tensorHom_id, id_tensorHom,
    comp_whiskerRight, whiskerLeft_comp, Category.assoc] using h

/-- Homogeneous multiplication is commutative, up to the transport identifying the degrees
`i + j` and `j + i`. -/
@[reassoc]
theorem mul_comm (A : GradedQuasicoherentAlgebra X) (i j : ℕ) :
    (β_ (A.obj.X i) (A.obj.X j)).hom ≫ A.mul j i =
      A.mul i j ≫ eqToHom (congrArg A.obj.X (add_comm i j)) := by
  have h := congrArg (GradedObject.Monoidal.ιTensorObj A.obj.X A.obj.X i j (i + j) rfl ≫ ·)
    (congrFun (IsCommMonObj.mul_comm A.obj.X) (i + j))
  -- As for `mul_assoc`, display the braiding component through its underlying construction.
  change GradedObject.Monoidal.ιTensorObj A.obj.X A.obj.X i j (i + j) rfl ≫
      (GradedObject.Monoidal.braiding A.obj.X A.obj.X).hom (i + j) ≫ μ[A.obj.X] (i + j) =
    A.mul i j at h
  dsimp only [GradedObject.Monoidal.braiding] at h
  rw [GradedObject.Monoidal.ι_tensorObjDesc_assoc, Category.assoc, ιTensorObj_mul] at h
  rw [← h]
  simp

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

/-- The unit is a left identity for homogeneous multiplication, up to the transport identifying
the degrees `0 + n` and `n`. -/
@[reassoc (attr := simp)]
theorem one_mul (A : GradedQuasicoherentAlgebra X) (n : ℕ) :
    (A.one ▷ A.obj.X n) ≫ A.mul 0 n =
      (λ_ (A.obj.X n)).hom ≫ eqToHom (congrArg A.obj.X (zero_add n).symm) := by
  have h : (λ_ A.obj.X).inv ≫ η[A.obj.X] ▷ A.obj.X ≫ μ[A.obj.X] = 𝟙 A.obj.X := by
    rw [MonObj.one_mul, Iso.inv_hom_id]
  replace h := congrFun h n
  -- As for `mul_assoc`, display the unitor component through its underlying construction.
  change (λ_ (A.obj.X n)).inv ≫ GradedObject.Monoidal.tensorUnit₀.inv ▷ A.obj.X n ≫
      GradedObject.Monoidal.ιTensorObj GradedObject.Monoidal.tensorUnit A.obj.X 0 n n
        (zero_add n) ≫
      GradedObject.Monoidal.tensorHom η[A.obj.X] (𝟙 A.obj.X) n ≫ μ[A.obj.X] n = 𝟙 _ at h
  rw [GradedObject.Monoidal.ι_tensorHom_assoc, ιTensorObj_mul] at h
  rw [← Iso.inv_comp_eq, ← cancel_mono (eqToHom (congrArg A.obj.X (zero_add n)))]
  simpa only [one, GradedObject.categoryOfGradedObjects_id, tensorHom_id, comp_whiskerRight,
    Category.assoc, eqToHom_trans, eqToHom_refl] using h

/-- The unit is a right identity for homogeneous multiplication, up to the transport identifying
the degrees `n + 0` and `n`. -/
@[reassoc (attr := simp)]
theorem mul_one (A : GradedQuasicoherentAlgebra X) (n : ℕ) :
    (A.obj.X n ◁ A.one) ≫ A.mul n 0 =
      (ρ_ (A.obj.X n)).hom ≫ eqToHom (congrArg A.obj.X (add_zero n).symm) := by
  have h : (ρ_ A.obj.X).inv ≫ A.obj.X ◁ η[A.obj.X] ≫ μ[A.obj.X] = 𝟙 A.obj.X := by
    rw [MonObj.mul_one, Iso.inv_hom_id]
  replace h := congrFun h n
  -- As for `mul_assoc`, display the unitor component through its underlying construction.
  change (ρ_ (A.obj.X n)).inv ≫ A.obj.X n ◁ GradedObject.Monoidal.tensorUnit₀.inv ≫
      GradedObject.Monoidal.ιTensorObj A.obj.X GradedObject.Monoidal.tensorUnit n 0 n
        (add_zero n) ≫
      GradedObject.Monoidal.tensorHom (𝟙 A.obj.X) η[A.obj.X] n ≫ μ[A.obj.X] n = 𝟙 _ at h
  rw [GradedObject.Monoidal.ι_tensorHom_assoc, ιTensorObj_mul] at h
  rw [← Iso.inv_comp_eq, ← cancel_mono (eqToHom (congrArg A.obj.X (add_zero n)))]
  simpa only [one, GradedObject.categoryOfGradedObjects_id, id_tensorHom, whiskerLeft_comp,
    Category.assoc, Category.comp_id, eqToHom_trans, eqToHom_refl] using h

end GradedQuasicoherentAlgebra

end


end AlgebraicGeometry

end TauCeti
