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
generated graded algebras and their associated linear schemes are recovered. The unit
`GradedQuasicoherentAlgebra.one` and the homogeneous multiplications
`GradedQuasicoherentAlgebra.mul` are morphisms of quasicoherent sheaves between these
components, satisfying the unit, associativity and commutativity laws and preserved by morphisms
of graded algebras. These are the data transported along monoidal functors out of
quasicoherent sheaves, such as pullback.

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
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.hom_ext_of_epi_mul`: morphisms out of a
  graded quasicoherent algebra generated in degree one are determined in degree one;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.degree`: extraction of a homogeneous
  component as a quasicoherent sheaf;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.degreeOne`: the degree-one functor;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.one` and
  `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.mul`: the unit and homogeneous
  multiplications as morphisms of quasicoherent sheaves, with their laws `one_mul`, `mul_one`,
  `mul_assoc`, `mul_comm`, `one_map` and `map_mul`;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.ofHomogeneous`: conversely, the graded
  quasicoherent algebra with given quasicoherent components, unit and homogeneous
  multiplications satisfying these laws;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.homMk`: the morphism of graded
  quasicoherent algebras given by componentwise maps preserving the unit and the homogeneous
  multiplications;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.homMkOfEq`: the same, for componentwise
  maps between families identified with the homogeneous components;
* `TauCeti.AlgebraicGeometry.GradedQuasicoherentAlgebra.isoMkOfEq`: the isomorphism given by
  componentwise isomorphisms between such families.
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

/-- Morphisms out of a graded quasicoherent algebra `A` generated in degree one are determined by
their degree-one components. Here generation in degree one means that the unit `𝒪_X ⟶ A₀` and
the multiplications `Aₙ ⊗ A₁ ⟶ Aₙ₊₁` are epimorphisms, as for symmetric algebras. -/
theorem hom_ext_of_epi_mul {A B : GradedQuasicoherentAlgebra X} [Epi A.obj.toMon.one]
    [∀ n, Epi (A.obj.toMon.mul n 1)] {f g : A ⟶ B} (h : f.hom.hom.hom 1 = g.hom.hom.hom 1) :
    f = g :=
  ObjectProperty.hom_ext _ (CommMon.hom_ext _ _ (congrArg Mon.Hom.hom (Mon.hom_ext_of_epi_mul h)))

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

/-- A morphism of graded quasicoherent algebras is an epimorphism in degree `n` when its image
under the degree-`n` functor is an epimorphism of the underlying modules. -/
theorem epi_hom_hom_of_epi_degree_map {A B : GradedQuasicoherentAlgebra X} (f : A ⟶ B) (n : ℕ)
    (h : Epi ((degree (X := X) n).map f).hom) : Epi (f.hom.hom.hom n) :=
  -- The `map` field of `degree` is the degree-`n` component by construction, so taking
  -- `.hom` of its quasicoherent-sheaf morphism gives `f.hom.hom.hom n` definitionally.
  h

/-- Extract the degree-one component of a graded quasicoherent algebra. This is the component
that generates a free graded algebra and therefore the coefficient sheaf of a linear scheme. -/
abbrev degreeOne : GradedQuasicoherentAlgebra X ⥤ QuasicoherentSheaf X :=
  degree (X := X) 1

section Structure

variable (A : GradedQuasicoherentAlgebra X)

/-- The unit `𝒪_X ⟶ A₀` of a graded quasicoherent algebra, as a morphism of quasicoherent
sheaves into its degree-zero component. -/
protected def one : 𝟙_ (QuasicoherentSheaf X) ⟶ (degree 0).obj A :=
  ObjectProperty.homMk A.obj.toMon.one

/-- The homogeneous multiplication `Aᵢ ⊗ Aⱼ ⟶ Aᵢ₊ⱼ` of a graded quasicoherent algebra, as a
morphism of quasicoherent sheaves between its homogeneous components. -/
protected def mul (i j : ℕ) : (degree i).obj A ⊗ (degree j).obj A ⟶ (degree (i + j)).obj A :=
  ObjectProperty.homMk (A.obj.toMon.mul i j)

/-- The unit of `A`, as a morphism of quasicoherent sheaves, is the unit of the underlying graded
algebra on modules, up to the identification `degree_obj_obj`. -/
@[simp]
protected theorem one_hom :
    A.one.hom = A.obj.toMon.one ≫ eqToHom (degree_obj_obj A 0).symm :=
  (Category.comp_id _).symm

/-- The homogeneous multiplication of `A`, as a morphism of quasicoherent sheaves, is that of the
underlying graded algebra on modules, up to the identifications `degree_obj_obj`. -/
@[simp]
protected theorem mul_hom (i j : ℕ) :
    (A.mul i j).hom =
      (eqToHom (degree_obj_obj A i) ⊗ₘ eqToHom (degree_obj_obj A j) :
          (((degree i).obj A).obj ⊗ ((degree j).obj A).obj : X.Modules) ⟶ _) ≫
        A.obj.toMon.mul i j ≫
        eqToHom (degree_obj_obj A (i + j)).symm := by
  -- The transports are identities, since `degree` unfolds to the underlying components here.
  change _ = (𝟙 (A.obj.X i) ⊗ₘ 𝟙 (A.obj.X j) : (A.obj.X i ⊗ A.obj.X j : X.Modules) ⟶ _) ≫
    A.obj.toMon.mul i j ≫ 𝟙 _
  rw [id_tensorHom_id, Category.id_comp]
  exact (Category.comp_id _).symm

/-- The unit of a graded quasicoherent algebra is a left identity for homogeneous
multiplication, up to the identification of the degrees `0 + n` and `n`. -/
@[reassoc]
protected theorem one_mul (n : ℕ) :
    (A.one ▷ (degree n).obj A) ≫ A.mul 0 n =
      (λ_ ((degree n).obj A)).hom ≫
        eqToHom (congrArg (fun k ↦ (degree k).obj A) (zero_add n).symm) := by
  apply ObjectProperty.hom_ext
  -- Composition, whiskering and unitors of the full monoidal subcategory are those of modules.
  change (A.obj.toMon.one ▷ A.obj.X n) ≫ A.obj.toMon.mul 0 n = (λ_ (A.obj.X n)).hom ≫ _
  rw [ObjectProperty.eqToHom_hom]
  exact Mon.one_mul A.obj.toMon n

/-- The unit of a graded quasicoherent algebra is a right identity for homogeneous
multiplication, up to the identification of the degrees `n + 0` and `n`. -/
@[reassoc]
protected theorem mul_one (n : ℕ) :
    ((degree n).obj A ◁ A.one) ≫ A.mul n 0 =
      (ρ_ ((degree n).obj A)).hom ≫
        eqToHom (congrArg (fun k ↦ (degree k).obj A) (add_zero n).symm) := by
  apply ObjectProperty.hom_ext
  -- As in `one_mul`, read the full-subcategory structure maps on underlying modules.
  change (A.obj.X n ◁ A.obj.toMon.one) ≫ A.obj.toMon.mul n 0 = (ρ_ (A.obj.X n)).hom ≫ _
  rw [ObjectProperty.eqToHom_hom]
  exact Mon.mul_one A.obj.toMon n

/-- Homogeneous multiplication of a graded quasicoherent algebra is associative, up to the
identification of the degrees `i + j + k` and `i + (j + k)`. -/
@[reassoc]
protected theorem mul_assoc (i j k : ℕ) :
    (A.mul i j ▷ (degree k).obj A) ≫ A.mul (i + j) k =
      (α_ _ _ _).hom ≫ ((degree i).obj A ◁ A.mul j k) ≫ A.mul i (j + k) ≫
        eqToHom (congrArg (fun n ↦ (degree n).obj A) (add_assoc i j k).symm) := by
  apply ObjectProperty.hom_ext
  -- As in `one_mul`, read the full-subcategory structure maps on underlying modules.
  change (A.obj.toMon.mul i j ▷ A.obj.X k) ≫ A.obj.toMon.mul (i + j) k =
    (α_ (A.obj.X i) (A.obj.X j) (A.obj.X k)).hom ≫ (A.obj.X i ◁ A.obj.toMon.mul j k) ≫
      A.obj.toMon.mul i (j + k) ≫ _
  rw [ObjectProperty.eqToHom_hom]
  exact Mon.mul_assoc A.obj.toMon i j k

/-- Homogeneous multiplication of a graded quasicoherent algebra is commutative, up to the
identification of the degrees `i + j` and `j + i`. -/
@[reassoc]
protected theorem mul_comm (i j : ℕ) :
    (β_ ((degree i).obj A) ((degree j).obj A)).hom ≫ A.mul j i =
      A.mul i j ≫ eqToHom (congrArg (fun n ↦ (degree n).obj A) (add_comm i j)) := by
  apply ObjectProperty.hom_ext
  -- As in `one_mul`, read the full-subcategory structure maps on underlying modules.
  change (β_ (A.obj.X i) (A.obj.X j)).hom ≫ A.obj.toMon.mul j i = A.obj.toMon.mul i j ≫ _
  rw [ObjectProperty.eqToHom_hom]
  exact CommMon.mul_comm A.obj i j

variable {A} {B : GradedQuasicoherentAlgebra X}

/-- A morphism of graded quasicoherent algebras preserves the unit in degree zero. -/
@[reassoc, simp]
protected theorem one_map (g : A ⟶ B) : A.one ≫ (degree 0).map g = B.one :=
  ObjectProperty.hom_ext _ (Mon.one_map g.hom.hom)

/-- A morphism of graded quasicoherent algebras commutes with homogeneous multiplication. -/
@[reassoc]
protected theorem map_mul (g : A ⟶ B) (i j : ℕ) :
    ((degree i).map g ⊗ₘ (degree j).map g) ≫ B.mul i j = A.mul i j ≫ (degree (i + j)).map g :=
  ObjectProperty.hom_ext _ (Mon.map_mul g.hom.hom i j)

end Structure

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
  Mon.mul_eq _ _ _ |>.trans
    ((GradedObject.Monoidal.ιTensorObj_mulOfHomogeneous M mul i j (i + j) rfl).trans
      (Category.comp_id _))

/-- The unit of `ofHomogeneous` is the given one, up to the identification
`ofHomogeneous_obj_X` of its degree-zero component with `M 0`. -/
@[simp]
theorem one_ofHomogeneous :
    (ofHomogeneous M one mul one_mul mul_one mul_assoc mul_comm).obj.toMon.one =
      one ≫ eqToHom (congrFun (ofHomogeneous_obj_X M one mul one_mul mul_one mul_assoc mul_comm)
        0).symm :=
  Mon.one_eq _ |>.trans
    ((congrArg (GradedObject.Monoidal.tensorUnit₀.inv ≫ ·)
      (GradedObject.Monoidal.oneOfDegreeZero_zero M one)).trans (Iso.inv_hom_id_assoc _ _))

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
      rw [Mon.one_eq, Mon.one_eq] at one_f
      rw [← cancel_epi (GradedObject.Monoidal.tensorUnit₀ (C := X.Modules)).inv]
      exact (Category.assoc _ _ _).symm.trans one_f)
    (fun i j ↦ by
      have h := mul_f i j
      rw [Mon.mul_eq, Mon.mul_eq] at h
      exact (Category.assoc _ _ _).symm.trans h.symm)
  ObjectProperty.homMk (CommMon.homMk (Mon.Hom.mk' (M := A.obj.toMon) (N := B.obj.toMon) f
    hf.one_hom hf.mul_hom))

/-- The components of `homMk f` are the given morphisms. -/
@[simp]
theorem homMk_hom_hom_hom {A B : GradedQuasicoherentAlgebra X} (f : ∀ n, A.obj.X n ⟶ B.obj.X n)
    (one_f : A.obj.toMon.one ≫ f 0 = B.obj.toMon.one)
    (mul_f : ∀ i j, (f i ⊗ₘ f j) ≫ B.obj.toMon.mul i j = A.obj.toMon.mul i j ≫ f (i + j)) :
    (homMk f one_f mul_f).hom.hom.hom = f :=
  (rfl)

/-- A morphism of graded quasicoherent algebras whose homogeneous components are identified with
families `M` and `N` carrying units and multiplications, given by componentwise maps `M n ⟶ N n`
preserving those units and multiplications. This transports `homMk` along identifications of
components such as those provided by `ofHomogeneous_obj_X`. -/
def homMkOfEq {A B : GradedQuasicoherentAlgebra X} {M N : ℕ → X.Modules}
    (hA : A.obj.X = M) (hB : B.obj.X = N) {oneM : 𝟙_ X.Modules ⟶ M 0}
    {oneN : 𝟙_ X.Modules ⟶ N 0} {mulM : ∀ i j, M i ⊗ M j ⟶ M (i + j)}
    {mulN : ∀ i j, N i ⊗ N j ⟶ N (i + j)}
    (hoA : A.obj.toMon.one = oneM ≫ eqToHom (congrFun hA 0).symm)
    (hoB : B.obj.toMon.one = oneN ≫ eqToHom (congrFun hB 0).symm)
    (hmA : ∀ i j, A.obj.toMon.mul i j =
      (eqToHom (by rw [hA]) : A.obj.X i ⊗ A.obj.X j ⟶ M i ⊗ M j) ≫ mulM i j ≫
        eqToHom (congrFun hA (i + j)).symm)
    (hmB : ∀ i j, B.obj.toMon.mul i j =
      (eqToHom (by rw [hB]) : B.obj.X i ⊗ B.obj.X j ⟶ N i ⊗ N j) ≫ mulN i j ≫
        eqToHom (congrFun hB (i + j)).symm)
    (f : ∀ n, M n ⟶ N n) (one_f : oneM ≫ f 0 = oneN)
    (mul_f : ∀ i j, (f i ⊗ₘ f j) ≫ mulN i j = mulM i j ≫ f (i + j)) : A ⟶ B :=
  homMk (fun n ↦ eqToHom (congrFun hA n) ≫ f n ≫ eqToHom (congrFun hB n).symm)
    (by subst hA hB; simp only [hoA, hoB, eqToHom_refl, Category.comp_id, Category.id_comp]
        exact one_f)
    (fun i j ↦ by
      subst hA hB
      simp only [hmA, hmB, eqToHom_refl, Category.comp_id, Category.id_comp]
      exact mul_f i j)

/-- The components of `homMkOfEq` are the given morphisms, transported along the identifications
of the homogeneous components. -/
@[simp]
theorem homMkOfEq_hom_hom_hom {A B : GradedQuasicoherentAlgebra X} {M N : ℕ → X.Modules}
    (hA : A.obj.X = M) (hB : B.obj.X = N) {oneM : 𝟙_ X.Modules ⟶ M 0}
    {oneN : 𝟙_ X.Modules ⟶ N 0} {mulM : ∀ i j, M i ⊗ M j ⟶ M (i + j)}
    {mulN : ∀ i j, N i ⊗ N j ⟶ N (i + j)}
    (hoA : A.obj.toMon.one = oneM ≫ eqToHom (congrFun hA 0).symm)
    (hoB : B.obj.toMon.one = oneN ≫ eqToHom (congrFun hB 0).symm)
    (hmA : ∀ i j, A.obj.toMon.mul i j =
      (eqToHom (by rw [hA]) : A.obj.X i ⊗ A.obj.X j ⟶ M i ⊗ M j) ≫ mulM i j ≫
        eqToHom (congrFun hA (i + j)).symm)
    (hmB : ∀ i j, B.obj.toMon.mul i j =
      (eqToHom (by rw [hB]) : B.obj.X i ⊗ B.obj.X j ⟶ N i ⊗ N j) ≫ mulN i j ≫
        eqToHom (congrFun hB (i + j)).symm)
    (f : ∀ n, M n ⟶ N n) (one_f : oneM ≫ f 0 = oneN)
    (mul_f : ∀ i j, (f i ⊗ₘ f j) ≫ mulN i j = mulM i j ≫ f (i + j)) (n : ℕ) :
    (homMkOfEq hA hB hoA hoB hmA hmB f one_f mul_f).hom.hom.hom n =
      eqToHom (congrFun hA n) ≫ f n ≫ eqToHom (congrFun hB n).symm :=
  (rfl)

/-- `homMkOfEq` sends a family of identities to the identity. -/
theorem homMkOfEq_id {A : GradedQuasicoherentAlgebra X} {M : ℕ → X.Modules} (hA : A.obj.X = M)
    {oneM : 𝟙_ X.Modules ⟶ M 0} {mulM : ∀ i j, M i ⊗ M j ⟶ M (i + j)}
    (hoA : A.obj.toMon.one = oneM ≫ eqToHom (congrFun hA 0).symm)
    (hmA : ∀ i j, A.obj.toMon.mul i j =
      (eqToHom (by rw [hA]) : A.obj.X i ⊗ A.obj.X j ⟶ M i ⊗ M j) ≫ mulM i j ≫
        eqToHom (congrFun hA (i + j)).symm)
    (f : ∀ n, M n ⟶ M n) (one_f : oneM ≫ f 0 = oneM)
    (mul_f : ∀ i j, (f i ⊗ₘ f j) ≫ mulM i j = mulM i j ≫ f (i + j)) (hf : ∀ n, f n = 𝟙 (M n)) :
    homMkOfEq hA hA hoA hoA hmA hmA f one_f mul_f = 𝟙 A :=
  hom_ext _ _ fun n ↦ by
    subst hA
    simp only [homMkOfEq_hom_hom_hom, hf, eqToHom_refl, Category.id_comp]
    -- The identity of a graded algebra is displayed on `A.obj.toMon.X n`, which is `A.obj.X n`
    -- by definition of `CommMon.toMon`.
    rfl

/-- `homMkOfEq` sends componentwise composites to composites. -/
theorem homMkOfEq_comp {A B C : GradedQuasicoherentAlgebra X} {M N P : ℕ → X.Modules}
    (hA : A.obj.X = M) (hB : B.obj.X = N) (hC : C.obj.X = P) {oneM : 𝟙_ X.Modules ⟶ M 0}
    {oneN : 𝟙_ X.Modules ⟶ N 0} {oneP : 𝟙_ X.Modules ⟶ P 0}
    {mulM : ∀ i j, M i ⊗ M j ⟶ M (i + j)} {mulN : ∀ i j, N i ⊗ N j ⟶ N (i + j)}
    {mulP : ∀ i j, P i ⊗ P j ⟶ P (i + j)}
    (hoA : A.obj.toMon.one = oneM ≫ eqToHom (congrFun hA 0).symm)
    (hoB : B.obj.toMon.one = oneN ≫ eqToHom (congrFun hB 0).symm)
    (hoC : C.obj.toMon.one = oneP ≫ eqToHom (congrFun hC 0).symm)
    (hmA : ∀ i j, A.obj.toMon.mul i j =
      (eqToHom (by rw [hA]) : A.obj.X i ⊗ A.obj.X j ⟶ M i ⊗ M j) ≫ mulM i j ≫
        eqToHom (congrFun hA (i + j)).symm)
    (hmB : ∀ i j, B.obj.toMon.mul i j =
      (eqToHom (by rw [hB]) : B.obj.X i ⊗ B.obj.X j ⟶ N i ⊗ N j) ≫ mulN i j ≫
        eqToHom (congrFun hB (i + j)).symm)
    (hmC : ∀ i j, C.obj.toMon.mul i j =
      (eqToHom (by rw [hC]) : C.obj.X i ⊗ C.obj.X j ⟶ P i ⊗ P j) ≫ mulP i j ≫
        eqToHom (congrFun hC (i + j)).symm)
    (f : ∀ n, M n ⟶ N n) (one_f : oneM ≫ f 0 = oneN)
    (mul_f : ∀ i j, (f i ⊗ₘ f j) ≫ mulN i j = mulM i j ≫ f (i + j))
    (g : ∀ n, N n ⟶ P n) (one_g : oneN ≫ g 0 = oneP)
    (mul_g : ∀ i j, (g i ⊗ₘ g j) ≫ mulP i j = mulN i j ≫ g (i + j))
    (h : ∀ n, M n ⟶ P n) (one_h : oneM ≫ h 0 = oneP)
    (mul_h : ∀ i j, (h i ⊗ₘ h j) ≫ mulP i j = mulM i j ≫ h (i + j))
    (hfg : ∀ n, f n ≫ g n = h n) :
    homMkOfEq hA hC hoA hoC hmA hmC h one_h mul_h =
      homMkOfEq hA hB hoA hoB hmA hmB f one_f mul_f ≫
        homMkOfEq hB hC hoB hoC hmB hmC g one_g mul_g :=
  hom_ext _ _ fun n ↦ by
    subst hA hB hC
    simp only [homMkOfEq_hom_hom_hom, ObjectProperty.FullSubcategory.comp_hom, CommMon.comp_hom,
      eqToHom_refl, Category.id_comp, Category.comp_id, ← hfg]
    -- The composite of graded morphisms is displayed through the middle object
    -- `B.obj.toMon.X n`, which is `B.obj.X n` by definition of `CommMon.toMon`.
    rfl

/-- An isomorphism of graded quasicoherent algebras whose homogeneous components are identified
with families `M` and `N` carrying units and multiplications, given by componentwise isomorphisms
`M n ≅ N n` preserving those units and multiplications. Both directions are built by
`homMkOfEq`. -/
def isoMkOfEq {P Q : GradedQuasicoherentAlgebra X} {M N : ℕ → X.Modules}
    (hP : P.obj.X = M) (hQ : Q.obj.X = N) {oneM : 𝟙_ X.Modules ⟶ M 0}
    {oneN : 𝟙_ X.Modules ⟶ N 0} {mulM : ∀ i j, M i ⊗ M j ⟶ M (i + j)}
    {mulN : ∀ i j, N i ⊗ N j ⟶ N (i + j)}
    (hoP : P.obj.toMon.one = oneM ≫ eqToHom (congrFun hP 0).symm)
    (hoQ : Q.obj.toMon.one = oneN ≫ eqToHom (congrFun hQ 0).symm)
    (hmP : ∀ i j, P.obj.toMon.mul i j =
      (eqToHom (by rw [hP]) : P.obj.X i ⊗ P.obj.X j ⟶ M i ⊗ M j) ≫ mulM i j ≫
        eqToHom (congrFun hP (i + j)).symm)
    (hmQ : ∀ i j, Q.obj.toMon.mul i j =
      (eqToHom (by rw [hQ]) : Q.obj.X i ⊗ Q.obj.X j ⟶ N i ⊗ N j) ≫ mulN i j ≫
        eqToHom (congrFun hQ (i + j)).symm)
    (e : ∀ n, M n ≅ N n) (one_e : oneM ≫ (e 0).hom = oneN)
    (mul_e : ∀ i j, ((e i).hom ⊗ₘ (e j).hom) ≫ mulN i j = mulM i j ≫ (e (i + j)).hom) :
    P ≅ Q where
  hom := homMkOfEq hP hQ hoP hoQ hmP hmQ (fun n ↦ (e n).hom) one_e mul_e
  inv := homMkOfEq hQ hP hoQ hoP hmQ hmP (fun n ↦ (e n).inv)
    (by rw [← one_e, Category.assoc, Iso.hom_inv_id, Category.comp_id])
    (fun i j ↦ by
      rw [Iso.eq_comp_inv, Category.assoc, ← mul_e, ← tensorIso_hom, ← tensorIso_inv,
        Iso.inv_hom_id_assoc])
  hom_inv_id := (homMkOfEq_comp hP hQ hP hoP hoQ hoP hmP hmQ hmP _ one_e mul_e _ _ _
    (fun n ↦ 𝟙 (M n)) (Category.comp_id _) (fun i j ↦ by simp)
      fun n ↦ (e n).hom_inv_id).symm.trans (homMkOfEq_id hP hoP hmP _ _ _ fun _ ↦ rfl)
  inv_hom_id := (homMkOfEq_comp hQ hP hQ hoQ hoP hoQ hmQ hmP hmQ _ _ _ _ one_e mul_e
    (fun n ↦ 𝟙 (N n)) (Category.comp_id _) (fun i j ↦ by simp)
      fun n ↦ (e n).inv_hom_id).symm.trans (homMkOfEq_id hQ hoQ hmQ _ _ _ fun _ ↦ rfl)

/-- The components of `isoMkOfEq` are the given isomorphisms, transported along the
identifications of the homogeneous components. -/
@[simp]
theorem isoMkOfEq_hom_hom_hom_hom {P Q : GradedQuasicoherentAlgebra X} {M N : ℕ → X.Modules}
    (hP : P.obj.X = M) (hQ : Q.obj.X = N) {oneM : 𝟙_ X.Modules ⟶ M 0}
    {oneN : 𝟙_ X.Modules ⟶ N 0} {mulM : ∀ i j, M i ⊗ M j ⟶ M (i + j)}
    {mulN : ∀ i j, N i ⊗ N j ⟶ N (i + j)}
    (hoP : P.obj.toMon.one = oneM ≫ eqToHom (congrFun hP 0).symm)
    (hoQ : Q.obj.toMon.one = oneN ≫ eqToHom (congrFun hQ 0).symm)
    (hmP : ∀ i j, P.obj.toMon.mul i j =
      (eqToHom (by rw [hP]) : P.obj.X i ⊗ P.obj.X j ⟶ M i ⊗ M j) ≫ mulM i j ≫
        eqToHom (congrFun hP (i + j)).symm)
    (hmQ : ∀ i j, Q.obj.toMon.mul i j =
      (eqToHom (by rw [hQ]) : Q.obj.X i ⊗ Q.obj.X j ⟶ N i ⊗ N j) ≫ mulN i j ≫
        eqToHom (congrFun hQ (i + j)).symm)
    (e : ∀ n, M n ≅ N n) (one_e : oneM ≫ (e 0).hom = oneN)
    (mul_e : ∀ i j, ((e i).hom ⊗ₘ (e j).hom) ≫ mulN i j = mulM i j ≫ (e (i + j)).hom) (n : ℕ) :
    (isoMkOfEq hP hQ hoP hoQ hmP hmQ e one_e mul_e).hom.hom.hom.hom n =
      eqToHom (congrFun hP n) ≫ (e n).hom ≫ eqToHom (congrFun hQ n).symm :=
  (rfl)

/-- The components of the inverse of `isoMkOfEq` are the inverses of the given isomorphisms,
transported along the identifications of the homogeneous components. -/
@[simp]
theorem isoMkOfEq_inv_hom_hom_hom {P Q : GradedQuasicoherentAlgebra X} {M N : ℕ → X.Modules}
    (hP : P.obj.X = M) (hQ : Q.obj.X = N) {oneM : 𝟙_ X.Modules ⟶ M 0}
    {oneN : 𝟙_ X.Modules ⟶ N 0} {mulM : ∀ i j, M i ⊗ M j ⟶ M (i + j)}
    {mulN : ∀ i j, N i ⊗ N j ⟶ N (i + j)}
    (hoP : P.obj.toMon.one = oneM ≫ eqToHom (congrFun hP 0).symm)
    (hoQ : Q.obj.toMon.one = oneN ≫ eqToHom (congrFun hQ 0).symm)
    (hmP : ∀ i j, P.obj.toMon.mul i j =
      (eqToHom (by rw [hP]) : P.obj.X i ⊗ P.obj.X j ⟶ M i ⊗ M j) ≫ mulM i j ≫
        eqToHom (congrFun hP (i + j)).symm)
    (hmQ : ∀ i j, Q.obj.toMon.mul i j =
      (eqToHom (by rw [hQ]) : Q.obj.X i ⊗ Q.obj.X j ⟶ N i ⊗ N j) ≫ mulN i j ≫
        eqToHom (congrFun hQ (i + j)).symm)
    (e : ∀ n, M n ≅ N n) (one_e : oneM ≫ (e 0).hom = oneN)
    (mul_e : ∀ i j, ((e i).hom ⊗ₘ (e j).hom) ≫ mulN i j = mulM i j ≫ (e (i + j)).hom) (n : ℕ) :
    (isoMkOfEq hP hQ hoP hoQ hmP hmQ e one_e mul_e).inv.hom.hom.hom n =
      eqToHom (congrFun hQ n) ≫ (e n).inv ≫ eqToHom (congrFun hP n).symm :=
  (rfl)

end GradedQuasicoherentAlgebra

end


end AlgebraicGeometry

end TauCeti
