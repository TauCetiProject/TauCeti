/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.GradedObject.Braiding
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import TauCeti.CategoryTheory.EqToHom

/-!
# Monoid objects in graded objects from homogeneous data

For a monoidal category `C` and an additive monoid `I`, the tensor product of graded objects
`X ⊗ Y` has the coproduct of the `X i ⊗ Y j` with `i + j = n` in degree `n`, and the unit is
`𝟙_ C` placed in degree `0`. A monoid object structure on a graded object `X` is therefore the
same as a family of homogeneous multiplications `X i ⊗ X j ⟶ X (i + j)` together with a unit
`𝟙_ C ⟶ X 0`, subject to the graded associativity and unit laws. This file proves the
introduction direction of that description: it assembles such homogeneous data into a monoid
object, a commutative monoid object when the homogeneous multiplications commute, and recognizes
morphisms of monoid objects by their homogeneous components. In the other direction, it extracts
the homogeneous unit and multiplications, together with their laws, from a monoid object in
graded objects, and their graded commutativity from a commutative one. This is how graded
algebras such as symmetric algebras, which are naturally described degree by degree, are given
and used as monoid objects in graded objects.

Homogeneous data can be transported along a lax monoidal functor `F : C ⥤ D`: given
identifications `e n : Y n ≅ F.obj (X n)`, the multiplications
`Y i ⊗ Y j ⟶ F.obj (X i) ⊗ F.obj (X j) ⟶ F.obj (X i ⊗ X j) ⟶ F.obj (X (i + j)) ⟶ Y (i + j)`
and the unit `𝟙_ D ⟶ F.obj (𝟙_ C) ⟶ F.obj (X 0) ⟶ Y 0` satisfy the graded laws whenever the
original data do, and the graded commutativity law too when `F` is lax braided. This is how a
graded algebra described degree by degree on presheaves, such as a sectionwise symmetric algebra,
passes to sheaves along sheafification.

## Main declarations

* `CategoryTheory.GradedObject.Monoidal.mulOfHomogeneous`: the morphism `X ⊗ X ⟶ X` assembled
  from homogeneous multiplications, characterized by
  `CategoryTheory.GradedObject.Monoidal.ιTensorObj_mulOfHomogeneous`;
* `CategoryTheory.GradedObject.Monoidal.oneOfDegreeZero`: the morphism `𝟙_ ⟶ X` determined by a
  morphism `𝟙_ C ⟶ X 0`;
* `CategoryTheory.GradedObject.monObjOfHomogeneous`: the monoid object structure defined by
  homogeneous data satisfying the graded associativity and unit laws;
* `CategoryTheory.GradedObject.isCommMonObj_monObjOfHomogeneous`: commutativity of that monoid
  object from graded commutativity of the homogeneous multiplications;
* `CategoryTheory.GradedObject.isMonHom_of_homogeneous`: a morphism of graded objects between
  monoid objects is a monoid morphism once it preserves the unit in degree zero and the
  multiplication of homogeneous components;
* `CategoryTheory.Mon.mul` and `CategoryTheory.Mon.one`: the homogeneous multiplication
  and degree-zero unit extracted from a monoid object in graded objects, together with their
  associativity, unit, and functoriality laws; `CategoryTheory.CommMon.mul_comm` is their
  graded commutativity for a commutative monoid object;
* `CategoryTheory.Mon.hom_ext_of_epi_mul`: morphisms out of an `ℕ`-graded monoid object
  generated in degree one, in the sense that its unit and the multiplications
  `A.X n ⊗ A.X 1 ⟶ A.X (n + 1)` are epimorphisms, are determined by their degree-one components;
* `CategoryTheory.GradedObject.mul_assoc_of_laxMonoidal`,
  `CategoryTheory.GradedObject.one_mul_of_laxMonoidal`,
  `CategoryTheory.GradedObject.mul_one_of_laxMonoidal` and
  `CategoryTheory.GradedObject.mul_comm_of_laxBraided`: the graded laws of homogeneous data
  transported along a lax monoidal (resp. lax braided) functor;
* `CategoryTheory.GradedObject.map_mul_of_laxMonoidal`: transported morphisms commute with the
  transported homogeneous multiplications.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory MonObj

namespace CategoryTheory.GradedObject

variable {I : Type*} {C : Type*} [Category* C] [MonoidalCategory C]

section AddMonoid

variable [AddMonoid I]

namespace Monoidal

section Mul

variable (X : GradedObject I C) [HasTensor X X]

/-- The morphism `X ⊗ X ⟶ X` of graded objects whose restriction to the summand `X i ⊗ X j` of
degree `i + j` is the homogeneous multiplication `mul i j`. -/
def mulOfHomogeneous (mul : ∀ i j, X i ⊗ X j ⟶ X (i + j)) : tensorObj X X ⟶ X :=
  fun _ ↦ tensorObjDesc fun i j h ↦ mul i j ≫ eqToHom (congrArg X h)

/-- On the summand `X i ⊗ X j` of degree `n = i + j`, the assembled multiplication is the
homogeneous multiplication followed by the transport along `i + j = n`. -/
@[reassoc (attr := simp)]
lemma ιTensorObj_mulOfHomogeneous (mul : ∀ i j, X i ⊗ X j ⟶ X (i + j)) (i j n : I)
    (h : i + j = n) :
    ιTensorObj X X i j n h ≫ mulOfHomogeneous X mul n = mul i j ≫ eqToHom (congrArg X h) :=
  ι_tensorObjDesc _ _ _ _

end Mul

section One

variable [DecidableEq I] [HasInitial C]

/-- Two morphisms out of the tensor unit of graded objects agree as soon as they agree in degree
zero, since the unit is initial in every other degree. -/
lemma tensorUnit_hom_ext {X : GradedObject I C} (f g : tensorUnit ⟶ X) (h : f 0 = g 0) :
    f = g := by
  ext i
  by_cases hi : i = 0
  · subst hi
    exact h
  · exact (isInitialTensorUnitApply i hi).hom_ext _ _

variable (X : GradedObject I C)

/-- The morphism `𝟙_ ⟶ X` of graded objects given in degree zero by `one : 𝟙_ C ⟶ X 0`; in
every other degree the tensor unit is initial. -/
def oneOfDegreeZero (one : 𝟙_ C ⟶ X 0) : tensorUnit ⟶ X := fun i ↦
  if h : i = 0 then (singleObjApplyIsoOfEq 0 (𝟙_ C) i h).hom ≫ one ≫ eqToHom (congrArg X h.symm)
  else (isInitialTensorUnitApply i h).to (X i)

/-- In degree zero, the unit determined by `one` is `one`, up to the identification of the
degree-zero part of the tensor unit with `𝟙_ C`. -/
@[simp]
lemma oneOfDegreeZero_zero (one : 𝟙_ C ⟶ X 0) :
    oneOfDegreeZero X one 0 = tensorUnit₀.hom ≫ one := by
  simp [oneOfDegreeZero, tensorUnit₀]

end One

end Monoidal

section MonObj

variable
  [∀ (X₁ X₂ : GradedObject I C), HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [DecidableEq I] [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), HasTensor₄ObjExt X₁ X₂ X₃ X₄]

/-- A morphism of graded objects between monoid objects is a morphism of monoid objects as soon
as it preserves the unit in degree zero and commutes with multiplication on every pair of
homogeneous components. -/
lemma isMonHom_of_homogeneous {X Y : GradedObject I C} [MonObj X] [MonObj Y] (f : X ⟶ Y)
    (one_f : η[X] 0 ≫ f 0 = η[Y] 0)
    (mul_f : ∀ i j, Monoidal.ιTensorObj X X i j (i + j) rfl ≫ μ[X] (i + j) ≫ f (i + j) =
      (f i ⊗ₘ f j) ≫ Monoidal.ιTensorObj Y Y i j (i + j) rfl ≫ μ[Y] (i + j)) :
    IsMonHom f where
  one_hom := Monoidal.tensorUnit_hom_ext _ _ one_f
  mul_hom := by
    ext n
    refine Monoidal.tensorObj_ext _ _ fun i j h ↦ ?_
    subst h
    -- The tensor product of morphisms of graded objects is `Monoidal.tensorHom`.
    change Monoidal.ιTensorObj X X i j (i + j) rfl ≫ (μ[X] ≫ f) (i + j) =
      Monoidal.ιTensorObj X X i j (i + j) rfl ≫ (Monoidal.tensorHom f f ≫ μ[Y]) (i + j)
    simpa using mul_f i j

variable (X : GradedObject I C) (one : 𝟙_ C ⟶ X 0) (mul : ∀ i j, X i ⊗ X j ⟶ X (i + j))
  (one_mul : ∀ n, (one ▷ X n) ≫ mul 0 n = (λ_ (X n)).hom ≫ eqToHom (congrArg X (zero_add n).symm))
  (mul_one : ∀ n, (X n ◁ one) ≫ mul n 0 = (ρ_ (X n)).hom ≫ eqToHom (congrArg X (add_zero n).symm))
  (mul_assoc : ∀ i j k, (mul i j ▷ X k) ≫ mul (i + j) k =
    (α_ _ _ _).hom ≫ (X i ◁ mul j k) ≫ mul i (j + k) ≫
      eqToHom (congrArg X (add_assoc i j k).symm))

/-- The monoid object structure on a graded object `X` given by a unit `one : 𝟙_ C ⟶ X 0` and
homogeneous multiplications `mul i j : X i ⊗ X j ⟶ X (i + j)` satisfying the graded unit and
associativity laws, in which the degrees are identified along `0 + n = n`, `n + 0 = n` and
`i + (j + k) = i + j + k`. -/
abbrev monObjOfHomogeneous :
    MonObj X where
  one := Monoidal.oneOfDegreeZero X one
  mul := Monoidal.mulOfHomogeneous X mul
  one_mul := by
    rw [← cancel_epi (λ_ X).inv, Iso.inv_hom_id]
    ext n
    -- The inverse left unitor of graded objects includes `𝟙_ C ⊗ X n` as the summand `(0, n)`,
    -- and right whiskering of graded objects is `Monoidal.tensorHom`.
    change ((Monoidal.leftUnitor X).inv ≫
      Monoidal.tensorHom (Monoidal.oneOfDegreeZero X one) (𝟙 X) ≫
        Monoidal.mulOfHomogeneous X mul) n = 𝟙 _
    simp [Monoidal.leftUnitor_inv_apply, reassoc_of% one_mul n]
  mul_one := by
    rw [← cancel_epi (ρ_ X).inv, Iso.inv_hom_id]
    ext n
    -- The inverse right unitor of graded objects includes `X n ⊗ 𝟙_ C` as the summand `(n, 0)`,
    -- and left whiskering of graded objects is `Monoidal.tensorHom`.
    change ((Monoidal.rightUnitor X).inv ≫
      Monoidal.tensorHom (𝟙 X) (Monoidal.oneOfDegreeZero X one) ≫
        Monoidal.mulOfHomogeneous X mul) n = 𝟙 _
    simp [Monoidal.rightUnitor_inv_apply, reassoc_of% mul_one n]
  mul_assoc := by
    ext n
    refine Monoidal.tensorObj₃'_ext _ _ fun i j k h ↦ ?_
    -- The associator of graded objects is `Monoidal.associator`, which sends the summand
    -- `(X i ⊗ X j) ⊗ X k` to `X i ⊗ (X j ⊗ X k)` by the associator of `C`; whiskering of
    -- graded objects is `Monoidal.tensorHom`.
    change Monoidal.ιTensorObj₃' X X X i j k n h ≫ (Monoidal.tensorHom
        (Monoidal.mulOfHomogeneous X mul) (𝟙 X) ≫ Monoidal.mulOfHomogeneous X mul) n =
      Monoidal.ιTensorObj₃' X X X i j k n h ≫ (Monoidal.associator X X X).hom n ≫
        (Monoidal.tensorHom (𝟙 X) (Monoidal.mulOfHomogeneous X mul) ≫
          Monoidal.mulOfHomogeneous X mul) n
    rw [Monoidal.ιTensorObj₃'_associator_hom_assoc,
      Monoidal.ιTensorObj₃'_eq X X X i j k n h (i + j) rfl,
      Monoidal.ιTensorObj₃_eq X X X i j k n h (j + k) rfl]
    simp [← comp_whiskerRight_assoc, ← whiskerLeft_comp_assoc, reassoc_of% mul_assoc i j k]

/-- The multiplication of the monoid object defined by homogeneous data is assembled from the
homogeneous multiplications. -/
@[simp]
lemma mul_monObjOfHomogeneous :
    MonObj.mul (self := monObjOfHomogeneous X one mul one_mul mul_one mul_assoc) =
      Monoidal.mulOfHomogeneous X mul :=
  rfl

/-- The unit of the monoid object defined by homogeneous data is the given unit in degree zero. -/
@[simp]
lemma one_monObjOfHomogeneous :
    MonObj.one (self := monObjOfHomogeneous X one mul one_mul mul_one mul_assoc) =
      Monoidal.oneOfDegreeZero X one :=
  rfl

end MonObj

end AddMonoid

section AddCommMonoid

variable [AddCommMonoid I] [BraidedCategory C]
  [∀ (X₁ X₂ : GradedObject I C), HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [DecidableEq I] [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), HasTensor₄ObjExt X₁ X₂ X₃ X₄]

/-- On the summand `X i ⊗ Y j`, the braiding of graded objects is the braiding of `C` followed
by the inclusion of the summand `Y j ⊗ X i`. -/
@[reassoc (attr := simp)]
lemma ιTensorObj_braiding_hom (X Y : GradedObject I C) (i j n : I) (h : i + j = n) :
    Monoidal.ιTensorObj X Y i j n h ≫ (β_ X Y).hom n =
      (β_ (X i) (Y j)).hom ≫ Monoidal.ιTensorObj Y X j i n (by rw [add_comm, h]) := by
  -- The braiding of graded objects is `Monoidal.braiding`, defined summand by summand.
  change Monoidal.ιTensorObj X Y i j n h ≫ (Monoidal.braiding X Y).hom n = _
  simp [Monoidal.braiding]

variable (X : GradedObject I C) (one : 𝟙_ C ⟶ X 0) (mul : ∀ i j, X i ⊗ X j ⟶ X (i + j))
  (one_mul : ∀ n, (one ▷ X n) ≫ mul 0 n = (λ_ (X n)).hom ≫ eqToHom (congrArg X (zero_add n).symm))
  (mul_one : ∀ n, (X n ◁ one) ≫ mul n 0 = (ρ_ (X n)).hom ≫ eqToHom (congrArg X (add_zero n).symm))
  (mul_assoc : ∀ i j k, (mul i j ▷ X k) ≫ mul (i + j) k =
    (α_ _ _ _).hom ≫ (X i ◁ mul j k) ≫ mul i (j + k) ≫
      eqToHom (congrArg X (add_assoc i j k).symm))

/-- The monoid object defined by homogeneous data is commutative when the homogeneous
multiplications commute up to the identification of the degrees `i + j` and `j + i`. -/
lemma isCommMonObj_monObjOfHomogeneous
    (mul_comm : ∀ i j, (β_ (X i) (X j)).hom ≫ mul j i =
      mul i j ≫ eqToHom (congrArg X (add_comm i j))) :
    letI := monObjOfHomogeneous X one mul one_mul mul_one mul_assoc
    IsCommMonObj X :=
  letI := monObjOfHomogeneous X one mul one_mul mul_one mul_assoc
  { mul_comm := by
      ext n
      refine Monoidal.tensorObj_ext _ _ fun i j h ↦ ?_
      simp [reassoc_of% mul_comm i j] }

end AddCommMonoid

section LaxMonoidal

variable {C D : Type*} [Category* C] [Category* D]
  [MonoidalCategory C] [MonoidalCategory D] {F : C ⥤ D} [F.LaxMonoidal]

section AddSemigroup

variable {I : Type*} [AddSemigroup I] {X : GradedObject I C} {Y : GradedObject I D}
  {e : ∀ n, Y n ≅ F.obj (X n)}
  (mul : ∀ i j, X i ⊗ X j ⟶ X (i + j)) (mul' : ∀ i j, Y i ⊗ Y j ⟶ Y (i + j))
  (hmul : ∀ i j, mul' i j =
    ((e i).hom ⊗ₘ (e j).hom) ≫ Functor.LaxMonoidal.μ F (X i) (X j) ≫ F.map (mul i j) ≫
      (e (i + j)).inv)
include hmul

/-- Homogeneous multiplications transported along a lax monoidal functor `F` and identifications
`e n : Y n ≅ F.obj (X n)` are associative, up to the identification of the degrees
`i + (j + k)` and `i + j + k`, when the original ones are. -/
lemma mul_assoc_of_laxMonoidal
    (mul_assoc : ∀ i j k, (mul i j ▷ X k) ≫ mul (i + j) k =
      (α_ _ _ _).hom ≫ (X i ◁ mul j k) ≫ mul i (j + k) ≫
        eqToHom (congrArg X (add_assoc i j k).symm)) (i j k : I) :
    (mul' i j ▷ Y k) ≫ mul' (i + j) k =
      (α_ _ _ _).hom ≫ (Y i ◁ mul' j k) ≫ mul' i (j + k) ≫
        eqToHom (congrArg Y (add_assoc i j k).symm) := by
  have core : ((Functor.LaxMonoidal.μ F (X i) (X j) ≫ F.map (mul i j)) ⊗ₘ 𝟙 (F.obj (X k))) ≫
      Functor.LaxMonoidal.μ F _ _ ≫ F.map (mul (i + j) k) =
        (α_ _ _ _).hom ≫ (𝟙 (F.obj (X i)) ⊗ₘ (Functor.LaxMonoidal.μ F _ _ ≫ F.map (mul j k))) ≫
          Functor.LaxMonoidal.μ F _ _ ≫ F.map (mul i (j + k)) ≫
            F.map (eqToHom (congrArg X (add_assoc i j k).symm)) := by
    rw [tensorHom_id, id_tensorHom, comp_whiskerRight, Category.assoc,
      Functor.LaxMonoidal.μ_natural_left_assoc, ← F.map_comp, mul_assoc]
    simp
  calc (mul' i j ▷ Y k) ≫ mul' (i + j) k
      = (((e i).hom ⊗ₘ (e j).hom) ⊗ₘ (e k).hom) ≫
          ((Functor.LaxMonoidal.μ F (X i) (X j) ≫ F.map (mul i j)) ⊗ₘ 𝟙 (F.obj (X k))) ≫
            Functor.LaxMonoidal.μ F _ _ ≫ F.map (mul (i + j) k) ≫ (e _).inv := by
        rw [hmul, hmul, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
          tensorHom_comp_tensorHom_assoc]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    _ = _ := by
        rw [reassoc_of% core, associator_naturality_assoc, tensorHom_comp_tensorHom_assoc,
          TauCeti.eqToHom_eq_iso_hom_map_eqToHom F e (add_assoc i j k).symm, hmul, hmul,
          ← id_tensorHom]
        simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id,
          Iso.inv_hom_id_assoc, Category.comp_id, Category.id_comp]

end AddSemigroup

section Add

variable {I : Type*} [Add I] {X : GradedObject I C} {Y : GradedObject I D}
  {e : ∀ n, Y n ≅ F.obj (X n)}
  (mul : ∀ i j, X i ⊗ X j ⟶ X (i + j)) (mul' : ∀ i j, Y i ⊗ Y j ⟶ Y (i + j))
  (hmul : ∀ i j, mul' i j =
    ((e i).hom ⊗ₘ (e j).hom) ≫ Functor.LaxMonoidal.μ F (X i) (X j) ≫ F.map (mul i j) ≫
      (e (i + j)).inv)
include hmul

/-- Morphisms transported along a lax monoidal functor `F` and identifications
`e n : Y n ≅ F.obj (X n)`, `e' n : Y' n ≅ F.obj (X' n)` commute with the transported homogeneous
multiplications when the original morphisms commute with the original ones. -/
lemma map_mul_of_laxMonoidal {X' : GradedObject I C} {Y' : GradedObject I D}
    {e' : ∀ n, Y' n ≅ F.obj (X' n)} (mulX' : ∀ i j, X' i ⊗ X' j ⟶ X' (i + j))
    (mulY' : ∀ i j, Y' i ⊗ Y' j ⟶ Y' (i + j))
    (hmulY' : ∀ i j, mulY' i j =
      ((e' i).hom ⊗ₘ (e' j).hom) ≫ Functor.LaxMonoidal.μ F (X' i) (X' j) ≫ F.map (mulX' i j) ≫
        (e' (i + j)).inv)
    (f : ∀ n, X n ⟶ X' n) (g : ∀ n, Y n ⟶ Y' n)
    (hg : ∀ n, g n = (e n).hom ≫ F.map (f n) ≫ (e' n).inv)
    (map_mul : ∀ i j, (f i ⊗ₘ f j) ≫ mulX' i j = mul i j ≫ f (i + j)) (i j : I) :
    (g i ⊗ₘ g j) ≫ mulY' i j = mul' i j ≫ g (i + j) := by
  rw [hg, hg, hg, hmul, hmulY']
  simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc,
    Category.comp_id]
  rw [← tensorHom_comp_tensorHom_assoc, Functor.LaxMonoidal.μ_natural_assoc, ← F.map_comp_assoc,
    map_mul, F.map_comp_assoc]

end Add

section AddZeroClass

variable {I : Type*} [AddZeroClass I] {X : GradedObject I C} {Y : GradedObject I D}
  {e : ∀ n, Y n ≅ F.obj (X n)}
  (mul : ∀ i j, X i ⊗ X j ⟶ X (i + j)) (mul' : ∀ i j, Y i ⊗ Y j ⟶ Y (i + j))
  (hmul : ∀ i j, mul' i j =
    ((e i).hom ⊗ₘ (e j).hom) ≫ Functor.LaxMonoidal.μ F (X i) (X j) ≫ F.map (mul i j) ≫
      (e (i + j)).inv)
include hmul

variable (one : 𝟙_ C ⟶ X 0) (one' : 𝟙_ D ⟶ Y 0)
  (hone : one' = Functor.LaxMonoidal.ε F ≫ F.map one ≫ (e 0).inv)
include hone

/-- A unit and homogeneous multiplications transported along a lax monoidal functor `F` and
identifications `e n : Y n ≅ F.obj (X n)` satisfy the left unit law, up to the identification of
the degrees `0 + n` and `n`, when the original ones do. -/
lemma one_mul_of_laxMonoidal
    (one_mul : ∀ n, (one ▷ X n) ≫ mul 0 n =
      (λ_ (X n)).hom ≫ eqToHom (congrArg X (zero_add n).symm)) (n : I) :
    (one' ▷ Y n) ≫ mul' 0 n = (λ_ (Y n)).hom ≫ eqToHom (congrArg Y (zero_add n).symm) := by
  have core : ((Functor.LaxMonoidal.ε F ≫ F.map one) ⊗ₘ 𝟙 (F.obj (X n))) ≫
      Functor.LaxMonoidal.μ F _ _ ≫ F.map (mul 0 n) =
        (λ_ _).hom ≫ F.map (eqToHom (congrArg X (zero_add n).symm)) := by
    rw [tensorHom_id, comp_whiskerRight, Category.assoc, Functor.LaxMonoidal.μ_natural_left_assoc,
      ← F.map_comp, one_mul, F.map_comp, Functor.LaxMonoidal.left_unitality]
    simp only [Category.assoc]
  calc (one' ▷ Y n) ≫ mul' 0 n
      = (𝟙_ D ◁ (e n).hom) ≫ ((Functor.LaxMonoidal.ε F ≫ F.map one) ⊗ₘ 𝟙 (F.obj (X n))) ≫
          Functor.LaxMonoidal.μ F _ _ ≫ F.map (mul 0 n) ≫ (e _).inv := by
        rw [hone, hmul, ← tensorHom_id, tensorHom_comp_tensorHom_assoc, ← id_tensorHom,
          tensorHom_comp_tensorHom_assoc]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    _ = _ := by
        rw [reassoc_of% core, leftUnitor_naturality_assoc,
          TauCeti.eqToHom_eq_iso_hom_map_eqToHom F e (zero_add n).symm]

/-- A unit and homogeneous multiplications transported along a lax monoidal functor `F` and
identifications `e n : Y n ≅ F.obj (X n)` satisfy the right unit law, up to the identification of
the degrees `n + 0` and `n`, when the original ones do. -/
lemma mul_one_of_laxMonoidal
    (mul_one : ∀ n, (X n ◁ one) ≫ mul n 0 =
      (ρ_ (X n)).hom ≫ eqToHom (congrArg X (add_zero n).symm)) (n : I) :
    (Y n ◁ one') ≫ mul' n 0 = (ρ_ (Y n)).hom ≫ eqToHom (congrArg Y (add_zero n).symm) := by
  have core : (𝟙 (F.obj (X n)) ⊗ₘ (Functor.LaxMonoidal.ε F ≫ F.map one)) ≫
      Functor.LaxMonoidal.μ F _ _ ≫ F.map (mul n 0) =
        (ρ_ _).hom ≫ F.map (eqToHom (congrArg X (add_zero n).symm)) := by
    rw [id_tensorHom, whiskerLeft_comp, Category.assoc, Functor.LaxMonoidal.μ_natural_right_assoc,
      ← F.map_comp, mul_one, F.map_comp, Functor.LaxMonoidal.right_unitality]
    simp only [Category.assoc]
  calc (Y n ◁ one') ≫ mul' n 0
      = ((e n).hom ▷ 𝟙_ D) ≫ (𝟙 (F.obj (X n)) ⊗ₘ (Functor.LaxMonoidal.ε F ≫ F.map one)) ≫
          Functor.LaxMonoidal.μ F _ _ ≫ F.map (mul n 0) ≫ (e _).inv := by
        rw [hone, hmul, ← id_tensorHom, tensorHom_comp_tensorHom_assoc, ← tensorHom_id,
          tensorHom_comp_tensorHom_assoc]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    _ = _ := by
        rw [reassoc_of% core, rightUnitor_naturality_assoc,
          TauCeti.eqToHom_eq_iso_hom_map_eqToHom F e (add_zero n).symm]

end AddZeroClass

end LaxMonoidal

section LaxBraided

variable {I : Type*} [AddCommMagma I] {C D : Type*} [Category* C] [Category* D]
  [MonoidalCategory C] [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
  {F : C ⥤ D} [F.LaxBraided] {X : GradedObject I C} {Y : GradedObject I D}
  {e : ∀ n, Y n ≅ F.obj (X n)}
  (mul : ∀ i j, X i ⊗ X j ⟶ X (i + j)) (mul' : ∀ i j, Y i ⊗ Y j ⟶ Y (i + j))
  (hmul : ∀ i j, mul' i j =
    ((e i).hom ⊗ₘ (e j).hom) ≫ Functor.LaxMonoidal.μ F (X i) (X j) ≫ F.map (mul i j) ≫
      (e (i + j)).inv)
include hmul

/-- Homogeneous multiplications transported along a lax braided functor `F` and identifications
`e n : Y n ≅ F.obj (X n)` are commutative, up to the identification of the degrees `i + j` and
`j + i`, when the original ones are. -/
lemma mul_comm_of_laxBraided
    (mul_comm : ∀ i j, (β_ (X i) (X j)).hom ≫ mul j i =
      mul i j ≫ eqToHom (congrArg X (add_comm i j))) (i j : I) :
    (β_ (Y i) (Y j)).hom ≫ mul' j i = mul' i j ≫ eqToHom (congrArg Y (add_comm i j)) := by
  rw [hmul, hmul, ← BraidedCategory.braiding_naturality_assoc, ← Functor.LaxBraided.braided_assoc,
    ← F.map_comp_assoc, mul_comm, TauCeti.eqToHom_eq_iso_hom_map_eqToHom F e (add_comm i j)]
  simp

end LaxBraided

end CategoryTheory.GradedObject

namespace CategoryTheory.Mon

variable {I : Type*} [AddMonoid I] [DecidableEq I] {C : Type*} [Category* C]
  [MonoidalCategory C]
  [∀ (X₁ X₂ : GradedObject I C), GradedObject.HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C),
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]

/-- Multiplication of homogeneous components of a monoid object in graded objects. -/
def mul (A : Mon (GradedObject I C)) (i j : I) : A.X i ⊗ A.X j ⟶ A.X (i + j) :=
  GradedObject.Monoidal.ιTensorObj A.X A.X i j (i + j) rfl ≫ μ[A.X] (i + j)

/-- Homogeneous multiplication is the restriction of the monoid multiplication to the
corresponding summand. -/
theorem mul_eq (A : Mon (GradedObject I C)) (i j : I) :
    A.mul i j =
      GradedObject.Monoidal.ιTensorObj A.X A.X i j (i + j) rfl ≫ μ[A.X] (i + j) := (rfl)

/-- Multiplication through the summand of degree `n = i + j` is homogeneous multiplication
followed by the transport along `i + j = n`. -/
theorem ιTensorObj_mul (A : Mon (GradedObject I C)) {i j n : I} (h : i + j = n) :
    GradedObject.Monoidal.ιTensorObj A.X A.X i j n h ≫ μ[A.X] n =
      A.mul i j ≫ eqToHom (congrArg A.X h) := by
  subst h
  rw [eqToHom_refl, Category.comp_id]
  rfl

/-- Homogeneous multiplication is associative, up to the transport identifying the degrees
`i + (j + k)` and `i + j + k`. -/
@[reassoc]
theorem mul_assoc (A : Mon (GradedObject I C)) (i j k : I) :
    (A.mul i j ▷ A.X k) ≫ A.mul (i + j) k =
      (α_ _ _ _).hom ≫ (A.X i ◁ A.mul j k) ≫ A.mul i (j + k) ≫
        eqToHom (congrArg A.X (add_assoc i j k).symm) := by
  have h := congrArg (GradedObject.Monoidal.ιTensorObj₃' A.X A.X A.X i j k _ rfl ≫ ·)
    (congrFun (MonObj.mul_assoc A.X) (i + j + k))
  -- The components of the monoidal structure maps of graded objects are displayed through the
  -- instance, while the summand-inclusion lemmas are stated for the underlying constructions.
  change GradedObject.Monoidal.ιTensorObj₃' A.X A.X A.X i j k _ rfl ≫
      GradedObject.Monoidal.tensorHom μ[A.X] (𝟙 A.X) (i + j + k) ≫ μ[A.X] (i + j + k) =
    GradedObject.Monoidal.ιTensorObj₃' A.X A.X A.X i j k _ rfl ≫
      (GradedObject.Monoidal.associator A.X A.X A.X).hom (i + j + k) ≫
      GradedObject.Monoidal.tensorHom (𝟙 A.X) μ[A.X] (i + j + k) ≫
        μ[A.X] (i + j + k) at h
  rw [GradedObject.Monoidal.ιTensorObj₃'_associator_hom_assoc,
    GradedObject.Monoidal.ιTensorObj₃_eq_assoc _ _ _ i j k _ _ (j + k) rfl,
    GradedObject.Monoidal.ι_tensorHom_assoc, ιTensorObj_mul,
    GradedObject.Monoidal.ιTensorObj₃'_eq_assoc _ _ _ i j k _ _ (i + j) rfl,
    GradedObject.Monoidal.ι_tensorHom_assoc] at h
  simpa only [mul, GradedObject.categoryOfGradedObjects_id, tensorHom_id, id_tensorHom,
    comp_whiskerRight, whiskerLeft_comp, Category.assoc] using h

/-- A morphism of monoid objects in graded objects commutes with multiplication on every pair of
homogeneous components. -/
@[reassoc]
theorem map_mul {A B : Mon (GradedObject I C)} (f : A ⟶ B) (i j : I) :
    (f.hom i ⊗ₘ f.hom j) ≫ B.mul i j = A.mul i j ≫ f.hom (i + j) := by
  have hmul := congrFun (IsMonHom.mul_hom f.hom) (i + j)
  -- The monoidal instance on graded objects stores its tensor map as the concrete `tensorHom`;
  -- there is no public equation relating the typeclass projection to that implementation.
  change μ[A.X] (i + j) ≫ f.hom (i + j) =
    GradedObject.Monoidal.tensorHom f.hom f.hom (i + j) ≫ μ[B.X] (i + j) at hmul
  rw [mul_eq, mul_eq]
  rw [← Category.assoc, ← GradedObject.Monoidal.ι_tensorHom f.hom f.hom i j (i + j) rfl,
    Category.assoc, ← hmul, Category.assoc]

/-- The unit of a monoid object in graded objects, regarded as a morphism to its degree-zero
component. -/
def one (A : Mon (GradedObject I C)) : 𝟙_ C ⟶ A.X 0 :=
  (GradedObject.Monoidal.tensorUnit₀ (C := C)).inv ≫ η[A.X] 0

/-- The homogeneous unit is the degree-zero component of the monoid unit, after identifying the
degree-zero part of the graded tensor unit with the tensor unit of the underlying category. -/
theorem one_eq (A : Mon (GradedObject I C)) :
    A.one = (GradedObject.Monoidal.tensorUnit₀ (C := C)).inv ≫ η[A.X] 0 := (rfl)

/-- A morphism of monoid objects in graded objects preserves the unit in degree zero. -/
@[reassoc, simp]
theorem one_map {A B : Mon (GradedObject I C)} (f : A ⟶ B) :
    A.one ≫ f.hom 0 = B.one := by
  have hone := congrFun (IsMonHom.one_hom f.hom) 0
  -- Composition of graded-object morphisms is stored componentwise, but its typeclass
  -- projection has no public component equation.
  change η[A.X] 0 ≫ f.hom 0 = η[B.X] 0 at hone
  rw [one_eq, one_eq]
  rw [Category.assoc, hone]

/-- The unit is a left identity for homogeneous multiplication, up to the transport identifying
the degrees `0 + n` and `n`. -/
@[reassoc (attr := simp)]
theorem one_mul (A : Mon (GradedObject I C)) (n : I) :
    (A.one ▷ A.X n) ≫ A.mul 0 n =
      (λ_ (A.X n)).hom ≫ eqToHom (congrArg A.X (zero_add n).symm) := by
  have h : (λ_ A.X).inv ≫ η[A.X] ▷ A.X ≫ μ[A.X] = 𝟙 A.X := by
    rw [MonObj.one_mul, Iso.inv_hom_id]
  replace h := congrFun h n
  dsimp only [GradedObject.categoryOfGradedObjects_comp] at h
  -- The graded monoidal instance has no public equations identifying its unitor and whiskering
  -- projections with the concrete constructions used by the component lemmas below.
  change (GradedObject.Monoidal.leftUnitor A.X).inv n ≫
    GradedObject.Monoidal.tensorHom η[A.X] (𝟙 A.X) n ≫ μ[A.X] n = 𝟙 A.X n at h
  rw [GradedObject.Monoidal.leftUnitor_inv_apply] at h
  simp only [Category.assoc] at h
  rw [GradedObject.Monoidal.ι_tensorHom_assoc, ιTensorObj_mul] at h
  rw [← Iso.inv_comp_eq, ← cancel_mono (eqToHom (congrArg A.X (zero_add n)))]
  simpa only [one_eq, GradedObject.categoryOfGradedObjects_id, tensorHom_id, comp_whiskerRight,
    Category.assoc, eqToHom_trans, eqToHom_refl] using h

/-- The unit is a right identity for homogeneous multiplication, up to the transport identifying
the degrees `n + 0` and `n`. -/
@[reassoc (attr := simp)]
theorem mul_one (A : Mon (GradedObject I C)) (n : I) :
    (A.X n ◁ A.one) ≫ A.mul n 0 =
      (ρ_ (A.X n)).hom ≫ eqToHom (congrArg A.X (add_zero n).symm) := by
  have h : (ρ_ A.X).inv ≫ A.X ◁ η[A.X] ≫ μ[A.X] = 𝟙 A.X := by
    rw [MonObj.mul_one, Iso.inv_hom_id]
  replace h := congrFun h n
  dsimp only [GradedObject.categoryOfGradedObjects_comp] at h
  -- As for `one_mul`, this identifies the unitor and whiskering projections of the graded
  -- monoidal instance with the concrete constructions used by their component lemmas.
  change (GradedObject.Monoidal.rightUnitor A.X).inv n ≫
    GradedObject.Monoidal.tensorHom (𝟙 A.X) η[A.X] n ≫ μ[A.X] n = 𝟙 A.X n at h
  rw [GradedObject.Monoidal.rightUnitor_inv_apply] at h
  simp only [Category.assoc] at h
  rw [GradedObject.Monoidal.ι_tensorHom_assoc, ιTensorObj_mul] at h
  rw [← Iso.inv_comp_eq, ← cancel_mono (eqToHom (congrArg A.X (add_zero n)))]
  simpa only [one_eq, GradedObject.categoryOfGradedObjects_id, id_tensorHom, whiskerLeft_comp,
    Category.assoc, Category.comp_id, eqToHom_trans, eqToHom_refl] using h

end CategoryTheory.Mon

namespace CategoryTheory.Mon

variable {C : Type*} [Category* C] [MonoidalCategory C]
  [∀ (X₁ X₂ : GradedObject ℕ C), GradedObject.HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℕ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℕ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℕ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]

/-- Morphisms out of an `ℕ`-graded monoid object `A` generated in degree one are determined by
their degree-one components. Here generation in degree one means that the unit `𝟙_ C ⟶ A.X 0`
and the multiplications `A.X n ⊗ A.X 1 ⟶ A.X (n + 1)` are epimorphisms. -/
theorem hom_ext_of_epi_mul {A B : Mon (GradedObject ℕ C)} [Epi A.one] [∀ n, Epi (A.mul n 1)]
    {f g : A ⟶ B} (h : f.hom 1 = g.hom 1) : f = g := by
  refine Hom.ext (GradedObject.hom_ext _ _ fun n ↦ ?_)
  induction n with
  | zero => rw [← cancel_epi A.one, one_map, one_map]
  | succ n ih => rw [← cancel_epi (A.mul n 1), ← map_mul, ← map_mul, ih, h]

end CategoryTheory.Mon

namespace CategoryTheory.CommMon

variable {I : Type*} [AddCommMonoid I] [DecidableEq I] {C : Type*} [Category* C]
  [MonoidalCategory C] [BraidedCategory C]
  [∀ (X₁ X₂ : GradedObject I C), GradedObject.HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C),
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]

/-- Homogeneous multiplication of a commutative monoid object is commutative, stated for the
underlying graded object, whose components are displayed without the `toMon` wrapper. -/
private theorem mul_comm_aux (X : GradedObject I C) [MonObj X] [IsCommMonObj X] (i j : I) :
    (β_ (X i) (X j)).hom ≫ (Mon.mk X).mul j i =
      (Mon.mk X).mul i j ≫ eqToHom (congrArg X (add_comm i j)) := by
  have h := congrArg (GradedObject.Monoidal.ιTensorObj X X i j (i + j) rfl ≫ ·)
    (congrFun (IsCommMonObj.mul_comm X) (i + j))
  -- As for `Mon.mul_assoc`, display the braiding component through its underlying construction.
  change GradedObject.Monoidal.ιTensorObj X X i j (i + j) rfl ≫
      (GradedObject.Monoidal.braiding X X).hom (i + j) ≫ μ[X] (i + j) = (Mon.mk X).mul i j at h
  dsimp only [GradedObject.Monoidal.braiding] at h
  rw [GradedObject.Monoidal.ι_tensorObjDesc_assoc, Category.assoc,
    Mon.ιTensorObj_mul (Mon.mk X)] at h
  rw [← h]
  simp

/-- Homogeneous multiplication of a commutative monoid object in graded objects is commutative,
up to the transport identifying the degrees `i + j` and `j + i`. -/
@[reassoc]
theorem mul_comm (A : CommMon (GradedObject I C)) (i j : I) :
    (β_ (A.toMon.X i) (A.toMon.X j)).hom ≫ A.toMon.mul j i =
      A.toMon.mul i j ≫ eqToHom (congrArg A.toMon.X (add_comm i j)) :=
  mul_comm_aux A.X i j

end CategoryTheory.CommMon
