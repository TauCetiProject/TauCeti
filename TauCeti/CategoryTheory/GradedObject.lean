/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Pi
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.GradedObject.Single
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Additive structures on graded objects

This file equips Mathlib's canonical category `CategoryTheory.GradedObject β C` with the
pointwise preadditive, linear, and abelian structures inherited from `C`, with morphisms added
and scaled componentwise (`CategoryTheory.GradedObject.add_apply`,
`CategoryTheory.GradedObject.smul_apply`).
It also records that the canonical reindexing and shift functors are additive and linear, that
evaluation in a single degree preserves finite limits and colimits, so that a short exact sequence
of graded objects is short exact in every degree, and that totalizing a graded object,
`X ↦ ∐ᵢ Xᵢ`, is left adjoint to the constant graded object
(`TauCeti.gradedObjectTotalAdjunction`), and is the colimit functor of the corresponding discrete
diagram (`TauCeti.gradedObjectTotalIso`). Totalizing is therefore additive and preserves finite
colimits; it also preserves finite limits when coproducts in `C` are exact, as for modules, so that
it is an exact functor. The total object of an object placed in a single degree is that object
(`TauCeti.gradedObjectTotalSingleIso`).

Mathlib provides the category of graded objects and its grading shift, but not these
structures. They are what homological algebra needs: `Ext` groups, and hence the graded
Ext-Euler form `χ_q(X, Y) = ∑ n, j, (-1)ⁿ q⁻ʲ dim Extⁿ(X, Y{j})`, are only defined in an abelian
category, and the q-Euler form uses the grading shift as a linear autoequivalence. With these
instances, categories of graded objects such as graded vector spaces
`GradedObjectWithShift (-1) (ModuleCat k)` become examples of the graded Ext-Euler formalism.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

universe w v u t

variable {C : Type u} [Category.{v} C]

namespace TauCeti

/-- Pointwise addition of morphisms of graded objects. -/
instance gradedObjectHomAdd (β : Type w) [Preadditive C] (X Y : GradedObject β C) :
    Add (X ⟶ Y) :=
  ⟨fun f g i => f i + g i⟩

/-- Pointwise negation of morphisms of graded objects. -/
instance gradedObjectHomNeg (β : Type w) [Preadditive C] (X Y : GradedObject β C) :
    Neg (X ⟶ Y) :=
  ⟨fun f i => -f i⟩

/-- The pointwise preadditive structure on Mathlib's category of graded objects. -/
instance gradedObjectPreadditive (β : Type w) [Preadditive C] :
    Preadditive (GradedObject β C) where
  homGroup X Y := inferInstanceAs (AddCommGroup (∀ i, X i ⟶ Y i))
  add_comp := by intros; funext i; apply add_comp
  comp_add := by intros; funext i; apply comp_add

/-- The pointwise linear structure on Mathlib's category of graded objects. -/
instance gradedObjectLinear (β : Type w) (R : Type t) [Semiring R] [Preadditive C] [Linear R C] :
    Linear R (GradedObject β C) where
  homModule X Y := inferInstanceAs (Module R (∀ i, X i ⟶ Y i))
  smul_comp := by intros; funext i; apply Linear.smul_comp
  comp_smul := by intros; funext i; apply Linear.comp_smul

end TauCeti

namespace CategoryTheory.GradedObject

/-- Morphisms of graded objects are added componentwise. -/
@[simp]
theorem add_apply {β : Type w} [Preadditive C] {X Y : GradedObject β C} (f g : X ⟶ Y) (i : β) :
    (f + g) i = f i + g i :=
  rfl

/-- Morphisms of graded objects are negated componentwise. -/
@[simp]
theorem neg_apply {β : Type w} [Preadditive C] {X Y : GradedObject β C} (f : X ⟶ Y) (i : β) :
    (-f) i = -f i :=
  rfl

/-- Morphisms of graded objects are subtracted componentwise. -/
@[simp]
theorem sub_apply {β : Type w} [Preadditive C] {X Y : GradedObject β C} (f g : X ⟶ Y) (i : β) :
    (f - g) i = f i - g i :=
  rfl

/-- Morphisms of graded objects are scaled componentwise. -/
@[simp]
theorem smul_apply {β : Type w} {R : Type t} [Semiring R] [Preadditive C] [Linear R C]
    {X Y : GradedObject β C} (r : R) (f : X ⟶ Y) (i : β) :
    (r • f) i = r • f i :=
  rfl

/-- A morphism of graded objects which is a monomorphism in every degree is a monomorphism. -/
theorem mono_of_mono_apply {β : Type w} {X Y : GradedObject β C} (f : X ⟶ Y)
    (hf : ∀ i, Mono (f i)) : Mono f :=
  ⟨fun _ _ h => funext fun i => (cancel_mono (f i)).1 (congr_fun h i)⟩

end CategoryTheory.GradedObject

namespace TauCeti

/-- Reindexing a graded object is additive. -/
instance gradedObjectComapAdditive {I J : Type*} [Preadditive C] (f : J → I) :
    (GradedObject.comap C f).Additive where
  map_add := rfl

/-- Reindexing a graded object is linear. -/
instance gradedObjectComapLinear {I J : Type*} [Preadditive C]
    (R : Type t) [Semiring R] [Linear R C] (f : J → I) :
    (GradedObject.comap C f).Linear R where
  map_smul _ _ := rfl

/-- Mathlib's canonical shift functor on graded objects is additive. -/
instance gradedObjectShiftFunctorAdditive {β : Type*} [AddCommGroup β] [Preadditive C]
    (s : β) (n : ℤ) : (shiftFunctor (GradedObjectWithShift s C) n).Additive where
  map_add := rfl

/-- Mathlib's canonical shift functor on graded objects is linear. -/
instance gradedObjectShiftFunctorLinear {β : Type*} [AddCommGroup β] [Preadditive C]
    (R : Type t) [Semiring R] [Linear R C] (s : β) (n : ℤ) :
    (shiftFunctor (GradedObjectWithShift s C) n).Linear R where
  map_smul _ _ := rfl

/-- The functor of Mathlib's canonical shift autoequivalence on graded objects is additive.
This is `gradedObjectShiftFunctorAdditive`, restated because `shiftEquiv'` is not reducible, so
instance search does not see that its functor is `shiftFunctor`. -/
instance gradedObjectShiftEquivFunctorAdditive {β : Type*} [AddCommGroup β] [Preadditive C]
    (s : β) (n : ℤ) : (shiftEquiv (GradedObjectWithShift s C) n).functor.Additive :=
  gradedObjectShiftFunctorAdditive s n

/-- The functor of Mathlib's canonical shift autoequivalence on graded objects is linear.
This is `gradedObjectShiftFunctorLinear`, restated because `shiftEquiv'` is not reducible, so
instance search does not see that its functor is `shiftFunctor`. -/
instance gradedObjectShiftEquivFunctorLinear {β : Type*} [AddCommGroup β] [Preadditive C]
    (R : Type t) [Semiring R] [Linear R C] (s : β) (n : ℤ) :
    (shiftEquiv (GradedObjectWithShift s C) n).functor.Linear R :=
  gradedObjectShiftFunctorLinear R s n

/-- Graded objects in a category with finite limits have finite limits, computed pointwise. -/
instance gradedObjectHasFiniteLimits (β : Type w) [HasFiniteLimits C] :
    HasFiniteLimits (GradedObject β C) :=
  ⟨fun _ => Adjunction.hasLimitsOfShape_of_equivalence (piEquivalenceFunctorDiscrete β C).functor⟩

/-- The projection `GradedObject.eval b` is evaluation at `⟨b⟩` under the equivalence of graded
objects with functors out of the discrete category. -/
private def gradedObjectEvalIso (β : Type w) (b : β) :
    (piEquivalenceFunctorDiscrete β C).functor ⋙ (evaluation _ C).obj ⟨b⟩ ≅
      GradedObject.eval b :=
  -- Both functors send `X` to `X b` and `f` to `f b`, by their definitions.
  Iso.refl _

/-- Finite limits of graded objects are computed pointwise. -/
instance gradedObjectEvalPreservesFiniteLimits [HasFiniteLimits C] (β : Type w) (b : β) :
    PreservesFiniteLimits (GradedObject.eval (C := C) b) :=
  preservesFiniteLimits_of_natIso (gradedObjectEvalIso β b)

/-- Finite colimits of graded objects are computed pointwise. -/
instance gradedObjectEvalPreservesFiniteColimits [HasFiniteColimits C] (β : Type w) (b : β) :
    PreservesFiniteColimits (GradedObject.eval (C := C) b) :=
  preservesFiniteColimits_of_natIso (gradedObjectEvalIso β b)

/-- The pointwise abelian structure on Mathlib's category of graded objects. -/
noncomputable instance gradedObjectAbelian (β : Type w) [Abelian C] :
    Abelian (GradedObject β C) := by
  let _ : Preadditive (β → C) := gradedObjectPreadditive β
  exact abelianOfEquivalence (piEquivalenceFunctorDiscrete β C).functor

/-- **Totalizing a graded object is left adjoint to the constant graded object**: morphisms
`∐ᵢ Xᵢ ⟶ Y` correspond to families of morphisms `Xᵢ ⟶ Y`. -/
noncomputable def gradedObjectTotalAdjunction (β : Type) (C : Type u) [Category.{v} C]
    [HasCoproducts.{0} C] : GradedObject.total β C ⊣ Functor.pi' fun _ : β ↦ 𝟭 C := by
  -- `GradedObject.total` is by definition `X ↦ ∐ᵢ Xᵢ`, the colimit of the diagram
  -- `Discrete β ⥤ C` corresponding to `X`.
  change (piEquivalenceFunctorDiscrete β C).functor ⋙ colim ⊣ _
  exact ((piEquivalenceFunctorDiscrete β C).toAdjunction.comp colimConstAdj).ofNatIsoRight
    (Iso.refl _)

/-- `GradedObject.total β C` is the colimit functor of the corresponding diagram
`Discrete β ⥤ C`. -/
noncomputable def gradedObjectTotalIso (β : Type) (C : Type u) [Category.{v} C]
    [HasCoproducts.{0} C] :
    (piEquivalenceFunctorDiscrete β C).functor ⋙ colim ≅ GradedObject.total β C :=
  -- Both functors send `X` to `∐ᵢ Xᵢ` and `f` to `Sigma.map f`, by their definitions.
  Iso.refl _

/-- Totalizing a graded object is additive, being left adjoint to the additive constant graded
object functor. -/
instance gradedObjectTotalAdditive (β : Type) (C : Type u) [Category.{v} C] [Preadditive C]
    [HasCoproducts.{0} C] : (GradedObject.total β C).Additive :=
  let _ : Preadditive (β → C) := gradedObjectPreadditive β
  have : (Functor.pi' fun _ : β ↦ 𝟭 C).Additive := ⟨rfl⟩
  (gradedObjectTotalAdjunction β C).left_adjoint_additive

/-- Totalizing a graded object preserves finite colimits, being a left adjoint. -/
instance gradedObjectTotalPreservesFiniteColimits (β : Type) (C : Type u) [Category.{v} C]
    [HasCoproducts.{0} C] : PreservesFiniteColimits (GradedObject.total β C) :=
  preservesFiniteColimits_of_natIso (gradedObjectTotalIso β C)

/-- **Totalizing a graded object preserves finite limits when coproducts indexed by the grading
are exact**, as in a category of modules. Together with
`TauCeti.gradedObjectTotalPreservesFiniteColimits` this makes totalizing an exact functor. -/
instance gradedObjectTotalPreservesFiniteLimits (β : Type) (C : Type u) [Category.{v} C]
    [HasCoproducts.{0} C] [HasExactColimitsOfShape (Discrete β) C] :
    PreservesFiniteLimits (GradedObject.total β C) :=
  have := HasExactColimitsOfShape.preservesFiniteLimits (J := Discrete β) (C := C)
  preservesFiniteLimits_of_natIso (gradedObjectTotalIso β C)

/-- **The total object of an object placed in a single degree is that object**: `∐ᵢ Xᵢ ≅ Y` for
`X = (GradedObject.single j).obj Y`, since every other piece is initial. -/
noncomputable def gradedObjectTotalSingleIso {β : Type} (C : Type u) [Category.{v} C]
    [HasCoproducts.{0} C] [DecidableEq β] (j : β) (Y : C) :
    (GradedObject.total β C).obj ((GradedObject.single j).obj Y) ≅ Y :=
  -- `GradedObject.total` is by definition `X ↦ ∐ᵢ Xᵢ`.
  show (∐ fun i ↦ (GradedObject.single j).obj Y i) ≅ Y from {
    hom := Sigma.desc fun i ↦ if hi : i = j then
      (GradedObject.singleObjApplyIsoOfEq j Y i hi).hom
      else (GradedObject.isInitialSingleObjApply j Y i hi).to Y
    inv := (GradedObject.singleObjApplyIso j Y).inv ≫ Sigma.ι _ j
    hom_inv_id := by
      apply Sigma.hom_ext
      intro i
      by_cases hi : i = j
      · subst i
        simp
      · exact (GradedObject.isInitialSingleObjApply j Y i hi).hom_ext _ _
    inv_hom_id := by simp }

/-- The inclusion of degree `j` into the total object of `(GradedObject.single j).obj Y`,
followed by `TauCeti.gradedObjectTotalSingleIso`, is `GradedObject.singleObjApplyIso`. -/
@[simp, reassoc]
theorem ι_gradedObjectTotalSingleIso_hom {β : Type} (C : Type u) [Category.{v} C]
    [HasCoproducts.{0} C] [DecidableEq β] (j : β) (Y : C) :
    Sigma.ι ((GradedObject.single j).obj Y) j ≫
        (gradedObjectTotalSingleIso C j Y).hom =
      (GradedObject.singleObjApplyIso j Y).hom := by
  simp [gradedObjectTotalSingleIso, GradedObject.singleObjApplyIso]

/-- The inverse of `TauCeti.gradedObjectTotalSingleIso` is the inclusion of degree `j`. -/
@[simp]
theorem gradedObjectTotalSingleIso_inv {β : Type} (C : Type u) [Category.{v} C]
    [HasCoproducts.{0} C] [DecidableEq β] (j : β) (Y : C) :
    (gradedObjectTotalSingleIso C j Y).inv =
      (GradedObject.singleObjApplyIso j Y).inv ≫
        Sigma.ι ((GradedObject.single j).obj Y) j := by
  unfold gradedObjectTotalSingleIso
  rfl

end TauCeti
