/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Projective
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.Algebra.Category.ModuleCat.Colimits
public import TauCeti.CategoryTheory.GradedObject.FiniteSupport

/-!
# Finiteness and projectivity of graded modules under convolution

Reindexing a finitely supported family of finite modules by coproducts again has finite
components. Consequently the convolution of two finitely supported graded finite modules has
finite components, even if the grading monoid is infinite. Reindexing any family of projective
modules by coproducts has projective components, with no finiteness assumption, since a coproduct
of projective objects is projective; so the convolution of two graded projective modules has
projective components. These facts allow restricting cocycle-twisted graded modules over a
commutative ring to the finitely supported objects with finite projective components, which are
the dualizable ones.
-/

public section

open CategoryTheory Limits MonoidalCategory
open scoped TensorProduct

namespace CategoryTheory.GradedObject

universe u w

variable {R : Type u} {I J : Type*}

section Ring

variable [Ring R]

/-- A finite module placed in a single degree has finite components in every degree. -/
lemma finite_single_obj [DecidableEq I] (i : I) (M : ModuleCat.{w} R)
    [Module.Finite R M] (j : I) :
    Module.Finite R ((single (C := ModuleCat.{w} R) i).obj M j) := by
  by_cases h : j = i
  · exact Module.Finite.equiv (singleObjApplyIsoOfEq i M j h).symm.toLinearEquiv
  · have := ModuleCat.isZero_iff_subsingleton.mp (isInitialSingleObjApply i M j h).isZero
    infer_instance

/-- Reindexing finitely supported finite modules by coproducts gives finite modules in each
degree, without a finiteness assumption on the fibres of the reindexing map. -/
lemma HasFiniteSupport.finite_mapObj {X : GradedObject I (ModuleCat.{w} R)}
    (hX : X.HasFiniteSupport) [∀ i, Module.Finite R (X i)] (p : I → J) [X.HasMap p]
    (j : J) : Module.Finite R (X.mapObj p j) :=
  TauCeti.ModuleCat.finite_coproduct_of_finite_support (X.mapObjFun p j) (by
    have hf := (hasFiniteSupport_iff_finite X).mp hX
    refine (hf.preimage (f := fun i : p ⁻¹' {j} ↦ i.val)
      Subtype.val_injective.injOn).subset ?_
    intro i hi
    exact (mem_support X i.val).mpr hi)

/-- A projective module placed in a single degree has projective components in every degree. -/
lemma projective_single_obj [DecidableEq I] (i : I) (M : ModuleCat.{w} R)
    [Module.Projective R M] (j : I) :
    Module.Projective R ((single (C := ModuleCat.{w} R) i).obj M j) := by
  by_cases h : j = i
  · exact .of_equiv' (singleObjApplyIsoOfEq i M j h).symm.toLinearEquiv
  · have := ModuleCat.isZero_iff_subsingleton.mp (isInitialSingleObjApply i M j h).isZero
    infer_instance

/-- Reindexing projective modules by coproducts gives projective modules in each degree. The
modules live in the universe of the ring, so that a categorically projective module is
projective (`ModuleCat.projective_of_module_projective`). -/
lemma projective_mapObj (X : GradedObject I (ModuleCat.{u} R)) [∀ i, Module.Projective R (X i)]
    (p : I → J) [X.HasMap p] (j : J) : Module.Projective R (X.mapObj p j) :=
  -- Each summand is a projective object of `ModuleCat R`, hence so is their coproduct
  -- `X.mapObj p j`. Mathlib's instance for coproducts of projective objects asks the index type to
  -- live in the universe of morphisms, so its one-line proof is repeated here.
  have (i : I) : Projective (X i) := ModuleCat.projective_of_categoryTheory_projective (X i)
  have : Projective (X.mapObj p j) :=
    ⟨fun f e _ ↦ ⟨X.descMapObj p fun i hi ↦ Projective.factorThru (X.ιMapObj p i j hi ≫ f) e,
      X.mapObj_ext p _ _ fun i hi ↦ by simp⟩⟩
  ModuleCat.projective_of_module_projective _

end Ring

variable [AddMonoid I] [CommRing R]

/-- Convolution of finitely supported graded finite modules has finite components. -/
lemma HasFiniteSupport.finite_tensorObj {X Y : GradedObject I (ModuleCat.{u} R)}
    (hX : X.HasFiniteSupport) (hY : Y.HasFiniteSupport)
    [∀ i, Module.Finite R (X i)] [∀ i, Module.Finite R (Y i)] [HasTensor X Y]
    (i : I) : Module.Finite R (Monoidal.tensorObj (C := ModuleCat.{u} R) X Y i) := by
  -- The external tensor product evaluates definitionally to the module tensor product:
  -- mapBifunctor evaluates pointwise, curriedTensor gives the categorical tensor, and
  -- ModuleCat's tensorObj is the raw tensor product with its canonical module structure.
  have (ij : I × I) : Module.Finite R
      ((((GradedObject.mapBifunctor (curriedTensor (ModuleCat R)) I I).obj X).obj Y) ij) :=
    inferInstanceAs (Module.Finite R (X ij.1 ⊗[R] Y ij.2))
  exact (hX.mapBifunctor (curriedTensor (ModuleCat R)) hY).finite_mapObj _ i

/-- Convolution of graded projective modules has projective components. -/
lemma projective_tensorObj (X Y : GradedObject I (ModuleCat.{u} R))
    [∀ i, Module.Projective R (X i)] [∀ i, Module.Projective R (Y i)] [HasTensor X Y]
    (i : I) : Module.Projective R (Monoidal.tensorObj (C := ModuleCat.{u} R) X Y i) := by
  -- As in `HasFiniteSupport.finite_tensorObj`, the external tensor product evaluates
  -- definitionally to the module tensor product.
  have (ij : I × I) : Module.Projective R
      ((((GradedObject.mapBifunctor (curriedTensor (ModuleCat R)) I I).obj X).obj Y) ij) :=
    inferInstanceAs (Module.Projective R (X ij.1 ⊗[R] Y ij.2))
  exact projective_mapObj _ _ i

end CategoryTheory.GradedObject
