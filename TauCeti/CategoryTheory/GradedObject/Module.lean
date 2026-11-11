/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.Algebra.Category.ModuleCat.Colimits
public import TauCeti.CategoryTheory.GradedObject.FiniteSupport

/-!
# Finiteness of graded modules under convolution

Reindexing a finitely supported family of finite modules by coproducts again has finite
components. Consequently the convolution of two finitely supported graded finite modules has
finite components, even if the grading monoid is infinite. These facts allow restricting
cocycle-twisted graded vector spaces to finite-dimensional objects.
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
    refine (hf.preimage (f := fun i : p ⁻¹' {j} ↦ i.1)
      Subtype.val_injective.injOn).subset ?_
    intro i hi
    exact (mem_support X i.1).mpr hi)

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

end CategoryTheory.GradedObject
