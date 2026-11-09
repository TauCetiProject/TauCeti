/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Balanced evaluation for linear functors

For a linear functor `F` to modules, evaluation sends `f ⊗ x` to `F.map f x`.
It is balanced over the actual categorical endomorphism ring of the source object:
the right action on morphisms is precomposition, and the left action on vectors is
the image under `F`. Evaluation is an isomorphism whenever the target is a retract
of a finite direct sum of copies of the source. The inverse uses the inclusions
and projections of that retraction, while evaluation itself is independent of them.

This is the reconstruction map for multiplicity spaces over nonscalar commutants.

## References

* C. W. Curtis and I. Reiner, *Methods of Representation Theory*, Vol. I.
* Mathlib's `CategoryTheory.moduleEndLeft` supplies the right endomorphism action.
-/

public section

namespace CategoryTheory.Functor

open TauCeti MulOpposite

universe u v w t

variable {k : Type u} [CommRing k] {C : Type v} [Category.{w} C] [Preadditive C]
  [CategoryTheory.Linear k C] (F : C ⥤ ModuleCat.{t} k) [F.Additive] [F.Linear k]

/-- The endomorphisms of an object act on its vectors through a module-valued functor.
This action is explicit, so different functors need not induce the same action. -/
abbrev endModule (X : C) : Module (End X) (F.obj X) :=
  Module.compHom (F.obj X)
    { toFun := fun a ↦ (F.map a.asHom).hom
      map_one' := by ext x; simp
      map_mul' := by intro a b; ext x; simp
      map_zero' := by ext x; simp
      map_add' := by intro a b; ext x; simp }

attribute [local instance] endModule

omit [CategoryTheory.Linear k C] [F.Linear k] in
/-- The endomorphism action evaluates the image morphism. -/
@[simp]
theorem endModule_smul (X : C) (a : End X) (x : F.obj X) :
    a • x = F.map a.asHom x := (rfl)

/-- The endomorphism action respects the ground-ring scalar tower. -/
instance endModule_isScalarTower (X : C) : IsScalarTower k (End X) (F.obj X) where
  smul_assoc r a x := by simp [endModule_smul]

/-- Ground-ring scalars commute with the endomorphism action. -/
instance endModule_smulCommClass (X : C) : SMulCommClass k (End X) (F.obj X) where
  smul_comm r a x := by simp [endModule_smul]

/-- Evaluation of morphisms on vectors, balanced over the source endomorphism ring. -/
def balancedEvaluation (X Y : C) :
    BalancedTensorProduct k (End X) (X ⟶ Y) (F.obj X) →ₗ[k] F.obj Y :=
  BalancedTensorProduct.lift
    { toFun := fun f ↦ (F.map f).hom
      map_add' := by intro f g; ext x; simp
      map_smul' := by intro r f; ext x; simp }
    (fun a f x ↦ by simp [End.smul_left])

@[simp]
theorem balancedEvaluation_tmul (X Y : C) (f : X ⟶ Y) (x : F.obj X) :
    F.balancedEvaluation X Y (BalancedTensorProduct.tmul k (End X) f x) = F.map f x := by
  simp [balancedEvaluation]

/-- Postcomposition on multiplicities corresponds to the target morphism on vectors. -/
theorem balancedEvaluation_naturality {X Y Z : C} (g : Y ⟶ Z)
    (z : BalancedTensorProduct k (End X) (X ⟶ Y) (F.obj X)) :
    F.balancedEvaluation X Z
        (BalancedTensorProduct.map (Linear.rightComp k X g) LinearMap.id
          (by intro a f; simp [End.smul_left]) (fun _ _ ↦ rfl) z) =
      F.map g (F.balancedEvaluation X Y z) := by
  induction z using BalancedTensorProduct.induction_on with
  | ht f x =>
    rw [BalancedTensorProduct.map_tmul, balancedEvaluation_tmul, balancedEvaluation_tmul]
    simp
  | ha a b ha hb => simp [ha, hb]

/-- Evaluation is bijective when the identity of the target is a finite sum of maps
factoring through the source. In particular this applies to every finite direct sum
of copies of the source, and to its retracts. -/
theorem balancedEvaluation_bijective_of_sum_id {X Y : C} {ι : Type*} [Fintype ι]
    (i : ι → (X ⟶ Y)) (p : ι → (Y ⟶ X)) (h : ∑ j, p j ≫ i j = 𝟙 Y) :
    Function.Bijective (F.balancedEvaluation X Y) := by
  let inv : F.obj Y →ₗ[k] BalancedTensorProduct k (End X) (X ⟶ Y) (F.obj X) :=
    ∑ j, (BalancedTensorProduct.mk k (End X) (i j)).comp (F.map (p j)).hom
  have hinv (y : F.obj Y) :
      inv y = ∑ j, BalancedTensorProduct.tmul k (End X) (i j) (F.map (p j) y) := by
    simp [inv]
  have hleft : inv.comp (F.balancedEvaluation X Y) = LinearMap.id := by
    apply BalancedTensorProduct.hom_ext
    intro f x
    simp only [LinearMap.comp_apply, balancedEvaluation_tmul, hinv, LinearMap.id_apply]
    calc
      _ = ∑ j, BalancedTensorProduct.tmul k (End X)
          (op (End.of (f ≫ p j)) • i j) x := by
        congr 1
        ext j
        rw [BalancedTensorProduct.balance, endModule_smul]
        simp
      _ = BalancedTensorProduct.tmul k (End X) f x := by
        simp only [End.smul_left, MulOpposite.unop_op, ← BalancedTensorProduct.mk_apply,
          ← LinearMap.sum_apply, ← _root_.map_sum, Category.assoc, ← Preadditive.comp_sum, h,
          Category.comp_id]
  have hright : (F.balancedEvaluation X Y).comp inv = LinearMap.id := by
    ext y
    simp only [LinearMap.comp_apply, hinv, _root_.map_sum, balancedEvaluation_tmul,
      LinearMap.id_apply]
    have hy := congrArg (fun f : Y ⟶ Y ↦ F.map f y) h
    simpa using hy
  exact ⟨LinearMap.injective_of_comp_eq_id _ _ hleft,
    LinearMap.surjective_of_comp_eq_id _ _ hright⟩

end CategoryTheory.Functor
