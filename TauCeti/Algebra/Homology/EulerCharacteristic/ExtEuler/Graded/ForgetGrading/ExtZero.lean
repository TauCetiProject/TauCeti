/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import TauCeti.Algebra.Category.GradedModuleCat.HomLaurentSupport
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Shift

/-!
# Degree-zero graded Ext after forgetting the grading

For graded modules over a graded algebra with a finitely generated source, the direct sum over all
internal degrees of degree-zero graded Ext is canonically the degree-zero Ext of the underlying
ungraded modules. Degree-zero Ext is Hom on both sides, and an ungraded module map is the finite
sum of its homogeneous parts.

## Main results

* `TauCeti.GradedModuleCat.gradedExtZeroForgetEquiv`: the direct sum of degree-zero graded Ext
  groups is canonically equivalent to ungraded degree-zero Ext.
* `TauCeti.GradedModuleCat.gradedExtZeroForgetEquiv_of`: on a single internal degree, the
  equivalence forgets the grading of the corresponding graded map.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for homogeneous
  decomposition of maps between graded modules.
-/

public section

noncomputable section

open scoped DirectSum

namespace TauCeti.GradedModuleCat

open CategoryTheory CategoryTheory.Abelian

universe w w' uk uA

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]
  [HasExt.{w} (GradedModuleCat.{uA} 𝒜)] [HasExt.{w'} (ModuleCat.{uA} A)]

/-- Regard an `A`-linear map between graded modules as a morphism of the underlying module
objects. The two induced `k`-actions agree by the scalar-tower law. -/
private def linearMapForgetEquiv (X Y : GradedModuleCat.{uA} 𝒜) :
    (X →ₗ[A] Y) ≃ₗ[k] (toModuleCat.obj X ⟶ toModuleCat.obj Y) where
  toFun := ModuleCat.ofHom
  invFun := ModuleCat.Hom.hom
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c f := by
    apply ModuleCat.hom_ext
    ext x
    exact (algebraMap_smul A c (f x)).symm

/-- **Degree-zero graded Ext assembles canonically into ungraded degree-zero Ext.** The
equivalence decomposes an ungraded module map into its finitely many homogeneous parts. -/
def gradedExtZeroForgetEquiv (X Y : GradedModuleCat.{uA} 𝒜) [Module.Finite A X] :
    (⨁ j : ℤ, GradedExt.{w} (shift 𝒜) X Y 0 j) ≃ₗ[k]
      Ext.{w'} (toModuleCat.obj X) (toModuleCat.obj Y) 0 :=
  (DirectSum.congrLinearEquiv fun j ↦
      Ext.linearEquiv₀.trans (homShiftPowEquiv 𝒜 X Y j)).trans
    ((homShiftDirectSumEquiv X Y).trans
      ((linearMapForgetEquiv 𝒜 X Y).trans Ext.linearEquiv₀.symm))

/-- On a single internal degree, `gradedExtZeroForgetEquiv` forgets the grading of the graded map
represented by a degree-zero Ext class. -/
@[simp]
theorem gradedExtZeroForgetEquiv_of (X Y : GradedModuleCat.{uA} 𝒜) [Module.Finite A X] (j : ℤ)
    (e : GradedExt.{w} (shift 𝒜) X Y 0 j) :
    gradedExtZeroForgetEquiv 𝒜 X Y (DirectSum.of _ j e) =
      (Ext.linearEquiv₀ (R := k) (X := toModuleCat.obj X) (Y := toModuleCat.obj Y)).symm
        (ModuleCat.ofHom (homShiftPowEquiv 𝒜 X Y j (Ext.linearEquiv₀ (R := k) e)).hom) := by
  classical
  simp only [gradedExtZeroForgetEquiv, LinearEquiv.trans_apply, DirectSum.coe_congrLinearEquiv,
    DirectSum.lmap_of, LinearEquiv.coe_coe, homShiftDirectSumEquiv_of]
  rfl

end TauCeti.GradedModuleCat
