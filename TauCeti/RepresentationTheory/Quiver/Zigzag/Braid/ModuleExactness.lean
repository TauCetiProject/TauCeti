/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Exactness
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.RightProjective
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Exactness of the fixed-term zigzag bimodule tensor actions

The vertex ideals are cyclic over the zigzag algebra, which is finite free over the
coefficient ring. Their tensor factorization makes the actual vertex bimodule finite
over that ring and hence finite over the algebra on the right. Together with the
established right projectivity, the general finite-projective graded tensor theorem
then proves homology preservation for the actual vertex bimodule, the regular
bimodule, and internal shifts of the vertex bimodule.

This is a fixed-term tensor result. Preservation of quasi-isomorphisms by the totalized
braid complexes, localization and derived action transfer require further steps.
-/

public section
noncomputable section

namespace TauCeti

open CategoryTheory MulOpposite
open scoped TensorProduct

universe u v w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

local notation "Z" => AlgCat.carrier (zigzagAlgebra k G)
local notation "Γ" => zigzagAlgebraInternalGrading k G
local notation "U" => zigzagGradedBraidBimodule k G
local notation "e" => fun i : V ↦ zigzagAlgebraBasis k G (Sum.inl i)
local notation "L" => fun i : V ↦ (Ideal.span {e i} : Ideal Z)
local notation "R" => fun i : V ↦ (Ideal.span {op (e i)} : Ideal Zᵐᵒᵖ)

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

private local instance rightModule
    (M : GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece) :
    Module Zᵐᵒᵖ M :=
  TauCeti.Algebra.TensorProduct.moduleRight (k := k) (A := Z) (B := Zᵐᵒᵖ) M

private local instance rightTower
    (M : GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece) :
    IsScalarTower k Zᵐᵒᵖ M :=
  TauCeti.Algebra.TensorProduct.moduleRightIsScalarTower (k := k) (A := Z) (B := Zᵐᵒᵖ) M

private theorem vertex_finite_k (i : V) : Module.Finite k (U i) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let : Fintype (ZigzagBasisIndex G) := inferInstance
  let : Module.Finite k Z := Module.Finite.of_basis (zigzagAlgebraBasis k G)
  let : Module.Finite k Zᵐᵒᵖ :=
    Module.Finite.equiv (MulOpposite.opLinearEquiv k : Z ≃ₗ[k] Zᵐᵒᵖ)
  let : Module.Finite k (L i) := Module.Finite.trans Z (L i)
  let : Module.Finite k (R i) := Module.Finite.trans Zᵐᵒᵖ (R i)
  exact Module.Finite.equiv (zigzagBraidBimoduleRightFactorsEquiv k G i).symm

/-- Tensoring with the actual vertex bimodule preserves homology of graded modules. -/
theorem preservesHomology_zigzagGradedBraidBimoduleTensor (i : V) :
    ((GradedModuleCat.bimoduleModuleTensor.{max u w, v} Γ Γ).obj
      (U i)).PreservesHomology := by
  let : Module.Finite k (U i) := vertex_finite_k k G i
  let : Module.Projective Zᵐᵒᵖ (U i) := projective_zigzagGradedBraidBimodule_right k G i
  let : Module.Finite Zᵐᵒᵖ (U i) :=
    Module.Finite.of_restrictScalars_finite k Zᵐᵒᵖ (U i)
  exact GradedModuleCat.bimoduleModuleTensor_preservesHomology Γ Γ (U i)

/-- Tensoring with the regular graded zigzag bimodule preserves homology. -/
theorem preservesHomology_zigzagGradedBimoduleTensor :
    ((GradedModuleCat.bimoduleModuleTensor.{max u w, v} Γ Γ).obj
      (zigzagGradedBimodule k G)).PreservesHomology := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let : Fintype (ZigzagBasisIndex G) := inferInstance
  let : Module.Finite k Z := Module.Finite.of_basis (zigzagAlgebraBasis k G)
  let : Module.Finite k (zigzagGradedBimodule k G) :=
    Module.Finite.equiv (Bimodule.of (AlgHom.id k Z))
  let : Module.Projective Zᵐᵒᵖ (zigzagGradedBimodule k G) :=
    inferInstanceAs (Module.Projective Zᵐᵒᵖ (Bimodule (AlgHom.id k Z)))
  let : Module.Finite Zᵐᵒᵖ (zigzagGradedBimodule k G) :=
    Module.Finite.of_restrictScalars_finite k Zᵐᵒᵖ (zigzagGradedBimodule k G)
  exact GradedModuleCat.bimoduleModuleTensor_preservesHomology.{max u w, v} Γ Γ
    (zigzagGradedBimodule k G)

/-- An internal shift of the vertex bimodule retains homology preservation of tensoring. -/
theorem preservesHomology_zigzagGradedBraidBimoduleTensor_shift (i : V) (n : ℤ) :
    ((GradedModuleCat.bimoduleModuleTensor.{max u w, v} Γ Γ).obj
      ((GradedModuleCat.shiftFunctor n).obj (U i))).PreservesHomology := by
  let : Module.Finite k ((GradedModuleCat.shiftFunctor n).obj (U i)) := by
    simpa only [GradedModuleCat.shiftFunctor_obj] using vertex_finite_k k G i
  let : Module.Projective Zᵐᵒᵖ ((GradedModuleCat.shiftFunctor n).obj (U i)) := by
    simpa only [GradedModuleCat.shiftFunctor_obj] using
      projective_zigzagGradedBraidBimodule_right k G i
  let : Module.Finite Zᵐᵒᵖ ((GradedModuleCat.shiftFunctor n).obj (U i)) :=
    Module.Finite.of_restrictScalars_finite k Zᵐᵒᵖ
      ((GradedModuleCat.shiftFunctor n).obj (U i))
  exact GradedModuleCat.bimoduleModuleTensor_preservesHomology.{max u w, v} Γ Γ
    ((GradedModuleCat.shiftFunctor n).obj (U i))

end TauCeti
