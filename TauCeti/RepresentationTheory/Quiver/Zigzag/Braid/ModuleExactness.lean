/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import Mathlib.CategoryTheory.Abelian.Exact
public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Basic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.RightProjective
import Mathlib.RingTheory.TensorProduct.Finite
import TauCeti.LinearAlgebra.Dual.FiniteProjective
import TauCeti.LinearAlgebra.Dual.Opposite
import TauCeti.LinearAlgebra.TensorProduct.Balanced.DualHom

/-!
# Exactness of the fixed-term zigzag bimodule tensor actions

The vertex ideals are cyclic over the zigzag algebra, which is finite free over the
coefficient ring. Their tensor factorization makes the actual vertex bimodule finite
over that ring and hence finite over the algebra on the right. Its established right
projectivity and opposite-dual reflexivity identify its balanced tensor carrier with
Hom out of a finite projective left module.

This carrier identification is natural in the left-module argument. Projective lifting
therefore proves exactness on underlying modules, and the existing exactness criterion
for graded modules recovers exactness of the actual graded tensor functor. No splitting
or duality map is asserted to preserve the internal grading or the outer left action.

The same argument applies to the regular bimodule and internal shifts of the vertex
bimodules, which are the remaining terms of the two braid support sequences.

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

private theorem rightDual_finite_projective
    (M : GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece)
    [Module.Finite k M] [Module.Projective Zᵐᵒᵖ M] :
    Module.Finite Z (M →ₗ[Zᵐᵒᵖ] Z) ∧ Module.Projective Z (M →ₗ[Zᵐᵒᵖ] Z) := by
  let : Module.Finite Zᵐᵒᵖ M := Module.Finite.of_restrictScalars_finite k Zᵐᵒᵖ M
  exact ⟨Module.Finite.of_surjective (opDualCodomainEquiv Z M).symm.toLinearMap
    (opDualCodomainEquiv Z M).symm.surjective,
    Module.Projective.of_equiv (opDualCodomainEquiv Z M).symm⟩

private def tensorHomEquiv
    (M : GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece)
    [Module.Finite k M] [Module.Projective Zᵐᵒᵖ M]
    (N : GradedModuleCat.{v} (Γ).piece) :
    GradedModuleCat.bimoduleModuleTensorObj Γ Γ M N ≃ₗ[k] ((M →ₗ[Zᵐᵒᵖ] Z) →ₗ[Z] N) := by
  let : Module.Finite Zᵐᵒᵖ M := Module.Finite.of_restrictScalars_finite k Zᵐᵒᵖ M
  let : Module.Finite Z (M →ₗ[Zᵐᵒᵖ] Z) := (rightDual_finite_projective k G M).1
  let : Module.Projective Z (M →ₗ[Zᵐᵒᵖ] Z) := (rightDual_finite_projective k G M).2
  exact (GradedModuleCat.bimoduleModuleTensorUnderlyingEquiv Γ Γ M N).trans
    ((BalancedTensorProduct.congr ((unopDualEvalEquiv Z M).restrictScalars k)
      (LinearEquiv.refl k N)
      (fun a m ↦ (unopDualEvalEquiv Z M).map_smul (op a) m) (fun _ _ ↦ rfl)).trans
      (balancedDualTensorHomEquiv k Z (M →ₗ[Zᵐᵒᵖ] Z) N))

private theorem tensorHomEquiv_tmul
    (M : GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece)
    [Module.Finite k M] [Module.Projective Zᵐᵒᵖ M]
    (N : GradedModuleCat.{v} (Γ).piece) (m : M) (n : N) (p : M →ₗ[Zᵐᵒᵖ] Z) :
    tensorHomEquiv k G M N (GradedModuleCat.bimoduleModuleTensorTmul Γ Γ M N m n) p =
      p m • n := by
  let : Module.Finite Zᵐᵒᵖ M := Module.Finite.of_restrictScalars_finite k Zᵐᵒᵖ M
  let : Module.Finite Z (M →ₗ[Zᵐᵒᵖ] Z) := (rightDual_finite_projective k G M).1
  let : Module.Projective Z (M →ₗ[Zᵐᵒᵖ] Z) := (rightDual_finite_projective k G M).2
  have hc := BalancedTensorProduct.congr_tmul
    ((unopDualEvalEquiv Z M).restrictScalars k) (LinearEquiv.refl k N)
    (fun a m ↦ (unopDualEvalEquiv Z M).map_smul (op a) m) (fun _ _ ↦ rfl) m n
  unfold tensorHomEquiv
  rw [LinearEquiv.trans_apply,
    GradedModuleCat.bimoduleModuleTensorUnderlyingEquiv_tmul,
    LinearEquiv.trans_apply]
  rw [hc]
  simp only [LinearEquiv.restrictScalars_apply, LinearEquiv.refl_apply,
    balancedDualTensorHomEquiv_apply, balancedDualTensorHom_tmul,
    unopDualEvalEquiv_apply]

private theorem tensorHomEquiv_naturality
    (M : GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece)
    [Module.Finite k M] [Module.Projective Zᵐᵒᵖ M]
    {N N' : GradedModuleCat.{v} (Γ).piece} (f : N ⟶ N') :
    (f.hom.compRight k).comp (tensorHomEquiv k G M N).toLinearMap =
      (tensorHomEquiv k G M N').toLinearMap.comp
        ((((GradedModuleCat.bimoduleModuleTensor Γ Γ).obj M).map f).hom.restrictScalars k) := by
  apply LinearMap.ext
  intro z
  apply LinearMap.ext
  intro p
  change f.hom (tensorHomEquiv k G M N z p) =
    tensorHomEquiv k G M N'
      ((((GradedModuleCat.bimoduleModuleTensor Γ Γ).obj M).map f).hom z) p
  obtain ⟨t, rfl⟩ := (GradedModuleCat.bimoduleModuleTensorUnderlyingEquiv Γ Γ M N).symm.surjective z
  induction t using BalancedTensorProduct.induction_on with
  | ht m n =>
    simp only [GradedModuleCat.bimoduleModuleTensorUnderlyingEquiv_symm_tmul]
    change f.hom (tensorHomEquiv k G M N
      (GradedModuleCat.bimoduleModuleTensorTmul Γ Γ M N m n) p) =
      tensorHomEquiv k G M N'
        ((GradedModuleCat.bimoduleModuleTensorMap Γ Γ (𝟙 M) f).hom
          (GradedModuleCat.bimoduleModuleTensorTmul Γ Γ M N m n)) p
    rw [GradedModuleCat.bimoduleModuleTensorMap_tmul, GradedModuleCat.hom_id,
      LinearMap.id_apply, tensorHomEquiv_tmul, tensorHomEquiv_tmul]
    exact f.hom.map_smul _ _
  | ha x y hx hy =>
    simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hx hy

private theorem tensor_preservesHomology
    (M : GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece)
    [Module.Finite k M] [Module.Projective Zᵐᵒᵖ M] :
    ((GradedModuleCat.bimoduleModuleTensor.{max u w, v} Γ Γ).obj M).PreservesHomology := by
  let P := M →ₗ[Zᵐᵒᵖ] Z
  let : Module.Projective Z P := (rightDual_finite_projective k G M).2
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  apply GradedModuleCat.exact_iff.mpr
  have H := GradedModuleCat.exact_iff.mp hS
  have hHom : Function.Exact
      ((S.f.hom.compRight k) : (P →ₗ[Z] S.X₁) →ₗ[k] (P →ₗ[Z] S.X₂))
      ((S.g.hom.compRight k) : (P →ₗ[Z] S.X₂) →ₗ[k] (P →ₗ[Z] S.X₃)) := by
    intro φ
    constructor
    · intro hφ
      let φRange : P →ₗ[Z] LinearMap.range S.f.hom :=
        φ.codRestrict _ fun p ↦ (H (φ p)).1 (by
          simpa using congrArg (fun f : P →ₗ[Z] S.X₃ ↦ f p) hφ)
      obtain ⟨ψ, hψ⟩ := Module.projective_lifting_property S.f.hom.rangeRestrict φRange
        (by rintro ⟨y, x, hx⟩; exact ⟨x, Subtype.ext hx⟩)
      refine ⟨ψ, ?_⟩
      ext p
      exact congrArg Subtype.val (LinearMap.congr_fun hψ p)
    · rintro ⟨ψ, rfl⟩
      ext p
      exact H.apply_apply_eq_zero (ψ p)
  exact (Function.Exact.iff_of_ladder_linearEquiv
    (tensorHomEquiv_naturality k G M S.f)
    (tensorHomEquiv_naturality k G M S.g)).mp hHom

/-- Tensoring with the actual vertex bimodule preserves homology of graded modules. -/
theorem preservesHomology_zigzagGradedBraidBimoduleTensor (i : V) :
    ((GradedModuleCat.bimoduleModuleTensor.{max u w, v} Γ Γ).obj
      (U i)).PreservesHomology := by
  let : Module.Finite k (U i) := vertex_finite_k k G i
  let : Module.Projective Zᵐᵒᵖ (U i) := projective_zigzagGradedBraidBimodule_right k G i
  exact tensor_preservesHomology k G (U i)

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
  exact tensor_preservesHomology.{u, v, w} k G (zigzagGradedBimodule k G)

/-- An internal shift of the vertex bimodule retains homology preservation of tensoring. -/
theorem preservesHomology_zigzagGradedBraidBimoduleTensor_shift (i : V) (n : ℤ) :
    ((GradedModuleCat.bimoduleModuleTensor.{max u w, v} Γ Γ).obj
      ((GradedModuleCat.shiftFunctor n).obj (U i))).PreservesHomology := by
  let : Module.Finite k ((GradedModuleCat.shiftFunctor n).obj (U i)) := by
    simpa only [GradedModuleCat.shiftFunctor_obj] using vertex_finite_k k G i
  let : Module.Projective Zᵐᵒᵖ ((GradedModuleCat.shiftFunctor n).obj (U i)) := by
    simpa only [GradedModuleCat.shiftFunctor_obj] using
      projective_zigzagGradedBraidBimodule_right k G i
  exact tensor_preservesHomology.{u, v, w} k G
    ((GradedModuleCat.shiftFunctor n).obj (U i))

end TauCeti
