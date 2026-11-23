/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Complexification
public import Mathlib.Topology.ContinuousMap.Compact

/-! # Actual compact-dual clients, including a nonnormed product module -/
public section
noncomputable section
open TauCeti
open scoped TensorProduct TauCeti.Complexification CompactConvergenceCLM
namespace TauCeti.Examples.CompactDualComplexification

universe u

/-- The identity functional in the native compact-convergence real dual. -/
def scalarId : ℝ →L_c[ℝ] ℝ :=
  (ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℝ) ℝ {K : Set ℝ | IsCompact K})
    (ContinuousLinearMap.id ℝ ℝ)

/-- Nonzero real coefficient and imaginary source are both retained. -/
theorem scalar_one_I :
    complexificationCompactDualEquiv ℝ (1 ⊗ₜ[ℝ] scalarId) (Complex.I ⊗ₜ[ℝ] (1 : ℝ)) =
      Complex.I := by
  simp [scalarId]

/-- Multiplying the coefficient by i also changes its actual evaluation. -/
theorem scalar_I_one :
    complexificationCompactDualEquiv ℝ (Complex.I ⊗ₜ[ℝ] scalarId) (1 ⊗ₜ[ℝ] (1 : ℝ)) =
      Complex.I := by
  simp [scalarId]

/-- Two imaginary factors produce minus one. -/
theorem scalar_I_I :
    complexificationCompactDualEquiv ℝ (Complex.I ⊗ₜ[ℝ] scalarId) (Complex.I ⊗ₜ[ℝ] (1 : ℝ)) =
      -1 := by
  simp [scalarId]

/-- A native complex functional constructed directly by scalar extension of the real identity. -/
def scalarComplex : (ℂ ⊗[ℝ] ℝ) →L_c[ℂ] ℂ :=
  (ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℂ) ℂ
    {K : Set (ℂ ⊗[ℝ] ℝ) | IsCompact K}) Complex.ofRealCLM.liftBaseChangeComplex

/-- The inverse recovers an imaginary tensor from an independently constructed native dual. -/
theorem inverse_native_imaginary :
    (complexificationCompactDualEquiv ℝ).symm (Complex.I • scalarComplex) =
      Complex.I ⊗ₜ[ℝ] scalarId := by
  apply complexification_ext <;> ext x <;>
    simp [scalarComplex, scalarId,
      realPart_tmul, imaginaryPart_tmul, ContinuousLinearMap.liftBaseChangeComplex_apply]

/-- The independently constructed real functional is fixed by the native dual conjugation. -/
theorem scalarComplex_fixed : compactDualConjCLE ℝ scalarComplex = scalarComplex := by
  ext v
  simp [compactDualConjCLE_apply, scalarComplex, ContinuousLinearMap.liftBaseChangeComplex_apply]

/-- The native fixed-space inverse retains the value of an independently constructed functional. -/
theorem fixed_scalar :
    (compactDualRealPointsCLE ℝ).symm
      ⟨scalarComplex, mem_realPoints.mpr scalarComplex_fixed⟩ 1 = 1 := by
  simp [compactDualRealPointsCLE_symm_apply, scalarComplex]

/-- Evaluation in the infinite-dimensional continuous-function model. -/
def intervalEvaluation : C(↥(Set.Icc (0 : ℝ) 1), ℝ) →L_c[ℝ] ℝ :=
  (ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℝ) ℝ
    {K : Set C(↥(Set.Icc (0 : ℝ) 1), ℝ) | IsCompact K})
    (ContinuousMap.evalCLM ℝ ⟨0, by constructor <;> norm_num⟩)

/-- Nonzero infinite-dimensional coefficients survive the complex dual comparison. -/
theorem infinite_evaluation :
    complexificationCompactDualEquiv C(↥(Set.Icc (0 : ℝ) 1), ℝ) (Complex.I ⊗ₜ[ℝ] intervalEvaluation)
      (1 ⊗ₜ[ℝ] (ContinuousMap.const _ (1 : ℝ))) =
      Complex.I := by
  simp [intervalEvaluation]

/-- The coordinate functional uses the original product topology on real sequences. -/
def sequenceEvaluation : (ℕ → ℝ) →L_c[ℝ] ℝ :=
  (ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℝ) ℝ
    {K : Set (ℕ → ℝ) | IsCompact K}) (ContinuousLinearMap.proj 0)

/-- The nonnormed product-topology client has an actual nonzero evaluation. -/
theorem sequence_nonzero :
    complexificationCompactDualEquiv (ℕ → ℝ) (Complex.I ⊗ₜ[ℝ] sequenceEvaluation)
      (1 ⊗ₜ[ℝ] (fun _ : ℕ ↦ (1 : ℝ))) =
      Complex.I := by
  simp [sequenceEvaluation]

/-- The native complex compact dual of any empty-index coefficient module is zero. -/
theorem emptyIndex_dual_zero {ι : Type u} [IsEmpty ι]
    (A : (ℂ ⊗[ℝ] (ι → ℝ)) →L_c[ℂ] ℂ) : A = 0 := by
  ext v
  obtain ⟨a, b, rfl⟩ := exists_one_tmul_add_I_tmul v
  have ha : a = 0 := Subsingleton.elim _ _
  have hb : b = 0 := Subsingleton.elim _ _
  simp [ha, hb]

/-- Rank-zero source modules have zero inverse, without nontriviality assumptions. -/
theorem rankZero_inverse (A : (ℂ ⊗[ℝ] (Fin 0 → ℝ)) →L_c[ℂ] ℂ) :
    (complexificationCompactDualEquiv (Fin 0 → ℝ)).symm A = 0 := by
  rw [emptyIndex_dual_zero A, map_zero]

/-- The fixed endpoint includes literal empty-index modules in arbitrary universes. -/
theorem emptyUniverse_fixed (A : realPoints (compactDualConjCLE (PEmpty.{u + 1} → ℝ)).toLinearMap) :
    (compactDualRealPointsCLE (PEmpty.{u + 1} → ℝ)).symm A = 0 := by
  ext x
  have hx : x = 0 := Subsingleton.elim _ _
  simp [hx]

example (A : realPoints (compactDualConjCLE (Empty → ℝ)).toLinearMap) :
    (compactDualRealPointsCLE (Empty → ℝ)).symm A = 0 := by
  ext x
  have hx : x = 0 := Subsingleton.elim _ _
  simp [hx]

section CompatibleTopologies

variable (E : Type*) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousNeg E]
  [TopologicalSpace (ℂ ⊗[ℝ] E)] [IsComplexificationTopology E]
  [TopologicalSpace (ℂ ⊗[ℝ] (E →L_c[ℝ] ℝ))]
  [IsComplexificationTopology (E →L_c[ℝ] ℝ)]

/-- The native fixed submodule's real action agrees with restriction of the ambient complex action.
This checks the actual `ComplexToReal` module used by `realPoints`, for arbitrary compatible
complexification topologies on both the source and its real dual. -/
theorem fixed_real_scalar (r : ℝ) (f : E →L_c[ℝ] ℝ) :
    (r • compactDualRealPointsCLE E f).val =
      (r : ℂ) • compactDualComplexExtension E f := by
  rw [← map_smul (compactDualRealPointsCLE E) r f, coe_compactDualRealPointsCLE,
    map_smul (compactDualComplexExtension E) r f]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) r _

end CompatibleTopologies

end TauCeti.Examples.CompactDualComplexification
