/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Module
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Family
public import TauCeti.Geometry.Manifold.Instances.Stiefel
public import TauCeti.Topology.Algebra.ProperAction.Basic
public import TauCeti.Topology.Algebra.UnitaryGroup

/-!
# Orthogonal changes of Stiefel frames

With frame vectors written as rows, the orthogonal group acts by left matrix multiplication.
This action is free and proper and preserves the span. The special orthogonal group acts by
restriction.
-/

public section

noncomputable section

open Matrix
open scoped InnerProductSpace

namespace TauCeti.stiefel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k : ℕ}

/-- Orthogonal matrices act on orthonormal frames by multiplying their matrix of
row vectors on the left. -/
instance instMulActionOrthogonalGroup :
    MulAction (orthogonalGroup (Fin k) ℝ) (stiefel E k) := by
  letI : Module (Matrix (Fin k) (Fin k) ℝ) (Fin k → E) := Matrix.Module.matrixModule
  letI : MulAction (orthogonalGroup (Fin k) ℝ) (Fin k → E) :=
    MulAction.compHom _ (orthogonalGroup (Fin k) ℝ).subtype
  letI : SMul (orthogonalGroup (Fin k) ℝ) (stiefel E k) :=
    ⟨fun A v ↦ ⟨A • v.val, mem_stiefel_iff.2 <|
      ((mem_stiefel_iff.1 v.property).orthonormal_sum_smul_iff_mem_unitaryGroup _).2
        A.property⟩⟩
  exact Subtype.val_injective.mulAction Subtype.val fun _ _ ↦ rfl

/-- The vectors after a change of orthonormal basis have the corresponding matrix coefficients. -/
@[simp]
theorem coe_orthogonalGroup_smul_apply (A : orthogonalGroup (Fin k) ℝ)
    (v : stiefel E k) (j : Fin k) :
    ((A • v : stiefel E k) : Fin k → E) j = ∑ i, A.val j i • v.val i :=
  (rfl)

/-- The action on the indices of an orthonormal frame is free. -/
instance instIsCancelSMulOrthogonalGroup :
    IsCancelSMul (orthogonalGroup (Fin k) ℝ) (stiefel E k) :=
  isCancelSMul_iff_eq_one_of_smul_eq.2 fun {A v} h ↦ by
    have hv := mem_stiefel_iff.1 v.property
    apply Subtype.ext
    ext j i
    have hi := congrArg (fun w : stiefel E k ↦ ⟪v.val i, w.val j⟫_ℝ) h
    simpa [hv.inner_right_fintype, orthonormal_iff_ite.1 hv, Matrix.one_apply, eq_comm] using hi

/-- The special orthogonal group acts through its inclusion in the orthogonal group. -/
instance instMulActionSpecialOrthogonalGroup :
    MulAction (specialOrthogonalGroup (Fin k) ℝ) (stiefel E k) :=
  MulAction.compHom _ (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup)

/-- A rotation acts on frames by its underlying orthogonal matrix. -/
theorem specialOrthogonalGroup_smul_def (A : specialOrthogonalGroup (Fin k) ℝ) (v : stiefel E k) :
    A • v = Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup A • v :=
  (rfl)

/-- The vectors of a rotated frame have the coefficients of the rotation matrix. -/
@[simp]
theorem coe_specialOrthogonalGroup_smul_apply (A : specialOrthogonalGroup (Fin k) ℝ)
    (v : stiefel E k) (j : Fin k) :
    ((A • v : stiefel E k) : Fin k → E) j = ∑ i, A.val j i • v.val i :=
  coe_orthogonalGroup_smul_apply (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup A) v j

/-- The restricted action of the special orthogonal group is free. -/
instance instIsCancelSMulSpecialOrthogonalGroup :
    IsCancelSMul (specialOrthogonalGroup (Fin k) ℝ) (stiefel E k) :=
  isCancelSMul_iff_eq_one_of_smul_eq.2 fun A v h ↦ by
    have hA : Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup A =
        (1 : orthogonalGroup (Fin k) ℝ) :=
      IsCancelSMul.eq_one_of_smul (h := (specialOrthogonalGroup_smul_def A v).symm.trans h)
    exact Subtype.ext (congrArg (fun B : orthogonalGroup (Fin k) ℝ ↦ B.val) hA)

/-- Changing the orthonormal basis is jointly continuous in the matrix and the frame. -/
instance instContinuousSMulOrthogonalGroup :
    ContinuousSMul (orthogonalGroup (Fin k) ℝ) (stiefel E k) := ⟨by
  refine continuous_induced_rng.2 (continuous_pi fun j ↦ ?_)
  simp only [Function.comp_def, coe_orthogonalGroup_smul_apply]
  exact continuous_finsetSum _ fun i _ ↦
    ((continuous_subtypeVal.comp continuous_fst).matrix_elem j i).smul
      ((continuous_apply i).comp (continuous_subtypeVal.comp continuous_snd))⟩

/-- The orthogonal action is proper because the orthogonal group is compact. -/
instance instProperSMulOrthogonalGroup :
    ProperSMul (orthogonalGroup (Fin k) ℝ) (stiefel E k) :=
  properSMul_of_compactSpace _ _

/-- The restricted action is continuous for the subspace topology of the rotation group. -/
instance instContinuousSMulSpecialOrthogonalGroup :
    ContinuousSMul (specialOrthogonalGroup (Fin k) ℝ) (stiefel E k) :=
  MulAction.continuousSMul_compHom (f := Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup)
    (continuous_subtypeVal.subtype_mk _)

/-- The special orthogonal action is proper because the rotation group is compact. -/
instance instProperSMulSpecialOrthogonalGroup :
    ProperSMul (specialOrthogonalGroup (Fin k) ℝ) (stiefel E k) :=
  properSMul_of_compactSpace _ _

open Set Submodule

/-- An orthogonal change of frame preserves the underlying subspace. -/
@[simp]
theorem span_range_orthogonalGroup_smul (A : orthogonalGroup (Fin k) ℝ)
    (v : stiefel E k) : span ℝ (range (A • v).val) = span ℝ (range v.val) := by
  let : FiniteDimensional ℝ (span ℝ (range v.val)) :=
    FiniteDimensional.span_of_finite ℝ (finite_range _)
  refine Submodule.eq_of_le_of_finrank_le (span_le.2 ?_) (by simp)
  rintro _ ⟨i, rfl⟩
  rw [coe_orthogonalGroup_smul_apply]
  exact Submodule.sum_mem _ fun j _ ↦ smul_mem _ _ (subset_span (mem_range_self j))

/-- A rotation of the frame preserves the underlying subspace. -/
@[simp]
theorem span_range_specialOrthogonalGroup_smul (A : specialOrthogonalGroup (Fin k) ℝ)
    (v : stiefel E k) : span ℝ (range (A • v).val) = span ℝ (range v.val) :=
  span_range_orthogonalGroup_smul (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup A) v

end TauCeti.stiefel
