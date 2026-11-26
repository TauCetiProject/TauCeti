/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Defect
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Order
public import TauCeti.Analysis.CStarAlgebra.Matrix.Trace
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic

/-!
# Completely positive contractions from matrices to `M₁`

A positive linear functional `ω` on a C⋆-algebra gives the completely positive map `a ↦ ω a • 1`
into the matrices `M_m = CStarMatrix m m ℂ` (`PositiveLinearMap.toCompletelyPositiveMapOfId`),
whose norm at `a` is `‖ω a‖`. For nonempty `m` (for instance `M₁ = CStarMatrix Unit Unit ℂ`) its
multiplicativity defects are scalar:
`d₂(ω, a) = Re ω(a⋆a) - |ω a|²` and `‖ω(ab) - ω(a)ω(b)‖₂ = |ω(ab) - ω(a)ω(b)|`
(`PositiveLinearMap.twoNormDefect_toCompletelyPositiveMapOfId`,
`PositiveLinearMap.normalizedTwoNorm_toCompletelyPositiveMapOfId_mul_sub`).

This file applies it to two functionals on `M_n = CStarMatrix n n ℂ`:

* the diagonal entry `x ↦ x i i` (`CStarMatrix.diagEntry`), a compression by a unit vector, giving
  the completely positive map `CStarMatrix.diagEntryCP i : M_n → M₁`;
* the normalized trace `tr_n` (`CStarMatrix.normalizedTraceMap`), giving
  `CStarMatrix.normalizedTraceCP : M_n → M₁`.

At a unitary `u` the 2-norm defect of the trace is `1 - |tr_n u|²`
(`CStarMatrix.twoNormDefect_normalizedTraceCP_of_mem_unitary`).

Both maps are contractions (`CStarMatrix.norm_diagEntryCP_apply_le`,
`CStarMatrix.norm_normalizedTraceCP_apply_le`), so they are completely positive contractions
into matrices, the maps whose multiplicativity defects are studied in
`TauCeti/Analysis/CStarAlgebra/CompletelyPositiveMap/Defect.lean`.
-/

public section

noncomputable section

open scoped CStarAlgebra ComplexOrder

namespace PositiveLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

/-- The 2-norm defect of `a ↦ ω a • 1` is `Re ω(a⋆a) - |ω a|²`. -/
theorem twoNormDefect_toCompletelyPositiveMapOfId (ω : A →ₚ[ℂ] ℂ) (a : A) :
    (ω.toCompletelyPositiveMapOfId (CStarMatrix m m ℂ)).twoNormDefect a =
      (ω (star a * a)).re - ‖ω a‖ ^ 2 := by
  simp only [CompletelyPositiveMap.twoNormDefect_def, toCompletelyPositiveMapOfId_apply,
    star_smul, star_one, smul_mul_smul, mul_one, ← sub_smul, CStarMatrix.normalizedTrace_smul,
    CStarMatrix.normalizedTrace_one, Complex.sub_re, Complex.star_def, Complex.conj_mul']
  norm_cast

/-- The norm defect of `a ↦ ω a • 1` is `|ω(a⋆a) - |ω a|²|`. -/
theorem normDefect_toCompletelyPositiveMapOfId (ω : A →ₚ[ℂ] ℂ) (a : A) :
    (ω.toCompletelyPositiveMapOfId (CStarMatrix m m ℂ)).normDefect a =
      ‖ω (star a * a) - star (ω a) * ω a‖ := by
  simp only [CompletelyPositiveMap.normDefect_def, toCompletelyPositiveMapOfId_apply,
    star_smul, star_one, smul_mul_smul, mul_one, ← sub_smul, norm_smul, norm_one]

/-- The 2-norm of the multiplicativity error of `a ↦ ω a • 1` is `|ω(ab) - ω(a)ω(b)|`. -/
theorem normalizedTwoNorm_toCompletelyPositiveMapOfId_mul_sub (ω : A →ₚ[ℂ] ℂ) (a b : A) :
    CStarMatrix.normalizedTwoNorm
        (ω.toCompletelyPositiveMapOfId (CStarMatrix m m ℂ) (a * b) -
          ω.toCompletelyPositiveMapOfId (CStarMatrix m m ℂ) a *
            ω.toCompletelyPositiveMapOfId (CStarMatrix m m ℂ) b) =
      ‖ω (a * b) - ω a * ω b‖ := by
  simp only [toCompletelyPositiveMapOfId_apply, smul_mul_smul, mul_one, ← sub_smul,
    CStarMatrix.normalizedTwoNorm_smul, CStarMatrix.normalizedTwoNorm_one]

end PositiveLinearMap

namespace CStarMatrix

variable {n : Type*} [Fintype n]

/-- The diagonal entry `x ↦ x i i` of a matrix, as a positive linear functional. -/
def diagEntry (i : n) : CStarMatrix n n ℂ →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    { toFun x := x i i
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    fun _ hx => diag_nonneg_of_nonneg hx i

/-- `diagEntry i x` is the entry `x i i`. -/
@[simp]
theorem diagEntry_apply (i : n) (x : CStarMatrix n n ℂ) : diagEntry i x = x i i :=
  (rfl)

/-- The completely positive compression `x ↦ x i i` from `M_n` to `M₁`. -/
def diagEntryCP (i : n) : CStarMatrix n n ℂ →CP CStarMatrix Unit Unit ℂ :=
  (diagEntry i).toCompletelyPositiveMapOfId (CStarMatrix Unit Unit ℂ)

/-- Unfolding lemma for `diagEntryCP`. -/
theorem diagEntryCP_def (i : n) :
    diagEntryCP i = (diagEntry i).toCompletelyPositiveMapOfId (CStarMatrix Unit Unit ℂ) :=
  (rfl)

/-- `diagEntryCP i x` is `x i i` times the identity of `M₁`. -/
@[simp]
theorem diagEntryCP_apply (i : n) (x : CStarMatrix n n ℂ) :
    diagEntryCP i x = x i i • (1 : CStarMatrix Unit Unit ℂ) := by
  simp [diagEntryCP]

/-- The compression `x ↦ x i i` is a contraction. -/
theorem norm_diagEntryCP_apply_le (i : n) (x : CStarMatrix n n ℂ) : ‖diagEntryCP i x‖ ≤ ‖x‖ := by
  rw [diagEntryCP, PositiveLinearMap.norm_toCompletelyPositiveMapOfId_apply, diagEntry_apply]
  exact norm_entry_le_norm

/-- The normalized trace `tr_n` as a completely positive map from `M_n` to `M₁`. -/
def normalizedTraceCP : CStarMatrix n n ℂ →CP CStarMatrix Unit Unit ℂ :=
  (normalizedTraceMap n).toPositiveLinearMap.toCompletelyPositiveMapOfId (CStarMatrix Unit Unit ℂ)

/-- Unfolding lemma for `normalizedTraceCP`. -/
theorem normalizedTraceCP_def :
    (normalizedTraceCP : CStarMatrix n n ℂ →CP CStarMatrix Unit Unit ℂ) =
      (normalizedTraceMap n).toPositiveLinearMap.toCompletelyPositiveMapOfId
        (CStarMatrix Unit Unit ℂ) :=
  (rfl)

/-- `normalizedTraceCP x` is `tr_n x` times the identity of `M₁`. -/
@[simp]
theorem normalizedTraceCP_apply (x : CStarMatrix n n ℂ) :
    normalizedTraceCP x = normalizedTrace x • (1 : CStarMatrix Unit Unit ℂ) := by
  simp [normalizedTraceCP]

/-- The normalized trace `tr_n : M_n → M₁` is a contraction. -/
theorem norm_normalizedTraceCP_apply_le (x : CStarMatrix n n ℂ) : ‖normalizedTraceCP x‖ ≤ ‖x‖ := by
  rw [normalizedTraceCP, PositiveLinearMap.norm_toCompletelyPositiveMapOfId_apply,
    PositiveContinuousLinearMap.coe_toPositiveLinearMap, normalizedTraceMap_apply]
  exact norm_normalizedTrace_le_norm x

/-- At a unitary `u`, the 2-norm defect of the normalized trace is `1 - |tr_n u|²`. -/
theorem twoNormDefect_normalizedTraceCP_of_mem_unitary [DecidableEq n] [Nonempty n]
    {u : CStarMatrix n n ℂ} (hu : u ∈ unitary (CStarMatrix n n ℂ)) :
    normalizedTraceCP.twoNormDefect u = 1 - ‖normalizedTrace u‖ ^ 2 := by
  rw [normalizedTraceCP_def, PositiveLinearMap.twoNormDefect_toCompletelyPositiveMapOfId,
    Unitary.star_mul_self_of_mem hu]
  simp

end CStarMatrix
