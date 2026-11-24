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
import TauCeti.Analysis.CStarAlgebra.Matrix.Order

/-!
# Completely positive contractions from matrices to `M₁`

A positive linear functional `ω` on a C⋆-algebra is completely positive
(`PositiveLinearMap.toCompletelyPositiveMap`), and so is `a ↦ ω a • 1` into the one-by-one matrices
`M₁ = CStarMatrix Unit Unit ℂ` (`PositiveLinearMap.toCompletelyPositiveMapMatrixOne`), whose norm
at `a` is `‖ω a‖`. Its multiplicativity defects are scalar:
`d₂(ω, a) = Re ω(a⋆a) - |ω a|²` and `‖ω(ab) - ω(a)ω(b)‖₂ = |ω(ab) - ω(a)ω(b)|`
(`PositiveLinearMap.twoNormDefect_toCompletelyPositiveMapMatrixOne`,
`PositiveLinearMap.normalizedTwoNorm_toCompletelyPositiveMapMatrixOne_mul_sub`).

This file applies it to two functionals on `M_n = CStarMatrix n n ℂ`:

* the diagonal entry `x ↦ x i i` (`CStarMatrix.diagEntry`), a compression by a unit vector, giving
  the completely positive map `CStarMatrix.diagEntryCP i : M_n → M₁`;
* the normalized trace `tr_n` (`CStarMatrix.normalizedTraceₚ`), giving
  `CStarMatrix.normalizedTraceCP : M_n → M₁`.

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

/-- A positive linear functional `ω : A →ₚ[ℂ] ℂ` as a completely positive map into the one-by-one
matrices, `a ↦ ω a • 1`. -/
def toCompletelyPositiveMapMatrixOne (ω : A →ₚ[ℂ] ℂ) : A →CP CStarMatrix Unit Unit ℂ :=
  CompletelyPositiveMap.comp
    (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
      (StarAlgHom.ofId ℂ (CStarMatrix Unit Unit ℂ)))
    ω.toCompletelyPositiveMap

/-- `ω.toCompletelyPositiveMapMatrixOne a` is `ω a` times the identity. -/
@[simp]
theorem toCompletelyPositiveMapMatrixOne_apply (ω : A →ₚ[ℂ] ℂ) (a : A) :
    ω.toCompletelyPositiveMapMatrixOne a = ω a • (1 : CStarMatrix Unit Unit ℂ) := by
  rw [toCompletelyPositiveMapMatrixOne, CompletelyPositiveMap.comp_apply,
    CompletelyPositiveMapClass.coe_toCompletelyPositiveLinearMap, toCompletelyPositiveMap_apply,
    StarAlgHom.ofId_apply, Algebra.algebraMap_eq_smul_one]

/-- The only entry of `ω.toCompletelyPositiveMapMatrixOne a` is `ω a`. -/
theorem toCompletelyPositiveMapMatrixOne_apply_apply (ω : A →ₚ[ℂ] ℂ) (a : A) (i j : Unit) :
    ω.toCompletelyPositiveMapMatrixOne a i j = ω a := by
  simp

/-- The norm of `ω.toCompletelyPositiveMapMatrixOne a` is `‖ω a‖`. -/
theorem norm_toCompletelyPositiveMapMatrixOne_apply (ω : A →ₚ[ℂ] ℂ) (a : A) :
    ‖ω.toCompletelyPositiveMapMatrixOne a‖ = ‖ω a‖ := by
  rw [toCompletelyPositiveMapMatrixOne_apply, norm_smul, norm_one, mul_one]

/-- The 2-norm defect of `a ↦ ω a • 1` is `Re ω(a⋆a) - |ω a|²`. -/
theorem twoNormDefect_toCompletelyPositiveMapMatrixOne (ω : A →ₚ[ℂ] ℂ) (a : A) :
    ω.toCompletelyPositiveMapMatrixOne.twoNormDefect a = (ω (star a * a)).re - ‖ω a‖ ^ 2 := by
  simp only [CompletelyPositiveMap.twoNormDefect_def, toCompletelyPositiveMapMatrixOne_apply,
    star_smul, star_one, smul_mul_smul, mul_one, ← sub_smul, CStarMatrix.normalizedTrace_smul,
    CStarMatrix.normalizedTrace_one, Complex.sub_re, Complex.star_def, Complex.conj_mul']
  norm_cast

/-- The norm defect of `a ↦ ω a • 1` is `|ω(a⋆a) - |ω a|²|`. -/
theorem normDefect_toCompletelyPositiveMapMatrixOne (ω : A →ₚ[ℂ] ℂ) (a : A) :
    ω.toCompletelyPositiveMapMatrixOne.normDefect a = ‖ω (star a * a) - star (ω a) * ω a‖ := by
  simp only [CompletelyPositiveMap.normDefect_def, toCompletelyPositiveMapMatrixOne_apply,
    star_smul, star_one, smul_mul_smul, mul_one, ← sub_smul, norm_smul, norm_one]

/-- The 2-norm of the multiplicativity error of `a ↦ ω a • 1` is `|ω(ab) - ω(a)ω(b)|`. -/
theorem normalizedTwoNorm_toCompletelyPositiveMapMatrixOne_mul_sub (ω : A →ₚ[ℂ] ℂ) (a b : A) :
    CStarMatrix.normalizedTwoNorm (ω.toCompletelyPositiveMapMatrixOne (a * b) -
      ω.toCompletelyPositiveMapMatrixOne a * ω.toCompletelyPositiveMapMatrixOne b) =
      ‖ω (a * b) - ω a * ω b‖ := by
  simp only [toCompletelyPositiveMapMatrixOne_apply, smul_mul_smul, mul_one, ← sub_smul,
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
    fun _ hx => (nonneg_iff_posSemidef.mp hx).diag_nonneg

/-- `diagEntry i x` is the entry `x i i`. -/
@[simp]
theorem diagEntry_apply (i : n) (x : CStarMatrix n n ℂ) : diagEntry i x = x i i :=
  (rfl)

/-- The normalized trace `tr_n`, as a positive linear functional. -/
def normalizedTraceₚ : CStarMatrix n n ℂ →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    { toFun := normalizedTrace
      map_add' := normalizedTrace_add
      map_smul' := normalizedTrace_smul }
    fun _ => normalizedTrace_nonneg

/-- `normalizedTraceₚ x` is the normalized trace of `x`. -/
@[simp]
theorem normalizedTraceₚ_apply (x : CStarMatrix n n ℂ) : normalizedTraceₚ x = normalizedTrace x :=
  (rfl)

/-- The completely positive compression `x ↦ x i i` from `M_n` to `M₁`. -/
def diagEntryCP (i : n) : CStarMatrix n n ℂ →CP CStarMatrix Unit Unit ℂ :=
  (diagEntry i).toCompletelyPositiveMapMatrixOne

/-- Unfolding lemma for `diagEntryCP`. -/
theorem diagEntryCP_def (i : n) :
    diagEntryCP i = (diagEntry i).toCompletelyPositiveMapMatrixOne :=
  (rfl)

/-- `diagEntryCP i x` is `x i i` times the identity of `M₁`. -/
@[simp]
theorem diagEntryCP_apply (i : n) (x : CStarMatrix n n ℂ) :
    diagEntryCP i x = x i i • (1 : CStarMatrix Unit Unit ℂ) := by
  simp [diagEntryCP]

/-- The compression `x ↦ x i i` is a contraction. -/
theorem norm_diagEntryCP_apply_le (i : n) (x : CStarMatrix n n ℂ) : ‖diagEntryCP i x‖ ≤ ‖x‖ := by
  rw [diagEntryCP, PositiveLinearMap.norm_toCompletelyPositiveMapMatrixOne_apply, diagEntry_apply]
  exact norm_entry_le_norm

/-- The normalized trace `tr_n` as a completely positive map from `M_n` to `M₁`. -/
def normalizedTraceCP : CStarMatrix n n ℂ →CP CStarMatrix Unit Unit ℂ :=
  normalizedTraceₚ.toCompletelyPositiveMapMatrixOne

/-- Unfolding lemma for `normalizedTraceCP`. -/
theorem normalizedTraceCP_def :
    (normalizedTraceCP : CStarMatrix n n ℂ →CP CStarMatrix Unit Unit ℂ) =
      normalizedTraceₚ.toCompletelyPositiveMapMatrixOne :=
  (rfl)

/-- `normalizedTraceCP x` is `tr_n x` times the identity of `M₁`. -/
@[simp]
theorem normalizedTraceCP_apply (x : CStarMatrix n n ℂ) :
    normalizedTraceCP x = normalizedTrace x • (1 : CStarMatrix Unit Unit ℂ) := by
  simp [normalizedTraceCP]

/-- The normalized trace `tr_n : M_n → M₁` is a contraction. -/
theorem norm_normalizedTraceCP_apply_le (x : CStarMatrix n n ℂ) : ‖normalizedTraceCP x‖ ≤ ‖x‖ := by
  rw [normalizedTraceCP, PositiveLinearMap.norm_toCompletelyPositiveMapMatrixOne_apply,
    normalizedTraceₚ_apply]
  exact norm_normalizedTrace_le_norm x

end CStarMatrix
