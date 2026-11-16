/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import TauCeti.Analysis.RCLike.Complex
import TauCeti.Analysis.Normed.Algebra.MatrixExponential
import TauCeti.Topology.Instances.Matrix

/-!
# Pushing matrices over an `RCLike` field into complex matrices

Entrywise application of `RCLike.toComplexStarAlgHom 𝕜 : 𝕜 →⋆ₐ[ℝ] ℂ` yields an injective
continuous unital `ℝ`-star-algebra homomorphism `Matrix.toComplexStarAlgHom n 𝕜` from
`Matrix n n 𝕜` into `Matrix n n ℂ`. Because the scalar embedding is a field homomorphism preserving
real parts, `Matrix.toComplexStarAlgHom` preserves and reflects invertibility, the real spectrum,
Hermitian symmetry, positive semidefiniteness, positive definiteness, and the Loewner order, and
commutes with the continuous functional calculus, the matrix exponential, and the real part of the
trace.

This transfers C⋆-algebraic and quantum-entropy inequalities proved over `ℂ` to matrices over an
arbitrary `RCLike` scalar field (`ℝ` or `ℂ`).

## Main definitions and results

* `Matrix.toComplexStarAlgHom`: entrywise pushforward `Matrix n n 𝕜 →⋆ₐ[ℝ] Matrix n n ℂ`.
* `Matrix.isHermitian_toComplexStarAlgHom_iff`, `Matrix.posSemidef_toComplexStarAlgHom_iff`,
  `Matrix.posDef_toComplexStarAlgHom_iff`, `Matrix.toComplexStarAlgHom_le_iff`: preservation and
  reflection of Hermitian symmetry, positivity, and the Loewner order.
* `Matrix.toComplexStarAlgHom_cfc`, `Matrix.toComplexStarAlgHom_exp`: compatibility with the
  continuous functional calculus and the matrix exponential.
-/

public section

noncomputable section

open NormedSpace
open scoped ComplexOrder MatrixOrder

namespace Matrix

variable (n 𝕜 : Type*) [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- Entrywise application of `RCLike.toComplexStarAlgHom 𝕜` bundled as a unital `ℝ`-star-algebra
homomorphism `Matrix n n 𝕜 →⋆ₐ[ℝ] Matrix n n ℂ`. -/
def toComplexStarAlgHom : Matrix n n 𝕜 →⋆ₐ[ℝ] Matrix n n ℂ :=
  { (RCLike.toComplexStarAlgHom 𝕜).toAlgHom.mapMatrix with
    map_star' := fun A ↦ by
      ext i j
      simp [star_eq_conjTranspose, AlgHom.mapMatrix_apply, map_apply] }

variable {n 𝕜}

@[simp]
theorem toComplexStarAlgHom_apply (A : Matrix n n 𝕜) (i j : n) :
    toComplexStarAlgHom n 𝕜 A i j = RCLike.toComplexStarAlgHom 𝕜 (A i j) :=
  (rfl)

theorem toComplexStarAlgHom_eq_map (A : Matrix n n 𝕜) :
    toComplexStarAlgHom n 𝕜 A = A.map (RCLike.toComplexStarAlgHom 𝕜) :=
  (rfl)

theorem toComplexStarAlgHom_injective : Function.Injective (toComplexStarAlgHom n 𝕜) := by
  intro A B h
  ext i j
  exact RCLike.toComplexStarAlgHom_injective (congrFun (congrFun h i) j)

@[fun_prop]
theorem continuous_toComplexStarAlgHom : Continuous (toComplexStarAlgHom n 𝕜) :=
  continuous_matrix fun i j ↦
    RCLike.continuous_toComplexStarAlgHom.comp (continuous_apply j |>.comp (continuous_apply i))

@[simp]
theorem trace_toComplexStarAlgHom (A : Matrix n n 𝕜) :
    (toComplexStarAlgHom n 𝕜 A).trace = RCLike.toComplexStarAlgHom 𝕜 A.trace := by
  simp [Matrix.trace, map_sum]

theorem re_trace_toComplexStarAlgHom (A : Matrix n n 𝕜) :
    ((toComplexStarAlgHom n 𝕜 A).trace).re = RCLike.re A.trace := by
  simp [trace_toComplexStarAlgHom]

@[simp]
theorem det_toComplexStarAlgHom (A : Matrix n n 𝕜) :
    (toComplexStarAlgHom n 𝕜 A).det = RCLike.toComplexStarAlgHom 𝕜 A.det :=
  ((RCLike.toComplexStarAlgHom 𝕜).toAlgHom.map_det A).symm

@[simp]
theorem isUnit_toComplexStarAlgHom_iff {A : Matrix n n 𝕜} :
    IsUnit (toComplexStarAlgHom n 𝕜 A) ↔ IsUnit A := by
  rw [isUnit_iff_isUnit_det, isUnit_iff_isUnit_det, det_toComplexStarAlgHom,
    isUnit_iff_ne_zero, isUnit_iff_ne_zero, map_ne_zero_iff _ RCLike.toComplexStarAlgHom_injective]

@[simp]
theorem isHermitian_toComplexStarAlgHom_iff {A : Matrix n n 𝕜} :
    (toComplexStarAlgHom n 𝕜 A).IsHermitian ↔ A.IsHermitian := by
  rw [isHermitian_iff_isSelfAdjoint, isHermitian_iff_isSelfAdjoint, IsSelfAdjoint,
    IsSelfAdjoint, ← map_star, toComplexStarAlgHom_injective.eq_iff]

@[simp]
theorem spectrum_real_toComplexStarAlgHom (A : Matrix n n 𝕜) :
    spectrum ℝ (toComplexStarAlgHom n 𝕜 A) = spectrum ℝ A := by
  ext r
  simp only [spectrum.mem_iff, ← AlgHomClass.commutes (toComplexStarAlgHom n 𝕜) r, ← map_sub,
    isUnit_toComplexStarAlgHom_iff]

@[simp]
theorem posSemidef_toComplexStarAlgHom_iff {A : Matrix n n 𝕜} :
    (toComplexStarAlgHom n 𝕜 A).PosSemidef ↔ A.PosSemidef := by
  rw [← nonneg_iff_posSemidef, ← nonneg_iff_posSemidef]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hA : IsSelfAdjoint A :=
      isHermitian_iff_isSelfAdjoint.1 (isHermitian_toComplexStarAlgHom_iff.1 h.isSelfAdjoint)
    rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ hA,
      ← spectrum_real_toComplexStarAlgHom]
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ h.isSelfAdjoint).1 h
  · have hC : IsSelfAdjoint (toComplexStarAlgHom n 𝕜 A) :=
      h.isSelfAdjoint.map (toComplexStarAlgHom n 𝕜)
    rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ hC,
      spectrum_real_toComplexStarAlgHom]
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ h.isSelfAdjoint).1 h

@[simp]
theorem toComplexStarAlgHom_le_iff {A B : Matrix n n 𝕜} :
    toComplexStarAlgHom n 𝕜 A ≤ toComplexStarAlgHom n 𝕜 B ↔ A ≤ B := by
  rw [← sub_nonneg, ← map_sub, nonneg_iff_posSemidef, posSemidef_toComplexStarAlgHom_iff,
    ← nonneg_iff_posSemidef, sub_nonneg]

@[simp]
theorem posDef_toComplexStarAlgHom_iff {A : Matrix n n 𝕜} :
    (toComplexStarAlgHom n 𝕜 A).PosDef ↔ A.PosDef := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact (posSemidef_toComplexStarAlgHom_iff.1 h.posSemidef).posDef_iff_isUnit.2
      (isUnit_toComplexStarAlgHom_iff.1 h.isUnit)
  · exact (posSemidef_toComplexStarAlgHom_iff.2 h.posSemidef).posDef_iff_isUnit.2
      (isUnit_toComplexStarAlgHom_iff.2 h.isUnit)

@[simp]
theorem toComplexStarAlgHom_cfc (f : ℝ → ℝ) (A : Matrix n n 𝕜) :
    toComplexStarAlgHom n 𝕜 (cfc f A) = cfc f (toComplexStarAlgHom n 𝕜 A) := by
  by_cases hA : IsSelfAdjoint A
  · exact StarAlgHom.map_cfc (toComplexStarAlgHom n 𝕜) f A
      (A.finite_real_spectrum.continuousOn _) continuous_toComplexStarAlgHom hA
      (hA.map (toComplexStarAlgHom n 𝕜))
  · have hA' : ¬IsSelfAdjoint (toComplexStarAlgHom n 𝕜 A) := fun h ↦
      hA (isHermitian_iff_isSelfAdjoint.1 (isHermitian_toComplexStarAlgHom_iff.1 h.isHermitian))
    rw [cfc_apply_of_not_predicate A hA, cfc_apply_of_not_predicate _ hA', map_zero]

@[simp]
theorem toComplexStarAlgHom_exp (A : Matrix n n 𝕜) :
    toComplexStarAlgHom n 𝕜 (exp A) = exp (toComplexStarAlgHom n 𝕜 A) := by
  open scoped Matrix.Norms.Operator in
  let _ : NormedAlgebra ℚ (Matrix n n 𝕜) := .restrictScalars ℚ 𝕜 _
  let _ : NormedAlgebra ℚ (Matrix n n ℂ) := .restrictScalars ℚ ℂ _
  ext i j
  have h1 : HasSum (fun k : ℕ ↦ (k.factorial⁻¹ : ℚ) • (toComplexStarAlgHom n 𝕜 A ^ k) i j)
      (RCLike.toComplexStarAlgHom 𝕜 (exp A i j)) :=
    ((exp_series_hasSum_exp_apply A i j).map
      (RCLike.toComplexStarAlgHom 𝕜).toAddMonoidHom RCLike.continuous_toComplexStarAlgHom).congr
      fun s ↦ Finset.sum_congr rfl fun k _ ↦ by
        dsimp
        rw [← map_pow, Rat.smul_def, Rat.smul_def, map_mul, map_ratCast]
        rfl
  exact h1.unique (exp_series_hasSum_exp_apply (toComplexStarAlgHom n 𝕜 A) i j)

end Matrix
