/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import TauCeti.Analysis.Matrix.L2OpNorm
public import TauCeti.Analysis.Matrix.SkewAdjoint
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# The unitary exponential of strict upper coordinates

The exponential of the zero-diagonal skew-adjoint extension of strict upper coordinates is a
unitary matrix. This parametrizes the unitary frames transverse to the diagonal unitary
subgroup near the identity. The underlying matrix is smooth in the coordinates, and its
derivative at zero is the skew-adjoint extension itself.

These are the angular coordinates of the spectral change of variables in Anderson, Guionnet
and Zeitouni, *An Introduction to Random Matrices* (2010), proof of Theorem 2.5.2 and §4.1.
-/

public section

noncomputable section

namespace TauCeti

open Matrix

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

open scoped Matrix.Norms.L2Operator in
/-- The unitary exponential of a zero-diagonal skew-adjoint matrix. -/
def expStrictUpper (x : StrictUpperFin n → 𝕜) : unitaryGroup (Fin n) 𝕜 :=
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) 𝕜) := .restrictScalars ℚ 𝕜 _
  ⟨NormedSpace.exp (skewAdjointOfStrictUpper x),
    NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjointOfStrictUpper_mem x)⟩

/-- The matrix underlying the transverse unitary exponential. -/
theorem coe_expStrictUpper (x : StrictUpperFin n → 𝕜) :
    (expStrictUpper x : Matrix (Fin n) (Fin n) 𝕜) = NormedSpace.exp (skewAdjointOfStrictUpper x) :=
  (rfl)

/-- Zero angles give the identity frame. -/
@[simp] theorem expStrictUpper_zero : expStrictUpper (0 : StrictUpperFin n → 𝕜) = 1 := by
  apply Subtype.ext
  simp [coe_expStrictUpper]

section Differentiation

open scoped Matrix.Norms.L2Operator

attribute [local instance] Matrix.l2OpNormedAlgebraReal

/-- The underlying matrix of the transverse unitary exponential is smooth in the angles. -/
theorem contDiff_expStrictUpper {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun a : StrictUpperFin n → 𝕜 ↦
      (expStrictUpper a : Matrix (Fin n) (Fin n) 𝕜)) := by
  simp only [coe_expStrictUpper]
  have he : ContDiff ℝ k (NormedSpace.exp : Matrix (Fin n) (Fin n) 𝕜 → _) :=
    contDiff_iff_contDiffAt.mpr fun z ↦ (NormedSpace.exp_analytic (𝕂 := ℝ) z).contDiffAt
  exact he.comp (skewAdjointOfStrictUpper (n := n) (𝕜 := 𝕜)).contDiff

/-- At zero, the derivative of the underlying matrix is the skew-adjoint extension of the
strict upper coordinates. -/
theorem hasFDerivAt_expStrictUpper_zero :
    HasFDerivAt (fun a : StrictUpperFin n → 𝕜 ↦
      (expStrictUpper a : Matrix (Fin n) (Fin n) 𝕜)) skewAdjointOfStrictUpper 0 := by
  let K := skewAdjointOfStrictUpper (n := n) (𝕜 := 𝕜)
  have h : HasFDerivAt NormedSpace.exp (ContinuousLinearMap.id ℝ (Matrix (Fin n) (Fin n) 𝕜))
      (K 0) := by
    simpa only [K, map_zero, ContinuousLinearMap.one_def] using
      (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Matrix (Fin n) (Fin n) 𝕜))
  have hh := h.comp (0 : StrictUpperFin n → 𝕜) K.hasFDerivAt
  rw [ContinuousLinearMap.id_comp] at hh
  exact hh.congr_of_eventuallyEq (Filter.Eventually.of_forall coe_expStrictUpper)

end Differentiation

end TauCeti
