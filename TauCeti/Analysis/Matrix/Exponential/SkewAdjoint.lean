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
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Calculus.FDeriv.Unitary

/-!
# The unitary exponential of strict upper coordinates

The exponential of the zero-diagonal skew-adjoint extension of strict upper coordinates is a
unitary matrix. This parametrizes the unitary frames transverse to the diagonal unitary
subgroup near the identity. The underlying matrix is smooth in the coordinates, and its
derivative at zero is the skew-adjoint extension itself.

The relative frame `TauCeti.relativeFrame a b` is the frame at angle `b` seen from the frame at
the base angle `a`. It is smooth in `b`, and its derivative at `b = a` is skew-adjoint. The
angular differential `TauCeti.spectralAngularFDeriv` differentiates the strict upper entries of
the relative frame at the base angle. At zero angle it is the identity.

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
def expStrictUpper (x : FinStrictUpper n → 𝕜) : unitaryGroup (Fin n) 𝕜 :=
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) 𝕜) := .restrictScalars ℚ 𝕜 _
  ⟨NormedSpace.exp (skewAdjointOfStrictUpper x),
    NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjointOfStrictUpper_mem x)⟩

/-- The matrix underlying the transverse unitary exponential. -/
theorem coe_expStrictUpper (x : FinStrictUpper n → 𝕜) :
    (expStrictUpper x : Matrix (Fin n) (Fin n) 𝕜) = NormedSpace.exp (skewAdjointOfStrictUpper x) :=
  (rfl)

/-- Zero angles give the identity frame. -/
@[simp] theorem expStrictUpper_zero : expStrictUpper (0 : FinStrictUpper n → 𝕜) = 1 := by
  apply Subtype.ext
  simp [coe_expStrictUpper]

/-- The unitary frame at angle `b` relative to the frame at the base angle `a`. -/
def relativeFrame (a b : FinStrictUpper n → 𝕜) : unitaryGroup (Fin n) 𝕜 :=
  star (expStrictUpper a) * expStrictUpper b

/-- A frame relative to itself is the identity. -/
@[simp] theorem relativeFrame_self (a : FinStrictUpper n → 𝕜) : relativeFrame a a = 1 := by
  simp [relativeFrame]

/-- The matrix underlying the relative frame. -/
theorem coe_relativeFrame (a b : FinStrictUpper n → 𝕜) :
    (relativeFrame a b : Matrix (Fin n) (Fin n) 𝕜) =
      star (expStrictUpper a : Matrix (Fin n) (Fin n) 𝕜) *
        (expStrictUpper b : Matrix (Fin n) (Fin n) 𝕜) := (rfl)

/-- The base frame followed by the relative frame is the frame at the target angle. -/
theorem expStrictUpper_mul_relativeFrame (a b : FinStrictUpper n → 𝕜) :
    expStrictUpper a * relativeFrame a b = expStrictUpper b := by
  simp [relativeFrame, ← mul_assoc]

/-- The differential of the angular coordinates in the moving unitary frame.
The differential is taken at the base angle, where the relative frame is the identity. -/
def spectralAngularFDeriv (a : FinStrictUpper n → 𝕜) :
    (FinStrictUpper n → 𝕜) →L[ℝ] (FinStrictUpper n → 𝕜) :=
  fderiv ℝ (fun b ij ↦ (relativeFrame a b : Matrix (Fin n) (Fin n) 𝕜) ij.val.1 ij.val.2) a

/-- The angular differential is the derivative of the strict upper entries of the unitary
frame relative to the frame at the base angle. -/
theorem spectralAngularFDeriv_def (a : FinStrictUpper n → 𝕜) :
    spectralAngularFDeriv a =
      fderiv ℝ (fun b ij ↦ (relativeFrame a b : Matrix (Fin n) (Fin n) 𝕜) ij.val.1 ij.val.2) a :=
  (rfl)

section Differentiation

open scoped Matrix.Norms.L2Operator

attribute [local instance] Matrix.l2OpNormedAlgebraReal

/-- The underlying matrix of the transverse unitary exponential is smooth in the angles. -/
theorem contDiff_expStrictUpper {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun a : FinStrictUpper n → 𝕜 ↦
      (expStrictUpper a : Matrix (Fin n) (Fin n) 𝕜)) := by
  simp only [coe_expStrictUpper]
  have he : ContDiff ℝ k (NormedSpace.exp : Matrix (Fin n) (Fin n) 𝕜 → _) :=
    contDiff_iff_contDiffAt.mpr fun z ↦ (NormedSpace.exp_analytic (𝕂 := ℝ) z).contDiffAt
  exact he.comp (skewAdjointOfStrictUpper (n := n) (E := 𝕜)).contDiff

/-- At zero, the derivative of the underlying matrix is the skew-adjoint extension of the
strict upper coordinates. -/
theorem hasFDerivAt_expStrictUpper_zero :
    HasFDerivAt (fun a : FinStrictUpper n → 𝕜 ↦
      (expStrictUpper a : Matrix (Fin n) (Fin n) 𝕜)) skewAdjointOfStrictUpper 0 := by
  let K := skewAdjointOfStrictUpper (n := n) (E := 𝕜)
  have h : HasFDerivAt NormedSpace.exp (ContinuousLinearMap.id ℝ (Matrix (Fin n) (Fin n) 𝕜))
      (K 0) := by
    simpa only [K, map_zero, ContinuousLinearMap.one_def] using
      (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Matrix (Fin n) (Fin n) 𝕜))
  have hh := h.comp (0 : FinStrictUpper n → 𝕜) K.hasFDerivAt
  rw [ContinuousLinearMap.id_comp] at hh
  exact hh.congr_of_eventuallyEq (Filter.Eventually.of_forall coe_expStrictUpper)

/-- The underlying matrix of the relative frame is smooth in the target angle. -/
theorem contDiff_relativeFrame (a : FinStrictUpper n → 𝕜) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun b ↦ (relativeFrame a b : Matrix (Fin n) (Fin n) 𝕜)) := by
  simp only [coe_relativeFrame]
  exact contDiff_const.mul contDiff_expStrictUpper

/-- At the base angle, the derivative of the relative frame is skew-adjoint. -/
theorem star_fderiv_relativeFrame (a v : FinStrictUpper n → 𝕜) :
    star (fderiv ℝ (fun b ↦ (relativeFrame a b : Matrix (Fin n) (Fin n) 𝕜)) a v) =
      -(fderiv ℝ (fun b ↦ (relativeFrame a b : Matrix (Fin n) (Fin n) 𝕜)) a v) :=
  star_fderiv_apply_eq_neg_of_mem_unitary
    (Filter.Eventually.of_forall fun b ↦ (relativeFrame a b).property)
    (by rw [relativeFrame_self, Submonoid.coe_one]) v

/-- Each entry of the angular differential is the derivative of the corresponding strict upper
entry of the frame relative to the frame at the base angle. -/
theorem spectralAngularFDeriv_apply (a v : FinStrictUpper n → 𝕜) (ij : FinStrictUpper n) :
    spectralAngularFDeriv a v ij =
      fderiv ℝ (fun b ↦ (relativeFrame a b : Matrix (Fin n) (Fin n) 𝕜)) a v
        ij.val.1 ij.val.2 := by
  let read : Matrix (Fin n) (Fin n) 𝕜 →L[ℝ] (FinStrictUpper n → 𝕜) :=
    (LinearMap.pi fun ij : FinStrictUpper n ↦
      Matrix.entryLinearMap ℝ 𝕜 ij.val.1 ij.val.2).toContinuousLinearMap
  have hF := ((contDiff_relativeFrame a (k := 1)).differentiable one_ne_zero a).hasFDerivAt
  have he : spectralAngularFDeriv a = read.comp (fderiv ℝ (fun b ↦
      (relativeFrame a b : Matrix (Fin n) (Fin n) 𝕜)) a) := by
    rw [spectralAngularFDeriv_def]
    exact (read.hasFDerivAt.comp a hF).fderiv
  rw [he, ContinuousLinearMap.comp_apply]
  simp only [read, LinearMap.coe_toContinuousLinearMap', LinearMap.pi_apply, entryLinearMap_apply]

/-- At zero angle, the angular differential is the identity. -/
@[simp] theorem spectralAngularFDeriv_zero :
    spectralAngularFDeriv (0 : FinStrictUpper n → 𝕜) = ContinuousLinearMap.id ℝ _ := by
  refine ContinuousLinearMap.ext fun v ↦ funext fun ij ↦ ?_
  have h : (fun b ↦ (relativeFrame (0 : FinStrictUpper n → 𝕜) b : Matrix (Fin n) (Fin n) 𝕜)) =
      fun b ↦ (expStrictUpper b : Matrix (Fin n) (Fin n) 𝕜) :=
    funext fun b ↦ by simp [relativeFrame]
  rw [spectralAngularFDeriv_apply, h, hasFDerivAt_expStrictUpper_zero.fderiv,
    skewAdjointOfStrictUpper_apply_of_lt _ ij.property, ContinuousLinearMap.id_apply]

end Differentiation

end TauCeti
