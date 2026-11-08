/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Operator convergence from inner-product entries in finite dimension

For operators from a finite-dimensional real normed space to a finite-dimensional real
inner-product space, convergence of every inner-product entry implies convergence in operator
norm. The proof passes through Mathlib's weak operator topology; its linear equivalence with
continuous linear maps is continuous because the operator space is finite-dimensional.
-/

public noncomputable section

open Filter
open scoped InnerProductSpace Topology

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- In finite dimension, convergence of inner-product entries gives operator-norm convergence. -/
theorem tendsto_of_forall_inner_apply_tendsto {α : Type*} {l : Filter α}
    {A : α → E →L[ℝ] F} {B : E →L[ℝ] F}
    (h : ∀ x y, Tendsto (fun a ↦ ⟪y, A a x⟫_ℝ) l (𝓝 ⟪y, B x⟫_ℝ)) :
    Tendsto A l (𝓝 B) := by
  have : FiniteDimensional ℝ (E →WOT[ℝ] F) :=
    FiniteDimensional.of_injective (ContinuousLinearMapWOT.linearEquiv ℝ).toLinearMap
      (ContinuousLinearMapWOT.linearEquiv ℝ).injective
  let e : (E →WOT[ℝ] F) ≃ₗ[ℝ] (E →L[ℝ] F) := ContinuousLinearMapWOT.linearEquiv ℝ
  have hc : Continuous (ContinuousLinearMapWOT.toCLM (σ := RingHom.id ℝ) :
      (E →WOT[ℝ] F) → E →L[ℝ] F) := by
    convert e.toLinearMap.continuous_of_finiteDimensional using 1
    funext T
    exact (ContinuousLinearMapWOT.linearEquiv_apply ℝ T).symm
  have hw : Tendsto (fun a ↦ ContinuousLinearMapWOT.ofCLM (A a)) l
      (𝓝 (ContinuousLinearMapWOT.ofCLM B)) :=
    ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr h
  exact hc.continuousAt.tendsto.comp hw

/-- Inner-product entry derivatives determine finite-dimensional operator-norm derivatives. -/
theorem hasDerivAt_of_forall_inner_apply_hasDerivAt {A : ℝ → E →L[ℝ] F}
    {B : E →L[ℝ] F} {t : ℝ}
    (h : ∀ x y, HasDerivAt (fun u ↦ ⟪y, A u x⟫_ℝ) ⟪y, B x⟫_ℝ t) :
    HasDerivAt A B t := by
  rw [hasDerivAt_iff_tendsto_slope]
  apply tendsto_of_forall_inner_apply_tendsto
  intro x y
  have heq : (fun u ↦ ⟪y, slope A t u x⟫_ℝ) = slope (fun u ↦ ⟪y, A u x⟫_ℝ) t := by
    funext u
    simp only [slope_def_module, smul_apply, sub_apply, real_inner_smul_right,
      inner_sub_right, smul_eq_mul]
  rw [heq]
  exact (h x y).tendsto_slope

end ContinuousLinearMap
