/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Alternating.Basic
public import Mathlib.LinearAlgebra.Alternating.DomCoprod
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.UniformSpace.Real
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import TauCeti.Data.Fin.Basic

/-!
# Paired wedges of continuous alternating maps

This file provides the unalternated pairing used to construct paired wedges on topological real
vector spaces. It requires no norm on the domain.
-/

public section

open TensorProduct

namespace ContinuousAlternatingMap

variable {E F₁ F₂ F₃ : Type*}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
  [AddCommGroup F₁] [Module ℝ F₁] [TopologicalSpace F₁]
  [IsTopologicalAddGroup F₁] [ContinuousSMul ℝ F₁]
  [AddCommGroup F₂] [Module ℝ F₂] [TopologicalSpace F₂]
  [IsTopologicalAddGroup F₂] [ContinuousSMul ℝ F₂]
  [AddCommGroup F₃] [Module ℝ F₃] [TopologicalSpace F₃]
  [IsTopologicalAddGroup F₃] [ContinuousSMul ℝ F₃]

/-- The linear map induced by a continuous bilinear pairing on the tensor product. -/
noncomputable def pairingLinear (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) :
    F₁ ⊗[ℝ] F₂ →ₗ[ℝ] F₃ :=
  TensorProduct.lift ((ContinuousLinearMap.coeLM ℝ).comp μ.toLinearMap)

omit [IsTopologicalAddGroup F₁] [ContinuousSMul ℝ F₁]
  [IsTopologicalAddGroup F₂] [ContinuousSMul ℝ F₂] in
/-- The pairing-induced linear map evaluates pure tensors by the original pairing. -/
@[simp]
theorem pairingLinear_tmul (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (x : F₁) (y : F₂) :
    pairingLinear μ (x ⊗ₜ[ℝ] y) = μ x y := by
  simp [pairingLinear]

/-- The unalternated multilinear pairing underlying the paired wedge. -/
noncomputable def wedgeWithUnalternated {k l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂) :
    MultilinearMap ℝ (fun _ : Fin (k + l) => E) F₃ :=
  (pairingLinear μ).compMultilinearMap <|
    (MultilinearMap.domCoprod φ.toAlternatingMap.toMultilinearMap
      ψ.toAlternatingMap.toMultilinearMap).domDomCongr finSumFinEquiv

omit [ContinuousAdd E] [ContinuousSMul ℝ E]
  [IsTopologicalAddGroup F₁] [ContinuousSMul ℝ F₁]
  [IsTopologicalAddGroup F₂] [ContinuousSMul ℝ F₂] in
/-- The tensor-product construction of the unalternated paired wedge. -/
theorem wedgeWithUnalternated_def {k l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂) :
    wedgeWithUnalternated μ φ ψ =
      (pairingLinear μ).compMultilinearMap
        ((MultilinearMap.domCoprod φ.toAlternatingMap.toMultilinearMap
          ψ.toAlternatingMap.toMultilinearMap).domDomCongr finSumFinEquiv) := (rfl)

omit [IsTopologicalAddGroup F₁] [ContinuousSMul ℝ F₁]
  [IsTopologicalAddGroup F₂] [ContinuousSMul ℝ F₂]
  [ContinuousAdd E] [ContinuousSMul ℝ E] in
/-- Evaluation of the unalternated pairing on concatenated vectors. -/
@[simp]
theorem wedgeWithUnalternated_apply {k l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂)
    (v : Fin (k + l) → E) :
    wedgeWithUnalternated μ φ ψ v =
      μ (φ (fun i => v (Fin.castAdd l i))) (ψ (fun j => v (Fin.natAdd k j))) := by
  simp [wedgeWithUnalternated, pairingLinear]

/-- The continuous multilinear map associated to the unalternated paired product. -/
noncomputable def wedgeWithUnalternatedContinuous {k l : ℕ}
    (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (fun p : F₁ × F₂ ↦ μ p.1 p.2))
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (k + l) => E) F₃ :=
  { toMultilinearMap := wedgeWithUnalternated μ φ ψ
    cont := by
      have hfun : (wedgeWithUnalternated μ φ ψ).toFun =
          (fun v ↦ μ (φ (fun i ↦ v (Fin.castAdd l i)))
            (ψ (fun j ↦ v (Fin.natAdd k j)))) :=
        funext (wedgeWithUnalternated_apply μ φ ψ)
      rw [hfun]
      fun_prop }

omit [ContinuousAdd E] [ContinuousSMul ℝ E]
  [IsTopologicalAddGroup F₁] [ContinuousSMul ℝ F₁]
  [IsTopologicalAddGroup F₂] [ContinuousSMul ℝ F₂] in
/-- Evaluation of the continuous unalternated pairing on concatenated vectors. -/
theorem wedgeWithUnalternatedContinuous_apply {k l : ℕ}
    (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (fun p : F₁ × F₂ ↦ μ p.1 p.2))
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂)
    (v : Fin (k + l) → E) :
    wedgeWithUnalternatedContinuous μ hμ φ ψ v =
      μ (φ (fun i ↦ v (Fin.castAdd l i))) (ψ (fun j ↦ v (Fin.natAdd k j))) := by
  exact wedgeWithUnalternated_apply μ φ ψ v

/-- The paired wedge of continuous alternating maps, normalized by the two input factorials. -/
noncomputable def pairedWedge {k l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (fun p : F₁ × F₂ ↦ μ p.1 p.2))
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂) :
    E [⋀^Fin (k + l)]→L[ℝ] F₃ :=
  (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
    (wedgeWithUnalternatedContinuous μ hμ φ ψ).alternatization

omit [ContinuousAdd E] [ContinuousSMul ℝ E]
  [IsTopologicalAddGroup F₁] [ContinuousSMul ℝ F₁]
  [IsTopologicalAddGroup F₂] [ContinuousSMul ℝ F₂] in
/-- The pointwise formula for the paired wedge in all degrees. -/
theorem pairedWedge_apply {k l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (fun p : F₁ × F₂ ↦ μ p.1 p.2))
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂)
    (v : Fin (k + l) → E) :
    pairedWedge μ hμ φ ψ v =
      (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
        ∑ σ : Equiv.Perm (Fin (k + l)), Equiv.Perm.sign σ •
          μ (φ (fun i ↦ v (σ (Fin.castAdd l i))))
            (ψ (fun j ↦ v (σ (Fin.natAdd k j)))) := by
  simp only [pairedWedge, ContinuousAlternatingMap.smul_apply,
    ContinuousMultilinearMap.alternatization_apply_apply,
    wedgeWithUnalternatedContinuous_apply]
  simp only [Function.comp_apply]

omit [ContinuousAdd E] [ContinuousSMul ℝ E]
  [IsTopologicalAddGroup F₁] [ContinuousSMul ℝ F₁]
  [IsTopologicalAddGroup F₂] [ContinuousSMul ℝ F₂] in
/-- On one-forms, the paired wedge is the usual two-term alternating product. -/
theorem pairedWedge_apply_one_one {μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃}
    (hμ : Continuous (fun p : F₁ × F₂ ↦ μ p.1 p.2))
    (φ : E [⋀^Fin 1]→L[ℝ] F₁) (ψ : E [⋀^Fin 1]→L[ℝ] F₂) (v w : E) :
    pairedWedge μ hμ φ ψ ![v, w] = μ (φ ![v]) (ψ ![w]) - μ (φ ![w]) (ψ ![v]) := by
  classical
  rw [pairedWedge_apply]
  rw [TauCeti.univ_perm_fin_two, Finset.sum_insert (by decide), Finset.sum_singleton,
    Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1)]
  simp [Fin.fin_one_eq_zero, Matrix.cons_fin_one, sub_eq_add_neg]

variable {E' : Type*} [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E']
  [ContinuousAdd E'] [ContinuousSMul ℝ E']

omit [ContinuousAdd E] [ContinuousSMul ℝ E] [IsTopologicalAddGroup F₁]
  [ContinuousSMul ℝ F₁] [IsTopologicalAddGroup F₂] [ContinuousSMul ℝ F₂]
  [ContinuousAdd E'] [ContinuousSMul ℝ E'] in
/-- Precomposing both inputs of a paired wedge by a continuous linear map is the same as
precomposing the resulting wedge. -/
@[simp]
theorem pairedWedge_compContinuousLinearMap {k l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (fun p : F₁ × F₂ ↦ μ p.1 p.2))
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂)
    (f : E' →L[ℝ] E) :
    (pairedWedge μ hμ φ ψ).compContinuousLinearMap f =
      pairedWedge μ hμ (φ.compContinuousLinearMap f) (ψ.compContinuousLinearMap f) := by
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, pairedWedge_apply]
  rfl

omit [ContinuousAdd E] [ContinuousSMul ℝ E] [ContinuousSMul ℝ F₁]
  [IsTopologicalAddGroup F₂] [ContinuousSMul ℝ F₂] in
/-- The paired wedge is additive in its first alternating map. -/
@[simp]
theorem pairedWedge_add_left {k l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (fun p : F₁ × F₂ ↦ μ p.1 p.2))
    (φ φ' : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂) :
    pairedWedge μ hμ (φ + φ') ψ = pairedWedge μ hμ φ ψ + pairedWedge μ hμ φ' ψ := by
  ext v
  simp only [pairedWedge_apply, ContinuousAlternatingMap.add_apply, map_add, _root_.add_apply,
    smul_add, Finset.sum_add_distrib]

omit [ContinuousAdd E] [ContinuousSMul ℝ E]
  [IsTopologicalAddGroup F₁] [ContinuousSMul ℝ F₁] [ContinuousSMul ℝ F₂] in
/-- The paired wedge is additive in its second alternating map. -/
@[simp]
theorem pairedWedge_add_right {k l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (fun p : F₁ × F₂ ↦ μ p.1 p.2))
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ ψ' : E [⋀^Fin l]→L[ℝ] F₂) :
    pairedWedge μ hμ φ (ψ + ψ') = pairedWedge μ hμ φ ψ + pairedWedge μ hμ φ ψ' := by
  ext v
  simp only [pairedWedge_apply, ContinuousAlternatingMap.add_apply, map_add,
    smul_add, Finset.sum_add_distrib]

omit [ContinuousAdd E] [ContinuousSMul ℝ E]
  [IsTopologicalAddGroup F₁] [IsTopologicalAddGroup F₂] [ContinuousSMul ℝ F₂] in
/-- The paired wedge respects scalar multiplication in its first alternating map. -/
@[simp]
theorem pairedWedge_smul_left {k l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (fun p : F₁ × F₂ ↦ μ p.1 p.2)) (c : ℝ)
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂) :
    pairedWedge μ hμ (c • φ) ψ = c • pairedWedge μ hμ φ ψ := by
  ext v
  simp only [pairedWedge_apply, ContinuousAlternatingMap.smul_apply, map_smul,
    _root_.smul_apply, Finset.smul_sum, smul_comm _ c]

omit [ContinuousAdd E] [ContinuousSMul ℝ E]
  [IsTopologicalAddGroup F₁] [ContinuousSMul ℝ F₁] [IsTopologicalAddGroup F₂] in
/-- The paired wedge respects scalar multiplication in its second alternating map. -/
@[simp]
theorem pairedWedge_smul_right {k l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (fun p : F₁ × F₂ ↦ μ p.1 p.2)) (c : ℝ)
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂) :
    pairedWedge μ hμ φ (c • ψ) = c • pairedWedge μ hμ φ ψ := by
  ext v
  simp only [pairedWedge_apply, ContinuousAlternatingMap.smul_apply, map_smul,
    Finset.smul_sum, smul_comm _ c]

end ContinuousAlternatingMap
