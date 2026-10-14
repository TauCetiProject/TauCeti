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
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.GroupTheory.Perm.Inversion

/-!
# Paired wedges of continuous alternating maps

This file constructs the paired wedge of continuous alternating maps on real modules with a
topology. Its determinant normalization is the signed-permutation sum divided by the two input
factorials. It provides bilinearity and pullback compatibility for general topological coefficient
spaces, and the flip and associativity laws for seminormed coefficients. No norm is required on
the domain.

The paired construction follows the design of Yury Kudryashov's
[`DeRhamCohomology`](https://github.com/urkud/DeRhamCohomology) project.
-/

public section

open TensorProduct

namespace ContinuousAlternatingMap

section Topological

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
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y))
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
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y))
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂)
    (v : Fin (k + l) → E) :
    wedgeWithUnalternatedContinuous μ hμ φ ψ v =
      μ (φ (fun i ↦ v (Fin.castAdd l i))) (ψ (fun j ↦ v (Fin.natAdd k j))) := by
  exact wedgeWithUnalternated_apply μ φ ψ v

/-- The paired wedge of continuous alternating maps, normalized by the two input factorials. -/
noncomputable def pairedWedge {k l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y))
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂) :
    E [⋀^Fin (k + l)]→L[ℝ] F₃ :=
  (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
    (wedgeWithUnalternatedContinuous μ hμ φ ψ).alternatization

omit [ContinuousAdd E] [ContinuousSMul ℝ E]
  [IsTopologicalAddGroup F₁] [ContinuousSMul ℝ F₁]
  [IsTopologicalAddGroup F₂] [ContinuousSMul ℝ F₂] in
/-- The pointwise formula for the paired wedge in all degrees. -/
theorem pairedWedge_apply {k l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y))
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
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y))
    (φ : E [⋀^Fin 1]→L[ℝ] F₁) (ψ : E [⋀^Fin 1]→L[ℝ] F₂) (v w : E) :
    pairedWedge μ hμ φ ψ ![v, w] = μ (φ ![v]) (ψ ![w]) - μ (φ ![w]) (ψ ![v]) := by
  classical
  rw [pairedWedge_apply]
  rw [TauCeti.univ_perm_fin_two, Finset.sum_insert (by decide), Finset.sum_singleton,
    Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1)]
  simp [Fin.fin_one_eq_zero, Matrix.cons_fin_one, sub_eq_add_neg]

omit [ContinuousAdd E] [ContinuousSMul ℝ E]
  [IsTopologicalAddGroup F₁] [ContinuousSMul ℝ F₁]
  [IsTopologicalAddGroup F₂] [ContinuousSMul ℝ F₂] in
/-- The underlying alternating map of the paired wedge is the alternatization of its unalternated
multilinear pairing, divided by `k! l!`. -/
@[simp]
theorem pairedWedge_toAlternatingMap {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hmu : Continuous (Function.uncurry fun x y ↦ mu x y))
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    (pairedWedge mu hmu phi psi).toAlternatingMap =
      (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
        (ContinuousAlternatingMap.wedgeWithUnalternated mu phi psi).alternatization := by
  ext v
  simp only [ContinuousAlternatingMap.coe_toAlternatingMap, pairedWedge_apply,
    AlternatingMap.smul_apply, MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply, ContinuousAlternatingMap.wedgeWithUnalternated_apply]

variable {E' : Type*} [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E']
  [ContinuousAdd E'] [ContinuousSMul ℝ E']

omit [ContinuousAdd E] [ContinuousSMul ℝ E] [IsTopologicalAddGroup F₁]
  [ContinuousSMul ℝ F₁] [IsTopologicalAddGroup F₂] [ContinuousSMul ℝ F₂]
  [ContinuousAdd E'] [ContinuousSMul ℝ E'] in
/-- Precomposing both inputs of a paired wedge by a continuous linear map is the same as
precomposing the resulting wedge. -/
@[simp]
theorem pairedWedge_compContinuousLinearMap {k l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y))
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
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y))
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
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y))
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
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y)) (c : ℝ)
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
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y)) (c : ℝ)
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂) :
    pairedWedge μ hμ φ (c • ψ) = c • pairedWedge μ hμ φ ψ := by
  ext v
  simp only [pairedWedge_apply, ContinuousAlternatingMap.smul_apply, map_smul,
    Finset.smul_sum, smul_comm _ c]

end Topological

open TauCeti

section NormedCoefficients

variable {E F₁ F₂ F₃ : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [SeminormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [SeminormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [SeminormedAddCommGroup F₃] [NormedSpace ℝ F₃]

/-- Postcomposing the pairing postcomposes the paired wedge. -/
@[simp]
theorem pairedWedge_postcomp {F₄ : Type*} [SeminormedAddCommGroup F₄] [NormedSpace ℝ F₄]
    {k l : ℕ} (nu : F₃ →L[ℝ] F₄) (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    pairedWedge ((ContinuousLinearMap.compL ℝ F₂ F₃ F₄ nu).comp mu)
        ((ContinuousLinearMap.compL ℝ F₂ F₃ F₄ nu).comp mu).continuous₂ phi psi =
      nu.compContinuousAlternatingMap (pairedWedge mu mu.continuous₂ phi psi) := by
  ext v
  simp only [pairedWedge_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.compContinuousAlternatingMap_coe, Function.comp_apply, _root_.map_smul,
    _root_.map_sum]
  congr 2
  funext sigma
  exact (nu.map_smul_of_tower (Equiv.Perm.sign sigma) _).symm

/-- The paired wedge is additive in the pairing. -/
@[simp]
theorem pairedWedge_add_pairing {k l : ℕ} (mu nu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    pairedWedge (mu + nu) (mu + nu).continuous₂ phi psi =
      pairedWedge mu mu.continuous₂ phi psi + pairedWedge nu nu.continuous₂ phi psi := by
  ext v
  simp only [pairedWedge_apply, _root_.add_apply, ContinuousAlternatingMap.add_apply,
    Finset.smul_sum, smul_add]
  rw [Finset.sum_add_distrib]

/-- The paired wedge respects scalar multiplication of the pairing. -/
@[simp]
theorem pairedWedge_smul_pairing {k l : ℕ} (c : ℝ) (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    pairedWedge (c • mu) (c • mu).continuous₂ phi psi =
      c • pairedWedge mu mu.continuous₂ phi psi := by
  ext v
  simp only [pairedWedge_apply, ContinuousAlternatingMap.smul_apply, _root_.smul_apply,
    Finset.smul_sum, smul_comm _ c]

/-- Negating the pairing negates the paired wedge. -/
@[simp]
theorem pairedWedge_neg_pairing {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    pairedWedge (-mu) (-mu).continuous₂ phi psi = -pairedWedge mu mu.continuous₂ phi psi := by
  rw [← neg_one_smul ℝ mu, pairedWedge_smul_pairing]
  simp

/-- The paired wedge for the zero pairing is zero. -/
@[simp]
theorem pairedWedge_zero_pairing {k l : ℕ} (phi : E [⋀^Fin k]→L[ℝ] F₁)
    (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    pairedWedge (0 : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (0 : F₁ →L[ℝ] F₂ →L[ℝ] F₃).continuous₂ phi psi = 0 := by
  ext v
  simp only [pairedWedge_apply, _root_.zero_apply, smul_zero, Finset.sum_const_zero,
    ContinuousAlternatingMap.coe_zero, Pi.zero_apply]

/-- Wedge with the zero form on the left is zero. -/
@[simp]
theorem pairedWedge_zero_left {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (psi : E [⋀^Fin l]→L[ℝ] F₂) :
    pairedWedge mu mu.continuous₂ (0 : E [⋀^Fin k]→L[ℝ] F₁) psi = 0 := by
  simpa only [zero_smul] using
    pairedWedge_smul_left mu mu.continuous₂ (0 : ℝ) (0 : E [⋀^Fin k]→L[ℝ] F₁) psi

/-- Wedge with the zero form on the right is zero. -/
@[simp]
theorem pairedWedge_zero_right {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) :
    pairedWedge mu mu.continuous₂ phi (0 : E [⋀^Fin l]→L[ℝ] F₂) = 0 := by
  simpa only [zero_smul] using
    pairedWedge_smul_right mu mu.continuous₂ (0 : ℝ) phi (0 : E [⋀^Fin l]→L[ℝ] F₂)

/-- The flip identity: swapping the two forms of a paired wedge flips the pairing and costs the
graded sign `(-1) ^ (k * l)`. This holds for every pairing. -/
theorem pairedWedge_flip {k l : ℕ} (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) (v : Fin (k + l) → E) :
    pairedWedge mu mu.continuous₂ phi psi v =
      (-1 : ℝ) ^ (k * l) • pairedWedge mu.flip mu.flip.continuous₂ psi phi (v ∘ Fin.cast
    (Nat.add_comm l k)) := by
  -- Reindex the permutation sum on the right by composing with the block swap `B`, which
  -- exchanges the first `k` and the last `l` indices and has sign `(-1) ^ (k * l)`.
  set c : Fin (l + k) ≃ Fin (k + l) := finCongr (Nat.add_comm l k)
  set B : Equiv.Perm (Fin (k + l)) := finAddFlip.trans c
  have hsum : ∑ tau : Equiv.Perm (Fin (l + k)), Equiv.Perm.sign tau •
        mu.flip (psi (fun i => (v ∘ Fin.cast (Nat.add_comm l k)) (tau (Fin.castAdd k i))))
          (phi (fun j => (v ∘ Fin.cast (Nat.add_comm l k)) (tau (Fin.natAdd l j)))) =
      Equiv.Perm.sign B • ∑ sigma : Equiv.Perm (Fin (k + l)), Equiv.Perm.sign sigma •
        mu (phi (fun i => v (sigma (Fin.castAdd l i))))
          (psi (fun j => v (sigma (Fin.natAdd k j)))) := by
    let f : Equiv.Perm (Fin (k + l)) → F₃ := fun sigma =>
      mu (phi (fun i => v (sigma (Fin.castAdd l i))))
        (psi (fun j => v (sigma (Fin.natAdd k j))))
    calc
      _ = ∑ tau : Equiv.Perm (Fin (l + k)), Equiv.Perm.sign tau •
          f (c.permCongr tau * B) := by
        apply Finset.sum_congr rfl
        intro tau _
        have hleft : (fun i => v ((c.permCongr tau * B) (Fin.castAdd l i))) =
            fun j => v (Fin.cast (Nat.add_comm l k) (tau (Fin.natAdd l j))) := by
          funext i
          simp [B, c, finAddFlip_apply_castAdd]
        have hright : (fun j => v ((c.permCongr tau * B) (Fin.natAdd k j))) =
            fun i => v (Fin.cast (Nat.add_comm l k) (tau (Fin.castAdd k i))) := by
          funext j
          simp [B, c, finAddFlip_apply_natAdd]
        simp only [f, Function.comp_apply, ContinuousLinearMap.flip_apply]
        rw [← hright, ← hleft]
      _ = _ := sum_sign_smul_permCongr_mul c B f
  rw [pairedWedge_apply, pairedWedge_apply, hsum, sign_finAddFlip_trans_finCongr]
  generalize (∑ sigma : Equiv.Perm (Fin (k + l)), (_ : F₃)) = S
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ]
  match_scalars
  ring_nf
  simp

/-- Anticommutation of a paired wedge along a skew-symmetric pairing. -/
theorem pairedWedge_anticomm {k l : ℕ} {mu : F₁ →L[ℝ] F₁ →L[ℝ] F₃}
    (hmu : ∀ a b, mu a b = -mu b a)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₁)
    (v : Fin (k + l) → E) :
    pairedWedge mu mu.continuous₂ phi psi v =
      -((-1 : ℝ) ^ (k * l) • pairedWedge mu mu.continuous₂ psi phi (v ∘ Fin.cast (Nat.add_comm l
    k))) := by
  have hflip : mu.flip = -mu := by
    ext a b
    simpa only [ContinuousLinearMap.flip_apply, _root_.neg_apply] using hmu b a
  rw [pairedWedge_flip, hflip, pairedWedge_neg_pairing]
  simp [smul_neg]

/-- Graded commutativity of the paired wedge along a symmetric pairing. -/
theorem pairedWedge_comm {k l : ℕ} {mu : F₁ →L[ℝ] F₁ →L[ℝ] F₃} (hmu : ∀ a b, mu a b = mu b a)
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₁) (v : Fin (k + l) → E) :
    pairedWedge mu mu.continuous₂ phi psi v =
      (-1 : ℝ) ^ (k * l) • pairedWedge mu mu.continuous₂ psi phi (v ∘ Fin.cast (Nat.add_comm l k))
    := by
  have hflip : mu.flip = mu := by
    ext a b
    exact hmu b a
  rw [pairedWedge_flip, hflip]

end NormedCoefficients

section Assoc

open Equiv

variable {E F₁ F₂ F₃ F₁₂ F₂₃ G : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [SeminormedAddCommGroup F₁] [NormedSpace ℝ F₁] [SeminormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [SeminormedAddCommGroup F₃] [NormedSpace ℝ F₃] [SeminormedAddCommGroup F₁₂] [NormedSpace ℝ F₁₂]
  [SeminormedAddCommGroup F₂₃] [NormedSpace ℝ F₂₃] [SeminormedAddCommGroup G] [NormedSpace ℝ G]
  {k l m : ℕ}

/-- A paired wedge whose left factor is itself a paired wedge is the signed sum over all
permutations of `k + l + m` slots, divided by `k! l! m!`. -/
theorem pairedWedge_pairedWedge_left_apply (mu₁₂ : F₁ →L[ℝ] F₂ →L[ℝ] F₁₂)
    (mu₁₂₃ : F₁₂ →L[ℝ] F₃ →L[ℝ] G) (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂)
    (chi : E [⋀^Fin m]→L[ℝ] F₃) (v : Fin (k + l + m) → E) :
    pairedWedge mu₁₂₃ mu₁₂₃.continuous₂ (pairedWedge mu₁₂ mu₁₂.continuous₂ phi psi) chi v =
      ((k.factorial : ℝ) * l.factorial * m.factorial)⁻¹ •
        ∑ sigma : Perm (Fin (k + l + m)), Perm.sign sigma •
          mu₁₂₃ (mu₁₂ (phi fun i => v (sigma (Fin.castAdd m (Fin.castAdd l i))))
              (psi fun j => v (sigma (Fin.castAdd m (Fin.natAdd k j)))))
            (chi fun r => v (sigma (Fin.natAdd (k + l) r))) := by
  have key := sum_sign_smul_sum_sign_smul_eq_card_nsmul
    (fun tau => finSumFinEquiv.permCongr (Perm.sumCongr tau (1 : Perm (Fin m))))
    (fun tau => by simp [Perm.sign_sumCongr])
    (fun sigma : Perm (Fin (k + l + m)) =>
      mu₁₂₃ (mu₁₂ (phi fun i => v (sigma (Fin.castAdd m (Fin.castAdd l i))))
          (psi fun j => v (sigma (Fin.castAdd m (Fin.natAdd k j)))))
        (chi fun r => v (sigma (Fin.natAdd (k + l) r))))
  simp only [Perm.mul_apply, permCongr_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, Perm.sumCongr_apply, Sum.map_inl, Sum.map_inr,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Perm.coe_one, id,
    Fintype.card_perm, Fintype.card_fin] at key
  simp only [pairedWedge_apply, _root_.map_smul, _root_.map_sum, _root_.smul_apply,
    FunLike.coe_sum, Finset.sum_apply,
    Units.smul_def, _root_.map_zsmul] at key ⊢
  simp_rw [smul_comm _ ((k.factorial : ℝ) * l.factorial)⁻¹, ← Finset.smul_sum, key, smul_smul,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  have : ((k + l).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- A paired wedge whose right factor is itself a paired wedge is the signed sum over all
permutations of `k + (l + m)` slots, divided by `k! l! m!`. -/
theorem pairedWedge_pairedWedge_right_apply (mu₂₃ : F₂ →L[ℝ] F₃ →L[ℝ] F₂₃)
    (mu₁₂₃' : F₁ →L[ℝ] F₂₃ →L[ℝ] G) (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂)
    (chi : E [⋀^Fin m]→L[ℝ] F₃) (v : Fin (k + (l + m)) → E) :
    pairedWedge mu₁₂₃' mu₁₂₃'.continuous₂ phi (pairedWedge mu₂₃ mu₂₃.continuous₂ psi chi) v =
      ((k.factorial : ℝ) * l.factorial * m.factorial)⁻¹ •
        ∑ sigma : Perm (Fin (k + (l + m))), Perm.sign sigma •
          mu₁₂₃' (phi fun i => v (sigma (Fin.castAdd (l + m) i)))
            (mu₂₃ (psi fun j => v (sigma (Fin.natAdd k (Fin.castAdd m j))))
              (chi fun r => v (sigma (Fin.natAdd k (Fin.natAdd l r))))) := by
  have key := sum_sign_smul_sum_sign_smul_eq_card_nsmul
    (fun tau => finSumFinEquiv.permCongr (Perm.sumCongr (1 : Perm (Fin k)) tau))
    (fun tau => by simp [Perm.sign_sumCongr])
    (fun sigma : Perm (Fin (k + (l + m))) =>
      mu₁₂₃' (phi fun i => v (sigma (Fin.castAdd (l + m) i)))
        (mu₂₃ (psi fun j => v (sigma (Fin.natAdd k (Fin.castAdd m j))))
          (chi fun r => v (sigma (Fin.natAdd k (Fin.natAdd l r))))))
  simp only [Perm.mul_apply, permCongr_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, Perm.sumCongr_apply, Sum.map_inl, Sum.map_inr,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Perm.coe_one, id,
    Fintype.card_perm, Fintype.card_fin] at key
  simp only [pairedWedge_apply, _root_.map_smul, _root_.map_sum, Units.smul_def, _root_.map_zsmul]
    at key ⊢
  simp_rw [smul_comm _ ((l.factorial : ℝ) * m.factorial)⁻¹, ← Finset.smul_sum, key, smul_smul,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  have : ((l + m).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- Associativity of the paired wedge, for pairings whose two composites agree:
`mu₁₂₃ (mu₁₂ a b) c = mu₁₂₃' a (mu₂₃ b c)`. For the multiplication of a normed algebra this
hypothesis is `mul_assoc`; for a Lie bracket it does not hold in general. -/
theorem pairedWedge_assoc (mu₁₂ : F₁ →L[ℝ] F₂ →L[ℝ] F₁₂) (mu₁₂₃ : F₁₂ →L[ℝ] F₃ →L[ℝ] G)
    (mu₂₃ : F₂ →L[ℝ] F₃ →L[ℝ] F₂₃) (mu₁₂₃' : F₁ →L[ℝ] F₂₃ →L[ℝ] G)
    (h : ∀ a b c, mu₁₂₃ (mu₁₂ a b) c = mu₁₂₃' a (mu₂₃ b c))
    (phi : E [⋀^Fin k]→L[ℝ] F₁) (psi : E [⋀^Fin l]→L[ℝ] F₂) (chi : E [⋀^Fin m]→L[ℝ] F₃)
    (v : Fin (k + l + m) → E) :
    pairedWedge mu₁₂₃ mu₁₂₃.continuous₂ (pairedWedge mu₁₂ mu₁₂.continuous₂ phi psi) chi v =
      pairedWedge mu₁₂₃' mu₁₂₃'.continuous₂ phi (pairedWedge mu₂₃ mu₂₃.continuous₂ psi chi) (v ∘
    Fin.cast (Nat.add_assoc k l m).symm) := by
  rw [pairedWedge_pairedWedge_left_apply, pairedWedge_pairedWedge_right_apply]
  congr 1
  refine Fintype.sum_equiv (finCongr (Nat.add_assoc k l m)).permCongr _ _ fun sigma => ?_
  have h₁ (i : Fin k) : Fin.cast (Nat.add_assoc k l m).symm (Fin.castAdd (l + m) i) =
      Fin.castAdd m (Fin.castAdd l i) := Fin.ext rfl
  have h₂ (j : Fin l) : Fin.cast (Nat.add_assoc k l m).symm (Fin.natAdd k (Fin.castAdd m j)) =
      Fin.castAdd m (Fin.natAdd k j) := Fin.ext rfl
  have h₃ (r : Fin m) : Fin.cast (Nat.add_assoc k l m).symm (Fin.natAdd k (Fin.natAdd l r)) =
      Fin.natAdd (k + l) r := Fin.ext (Nat.add_assoc k l r).symm
  simp [h, h₁, h₂, h₃, Perm.sign_permCongr]

end Assoc

end ContinuousAlternatingMap
