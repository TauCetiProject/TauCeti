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
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.GroupTheory.Perm.Inversion

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

section TopologicalFlip

variable {X G₁ G₂ G₃ : Type*}
  [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [AddCommGroup G₁] [Module ℝ G₁] [TopologicalSpace G₁]
  [IsTopologicalAddGroup G₁] [ContinuousSMul ℝ G₁]
  [AddCommGroup G₂] [Module ℝ G₂] [TopologicalSpace G₂]
  [IsTopologicalAddGroup G₂] [ContinuousSMul ℝ G₂]
  [AddCommGroup G₃] [Module ℝ G₃] [TopologicalSpace G₃]
  [IsTopologicalAddGroup G₃] [ContinuousSMul ℝ G₃]

/-- The flipped continuous pairing obtained from a jointly continuous pairing.

The continuity hypothesis is needed because, outside the normed setting, joint continuity gives
the required continuity of the curried map through the topology of bounded convergence. -/
noncomputable def pairingFlip (μ : G₁ →L[ℝ] G₂ →L[ℝ] G₃)
    (hμ : Continuous (fun p : G₁ × G₂ ↦ μ p.1 p.2)) : G₂ →L[ℝ] G₁ →L[ℝ] G₃ :=
  let μ' : G₂ →ₗ[ℝ] G₁ →L[ℝ] G₃ :=
    { toFun := fun y =>
        ContinuousLinearMap.mk
          { toFun := fun x => μ x y
            map_add' := fun x z => by simp
            map_smul' := fun c x => by simp } <|
          hμ.comp (continuous_id.prodMk continuous_const)
      map_add' := fun y z => by
        ext x
        simp
      map_smul' := fun c y => by
        ext x
        simp }
  ContinuousLinearMap.mk μ'
    (ContinuousLinearMap.continuous_of_continuous_uncurry μ' <| by
      convert hμ.comp (continuous_swap : Continuous (Prod.swap : G₂ × G₁ → G₁ × G₂)) using 1
      ext p
      simp [μ', Function.comp_apply])

omit [IsTopologicalAddGroup G₁] [ContinuousSMul ℝ G₁] in
@[simp]
theorem pairingFlip_apply (μ : G₁ →L[ℝ] G₂ →L[ℝ] G₃)
    (hμ : Continuous (fun p : G₁ × G₂ ↦ μ p.1 p.2)) (x : G₂) (y : G₁) :
    pairingFlip μ hμ x y = μ y x := by
  simp [pairingFlip]

omit [IsTopologicalAddGroup G₁] [ContinuousSMul ℝ G₁] in
/-- Swapping the two factors of a paired wedge flips the pairing and contributes the graded sign.
This identity is valid for every continuous bilinear pairing and requires no norm on the domain. -/
theorem pairedWedge_flip {k l : ℕ}
    (μ : G₁ →L[ℝ] G₂ →L[ℝ] G₃)
    (hμ : Continuous (fun p : G₁ × G₂ ↦ μ p.1 p.2))
    (φ : X [⋀^Fin k]→L[ℝ] G₁) (ψ : X [⋀^Fin l]→L[ℝ] G₂) (v : Fin (k + l) → X) :
    pairedWedge μ hμ φ ψ v =
      (-1 : ℝ) ^ (k * l) •
        pairedWedge (μ := pairingFlip μ hμ)
          (hμ := show Continuous (fun p : G₂ × G₁ ↦ pairingFlip μ hμ p.1 p.2) from by
          convert hμ.comp (continuous_swap : Continuous (Prod.swap : G₂ × G₁ → G₁ × G₂)) using 1
          ext p
          simp [pairingFlip_apply, Function.comp_apply]) ψ φ
          (v ∘ Fin.cast (Nat.add_comm l k)) := by
  classical
  -- Reindex the permutation sum by the block swap, whose sign is `(-1) ^ (k * l)`.
  set c : Fin (l + k) ≃ Fin (k + l) := finCongr (Nat.add_comm l k)
  set B : Equiv.Perm (Fin (k + l)) := finAddFlip.trans c
  have hsum : ∑ tau : Equiv.Perm (Fin (l + k)), Equiv.Perm.sign tau •
        pairingFlip μ hμ (ψ (fun i => (v ∘ Fin.cast (Nat.add_comm l k)) (tau (Fin.castAdd k i))))
          (φ (fun j => (v ∘ Fin.cast (Nat.add_comm l k)) (tau (Fin.natAdd l j)))) =
      Equiv.Perm.sign B • ∑ sigma : Equiv.Perm (Fin (k + l)), Equiv.Perm.sign sigma •
        μ (φ (fun i => v (sigma (Fin.castAdd l i))))
          (ψ (fun j => v (sigma (Fin.natAdd k j)))) := by
    let f : Equiv.Perm (Fin (k + l)) → G₃ := fun sigma =>
      μ (φ (fun i => v (sigma (Fin.castAdd l i))))
        (ψ (fun j => v (sigma (Fin.natAdd k j))))
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
        simp only [f, Function.comp_apply, pairingFlip_apply]
        rw [← hright, ← hleft]
      _ = _ := TauCeti.sum_sign_smul_permCongr_mul c B f
  rw [pairedWedge_apply μ hμ φ ψ v,
    pairedWedge_apply (μ := pairingFlip μ hμ)
      (hμ := show Continuous (fun p : G₂ × G₁ ↦ pairingFlip μ hμ p.1 p.2) from by
        convert hμ.comp (continuous_swap : Continuous (Prod.swap : G₂ × G₁ → G₁ × G₂)) using 1
        ext p
        simp [pairingFlip_apply, Function.comp_apply]) ψ φ
      (v ∘ Fin.cast (Nat.add_comm l k))]
  rw [hsum, TauCeti.sign_finAddFlip_trans_finCongr]
  generalize (∑ sigma : Equiv.Perm (Fin (k + l)), (_ : G₃)) = S
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ]
  match_scalars
  ring_nf
  simp

end TopologicalFlip

end ContinuousAlternatingMap
