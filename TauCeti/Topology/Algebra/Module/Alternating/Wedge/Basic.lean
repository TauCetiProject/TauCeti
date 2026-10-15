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
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Pairing
public import TauCeti.Data.Fin.Basic
public import TauCeti.Topology.Algebra.Module.Alternating.Curry
import TauCeti.GroupTheory.Perm.Inversion
import TauCeti.GroupTheory.Perm.Basic

/-!
# Paired wedges of continuous alternating maps

This file provides the unalternated pairing and paired wedge on topological real vector spaces.
It also proves the norm-free interior-product antiderivation law
`ι_v (φ ∧ ψ) = ι_v φ ∧ ψ + (-1) ^ (deg φ) • φ ∧ ι_v ψ`, using
`ContinuousAlternatingMap.curryLeftTopological` from the accompanying Curry module. The construction
requires no norm on the domain and is the topological counterpart of `curryLeft_wedgeWith`.

The alternating-map API follows Mathlib's `AlternatingMap.curryLeft` and `map_insertNth`, and the
paired-wedge design follows Yury Kudryashov's `DeRhamCohomology` project.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Lemma 14.13.
* Yury Kudryashov's `DeRhamCohomology` project.
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

omit [IsTopologicalAddGroup G₁] [ContinuousSMul ℝ G₁] in
/-- Swapping the two factors of a paired wedge flips the pairing and contributes the graded sign.
This identity is valid for every continuous bilinear pairing and requires no norm on the domain. -/
theorem pairedWedge_flip {k l : ℕ}
    (μ : G₁ →L[ℝ] G₂ →L[ℝ] G₃)
    (hμ : Continuous (fun p : G₁ × G₂ ↦ μ p.1 p.2))
    (φ : X [⋀^Fin k]→L[ℝ] G₁) (ψ : X [⋀^Fin l]→L[ℝ] G₂) (v : Fin (k + l) → X) :
    pairedWedge μ hμ φ ψ v =
      (-1 : ℝ) ^ (k * l) •
        pairedWedge (μ := ContinuousLinearMap.pairingFlip μ hμ)
          (hμ := ContinuousLinearMap.pairingFlip_continuous μ hμ) ψ φ
          (v ∘ Fin.cast (Nat.add_comm l k)) := by
  classical
  -- Reindex the permutation sum by the block swap, whose sign is `(-1) ^ (k * l)`.
  set c : Fin (l + k) ≃ Fin (k + l) := finCongr (Nat.add_comm l k)
  set B : Equiv.Perm (Fin (k + l)) := finAddFlip.trans c
  have hsum : ∑ tau : Equiv.Perm (Fin (l + k)), Equiv.Perm.sign tau •
        (ContinuousLinearMap.pairingFlip μ hμ)
          (ψ (fun i => (v ∘ Fin.cast (Nat.add_comm l k)) (tau (Fin.castAdd k i))))
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
        simp only [f, Function.comp_apply, ContinuousLinearMap.pairingFlip_apply]
        rw [← hright, ← hleft]
      _ = _ := TauCeti.sum_sign_smul_permCongr_mul c B f
  rw [pairedWedge_apply μ hμ φ ψ v,
    pairedWedge_apply (μ := ContinuousLinearMap.pairingFlip μ hμ)
      (hμ := ContinuousLinearMap.pairingFlip_continuous μ hμ) ψ φ
      (v ∘ Fin.cast (Nat.add_comm l k))]
  rw [hsum, TauCeti.sign_finAddFlip_trans_finCongr]
  generalize (∑ sigma : Equiv.Perm (Fin (k + l)), (_ : G₃)) = S
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ]
  match_scalars
  ring_nf
  simp

end TopologicalFlip

section InteriorProduct
open Equiv
variable {E F₁ F₂ F₃ : Type*}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F₁] [Module ℝ F₁] [TopologicalSpace F₁]
  [IsTopologicalAddGroup F₁] [ContinuousConstSMul ℝ F₁]
  [AddCommGroup F₂] [Module ℝ F₂] [TopologicalSpace F₂]
  [IsTopologicalAddGroup F₂] [ContinuousConstSMul ℝ F₂]
  [AddCommGroup F₃] [Module ℝ F₃] [TopologicalSpace F₃]
  [IsTopologicalAddGroup F₃] [ContinuousSMul ℝ F₃]
  {k l : ℕ}

omit [IsTopologicalAddGroup F₂] [ContinuousConstSMul ℝ F₂] in
private lemma sum_sign_smul_insertNth_castAdd (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin (k + 1)]→L[ℝ] F₁) (psi : E [⋀^Fin (l + 1)]→L[ℝ] F₂) (v : E)
    (w : Fin (k + 1 + l) → E) (i : Fin (k + 1)) :
    (-1 : ℤ) ^ (Fin.castAdd (l + 1) i : ℕ) • ∑ τ : Perm (Fin (k + 1 + l)), Perm.sign τ •
      mu (phi fun a => Fin.insertNth (α := fun _ => E)
          (Fin.castAdd (l + 1) i : Fin (k + 1 + l + 1)) v (w ∘ τ) (Fin.castAdd (l + 1) a))
        (psi fun b => Fin.insertNth (α := fun _ => E)
          (Fin.castAdd (l + 1) i : Fin (k + 1 + l + 1)) v (w ∘ τ) (Fin.natAdd (k + 1) b)) =
      ∑ sigma : Perm (Fin (k + (l + 1))), Perm.sign sigma •
        mu (phi.curryLeftTopological v fun a =>
            (w ∘ Fin.cast (show k + (l + 1) = k + 1 + l by omega)) (sigma (Fin.castAdd (l + 1) a)))
          (psi fun b =>
            (w ∘ Fin.cast (show k + (l + 1) = k + 1 + l by omega)) (sigma (Fin.natAdd k b))) := by
  have hsign : (-1 : ℤ) ^ (Fin.castAdd (l + 1) i : ℕ) * (-1) ^ (i : ℕ) = 1 := by
    simp [← mul_pow]
  simp_rw [Fin.insertNth_castAdd_comp_castAdd, Fin.insertNth_castAdd_apply_natAdd,
    ContinuousAlternatingMap.map_insertNth', ← curryLeftTopological_apply_apply]
  simp only [map_zsmul, FunLike.coe_smul, Pi.smul_apply, smul_comm (Perm.sign _),
    ← Finset.smul_sum, smul_smul, hsign, one_smul]
  symm
  refine Fintype.sum_equiv (finCongr (show k + (l + 1) = k + 1 + l by omega)).permCongr _ _
    fun sigma => ?_
  simp [Perm.sign_permCongr]

omit [IsTopologicalAddGroup F₁] [ContinuousConstSMul ℝ F₁] in
private lemma sum_sign_smul_insertNth_natAdd (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (phi : E [⋀^Fin (k + 1)]→L[ℝ] F₁) (psi : E [⋀^Fin (l + 1)]→L[ℝ] F₂) (v : E)
    (w : Fin (k + 1 + l) → E) (i : Fin (l + 1)) :
    (-1 : ℤ) ^ (Fin.natAdd (k + 1) i : ℕ) • ∑ τ : Perm (Fin (k + 1 + l)), Perm.sign τ •
      mu (phi fun a => Fin.insertNth (α := fun _ => E)
          (Fin.natAdd (k + 1) i : Fin (k + 1 + l + 1)) v (w ∘ τ) (Fin.castAdd (l + 1) a))
        (psi fun b => Fin.insertNth (α := fun _ => E)
          (Fin.natAdd (k + 1) i : Fin (k + 1 + l + 1)) v (w ∘ τ) (Fin.natAdd (k + 1) b)) =
      (-1 : ℝ) ^ (k + 1) • ∑ sigma : Perm (Fin (k + 1 + l)), Perm.sign sigma •
        mu (phi fun a => w (sigma (Fin.castAdd l a)))
          (psi.curryLeftTopological v fun b => w (sigma (Fin.natAdd (k + 1) b))) := by
  have hsign : (-1 : ℤ) ^ (Fin.natAdd (k + 1) i : ℕ) * (-1 : ℤ) ^ (i : ℕ) = (-1 : ℤ) ^ (k + 1) := by
    simp [pow_add, mul_assoc, ← mul_pow]
  simp_rw [Fin.insertNth_natAdd_apply_castAdd, Fin.insertNth_natAdd_comp_natAdd,
    ContinuousAlternatingMap.map_insertNth', ← curryLeftTopological_apply_apply]
  simp only [map_zsmul, smul_comm (Perm.sign _), ← Finset.smul_sum, smul_smul, hsign,
    Function.comp_apply]
  rw [← Int.cast_smul_eq_zsmul ℝ]
  simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- The interior product is an antiderivation of degree `-1` for the paired wedge:
`ι_v (φ ∧ ψ) = ι_v φ ∧ ψ + (-1) ^ (k + 1) • φ ∧ ι_v ψ` for a `(k + 1)`-form `φ`.
This is the topological counterpart of `TauCeti.curryLeft_wedgeWith` and the formula of Lee,
*Introduction to Smooth Manifolds*, 2nd ed., Lemma 14.13. -/
theorem curryLeftTopological_pairedWedge (mu : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hmu : Continuous (fun p : F₁ × F₂ ↦ mu p.1 p.2))
    (phi : E [⋀^Fin (k + 1)]→L[ℝ] F₁)
    (psi : E [⋀^Fin (l + 1)]→L[ℝ] F₂) (v : E)
    (w : Fin (k + 1 + l) → E) :
    curryLeftTopological (n := k + 1 + l)
      (pairedWedge (k := k + 1) (l := l + 1) mu hmu phi psi) v w =
      pairedWedge (k := k) (l := l + 1) mu hmu (curryLeftTopological (n := k) phi v) psi
        (w ∘ Fin.cast (show k + (l + 1) = k + 1 + l by omega)) +
        (-1 : ℝ) ^ (k + 1) •
          pairedWedge (k := k + 1) (l := l) mu hmu phi (curryLeftTopological (n := l) psi v) w := by
  rw [curryLeftTopological_apply_apply, pairedWedge_apply, pairedWedge_apply, pairedWedge_apply]
  let g : (Fin (k + 1 + l + 1) → E) → F₃ := fun y =>
    mu (phi fun i => y (Fin.castAdd (l + 1) i))
      (psi fun j => y (Fin.natAdd (k + 1) j))
  have hexp := TauCeti.sum_sign_smul_cons_comp_eq_sum_insertNth
    (n := k + 1 + l) g v w
  simp only [g, Function.comp_apply] at hexp
  have hexp' : (∑ sigma : Perm (Fin (k + 1 + (l + 1))), Perm.sign sigma •
      mu (phi fun i =>
        Fin.cons (α := fun _ : Fin (k + 1 + l + 1) => E) v w
          (sigma (Fin.castAdd (l + 1) i)))
        (psi fun j =>
          Fin.cons (α := fun _ : Fin (k + 1 + l + 1) => E) v w
            (sigma (Fin.natAdd (k + 1) j)))) =
      ∑ j : Fin (k + 1 + l + 1), (-1 : ℤ) ^ (j : ℕ) •
        ∑ tau : Perm (Fin (k + 1 + l)), Perm.sign tau •
          mu (phi fun i => Fin.insertNth (α := fun _ => E) j v (w ∘ tau)
              (Fin.castAdd (l + 1) i))
            (psi fun q => Fin.insertNth (α := fun _ => E) j v (w ∘ tau)
              (Fin.natAdd (k + 1) q)) := by
    -- The paired-wedge expression uses the other parenthesization of the sum of degrees;
    -- `convert` transports the expansion across that definitional equality.
    convert hexp using 1
  have hsplit (f : Fin (k + 1 + l + 1) → F₃) :
      ∑ j, f j = ∑ i : Fin (k + 1), f (Fin.castAdd (l + 1) i) +
        ∑ i : Fin (l + 1), f (Fin.natAdd (k + 1) i) :=
    Fin.sum_univ_add (a := k + 1) (b := l + 1) f
  have hvecCons (x : E) (y : Fin (k + 1 + l) → E) :
      Matrix.vecCons x y = Fin.cons x y := rfl
  rw [hvecCons]
  rw [hexp', hsplit]
  simp only [sum_sign_smul_insertNth_castAdd, sum_sign_smul_insertNth_natAdd, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  rw [Nat.factorial_succ k, Nat.factorial_succ l]
  match_scalars <;> field_simp
end InteriorProduct

end ContinuousAlternatingMap
