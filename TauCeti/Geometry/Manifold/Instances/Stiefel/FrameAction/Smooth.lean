/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Stiefel.FrameAction.Basic
public import TauCeti.Geometry.Manifold.Instances.Unitary.Special

/-!
# Smooth rotation of Stiefel frames

Changing the basis of an orthonormal frame by a special orthogonal matrix is jointly smooth.
-/

public section

noncomputable section

open Matrix Module
open scoped ContDiff Manifold

namespace TauCeti.stiefel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k : ℕ}

open scoped Matrix.Norms.L2Operator
attribute [local instance] Matrix.l2OpNormedAlgebraReal

variable [FiniteDimensional ℝ E]

local notation "SO(" k ")" => specialOrthogonalGroup (Fin k) ℝ
local notation "𝓢𝓞(" k ")" => specialUnitaryGroup.model (Fin k) ℝ
local notation "𝓥(" E ", " k ")" => 𝓘(ℝ, Fin (k * finrank ℝ E - Nat.choose (k + 1) 2) → ℝ)

/-- Changing the orthonormal basis is jointly smooth in the matrix and the frame. -/
instance instContMDiffSMulSpecialOrthogonalGroup :
    ContMDiffSMul 𝓢𝓞(k) 𝓥(E, k) ∞ (SO(k)) (stiefel E k) where
  contMDiff_smul := by
    refine ContMDiff.codRestrict_stiefel
      (g := fun p : SO(k) × stiefel E k ↦ (p.1 • p.2).val) ?_ (fun p ↦ (p.1 • p.2).property)
    have hA := (specialUnitaryGroup.contMDiff_val (n := Fin k) (𝕜 := ℝ)).comp
      (contMDiff_fst (I := 𝓢𝓞(k)) (J := 𝓥(E, k)) (M := SO(k)) (N := stiefel E k))
    have hv := (contMDiff_coe_stiefel E k (r := ∞)).comp
      (contMDiff_snd (I := 𝓢𝓞(k)) (J := 𝓥(E, k)) (M := SO(k)) (N := stiefel E k))
    refine contMDiff_pi_module_iff.2 fun j ↦ ?_
    simp only [coe_specialOrthogonalGroup_smul_apply]
    refine ContMDiff.sum fun i _ ↦ ?_
    exact (((Matrix.entryLinearMap ℝ ℝ j i).toContinuousLinearMap).contMDiff.comp hA).smul
      (contMDiff_pi_module_iff.1 hv i)

end TauCeti.stiefel
