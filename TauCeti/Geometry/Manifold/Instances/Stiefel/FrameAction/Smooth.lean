/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Stiefel.FrameAction.Basic
public import TauCeti.Geometry.Manifold.Instances.Unitary.Special

/-!
# Smooth orthogonal changes of Stiefel frames

Changing the basis of an orthonormal frame by an orthogonal matrix is jointly smooth.
-/

public section

noncomputable section

open Matrix
open scoped ContDiff Manifold

namespace TauCeti.stiefel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k : ℕ}

open scoped Matrix.Norms.L2Operator
attribute [local instance] Matrix.l2OpNormedAlgebraReal

variable [FiniteDimensional ℝ E]

local notation "SO(" k ")" => specialOrthogonalGroup (Fin k) ℝ
local notation "𝓢𝓞(" k ")" => specialUnitaryGroup.model (Fin k) ℝ
local notation "O(" k ")" => orthogonalGroup (Fin k) ℝ
local notation "𝓞(" k ")" => Unitary.model (Matrix (Fin k) (Fin k) ℝ)
local notation "𝓥(" E ", " k ")" => 𝓘(ℝ, stiefel.Model E k)

/-- Changing the orthonormal basis is jointly smooth in the matrix and the frame. -/
instance instContMDiffSMulOrthogonalGroup :
    ContMDiffSMul 𝓞(k) 𝓥(E, k) ∞ (O(k)) (stiefel E k) where
  contMDiff_smul := by
    refine ContMDiff.codRestrict_stiefel
      (g := fun p : O(k) × stiefel E k ↦ (p.1 • p.2).val) ?_ (fun p ↦ (p.1 • p.2).property)
    have hA := (Unitary.contMDiff_val (R := Matrix (Fin k) (Fin k) ℝ)).comp
      (contMDiff_fst (I := 𝓞(k)) (J := 𝓥(E, k)) (M := O(k)) (N := stiefel E k))
    have hv := (contMDiff_coe_stiefel E k (r := ∞)).comp
      (contMDiff_snd (I := 𝓞(k)) (J := 𝓥(E, k)) (M := O(k)) (N := stiefel E k))
    refine contMDiff_pi_module_iff.2 fun j ↦ ?_
    simp only [coe_orthogonalGroup_smul_apply]
    refine ContMDiff.sum fun i _ ↦ ?_
    exact (((Matrix.entryLinearMap ℝ ℝ j i).toContinuousLinearMap).contMDiff.comp hA).smul
      (contMDiff_pi_module_iff.1 hv i)

/-- The rotation action is smooth by restriction along the inclusion into the orthogonal group. -/
instance instContMDiffSMulSpecialOrthogonalGroup :
    ContMDiffSMul 𝓢𝓞(k) 𝓥(E, k) ∞ (SO(k)) (stiefel E k) :=
  MulAction.contMDiffSMul_compHom
    (specialUnitaryGroup.isSmoothEmbedding_inclusion_unitaryGroup (n := Fin k) (𝕜 := ℝ)).contMDiff

end TauCeti.stiefel
