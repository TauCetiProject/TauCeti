/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Flips of continuous pairings

This file defines the continuous pairing obtained by exchanging the arguments of a jointly
continuous continuous linear pairing, together with its evaluation and joint-continuity lemmas.
-/

public section

namespace ContinuousLinearMap

variable {G₁ G₂ G₃ : Type*}
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
      convert hμ.comp (continuous_swap : Continuous
        (Prod.swap : G₂ × G₁ → G₁ × G₂)) using 1
      ext p
      simp [μ', Function.comp_apply])

omit [IsTopologicalAddGroup G₁] [ContinuousSMul ℝ G₁] in
@[simp]
theorem pairingFlip_apply (μ : G₁ →L[ℝ] G₂ →L[ℝ] G₃)
    (hμ : Continuous (fun p : G₁ × G₂ ↦ μ p.1 p.2)) (x : G₂) (y : G₁) :
    pairingFlip μ hμ x y = μ y x := by
  simp [pairingFlip]

omit [IsTopologicalAddGroup G₁] [ContinuousSMul ℝ G₁] in
/-- The flipped pairing is jointly continuous after exchanging the two arguments. -/
theorem pairingFlip_continuous (μ : G₁ →L[ℝ] G₂ →L[ℝ] G₃)
    (hμ : Continuous (fun p : G₁ × G₂ ↦ μ p.1 p.2)) :
    Continuous (fun p : G₂ × G₁ ↦ pairingFlip μ hμ p.1 p.2) := by
  convert hμ.comp (continuous_swap : Continuous
    (Prod.swap : G₂ × G₁ → G₁ × G₂)) using 1
  ext p
  simp [pairingFlip_apply, Function.comp_apply]

end ContinuousLinearMap
