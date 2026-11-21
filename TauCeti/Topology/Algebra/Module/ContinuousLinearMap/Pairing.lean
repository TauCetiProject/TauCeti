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
continuous pairing `μ : G₁ →ₛₗ[σ₁₃] G₂ →SL[σ₂₃] G₃`, together with its evaluation and
joint-continuity lemmas. The pairing `μ` is semilinear in both arguments, possibly with different
scalar homomorphisms, as for a sesquilinear complex pairing. Each slice `μ x` is bundled as a
continuous semilinear map, but the curried map `x ↦ μ x` is only semilinear: it need not be
continuous for the topology of bounded convergence, and only joint continuity of `μ` is assumed.
The scalar field of `G₁` is nontrivially normed, the scalar homomorphism `σ₂₃` of the second
argument is surjective, and scalar multiplication is only assumed continuous for each fixed
scalar. Forgetting continuity, the flip is Mathlib's algebraic flip `LinearMap.flip`
(`LinearMap.toLinearMap₁₂_pairingFlip`).

When the hypotheses hold in both orientations, flipping twice gives the pairing back: forgetting
continuity of the curried map in general (`LinearMap.pairingFlip_pairingFlip`), and exactly for a
continuous pairing (`ContinuousLinearMap.pairingFlip_pairingFlip`).
-/

public section

namespace LinearMap

variable {𝕜₁ 𝕜₂ 𝕜₃ G₁ G₂ G₃ : Type*} [NontriviallyNormedField 𝕜₁] [NormedField 𝕜₂]
  [NormedField 𝕜₃] {σ₁₃ : 𝕜₁ →+* 𝕜₃} {σ₂₃ : 𝕜₂ →+* 𝕜₃} [RingHomSurjective σ₂₃]
  [AddCommGroup G₁] [Module 𝕜₁ G₁] [TopologicalSpace G₁]
  [AddCommGroup G₂] [Module 𝕜₂ G₂] [TopologicalSpace G₂]
  [IsTopologicalAddGroup G₂] [ContinuousConstSMul 𝕜₂ G₂]
  [AddCommGroup G₃] [Module 𝕜₃ G₃] [TopologicalSpace G₃]
  [IsTopologicalAddGroup G₃] [ContinuousConstSMul 𝕜₃ G₃]

/-- The flipped continuous pairing `y ↦ (x ↦ μ x y)` of a jointly continuous pairing `μ`.

Only joint continuity `hμ` of `μ` is used: the curried map `μ` need not be continuous.
Outside the normed setting, continuity of a curried pairing does not in general imply joint
continuity, so continuous pairings `μ : G₁ →SL[σ₁₃] G₂ →SL[σ₂₃] G₃` enter as `μ.toLinearMap`
with `hμ` supplied separately. Joint continuity makes the flipped curried map continuous for the
topology of bounded convergence, by `ContinuousLinearMap.continuous_of_continuous_uncurry`. -/
noncomputable def pairingFlip (μ : G₁ →ₛₗ[σ₁₃] G₂ →SL[σ₂₃] G₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y)) : G₂ →SL[σ₂₃] G₁ →SL[σ₁₃] G₃ :=
  let μ' : G₂ →ₛₗ[σ₂₃] G₁ →SL[σ₁₃] G₃ :=
    { toFun := fun y =>
        ContinuousLinearMap.mk (((ContinuousLinearMap.coeLMₛₗ σ₂₃).comp μ).flip y) <|
          hμ.comp (continuous_id.prodMk continuous_const)
      map_add' := fun y z => by
        ext x
        exact (μ x).map_add y z
      map_smul' := fun c y => by
        ext x
        exact (μ x).map_smulₛₗ c y }
  ContinuousLinearMap.mk μ'
    (ContinuousLinearMap.continuous_of_continuous_uncurry μ' (hμ.comp continuous_swap))

@[simp]
theorem pairingFlip_apply (μ : G₁ →ₛₗ[σ₁₃] G₂ →SL[σ₂₃] G₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y)) (x : G₂) (y : G₁) :
    pairingFlip μ hμ x y = μ y x := (rfl)

/-- The flipped pairing is jointly continuous after exchanging the two arguments. -/
theorem pairingFlip_continuous (μ : G₁ →ₛₗ[σ₁₃] G₂ →SL[σ₂₃] G₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y)) :
    Continuous (Function.uncurry fun x y ↦ pairingFlip μ hμ x y) := by
  simpa only [Function.uncurry_def, Function.comp_def, Prod.swap, pairingFlip_apply]
    using hμ.comp continuous_swap

/-- Forgetting continuity, the flip of a jointly continuous pairing is the algebraic flip
`LinearMap.flip` of `μ` with its slices viewed as semilinear maps. -/
@[simp]
theorem toLinearMap₁₂_pairingFlip (μ : G₁ →ₛₗ[σ₁₃] G₂ →SL[σ₂₃] G₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y)) :
    (pairingFlip μ hμ).toLinearMap₁₂ = ((ContinuousLinearMap.coeLMₛₗ σ₂₃).comp μ).flip :=
  (rfl)

end LinearMap

section PairingFlipPairingFlip

variable {𝕜₁ 𝕜₂ 𝕜₃ G₁ G₂ G₃ : Type*} [NontriviallyNormedField 𝕜₁]
  [NontriviallyNormedField 𝕜₂] [NormedField 𝕜₃] {σ₁₃ : 𝕜₁ →+* 𝕜₃} {σ₂₃ : 𝕜₂ →+* 𝕜₃}
  [RingHomSurjective σ₁₃] [RingHomSurjective σ₂₃]
  [AddCommGroup G₁] [Module 𝕜₁ G₁] [TopologicalSpace G₁]
  [IsTopologicalAddGroup G₁] [ContinuousConstSMul 𝕜₁ G₁]
  [AddCommGroup G₂] [Module 𝕜₂ G₂] [TopologicalSpace G₂]
  [IsTopologicalAddGroup G₂] [ContinuousConstSMul 𝕜₂ G₂]
  [AddCommGroup G₃] [Module 𝕜₃ G₃] [TopologicalSpace G₃]
  [IsTopologicalAddGroup G₃] [ContinuousConstSMul 𝕜₃ G₃]

/-- Flipping a jointly continuous pairing `μ : G₁ →ₛₗ[σ₁₃] G₂ →SL[σ₂₃] G₃` twice gives it back,
after forgetting continuity of the resulting curried map. -/
@[simp]
theorem LinearMap.pairingFlip_pairingFlip (μ : G₁ →ₛₗ[σ₁₃] G₂ →SL[σ₂₃] G₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y)) :
    ((μ.pairingFlip hμ).toLinearMap.pairingFlip (μ.pairingFlip_continuous hμ)).toLinearMap =
      μ := by
  ext x y
  simp only [ContinuousLinearMap.coe_coe, pairingFlip_apply]

/-- Flipping a jointly continuous pairing `μ : G₁ →SL[σ₁₃] G₂ →SL[σ₂₃] G₃` twice gives it back. -/
@[simp]
theorem ContinuousLinearMap.pairingFlip_pairingFlip (μ : G₁ →SL[σ₁₃] G₂ →SL[σ₂₃] G₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y)) :
    (μ.toLinearMap.pairingFlip hμ).toLinearMap.pairingFlip
      (μ.toLinearMap.pairingFlip_continuous hμ) = μ :=
  coe_injective (μ.toLinearMap.pairingFlip_pairingFlip hμ)

end PairingFlipPairingFlip
