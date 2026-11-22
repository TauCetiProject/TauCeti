/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Basic

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
(`LinearMap.toLinearMap₁₂_pairingFlip`). The flip sends zero, sums and scalar multiples of
jointly continuous pairings to the corresponding combinations of their flips
(`LinearMap.pairingFlip_zero`, `LinearMap.pairingFlip_add`, `LinearMap.pairingFlip_smul`).

When the hypotheses hold in both orientations, flipping twice gives the pairing back: forgetting
continuity of the curried map in general (`LinearMap.toLinearMap_pairingFlip_pairingFlip`), and
exactly for a continuous pairing (`ContinuousLinearMap.pairingFlip_pairingFlip`).
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

omit [RingHomSurjective σ₂₃] in
/-- The semilinear curried map underlying `pairingFlip`: the algebraic flip of `μ`, lifted along
the injective coercion `ContinuousLinearMap.coeLMₛₗ σ₁₃` by `LinearMap.codLift`, since each slice
`x ↦ μ x y` is continuous by joint continuity. -/
private noncomputable def pairingFlipAux (μ : G₁ →ₛₗ[σ₁₃] G₂ →SL[σ₂₃] G₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y)) : G₂ →ₛₗ[σ₂₃] G₁ →SL[σ₁₃] G₃ :=
  ((ContinuousLinearMap.coeLMₛₗ σ₂₃).comp μ).flip.codLift (ContinuousLinearMap.coeLMₛₗ σ₁₃)
    (fun f g h ↦ ContinuousLinearMap.coe_injective <| by
      rwa [ContinuousLinearMap.coeLMₛₗ_apply, ContinuousLinearMap.coeLMₛₗ_apply] at h)
    fun y ↦ mem_range.2
      ⟨ContinuousLinearMap.mk _ <|
          (hμ.uncurry_right y).congr fun x ↦ (flip_coeLMₛₗ_comp_apply μ y x).symm, by
        rw [ContinuousLinearMap.coeLMₛₗ_apply, ContinuousLinearMap.coe_mk]⟩

omit [RingHomSurjective σ₂₃] [IsTopologicalAddGroup G₂] [ContinuousConstSMul 𝕜₂ G₂] in
private theorem pairingFlipAux_apply (μ : G₁ →ₛₗ[σ₁₃] G₂ →SL[σ₂₃] G₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y)) (y : G₂) (x : G₁) :
    pairingFlipAux μ hμ y x = μ x y := by
  have h : (ContinuousLinearMap.coeLMₛₗ σ₁₃).comp (pairingFlipAux μ hμ) =
      ((ContinuousLinearMap.coeLMₛₗ σ₂₃).comp μ).flip :=
    comp_codLift _ _ _ _
  rw [← flip_coeLMₛₗ_comp_apply μ y x, ← h, comp_apply, ContinuousLinearMap.coeLMₛₗ_apply,
    ContinuousLinearMap.coe_coe]

/-- The flipped continuous pairing `y ↦ (x ↦ μ x y)` of a jointly continuous pairing `μ`.

Only joint continuity `hμ` of `μ` is used: the curried map `μ` need not be continuous.
Outside the normed setting, continuity of a curried pairing does not in general imply joint
continuity, so continuous pairings `μ : G₁ →SL[σ₁₃] G₂ →SL[σ₂₃] G₃` enter as `μ.toLinearMap`
with `hμ` supplied separately. Joint continuity makes the flipped curried map continuous for the
topology of bounded convergence, by `ContinuousLinearMap.continuous_of_continuous_uncurry`. -/
noncomputable def pairingFlip (μ : G₁ →ₛₗ[σ₁₃] G₂ →SL[σ₂₃] G₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y)) : G₂ →SL[σ₂₃] G₁ →SL[σ₁₃] G₃ :=
  ContinuousLinearMap.mk (pairingFlipAux μ hμ) <|
    ContinuousLinearMap.continuous_of_continuous_uncurry (pairingFlipAux μ hμ) <|
      (hμ.comp continuous_swap).congr fun p ↦ by
        simp only [Function.comp_apply, Function.uncurry_def, Prod.fst_swap, Prod.snd_swap,
          pairingFlipAux_apply]

/-- Evaluating the flipped pairing at `x` and then at `y` gives `μ y x`. -/
@[simp]
theorem pairingFlip_apply (μ : G₁ →ₛₗ[σ₁₃] G₂ →SL[σ₂₃] G₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y)) (x : G₂) (y : G₁) :
    pairingFlip μ hμ x y = μ y x := by
  simp only [pairingFlip, ContinuousLinearMap.coe_mk', pairingFlipAux_apply]

/-- The flipped pairing is jointly continuous after exchanging the two arguments. -/
theorem continuous_uncurry_pairingFlip (μ : G₁ →ₛₗ[σ₁₃] G₂ →SL[σ₂₃] G₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y)) :
    Continuous (Function.uncurry fun x y ↦ pairingFlip μ hμ x y) := by
  simpa only [Function.uncurry_def, Function.comp_def, Prod.swap, pairingFlip_apply]
    using hμ.comp continuous_swap

/-- Forgetting continuity, the flip of a jointly continuous pairing is the algebraic flip
`LinearMap.flip` of `μ` with its slices viewed as semilinear maps. -/
@[simp]
theorem toLinearMap₁₂_pairingFlip (μ : G₁ →ₛₗ[σ₁₃] G₂ →SL[σ₂₃] G₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y)) :
    (pairingFlip μ hμ).toLinearMap₁₂ = ((ContinuousLinearMap.coeLMₛₗ σ₂₃).comp μ).flip := by
  ext y x
  rw [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, pairingFlip_apply,
    flip_coeLMₛₗ_comp_apply]

/-- The flip of the zero pairing is zero. -/
@[simp]
theorem pairingFlip_zero
    (h : Continuous (Function.uncurry fun x y ↦ (0 : G₁ →ₛₗ[σ₁₃] G₂ →SL[σ₂₃] G₃) x y)) :
    pairingFlip 0 h = 0 := by
  ext y x
  simp only [pairingFlip_apply, LinearMap.zero_apply, _root_.zero_apply]

/-- The flip of a sum of jointly continuous pairings is the sum of their flips. Joint continuity
`h` of the sum follows from `hμ` and `hν`, but any proof of it is accepted, so that the lemma
rewrites every flip of `μ + ν`. -/
theorem pairingFlip_add (μ ν : G₁ →ₛₗ[σ₁₃] G₂ →SL[σ₂₃] G₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y))
    (hν : Continuous (Function.uncurry fun x y ↦ ν x y))
    (h : Continuous (Function.uncurry fun x y ↦ (μ + ν) x y)) :
    pairingFlip (μ + ν) h = pairingFlip μ hμ + pairingFlip ν hν := by
  ext y x
  simp only [pairingFlip_apply, LinearMap.add_apply, _root_.add_apply]

/-- The flip of a scalar multiple of a jointly continuous pairing is the scalar multiple of its
flip. Joint continuity `h` of `c • μ` follows from `hμ`, but any proof of it is accepted, so that
the lemma rewrites every flip of `c • μ`. -/
theorem pairingFlip_smul {S : Type*} [Monoid S] [DistribMulAction S G₃] [SMulCommClass 𝕜₃ S G₃]
    [ContinuousConstSMul S G₃] (c : S) (μ : G₁ →ₛₗ[σ₁₃] G₂ →SL[σ₂₃] G₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y))
    (h : Continuous (Function.uncurry fun x y ↦ (c • μ) x y)) :
    pairingFlip (c • μ) h = c • pairingFlip μ hμ := by
  ext y x
  simp only [pairingFlip_apply, LinearMap.smul_apply, _root_.smul_apply]

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
theorem LinearMap.toLinearMap_pairingFlip_pairingFlip (μ : G₁ →ₛₗ[σ₁₃] G₂ →SL[σ₂₃] G₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y)) :
    ((μ.pairingFlip hμ).toLinearMap.pairingFlip (μ.continuous_uncurry_pairingFlip hμ)).toLinearMap =
      μ := by
  ext x y
  simp only [ContinuousLinearMap.coe_coe, pairingFlip_apply]

/-- Flipping a jointly continuous pairing `μ : G₁ →SL[σ₁₃] G₂ →SL[σ₂₃] G₃` twice gives it back. -/
@[simp]
theorem ContinuousLinearMap.pairingFlip_pairingFlip (μ : G₁ →SL[σ₁₃] G₂ →SL[σ₂₃] G₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y)) :
    (μ.toLinearMap.pairingFlip hμ).toLinearMap.pairingFlip
      (μ.toLinearMap.continuous_uncurry_pairingFlip hμ) = μ :=
  coe_injective (μ.toLinearMap.toLinearMap_pairingFlip_pairingFlip hμ)

end PairingFlipPairingFlip
