/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Lie.Tangent.Differential
import TauCeti.Geometry.Manifold.MFDeriv.ContinuousLinearMap

/-!
# The derivative of a coadjoint-equivariant map along fundamental vector fields

Let `G` be a real Lie group with Lie algebra `𝔤`, let `K` be a subgroup of `G` with Lie algebra
`𝔨`, included in `𝔤` by the differential `ι` of the inclusion, and let `K` act on a manifold `N`.
A map `f : N → 𝔤*` that is equivariant along the orbit of `n`,
`f (k • n) = Ad*_k (f n) = f n ∘ Ad_{k⁻¹}`, has derivative along the fundamental vector field of
`ζ ∈ 𝔨`

`df_n (ζ_N n) = -f n ∘ ad_(ι ζ)`

(`TauCeti.mvfderiv_fundamentalVectorField_apply_of_apply_smul`). Both sides are the derivative at
`1` of `k ↦ f (k • n) η = (Ad*_k (f n)) η`: once through the orbit map of `n`, and once through
the coadjoint action (`TauCeti.Lie.mvfderiv_coadjointRepresentation_apply_one`).

This is the infinitesimal equivariance used to show that the induced form of symplectic induction
is basic for the projection onto a balanced product `G ×_K N`.

## Main results

* `TauCeti.mvfderiv_fundamentalVectorField_apply_of_apply_smul`: the derivative of the
  equivariance of a map to `𝔤*`.
-/

public section

noncomputable section

open Function Manifold
open scoped ContDiff Manifold

namespace TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {G : Type*} [Group G] {K : Subgroup G}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace G] [ChartedSpace H G]
  [LieGroup I ∞ G]
  {EK HK : Type*} [NormedAddCommGroup EK] [NormedSpace ℝ EK] [TopologicalSpace HK]
  {IK : ModelWithCorners ℝ EK HK} [ChartedSpace HK K] [ContMDiffSMul IK I ∞ K G]
  {EN HN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {IN : ModelWithCorners ℝ EN HN} {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
  [MulAction K N] [ContMDiffSMul IK IN ∞ K N]

/-- **Infinitesimal equivariance of a map to `𝔤*`.** Let a subgroup `K` of `G` act on `N`, and let
`f : N → 𝔤*` be equivariant along the orbit of `n`, `f (k • n) = f n ∘ Ad_{k⁻¹}`. Then the
derivative of `f` along the fundamental vector field of `ζ ∈ Lie(K)` is
`df_n (ζ_N n) = -f n ∘ ad_(ι ζ)`, where `ι ζ` is the image of `ζ` in the Lie algebra of `G`. -/
theorem mvfderiv_fundamentalVectorField_apply_of_apply_smul {f : N → E →L[ℝ] ℝ} {n : N}
    (hf : MDifferentiableAt IN 𝓘(ℝ, E →L[ℝ] ℝ) f n)
    (hfK : ∀ k : K, f (k • n) = f n ∘L Lie.adjointContinuousLinearMap (I := I) ((k : G)⁻¹))
    (ζ : GroupLieAlgebra IK K) (η : GroupLieAlgebra I G) :
    mvfderiv IN f n (fundamentalVectorField IN ζ n) η =
      -f n (⁅K.subtype.groupLieAlgebraMap IK I ζ, η⁆ : GroupLieAlgebra I G) := by
  have hι : MDifferentiableAt IK I ((↑) : K → G) 1 :=
    (K.contMDiff_subtypeVal_of_contMDiffSMul (I' := IK) (n := ∞)).mdifferentiableAt (by simp)
  have horbit : MDifferentiableAt IK IN (fun k : K ↦ k • n) 1 :=
    (ContMDiffSMul.contMDiff_smul_const (I := IK) (I' := IN) (n := ∞) n).mdifferentiableAt
      (by simp)
  -- Differentiate `k ↦ f (k • n) η = (Ad*_k (f n)) η` at `k = 1` in the direction `ζ`, once
  -- through the orbit map of `n` and once through the coadjoint action.
  have h₁ : mvfderiv IK (fun k : K ↦ f (k • n) η) 1 ζ =
      mvfderiv IN f n (fundamentalVectorField IN ζ n) η :=
    (mvfderiv_comp_apply_of_eq (g := fun m ↦ f m η) 1 (hf.clm_apply mdifferentiableAt_const)
      horbit (one_smul K n) ζ).trans <| by
        rw [fundamentalVectorField_apply]
        exact mvfderiv_clm_apply_const hf η _
  -- `f n` as an element of `𝔤*`, the domain of the coadjoint representation.
  obtain ⟨ν, hν⟩ : ∃ ν : Module.Dual ℝ (GroupLieAlgebra I G), ∀ X, ν X = f n X :=
    ⟨(f n : E →ₗ[ℝ] ℝ), fun _ ↦ rfl⟩
  have hfun : (fun k : K ↦ f (k • n) η) =
      (fun g : G ↦ Lie.coadjointRepresentation ℝ I G g ν η) ∘ ((↑) : K → G) :=
    funext fun k ↦ by
      rw [comp_apply, hfK, Lie.coadjointRepresentation_apply, hν]
      -- `(f n ∘L A) η` is `f n (A η)` by definition; `ContinuousLinearMap.comp_apply` does not
      -- rewrite it, as `f n` reads `GroupLieAlgebra I G` as its model `E`.
      rfl
  rw [MonoidHom.groupLieAlgebraMap_apply, Subgroup.coe_subtype, ← h₁, hfun,
    mvfderiv_comp_apply_of_eq (y := 1) 1
      ((Lie.contMDiff_coadjointRepresentation_apply ν η).mdifferentiableAt (by simp)) hι rfl ζ,
    Lie.mvfderiv_coadjointRepresentation_apply_one, ← lie_skew, map_neg, hν]

end TauCeti
