/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.Geometry.Lie.FundamentalVectorField
import TauCeti.Geometry.Manifold.MFDeriv.ContinuousLinearMap

/-!
# Fundamental vector fields and coadjoint-equivariant maps

Let a real Lie group `G` with Lie algebra `𝔤` and finite-dimensional model have its coadjoint
action `Ad*_g ν = ν ∘ Ad_{g⁻¹}` on `𝔤*`, and let a Lie group `K` act on a manifold `N` and map to
`G` by a homomorphism `φ : K →* G`, differentiable at the identity. This file differentiates the
equivariance `f (k • n) = Ad*_{φ k} (f n)` of a map `f : N → 𝔤*` at `k = 1`: along the
fundamental vector field of `ξ ∈ Lie(K)`,

`df_n (ξ_N n) ζ = f n ⁅ζ, dφ ξ⁆`

(`TauCeti.mvfderiv_apply_fundamentalVectorField`). This is the equivariant counterpart of
`TauCeti.mvfderiv_fundamentalVectorField_eq_zero_of_smul_invariant`. The case `φ = id` is a
`G`-equivariant map, and the inclusion of a subgroup `K` of `G` gives a map which is equivariant
for the restriction of the coadjoint action to `K`.

## Main results

* `TauCeti.mvfderiv_apply_fundamentalVectorField`: the derivative of a coadjoint-equivariant map
  along fundamental vector fields.
-/

public section

noncomputable section

open Function Manifold
open scoped ContDiff Manifold

namespace TauCeti

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {G : Type*} [TopologicalSpace G]
  [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {EK HK : Type*} [NormedAddCommGroup EK] [NormedSpace ℝ EK] [TopologicalSpace HK]
  {J : ModelWithCorners ℝ EK HK} {K : Type*} [TopologicalSpace K] [ChartedSpace HK K] [Group K]
  {EN HN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {IN : ModelWithCorners ℝ EN HN} {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
  [MulAction K N] [ContMDiffSMul J IN 1 K N]

/-- **The derivative of coadjoint equivariance.** Let `K` act on `N` and map to `G` by
`φ : K →* G`, differentiable at the identity. If `f : N → 𝔤*` is differentiable at `n` and
`f (k • n) = Ad*_{φ k} (f n)` for every `k`, then along the fundamental vector field of
`ξ ∈ Lie(K)`, `df_n (ξ_N n) ζ = f n ⁅ζ, dφ ξ⁆`. -/
theorem mvfderiv_apply_fundamentalVectorField {f : N → E →L[ℝ] ℝ} {n : N}
    (hf : MDifferentiableAt IN 𝓘(ℝ, E →L[ℝ] ℝ) f n) (φ : K →* G)
    (hφ : MDifferentiableAt J I φ 1)
    (hfK : ∀ k : K, f (k • n) = f n ∘L Lie.adjointContinuousLinearMap (I := I) (φ k)⁻¹)
    (ξ : GroupLieAlgebra J K) (ζ : GroupLieAlgebra I G) :
    mvfderiv IN f n (fundamentalVectorField IN ξ n) ζ =
      f n (⁅ζ, φ.groupLieAlgebraMap J I ξ⁆ : GroupLieAlgebra I G) := by
  have horbit : MDifferentiableAt J IN (fun k : K ↦ k • n) 1 :=
    (ContMDiffSMul.contMDiff_smul_const (I := J) (I' := IN) (n := 1) n).mdifferentiableAt
      one_ne_zero
  have hAd : MDifferentiableAt I 𝓘(ℝ)
      (fun g : G ↦ Lie.coadjointRepresentation ℝ I G g (f n : E →ₗ[ℝ] ℝ) ζ) 1 :=
    (Lie.contMDiff_coadjointRepresentation_apply _ ζ).mdifferentiableAt (by simp)
  -- The function `k ↦ f (k • n) ζ` is `(y ↦ f y ζ) ∘ (k ↦ k • n)`, and by equivariance it is also
  -- `(g ↦ (Ad*_g (f n)) ζ) ∘ φ`; differentiate both at `1` in the direction `ξ`.
  have hcomp : (fun y ↦ f y ζ) ∘ (fun k : K ↦ k • n) =
      (fun g : G ↦ Lie.coadjointRepresentation ℝ I G g (f n : E →ₗ[ℝ] ℝ) ζ) ∘ φ :=
    funext fun k ↦ by
      rw [comp_apply, comp_apply, hfK]
      -- `(f n ∘ Ad_{(φ k)⁻¹}) ζ = f n (Ad_{(φ k)⁻¹} ζ)` holds by definition of the composition,
      -- which `rw` cannot use since `Ad_{(φ k)⁻¹}` acts on `GroupLieAlgebra I G` and `f n` on `E`.
      exact (Lie.coadjointRepresentation_apply (I := I) (φ k) (f n : E →ₗ[ℝ] ℝ) ζ).symm
  have hfζ : MDifferentiableAt IN 𝓘(ℝ) (fun y ↦ f y ζ) n := hf.clm_apply mdifferentiableAt_const
  rw [MonoidHom.groupLieAlgebraMap_apply, fundamentalVectorField_apply]
  -- The steps are chained with `trans`, as their two sides differ from the goal by the
  -- identification of `GroupLieAlgebra I G` with the model space `E`.
  calc mvfderiv IN f n (mfderiv J IN (fun k : K ↦ k • n) 1 ξ) ζ
      = mvfderiv J ((fun y ↦ f y ζ) ∘ fun k : K ↦ k • n) 1 ξ :=
        (mvfderiv_clm_apply_const hf ζ _).symm.trans
          (mvfderiv_comp_apply_of_eq (1 : K) hfζ horbit (one_smul K n) ξ).symm
    _ = mvfderiv J ((fun g : G ↦
          Lie.coadjointRepresentation ℝ I G g (f n : E →ₗ[ℝ] ℝ) ζ) ∘ φ) 1 ξ := by
        rw [hcomp]
    _ = _ := (mvfderiv_comp_apply_of_eq (1 : K) hAd hφ (map_one φ) ξ).trans
        (Lie.mvfderiv_coadjointRepresentation_apply_one _ ζ _)

end TauCeti
