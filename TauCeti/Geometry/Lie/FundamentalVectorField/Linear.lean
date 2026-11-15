/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.FundamentalVectorField

/-!
# Fundamental vector fields of linear actions

Let a group `G` modelled on a manifold act `C¹` and linearly on a normed space `V`, that is, by a
`DistribMulAction` commuting with the scalars. The fundamental vector field
`ξ_V(v) = d_1(g ↦ g • v)(ξ)` (`TauCeti.fundamentalVectorField`) of every `ξ` in the Lie algebra is
then a linear vector field: `ξ_V(u + v) = ξ_V(u) + ξ_V(v)` and `ξ_V(c • v) = c • ξ_V(v)`, because
the orbit maps of `u + v` and `c • v` are the sum and the scalar multiple of the orbit maps of `u`
and `v`. The resulting endomorphism `ξ_V` of `V` is the derivative at the identity of the
representation `g ↦ (v ↦ g • v)`.

This file bundles these endomorphisms as a linear map from the Lie algebra to `V →ₗ V`
(`TauCeti.fundamentalLinearMap`). If the action preserves a continuous bilinear map `B`, then
every `ξ_V` is skew for `B`, `B (ξ_V u) w = -B u (ξ_V w)`
(`ContinuousLinearMap.apply_fundamentalLinearMap_left`): this is the derivative at the identity
of `B (g • u) (g • w) = B u w`. For a symplectic form it places `ξ_V` in the symplectic Lie algebra,
which is the input for the quadratic moment map of a linear symplectic representation.

## Main definitions

* `TauCeti.fundamentalLinearMap I G V`: the linear map `ξ ↦ ξ_V` from the Lie algebra of `G` to
  the endomorphisms of `V`, for a linear action of `G` on `V`.

## Main results

* `TauCeti.fundamentalLinearMap_apply_eq_fundamentalVectorField`: `fundamentalLinearMap I G V ξ`
  is the fundamental vector field `ξ_V`, read in `V`.
* `ContinuousLinearMap.apply_fundamentalLinearMap_left`: an action preserving a continuous
  bilinear map acts infinitesimally by skew maps.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 20 (the induced Lie algebra action and the differential of a
  representation).
-/

public section

noncomputable section

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [DistribMulAction G V] [SMulCommClass G 𝕜 V] [ContMDiffSMul I 𝓘(𝕜, V) 1 G V]

namespace TauCeti

variable (I G V) in
/-- For a linear action of `G` on `V`, the linear map sending `ξ` in the Lie algebra to the
endomorphism `v ↦ d_1(g ↦ g • v)(ξ)` of `V`, the fundamental vector field `ξ_V` read in `V`
(`TauCeti.fundamentalLinearMap_apply_eq_fundamentalVectorField`). Each `ξ_V` is linear because the
orbit maps of `u + v` and `c • v` are the sum and the scalar multiple of those of `u` and `v`. This
is the derivative at the identity of the representation `g ↦ (v ↦ g • v)`. -/
def fundamentalLinearMap : GroupLieAlgebra I G →ₗ[𝕜] V →ₗ[𝕜] V where
  toFun ξ :=
    { toFun v := mvfderiv I (fun g : G ↦ g • v) 1 ξ
      map_add' u v := by
        have hu := (ContMDiffSMul.contMDiff_smul_const (I := I) (I' := 𝓘(𝕜, V)) (n := 1) u)
          |>.mdifferentiableAt one_ne_zero (x := (1 : G))
        have hv := (ContMDiffSMul.contMDiff_smul_const (I := I) (I' := 𝓘(𝕜, V)) (n := 1) v)
          |>.mdifferentiableAt one_ne_zero (x := (1 : G))
        have horbit : (fun g : G ↦ g • (u + v)) = (fun g : G ↦ g • u) + fun g : G ↦ g • v :=
          funext fun g ↦ smul_add g u v
        rw [horbit, mvfderiv_add hu hv, add_apply]
      map_smul' c v := by
        have horbit : (fun g : G ↦ g • (c • v)) = c • fun g : G ↦ g • v :=
          funext fun g ↦ smul_comm g c v
        rw [horbit, mvfderiv_const_smul_field, smul_apply, RingHom.id_apply] }
  map_add' ξ η := by
    ext v
    simp only [LinearMap.coe_mk, AddHom.coe_mk, map_add, LinearMap.add_apply]
  map_smul' c ξ := by
    ext v
    simp only [LinearMap.coe_mk, AddHom.coe_mk, map_smul, LinearMap.smul_apply, RingHom.id_apply]

/-- The fundamental linear map evaluates to the derivative at the identity of the orbit map. -/
theorem fundamentalLinearMap_apply (ξ : GroupLieAlgebra I G) (v : V) :
    fundamentalLinearMap I G V ξ v = mvfderiv I (fun g : G ↦ g • v) 1 ξ :=
  (rfl)

/-- The fundamental linear map evaluates to the fundamental vector field, read in `V` through the
canonical identification of the tangent spaces of `V` with `V`. -/
theorem fundamentalLinearMap_apply_eq_fundamentalVectorField (ξ : GroupLieAlgebra I G) (v : V) :
    fundamentalLinearMap I G V ξ v =
      NormedSpace.fromTangentSpace v (fundamentalVectorField 𝓘(𝕜, V) ξ v) := by
  rw [fundamentalLinearMap_apply, mvfderiv_apply_eq_mfderiv_apply, fundamentalVectorField_apply]
  exact (NormedSpace.fromTangentSpace_apply (𝕜 := 𝕜) v _).symm

end TauCeti

namespace ContinuousLinearMap

open TauCeti

/-- **Linear actions preserving a bilinear map act infinitesimally by skew maps.** If every element
of `G` preserves a continuous bilinear map `B`, that is `B (g • u) (g • w) = B u w`, then each
`ξ_V` is skew for `B`: `B (ξ_V u) w = -B u (ξ_V w)`. This is the derivative at the identity of the
invariance identity. -/
theorem apply_fundamentalLinearMap_left {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (B : V →L[𝕜] V →L[𝕜] F) (hB : ∀ (g : G) (u w : V), B (g • u) (g • w) = B u w)
    (ξ : GroupLieAlgebra I G) (u w : V) :
    B (fundamentalLinearMap I G V ξ u) w = -B u (fundamentalLinearMap I G V ξ w) := by
  have hu := (ContMDiffSMul.contMDiff_smul_const (I := I) (I' := 𝓘(𝕜, V)) (n := 1) u)
    |>.mdifferentiableAt one_ne_zero (x := (1 : G))
  have hw := (ContMDiffSMul.contMDiff_smul_const (I := I) (I' := 𝓘(𝕜, V)) (n := 1) w)
    |>.mdifferentiableAt one_ne_zero (x := (1 : G))
  -- The pair of orbit maps `g ↦ (g • u, g • w)` and its derivative, read componentwise.
  have hk : MDifferentiableAt I 𝓘(𝕜, V × V) (fun g : G ↦ (g • u, g • w)) 1 :=
    hu.prodMk_space hw
  have hfst := (ContinuousLinearMap.fst 𝕜 V V).mvfderiv_comp_apply hk ξ
  have hsnd := (ContinuousLinearMap.snd 𝕜 V V).mvfderiv_comp_apply hk ξ
  -- Composed with `B`, the pair of orbit maps is constant, so its derivative vanishes.
  have hconst : (fun p : V × V ↦ B p.1 p.2) ∘ (fun g : G ↦ (g • u, g • w)) = fun _ ↦ B u w :=
    funext fun g ↦ hB g u w
  have hzero := mvfderiv_comp_apply_of_differentiableAt (φ := fun p : V × V ↦ B p.1 p.2)
    (g := fun g : G ↦ (g • u, g • w)) (x := 1)
    (B.isBoundedBilinearMap.differentiableAt ((1 : G) • u, (1 : G) • w)) hk ξ
  rw [hconst, mvfderiv_const, B.isBoundedBilinearMap.fderiv,
    IsBoundedBilinearMap.deriv_apply] at hzero
  simp only [Function.comp_def, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    one_smul] at hfst hsnd hzero
  rw [fundamentalLinearMap_apply, fundamentalLinearMap_apply, hfst, hsnd]
  rw [zero_apply, add_comm] at hzero
  exact eq_neg_of_add_eq_zero_left hzero.symm

end ContinuousLinearMap
