/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Lie.RightInvariantVectorField

/-!
# The differential and the rank of the orbit map of a Lie group action

Let a Lie group `G` with Lie algebra `𝔤 = GroupLieAlgebra I G` act smoothly on the left on a
manifold `M`, and fix `x ∈ M`. This file computes the differential of the **orbit map**
`h ↦ h • x` at an arbitrary point `g ∈ G`, not only at the identity, where it is the evaluation
`ξ ↦ ξ_M(x)` of the fundamental vector fields.

Every tangent vector at `g` is the value `ξ^R(g)` of a unique right-invariant vector field
(`TauCeti.bijective_mulRightInvariantVectorField`), with `ξ = d(R_{g⁻¹}) w`, and the orbit map
carries `ξ^R` to `ξ_M` (`TauCeti.mfderiv_smul_mulRightInvariantVectorField`). Hence

`d(h ↦ h • x)_g (ξ^R(g)) = ξ_M(g • x)`,

so up to the linear isomorphism `ξ ↦ ξ^R(g)` the differential at `g` is the evaluation of the
fundamental fields at `g • x`. Its image is the orbit tangent space
`T_{g • x}(G • x) = {ξ_M(g • x)}`, and its kernel is the right translate of the isotropy algebra
`𝔤_{g • x}`.

Along an orbit the isotropy algebras are conjugate, `𝔤_{g • x} = Ad_g 𝔤_x`, and the orbit tangent
spaces correspond under the differential of `y ↦ g • y`. So the **rank of the orbit map** is
constant on `G`: for finite-dimensional `G`,

`rank d(h ↦ h • x)_g + dim 𝔤_x = dim 𝔤`.

In particular the orbit map is an immersion at one point, equivalently at every point, exactly
when `𝔤_x = 0`, that is when the action is locally free at `x`; and it is a submersion exactly
when the fundamental vector fields span `T_x M`, as for a transitive action.

## Main results

* `TauCeti.isotropy_fundamental_smul`: `𝔤_{g • x} = Ad_g 𝔤_x`.
* `TauCeti.orbitTangent_fundamental_smul`: `T_{g • x}(G • x) = d(y ↦ g • y)_x (T_x(G • x))`.
* `TauCeti.range_mfderiv_smul_const`: the image of the differential of the orbit map at `g` is the
  orbit tangent space at `g • x`.
* `TauCeti.mfderiv_smul_const_mulRightInvariantVectorField_eq_zero_iff`: its kernel consists of the
  values `ξ^R(g)` with `ξ ∈ 𝔤_{g • x}`.
* `TauCeti.finrank_range_mfderiv_smul_const_add_finrank_isotropy`: **the rank of the orbit map**,
  `rank d(h ↦ h • x)_g + dim 𝔤_x = dim 𝔤`.
* `TauCeti.injective_mfderiv_smul_const_iff`: the differential at `g` is injective exactly when
  `𝔤_x = 0`.
* `TauCeti.surjective_mfderiv_smul_const_iff`: it is surjective exactly when the orbit tangent
  space at `x` is all of `T_x M`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 7 (the equivariant
  rank theorem, which makes orbit maps of constant rank) and Chapter 20 (infinitesimal
  generators).
* Jerrold Marsden and Tudor Ratiu, *Introduction to Mechanics and Symmetry*, second edition, §9.3
  (orbit tangent spaces and isotropy algebras).
-/

public section

noncomputable section

open Function Manifold
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I (minSmoothness ℝ 3) G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M]

attribute [local instance] lieGroupOne

/-- The orbit maps and translations only need a `C¹` action. -/
local instance contMDiffSMulOneOfInfty : ContMDiffSMul I I' 1 G M :=
  ContMDiffSMul.of_le (M := M) ENat.LEInfty.out

/-! ### Conjugacy along an orbit -/

/-- **The isotropy algebras along an orbit are conjugate**: `𝔤_{g • x} = Ad_g 𝔤_x`. -/
theorem isotropy_fundamental_smul (g : G) (x : M) :
    (InfinitesimalAction.fundamental I G I' M).isotropy (g • x) =
      ((InfinitesimalAction.fundamental I G I' M).isotropy x).map
        (Lie.tangentAd (I := I) g : GroupLieAlgebra I G →ₗ⁅ℝ⁆ GroupLieAlgebra I G) := by
  ext ξ
  rw [LieSubalgebra.mem_map]
  simp only [LieEquiv.coe_toLieHom, Lie.tangentAd_apply]
  constructor
  · -- `ξ = Ad_g (Ad_{g⁻¹} ξ)`, and `Ad_{g⁻¹} ξ` lies in the isotropy algebra of `x`.
    intro hξ
    have hAd : Lie.adjointContinuousLinearMap (I := I) g
        (Lie.adjointContinuousLinearMap (I := I) g⁻¹ ξ) = ξ := by
      rw [← ContinuousLinearMap.comp_apply, ← Lie.adjointContinuousLinearMap_mul, mul_inv_cancel,
        Lie.adjointContinuousLinearMap_one, ContinuousLinearMap.id_apply]
    refine ⟨Lie.adjointContinuousLinearMap (I := I) g⁻¹ ξ, ?_, hAd⟩
    rwa [← adjointContinuousLinearMap_mem_isotropy_smul_iff (g := g), hAd]
  · rintro ⟨η, hη, rfl⟩
    exact adjointContinuousLinearMap_mem_isotropy_smul_iff.mpr hη

/-- The isotropy algebras along an orbit have the same dimension. -/
theorem finrank_isotropy_fundamental_smul (g : G) (x : M) :
    Module.finrank ℝ ((InfinitesimalAction.fundamental I G I' M).isotropy (g • x)) =
      Module.finrank ℝ ((InfinitesimalAction.fundamental I G I' M).isotropy x) := by
  rw [isotropy_fundamental_smul]
  exact (LieSubalgebra.equivMapOfInjective _ _
    (Lie.tangentAd (I := I) g).injective).toLinearEquiv.finrank_eq.symm

/-- The action is locally free at `g • x` exactly when it is locally free at `x`. -/
theorem isotropy_fundamental_smul_eq_bot_iff (g : G) (x : M) :
    (InfinitesimalAction.fundamental I G I' M).isotropy (g • x) = ⊥ ↔
      (InfinitesimalAction.fundamental I G I' M).isotropy x = ⊥ := by
  rw [isotropy_fundamental_smul, LieSubalgebra.eq_bot_iff, LieSubalgebra.eq_bot_iff]
  constructor
  · intro h η hη
    exact (Lie.tangentAd (I := I) g).injective
      ((h _ ((LieSubalgebra.mem_map _ _ _).mpr ⟨η, hη, rfl⟩)).trans (map_zero _).symm)
  · intro h ξ hξ
    obtain ⟨η, hη, rfl⟩ := (LieSubalgebra.mem_map _ _ _).mp hξ
    rw [h η hη, map_zero]

/-- **The orbit tangent spaces along an orbit correspond**: the differential of `y ↦ g • y` at `x`
carries the orbit tangent space at `x` onto that at `g • x`. -/
theorem orbitTangent_fundamental_smul (g : G) (x : M) :
    (InfinitesimalAction.fundamental I G I' M).orbitTangent (g • x) =
      ((InfinitesimalAction.fundamental I G I' M).orbitTangent x).map
        (mfderiv I' I' (fun y : M ↦ g • y) x).toLinearMap := by
  ext v
  simp only [Submodule.mem_map, InfinitesimalAction.mem_orbitTangent_iff,
    InfinitesimalAction.fundamental_apply, ContinuousLinearMap.coe_coe]
  constructor
  · rintro ⟨ξ, rfl⟩
    refine ⟨_, ⟨Lie.adjointContinuousLinearMap (I := I) g⁻¹ ξ, rfl⟩, ?_⟩
    rw [mfderiv_smul_fundamentalVectorField, ← ContinuousLinearMap.comp_apply,
      ← Lie.adjointContinuousLinearMap_mul, mul_inv_cancel, Lie.adjointContinuousLinearMap_one,
      ContinuousLinearMap.id_apply]
  · rintro ⟨_, ⟨ξ, rfl⟩, rfl⟩
    exact ⟨_, (mfderiv_smul_fundamentalVectorField g ξ x).symm⟩

/-- The orbit tangent spaces along an orbit have the same dimension. -/
theorem finrank_orbitTangent_fundamental_smul (g : G) (x : M) :
    Module.finrank ℝ ((InfinitesimalAction.fundamental I G I' M).orbitTangent (g • x)) =
      Module.finrank ℝ ((InfinitesimalAction.fundamental I G I' M).orbitTangent x) := by
  have hinv : (mfderiv I' I' (fun y : M ↦ g • y) x).IsInvertible :=
    (Diffeomorph.smul I I' 1 g).isInvertible_mfderiv one_ne_zero
  rw [orbitTangent_fundamental_smul]
  exact (Submodule.equivMapOfInjective _ hinv.injective _).finrank_eq.symm

/-- The fundamental vector fields span the tangent space at `g • x` exactly when they span it at
`x`. -/
theorem orbitTangent_fundamental_smul_eq_top_iff (g : G) (x : M) :
    (InfinitesimalAction.fundamental I G I' M).orbitTangent (g • x) = ⊤ ↔
      (InfinitesimalAction.fundamental I G I' M).orbitTangent x = ⊤ := by
  -- Spanning is carried forward along `y ↦ k • y`, whose differential is surjective.
  have key (k : G) (y : M) (h : (InfinitesimalAction.fundamental I G I' M).orbitTangent y = ⊤) :
      (InfinitesimalAction.fundamental I G I' M).orbitTangent (k • y) = ⊤ := by
    have hinv : (mfderiv I' I' (fun z : M ↦ k • z) y).IsInvertible :=
      (Diffeomorph.smul I I' 1 k).isInvertible_mfderiv one_ne_zero
    rw [orbitTangent_fundamental_smul, h, Submodule.map_top, LinearMap.range_eq_top]
    exact hinv.surjective
  refine ⟨fun h ↦ ?_, key g x⟩
  have h' := key g⁻¹ (g • x) h
  rwa [inv_smul_smul] at h'

/-! ### The differential of the orbit map -/

/-- **The image of the differential of the orbit map** at `g` is the orbit tangent space at
`g • x`, spanned by the values of the fundamental vector fields. -/
theorem range_mfderiv_smul_const (x : M) (g : G) :
    LinearMap.range (mfderiv I I' (fun h : G ↦ h • x) g).toLinearMap =
      (InfinitesimalAction.fundamental I G I' M).orbitTangent (g • x) := by
  ext v
  simp only [LinearMap.mem_range, InfinitesimalAction.mem_orbitTangent_iff,
    InfinitesimalAction.fundamental_apply, ContinuousLinearMap.coe_coe]
  constructor
  · -- Every tangent vector at `g` is the value at `g` of a right-invariant field.
    rintro ⟨w, rfl⟩
    obtain ⟨ξ, rfl⟩ := (bijective_mulRightInvariantVectorField (I := I) g).surjective w
    exact ⟨ξ, (mfderiv_smul_mulRightInvariantVectorField ξ g x).symm⟩
  · rintro ⟨ξ, rfl⟩
    exact ⟨_, mfderiv_smul_mulRightInvariantVectorField ξ g x⟩

/-- **The kernel of the differential of the orbit map** at `g`: the value `ξ^R(g)` of the
right-invariant field generated by `ξ` is killed exactly when `ξ` lies in the isotropy algebra of
`g • x`. Since every tangent vector at `g` is such a value
(`TauCeti.bijective_mulRightInvariantVectorField`), the kernel is the right translate
`d(R_g) 𝔤_{g • x}`. -/
theorem mfderiv_smul_const_mulRightInvariantVectorField_eq_zero_iff (x : M) (g : G)
    (ξ : GroupLieAlgebra I G) :
    mfderiv I I' (fun h : G ↦ h • x) g (mulRightInvariantVectorField ξ g) = 0 ↔
      ξ ∈ (InfinitesimalAction.fundamental I G I' M).isotropy (g • x) := by
  rw [mfderiv_smul_mulRightInvariantVectorField, InfinitesimalAction.mem_isotropy_iff,
    InfinitesimalAction.fundamental_apply]

/-- The image of the differential of the orbit map has the dimension of the orbit tangent space at
`x`, at every point `g` of the group. -/
theorem finrank_range_mfderiv_smul_const (x : M) (g : G) :
    Module.finrank ℝ (LinearMap.range (mfderiv I I' (fun h : G ↦ h • x) g).toLinearMap) =
      Module.finrank ℝ ((InfinitesimalAction.fundamental I G I' M).orbitTangent x) := by
  rw [range_mfderiv_smul_const, finrank_orbitTangent_fundamental_smul]

/-- **The rank of the orbit map.** At every point `g` of a finite-dimensional Lie group, the rank
of the differential of the orbit map `h ↦ h • x` is `dim 𝔤 - dim 𝔤_x`. -/
theorem finrank_range_mfderiv_smul_const_add_finrank_isotropy [FiniteDimensional ℝ E] (x : M)
    (g : G) :
    Module.finrank ℝ (LinearMap.range (mfderiv I I' (fun h : G ↦ h • x) g).toLinearMap) +
        Module.finrank ℝ ((InfinitesimalAction.fundamental I G I' M).isotropy x) =
      Module.finrank ℝ (GroupLieAlgebra I G) := by
  rw [finrank_range_mfderiv_smul_const]
  exact InfinitesimalAction.finrank_orbitTangent_add_finrank_isotropy _ x

/-- **The orbit map is an immersion exactly where the action is locally free.** The differential
of `h ↦ h • x` at any point `g` is injective exactly when the isotropy algebra `𝔤_x` vanishes. -/
theorem injective_mfderiv_smul_const_iff (x : M) (g : G) :
    Injective (mfderiv I I' (fun h : G ↦ h • x) g) ↔
      (InfinitesimalAction.fundamental I G I' M).isotropy x = ⊥ := by
  rw [← isotropy_fundamental_smul_eq_bot_iff g, LieSubalgebra.eq_bot_iff,
    injective_iff_map_eq_zero]
  have hzero : mulRightInvariantVectorField (0 : GroupLieAlgebra I G) g = 0 :=
    (mulRightInvariantVectorField_apply 0 g).trans (map_zero _)
  constructor
  · -- `ξ ∈ 𝔤_{g • x}` puts `ξ^R(g)` in the kernel, so `ξ^R(g) = 0` and `ξ = 0`.
    intro h ξ hξ
    refine (bijective_mulRightInvariantVectorField g).injective ?_
    exact (h _ ((mfderiv_smul_const_mulRightInvariantVectorField_eq_zero_iff x g ξ).mpr hξ)).trans
      hzero.symm
  · -- A tangent vector in the kernel is `ξ^R(g)` with `ξ ∈ 𝔤_{g • x}`, so `ξ = 0`.
    intro h w hw
    obtain ⟨ξ, rfl⟩ := (bijective_mulRightInvariantVectorField (I := I) g).surjective w
    rw [h ξ ((mfderiv_smul_const_mulRightInvariantVectorField_eq_zero_iff x g ξ).mp hw)]
    exact hzero

/-- **The orbit map is a submersion exactly where the fundamental fields span.** The
differential of `h ↦ h • x` at any point `g` is surjective exactly when the orbit tangent space at
`x` is the whole tangent space `T_x M`. -/
theorem surjective_mfderiv_smul_const_iff (x : M) (g : G) :
    Surjective (mfderiv I I' (fun h : G ↦ h • x) g) ↔
      (InfinitesimalAction.fundamental I G I' M).orbitTangent x = ⊤ := by
  rw [← orbitTangent_fundamental_smul_eq_top_iff g, ← range_mfderiv_smul_const,
    LinearMap.range_eq_top, ContinuousLinearMap.coe_coe]

end TauCeti
