/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.FundamentalVectorField

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

Along an orbit the isotropy algebras are conjugate, `𝔤_{g • x} = Ad_g 𝔤_x`
(`TauCeti.isotropy_fundamental_smul`), and the orbit tangent spaces correspond under the
differential of `y ↦ g • y` (`TauCeti.orbitTangent_fundamental_smul`). So the **rank of the orbit
map** is constant on `G`: for finite-dimensional `G`,

`rank d(h ↦ h • x)_g + dim 𝔤_x = dim 𝔤`.

In particular the differential of the orbit map is injective at one point, equivalently at every
point, exactly when `𝔤_x = 0`, that is when the action is locally free at `x`; and it is
surjective at one point, equivalently at every point, exactly when the fundamental vector fields
span `T_x M`. For finite-dimensional `G` and `M` these are the conditions for the orbit map to be
an immersion, respectively a submersion.

## Main results

* `TauCeti.mfderiv_smul_const_apply`: the differential of the orbit map at `g` is that of the orbit
  map of `g • x` at the identity, precomposed with the differential of right translation by `g⁻¹`.
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

/-! ### The differential of the orbit map -/

section Differential

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [ContMDiffMul I 1 G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [MulAction G M]
  [ContMDiffSMul I I' 1 G M]

/-- The derivative at `g` of the orbit map of `x` is that of the orbit map of `g • x` at the
identity, precomposed with the derivative of right translation by `g⁻¹`. -/
theorem mfderiv_smul_const_apply (g : G) (x : M) (v : TangentSpace I g) :
    mfderiv I I' (fun h : G ↦ h • x) g v =
      mfderiv I I' (fun h : G ↦ h • g • x) 1 (mfderiv I I (· * g⁻¹) g v) := by
  have hfun : (fun h : G ↦ h • x) = (fun h : G ↦ h • g • x) ∘ ((· * g⁻¹) : G → G) :=
    funext fun h ↦ by simp [mul_smul]
  rw [hfun]
  exact mfderiv_comp_apply_of_eq g (ContMDiffSMul.mdifferentiableAt_smul_const (g • x) 1)
    (mdifferentiableAt_mul_right (a := g⁻¹)) (mul_inv_cancel g) v

end Differential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I (minSmoothness ℝ 3) G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M]

attribute [local instance] lieGroupOne
attribute [local instance] contMDiffSMulOneOfInfty

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

/-- **The differential of the orbit map is injective exactly where the action is locally free.**
The differential of `h ↦ h • x` at any point `g` is injective exactly when the isotropy algebra
`𝔤_x` vanishes. -/
theorem injective_mfderiv_smul_const_iff (x : M) (g : G) :
    Injective (mfderiv I I' (fun h : G ↦ h • x) g) ↔
      (InfinitesimalAction.fundamental I G I' M).isotropy x = ⊥ := by
  -- Up to the bijection `ξ ↦ ξ^R(g)`, the differential at `g` is evaluation at `g • x`.
  rw [← isotropy_smul_eq_bot_iff (g := g), InfinitesimalAction.isotropy_eq_bot_iff,
    ← Injective.of_comp_iff' _ (bijective_mulRightInvariantVectorField (I := I) g)]
  congr! 1
  ext ξ
  rw [comp_apply, mfderiv_smul_mulRightInvariantVectorField, InfinitesimalAction.eval_apply,
    InfinitesimalAction.fundamental_apply]

/-- **The differential of the orbit map is surjective exactly where the fundamental fields span.**
The differential of `h ↦ h • x` at any point `g` is surjective exactly when the orbit tangent space
at `x` is the whole tangent space `T_x M`. -/
theorem surjective_mfderiv_smul_const_iff (x : M) (g : G) :
    Surjective (mfderiv I I' (fun h : G ↦ h • x) g) ↔
      (InfinitesimalAction.fundamental I G I' M).orbitTangent x = ⊤ := by
  rw [← orbitTangent_fundamental_smul_eq_top_iff g, ← range_mfderiv_smul_const,
    LinearMap.range_eq_top, ContinuousLinearMap.coe_coe]

end TauCeti
