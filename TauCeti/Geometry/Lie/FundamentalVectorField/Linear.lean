/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.SkewAdjoint
public import TauCeti.Geometry.Lie.FundamentalVectorField

import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Fundamental vector fields of linear actions

Let a Lie group `G` act smoothly and linearly on a finite-dimensional real normed space `V`, so
that each `g` acts by a linear map `x ↦ g • x`. The fundamental vector field `ξ_V` of an element
`ξ` of the Lie algebra is then itself linear: `ξ_V(x) = dρ(ξ) x` for the derivative
`dρ(ξ) ∈ End V` of the representation `g ↦ (x ↦ g • x)` at the identity. This file packages
`ξ ↦ dρ(ξ)` as a homomorphism of Lie algebras `TauCeti.fundamentalLieHom`, identifies the
infinitesimal action by fundamental vector fields with the action of `End V` by linear vector
fields along it, and shows that `dρ(ξ)` is skew-adjoint for every bilinear form that the group
preserves (`TauCeti.fundamentalLieHom_mem_skewAdjointLieSubalgebra`). For a symplectic form this
places `dρ(ξ)` in the symplectic Lie algebra `𝔰𝔭(V, ω)`, the input of the moment map
`μ(x)(ξ) = ½ ω(ξ_V x, x)` of a linear symplectic representation.

## Main definitions

* `TauCeti.fundamentalLieHom I G V`: the derivative at the identity of a smooth linear action of
  `G` on `V`, as a Lie algebra homomorphism `GroupLieAlgebra I G →ₗ⁅ℝ⁆ Module.End ℝ V`.
* `TauCeti.fundamentalSkewAdjointLieHom`: the same map with codomain the skew-adjoint
  endomorphisms of a `G`-invariant bilinear form.

## Main results

* `TauCeti.mfderiv_smul_apply`: the derivative of `x ↦ g • x` is `v ↦ g • v`.
* `TauCeti.fundamentalLieHom_apply_apply`: `dρ(ξ) x = ξ_V(x)`; in particular `ξ_V` is linear.
* `TauCeti.InfinitesimalAction.fundamental_eq_linear_comp`: the fundamental vector fields are the
  linear vector fields `x ↦ dρ(ξ) x`.
* `TauCeti.fundamentalLieHom_mem_skewAdjointLieSubalgebra`: `dρ(ξ)` is skew-adjoint for every
  invariant bilinear form.

## References

* Jerrold Marsden and Tudor Ratiu, *Introduction to Mechanics and Symmetry*, second edition,
  §§9.3 and 12.4 (infinitesimal generators of linear actions).
-/

public section

noncomputable section

open Manifold
open scoped ContDiff Manifold

namespace TauCeti

section Linear

attribute [local instance 100] LieRing.ofAssociativeRing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [DistribMulAction G V] [SMulCommClass G ℝ V]

section One

variable [ContMDiffSMul I 𝓘(ℝ, V) 1 G V]

omit [SMulCommClass G ℝ V] in
/-- Every orbit map of a `C¹` action is differentiable. -/
private theorem mdifferentiableAt_smul_const (x : V) (g : G) :
    MDifferentiableAt I 𝓘(ℝ, V) (fun h : G ↦ h • x) g :=
  (ContMDiffSMul.contMDiff_smul_const (I := I) (I' := 𝓘(ℝ, V)) (n := 1) x).mdifferentiableAt
    one_ne_zero

variable (V) in
/-- The fundamental vector field `x ↦ ξ_V(x)` of a smooth linear action, as an endomorphism of
`V`: it is additive and homogeneous since every orbit map `g ↦ g • x` is linear in `x`. -/
private def fundamentalEnd (ξ : GroupLieAlgebra I G) : Module.End ℝ V where
  toFun x := fundamentalVectorField 𝓘(ℝ, V) ξ x
  map_add' x y := by
    have h : (fun g : G ↦ g • (x + y)) = (fun g : G ↦ g • x) + fun g : G ↦ g • y :=
      funext fun g ↦ smul_add g x y
    rw [fundamentalVectorField_apply, fundamentalVectorField_apply, fundamentalVectorField_apply, h,
      mfderiv_add (mdifferentiableAt_smul_const x 1) (mdifferentiableAt_smul_const y 1)]
    rfl
  map_smul' c x := by
    have h : (fun g : G ↦ g • c • x) = c • fun g : G ↦ g • x :=
      funext fun g ↦ smul_comm g c x
    rw [fundamentalVectorField_apply, fundamentalVectorField_apply, h,
      ((mdifferentiableAt_smul_const x 1).hasMFDerivAt.const_smul c).mfderiv]
    rfl

private theorem fundamentalEnd_apply (ξ : GroupLieAlgebra I G) (x : V) :
    fundamentalEnd V ξ x = fundamentalVectorField 𝓘(ℝ, V) ξ x :=
  (rfl)

end One

variable [CompleteSpace E] [LieGroup I (minSmoothness ℝ 3) G] [FiniteDimensional ℝ V]
  [ContMDiffSMul I 𝓘(ℝ, V) ∞ G V]

omit [TopologicalSpace G] in
/-- For a linear action on a finite-dimensional space, the derivative of `x ↦ g • x` is
`v ↦ g • v`. -/
@[simp]
theorem mfderiv_smul_apply (g : G) (x v : V) :
    mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) (fun y : V ↦ g • y) x v = g • v :=
  congrArg (· v)
    ((LinearMap.toContinuousLinearMap (DistribSMul.toLinearMap ℝ V g)).hasFDerivAt
      (x := x)).hasMFDerivAt.mfderiv

/-- A smooth action is in particular `C¹`. -/
local instance contMDiffSMulOne : ContMDiffSMul I 𝓘(ℝ, V) 1 G V :=
  ContMDiffSMul.of_le (M := V) (by exact ENat.LEInfty.out)

variable (I G V) in
/-- The **derivative of a smooth linear representation** at the identity: `ξ` is sent to the
endomorphism `x ↦ ξ_V(x)` of `V`, its fundamental vector field. This is a homomorphism of Lie
algebras, since both the fundamental vector fields and the linear vector fields `x ↦ A x` form
antihomomorphisms into vector fields. -/
def fundamentalLieHom : GroupLieAlgebra I G →ₗ⁅ℝ⁆ Module.End ℝ V where
  toFun := fundamentalEnd V
  map_add' ξ η := LinearMap.ext fun x ↦ by
    simp only [LinearMap.add_apply, fundamentalEnd_apply, fundamentalVectorField_add]
    rfl
  map_smul' c ξ := LinearMap.ext fun x ↦ by
    simp only [LinearMap.smul_apply, fundamentalEnd_apply, fundamentalVectorField_smul]
    rfl
  map_lie' {ξ η} := by
    -- The linear vector field of each image is the corresponding fundamental vector field.
    have hlin (ζ : GroupLieAlgebra I G) :
        InfinitesimalAction.fundamental I G 𝓘(ℝ, V) V ζ =
          InfinitesimalAction.linear V (fundamentalEnd V ζ) := by
      funext x
      rw [InfinitesimalAction.fundamental_apply, InfinitesimalAction.linear_apply,
        fundamentalEnd_apply]
    ext x
    have h := congrFun ((InfinitesimalAction.fundamental I G 𝓘(ℝ, V) V).map_lie ξ η) x
    rw [hlin ξ, hlin η, ← InfinitesimalAction.map_lie, hlin, InfinitesimalAction.linear_apply,
      InfinitesimalAction.linear_apply] at h
    exact h

/-- The endomorphism `dρ(ξ)` sends `x` to the value of the fundamental vector field `ξ_V(x)`. -/
@[simp]
theorem fundamentalLieHom_apply_apply (ξ : GroupLieAlgebra I G) (x : V) :
    fundamentalLieHom I G V ξ x = fundamentalVectorField 𝓘(ℝ, V) ξ x :=
  (rfl)

/-- **The fundamental vector fields of a linear action are linear vector fields**: the
infinitesimal action of `G` on `V` is the action of `End V` by `x ↦ A x`, restricted along the
derivative `dρ` of the representation. -/
theorem InfinitesimalAction.fundamental_eq_linear_comp :
    InfinitesimalAction.fundamental I G 𝓘(ℝ, V) V =
      (InfinitesimalAction.linear V).comp (fundamentalLieHom I G V) :=
  InfinitesimalAction.ext fun ξ ↦ funext fun x ↦ by
    rw [InfinitesimalAction.comp_apply, InfinitesimalAction.linear_apply,
      fundamentalLieHom_apply_apply, InfinitesimalAction.fundamental_apply]

/-- **The derivative of a representation preserving a bilinear form is skew-adjoint.** If
`B (g • x) (g • y) = B x y` for all `g`, then `B (ξ_V x) y + B x (ξ_V y) = 0`, obtained by
differentiating the constant function `g ↦ B (g • x) (g • y)` at the identity. -/
theorem fundamentalLieHom_mem_skewAdjointLieSubalgebra {B : LinearMap.BilinForm ℝ V}
    (hB : ∀ (g : G) (x y : V), B (g • x) (g • y) = B x y) (ξ : GroupLieAlgebra I G) :
    fundamentalLieHom I G V ξ ∈ skewAdjointLieSubalgebra B := by
  refine (LinearMap.mem_skewAdjointSubmodule _).2 fun x y ↦ ?_
  let b : V →L[ℝ] V →L[ℝ] ℝ := B.toContinuousBilinearMap
  have hb : IsBoundedBilinearMap ℝ fun p : V × V ↦ b p.1 p.2 := b.isBoundedBilinearMap
  have hΦ : MDifferentiableAt I 𝓘(ℝ, V × V) (fun g : G ↦ (g • x, g • y)) 1 :=
    (mdifferentiableAt_smul_const x 1).prodMk_space (mdifferentiableAt_smul_const y 1)
  -- The derivative of the orbit map of the pair is the pair of fundamental vectors.
  have hpair : mvfderiv I (fun g : G ↦ (g • x, g • y)) 1 ξ =
      (fundamentalLieHom I G V ξ x, fundamentalLieHom I G V ξ y) := by
    have h₁ := (ContinuousLinearMap.fst ℝ V V).mvfderiv_comp_apply hΦ ξ
    have h₂ := (ContinuousLinearMap.snd ℝ V V).mvfderiv_comp_apply hΦ ξ
    simp only [Function.comp_def, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      mvfderiv_apply_eq_mfderiv_apply] at h₁ h₂
    rw [fundamentalLieHom_apply_apply, fundamentalLieHom_apply_apply, fundamentalVectorField_apply,
      fundamentalVectorField_apply]
    exact Prod.ext h₁.symm h₂.symm
  -- The function `g ↦ B (g • x) (g • y)` is constant, so its derivative vanishes.
  have hconst : ((fun p : V × V ↦ b p.1 p.2) ∘ fun g : G ↦ (g • x, g • y)) =
      fun _ ↦ B x y := by
    funext g
    simp [b, hB]
  have hderiv := mvfderiv_comp_apply_of_differentiableAt (hb.differentiableAt _) hΦ ξ
  rw [hconst, hb.fderiv, hpair, IsBoundedBilinearMap.deriv_apply] at hderiv
  simp only [one_smul, LinearMap.toContinuousBilinearMap_apply, b] at hderiv
  have h0 : mvfderiv I (fun _ : G ↦ B x y) 1 ξ = 0 := by
    rw [mvfderiv_apply_eq_mfderiv_apply, mfderiv_const]
    rfl
  rw [h0] at hderiv
  rw [Pi.neg_apply, map_neg]
  linarith

variable (I G V) in
/-- The derivative of a smooth linear representation preserving a bilinear form `B`, as a Lie
algebra homomorphism into the skew-adjoint endomorphisms of `B`. -/
def fundamentalSkewAdjointLieHom {B : LinearMap.BilinForm ℝ V}
    (hB : ∀ (g : G) (x y : V), B (g • x) (g • y) = B x y) :
    GroupLieAlgebra I G →ₗ⁅ℝ⁆ skewAdjointLieSubalgebra B where
  toFun ξ := ⟨fundamentalLieHom I G V ξ, fundamentalLieHom_mem_skewAdjointLieSubalgebra hB ξ⟩
  map_add' ξ η := Subtype.ext (map_add _ ξ η)
  map_smul' c ξ := Subtype.ext (map_smul _ c ξ)
  map_lie' {ξ η} := Subtype.ext (LieHom.map_lie _ ξ η)

/-- The skew-adjoint derivative of a representation is the derivative with its codomain
restricted. -/
@[simp]
theorem coe_fundamentalSkewAdjointLieHom {B : LinearMap.BilinForm ℝ V}
    (hB : ∀ (g : G) (x y : V), B (g • x) (g • y) = B x y) (ξ : GroupLieAlgebra I G) :
    (fundamentalSkewAdjointLieHom I G V hB ξ : Module.End ℝ V) = fundamentalLieHom I G V ξ :=
  (rfl)

end Linear

end TauCeti
