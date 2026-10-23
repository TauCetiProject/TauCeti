/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.Classification
public import TauCeti.Geometry.Lie.Exponential.Smoothness
public import TauCeti.Geometry.Lie.Exponential.Trotter
public import TauCeti.Geometry.Manifold.Algebra.Monoid

/-!
# Continuous homomorphisms of Lie groups are smooth

Every continuous group homomorphism `f : G → G'` between finite-dimensional real Lie groups is
smooth. Consequently a Lie-group homomorphism may be specified as a continuous homomorphism, and
the Lie functor `lieMap` applies to every continuous homomorphism.

## The argument

For a left-invariant derivation `X` of `G`, the composite `t ↦ f (lieExp (t • X))` is a continuous
one-parameter subgroup of `G'`, so by the classification of continuous one-parameter subgroups it
is `t ↦ lieExp (t • L X)` for a unique left-invariant derivation `L X` of `G'`. Uniqueness makes
`L` homogeneous, and the Trotter product formula

`lieExp (t • (X + Y)) = lim (lieExp ((t / n) • X) * lieExp ((t / n) • Y)) ^ n`,

which `f` preserves because it is a continuous homomorphism, makes it additive. So `L` is linear
between finite-dimensional spaces, hence smooth, and `f (lieExp X) = lieExp (L X)`.
Near the identity `f = lieExp ∘ L ∘ lieLog`, so `f` is smooth at the identity, and a homomorphism
smooth at one point is smooth everywhere by translation
(`TauCeti.contMDiff_of_contMDiffAt_mulHom`).

The linear map `L` is not exposed: once `f` is known to be smooth, it is the differential
`lieMap` of the bundled smooth homomorphism, characterized by `map_lieExp`.

## Main results

* `TauCeti.Lie.contMDiff_of_continuous_monoidHom`: **automatic smoothness.** A continuous
  homomorphism between finite-dimensional real Lie groups is smooth.
* `ContinuousMonoidHom.toContMDiffMonoidMorphism`: a continuous homomorphism of such Lie groups,
  bundled as a smooth monoid morphism.

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer GTM 222 (2015),
  Chapter 3: a continuous homomorphism of matrix Lie groups intertwines the exponentials through a
  linear map, proved with one-parameter subgroups and the Lie product formula.
-/

public section

noncomputable section

open Filter Function Manifold
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']

attribute [local instance] LieGroup.minSmoothnessThree
attribute [local instance] ContMDiffMul.boundarylessManifold

namespace TauCeti.Lie

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [LieGroup I ∞ G] [LieGroup I' ∞ G']

section Generator

variable [T2Space G] [T2Space G']

/-- The generator of the continuous one-parameter subgroup `t ↦ f (lieExp (t • X))` of `G'`. -/
private def homGenerator (f : G →ₜ* G') (X : LeftInvariantDerivation I G) :
    LeftInvariantDerivation I' G' :=
  (oneParameterSubgroupEquiv (I := I') (G := G')).symm (f.comp (oneParameterSubgroup X))

/-- The defining property of the generator: `f (lieExp (t • X)) = lieExp (t • Y)`. -/
private theorem map_lieExp_smul (f : G →ₜ* G') (X : LeftInvariantDerivation I G) (t : ℝ) :
    f (lieExp (t • X)) = lieExp (t • homGenerator (I' := I') f X) := by
  have h := (oneParameterSubgroupEquiv (I := I') (G := G')).apply_symm_apply
    (f.comp (oneParameterSubgroup X))
  rw [oneParameterSubgroupEquiv_apply] at h
  rw [← oneParameterSubgroup_apply, ← oneParameterSubgroup_apply, homGenerator, h,
    ContinuousMonoidHom.coe_comp, comp_apply]

/-- The generator is determined by the values of `f` along the one-parameter subgroup. -/
private theorem homGenerator_eq_of_forall (f : G →ₜ* G') {X : LeftInvariantDerivation I G}
    {Y : LeftInvariantDerivation I' G'} (h : ∀ t : ℝ, f (lieExp (t • X)) = lieExp (t • Y)) :
    homGenerator f X = Y := by
  apply oneParameterSubgroup_injective (I := I') (G := G')
  ext t
  rw [← ofAdd_toAdd t, oneParameterSubgroup_apply, oneParameterSubgroup_apply,
    ← map_lieExp_smul, h]

private theorem homGenerator_smul (f : G →ₜ* G') (c : ℝ) (X : LeftInvariantDerivation I G) :
    homGenerator f (c • X) = c • homGenerator (I' := I') f X :=
  homGenerator_eq_of_forall (I' := I') f fun t ↦ by
    rw [smul_smul, smul_smul, map_lieExp_smul (I' := I')]

/-- Additivity of the generator: `f` carries the Trotter approximants of `X + Y` to those of the
two generators, and both sequences converge. -/
private theorem homGenerator_add (f : G →ₜ* G') (X Y : LeftInvariantDerivation I G) :
    homGenerator f (X + Y) = homGenerator (I' := I') f X + homGenerator (I' := I') f Y := by
  refine homGenerator_eq_of_forall f fun t ↦ ?_
  have hG := ((map_continuous f).tendsto _).comp (tendsto_lieExp_smul_mul_lieExp_smul_pow X Y t)
  have hG' := tendsto_lieExp_smul_mul_lieExp_smul_pow
    (homGenerator (I' := I') f X) (homGenerator (I' := I') f Y) t
  refine tendsto_nhds_unique (hG.congr fun n ↦ ?_) hG'
  rw [comp_apply, map_pow, map_mul, map_lieExp_smul (I' := I'), map_lieExp_smul (I' := I')]

/-- The generator map as a linear map. -/
private def homGeneratorLinearMap (f : G →ₜ* G') :
    LeftInvariantDerivation I G →ₗ[ℝ] LeftInvariantDerivation I' G' where
  toFun := homGenerator f
  map_add' := homGenerator_add f
  map_smul' := homGenerator_smul f

end Generator

/-- **Automatic smoothness.** A continuous homomorphism between finite-dimensional real Lie groups
is smooth. Near the identity it is `lieExp ∘ L ∘ lieLog` for the linear map `L` sending a
left-invariant derivation `X` to the generator of the one-parameter subgroup
`t ↦ f (lieExp (t • X))`. -/
theorem contMDiff_of_continuous_monoidHom {F : Type*} [FunLike F G G'] [MonoidHomClass F G G']
    (f : F) (hf : Continuous f) : ContMDiff I I' ∞ f := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  let _ : T2Space G' := t2Space_of_lieGroup (I := I') (n := ∞)
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint
  let φ : G →ₜ* G' := ⟨MonoidHom.ofClass f, hf⟩
  let L := LinearMap.toContinuousLinearMap (homGeneratorLinearMap (I := I) (I' := I') φ)
  have hev : (fun g ↦ lieExp (L (lieLog (I := I) g))) =ᶠ[𝓝 1] f := by
    filter_upwards [eventually_lieExp_lieLog (I := I) (G := G)] with g hg
    have h := map_lieExp_smul (I' := I') φ (lieLog (I := I) g) 1
    rw [one_smul, one_smul, hg] at h
    exact h.symm
  have hsmooth : ContMDiffAt I I' ∞ (fun g ↦ lieExp (L (lieLog (I := I) g))) 1 :=
    (contMDiff_lieExp (I := I') (G := G')).contMDiffAt.comp 1
      (L.contDiff.contMDiff.contMDiffAt.comp 1 (contMDiffAt_lieLog_one (I := I) (G := G)))
  exact contMDiff_of_contMDiffAt_mulHom f (hsmooth.congr_of_eventuallyEq hev.symm)

end TauCeti.Lie

namespace ContinuousMonoidHom

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [LieGroup I ∞ G] [LieGroup I' ∞ G']

variable (I I') in
/-- A continuous homomorphism between finite-dimensional real Lie groups, as a smooth monoid
morphism (`TauCeti.Lie.contMDiff_of_continuous_monoidHom`). -/
def toContMDiffMonoidMorphism (f : G →ₜ* G') : ContMDiffMonoidMorphism I I' ∞ G G' where
  toMonoidHom := f.toMonoidHom
  contMDiff_toFun := TauCeti.Lie.contMDiff_of_continuous_monoidHom f f.continuous

@[simp]
theorem coe_toContMDiffMonoidMorphism (f : G →ₜ* G') :
    ⇑(f.toContMDiffMonoidMorphism I I') = f :=
  (rfl)

end ContinuousMonoidHom
