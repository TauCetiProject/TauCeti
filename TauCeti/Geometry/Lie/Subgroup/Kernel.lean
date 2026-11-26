/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.ContinuousFunctor
public import TauCeti.Geometry.Lie.Subgroup.Embedded
public import TauCeti.Geometry.Lie.InvariantVectorField.Basic
import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# Lie maps of homomorphisms with discrete kernel

If a continuous homomorphism `f : G → G'` of finite-dimensional real Lie groups has discrete kernel,
then its Lie map `df` is injective. For `df X = 0` the one-parameter subgroup `t ↦ exp(t X)` lies in
`ker f`, so `X` lies in the Lie algebra of the closed subgroup `ker f`, which is trivial because
`ker f` is discrete (`TauCeti.Lie.discreteTopology_iff_lieSubalgebraOfSubgroup_eq_bot`).

The Lie map is the differential at the identity. A homomorphism carries left-invariant vector
fields to left-invariant vector fields, so such a homomorphism has injective differential at every
point and is an immersion. In particular this applies to injective continuous homomorphisms, whose
kernel is trivial.

## Main results

* `ContinuousMonoidHom.lieMap_injective_of_discreteTopology_ker`: a continuous homomorphism with
  discrete kernel has injective Lie map.
* `ContinuousMonoidHom.injective_mfderiv_of_discreteTopology_ker`,
  `ContinuousMonoidHom.isImmersion_of_discreteTopology_ker`: a continuous homomorphism with discrete
  kernel has injective differential at every point, so it is an immersion.
* `ContinuousMonoidHom.isImmersion_of_injective`: in particular an injective continuous
  homomorphism is an immersion.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter I, § 3 (The Exponential Map).
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace ContinuousMonoidHom

open TauCeti.Lie

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [LieGroup I ∞ G] [LieGroup I' ∞ G']

/-- **A continuous homomorphism with discrete kernel has injective Lie map.** In particular the Lie
map of a homomorphism with finite kernel is injective. -/
theorem lieMap_injective_of_discreteTopology_ker (f : G →ₜ* G') [DiscreteTopology f.ker] :
    Function.Injective (lieMap (I := I) (I' := I') f) := by
  refine (injective_iff_map_eq_zero (lieMap (I := I) (I' := I') f).toLinearMap).2 fun X hX ↦ ?_
  have hX' : lieMap (I := I) (I' := I') f X = 0 := hX
  -- The exponentials of `G` and `G'` need these instances; they hold for every Lie group.
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
  have : T2Space G' := I'.t2Space_of_lieGroup ∞
  have : BoundarylessManifold I' G' := ContMDiffMul.boundarylessManifold
  -- The one-parameter subgroup through `X` lies in the kernel of `f`.
  have hker (t : ℝ) : lieExp (I := I) (G := G) (t • X) ∈ f.ker := by
    rw [MonoidHom.mem_ker, ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_ofClass,
      map_lieExp (I' := I'), map_smul, hX', smul_zero, lieExp_zero]
  -- So `X` lies in the Lie algebra of the closed discrete subgroup `ker f`, which is trivial.
  have hclosed : IsClosed (f.ker : Set G) := isClosed_singleton.preimage f.continuous
  have hmem := mem_lieSubalgebraOfSubgroup_of_forall (K := f.ker) hker
  rwa [(discreteTopology_iff_lieSubalgebraOfSubgroup_eq_bot (I := I) hclosed).1 inferInstance,
    LieSubalgebra.mem_bot] at hmem

/-- **A continuous homomorphism with discrete kernel has injective differential** at every point.
Its Lie map, which is its differential at the identity, is injective
(`ContinuousMonoidHom.lieMap_injective_of_discreteTopology_ker`). The differential at `g` carries
the left-invariant vector field of `X` to that of its image
(`ContMDiffMonoidMorphism.mfderiv_mulInvariantVectorField`), so it is injective too. -/
theorem injective_mfderiv_of_discreteTopology_ker (f : G →ₜ* G') [DiscreteTopology f.ker]
    (g : G) : Function.Injective (mfderiv I I' f g) := by
  let φ := f.toContMDiffMonoidMorphism I I'
  -- At the identity the differential is the Lie map, read through evaluation at the identity.
  have h1 : Function.Injective (mfderiv I I' f 1) := by
    let e := leftInvariantDerivationLieEquivGroupLieAlgebra
      (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))
    let e' := leftInvariantDerivationLieEquivGroupLieAlgebra
      (ContMDiffMul.isInteriorPoint (I := I') (n := ∞) (by simp) (1 : G'))
    intro v w hvw
    obtain ⟨X, rfl⟩ := e.surjective v
    obtain ⟨Y, rfl⟩ := e.surjective w
    have hX := leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap φ X
    have hY := leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap φ Y
    rw [coe_toContMDiffMonoidMorphism, ← lieMap_def] at hX hY
    exact congrArg e (lieMap_injective_of_discreteTopology_ker (I := I) (I' := I') f
      (e'.injective (hX.trans (hvw.trans hY.symm))))
  -- Every tangent vector at `g` is the value of a left-invariant vector field, and the
  -- differential at `g` carries these fields to the fields of their images.
  intro v w hvw
  obtain ⟨X, rfl⟩ := TauCeti.exists_mulInvariantVectorField_eq (I := I) v
  obtain ⟨Y, rfl⟩ := TauCeti.exists_mulInvariantVectorField_eq (I := I) w
  have h := φ.mfderiv_mulInvariantVectorField g X
  rw [coe_toContMDiffMonoidMorphism, hvw, ← coe_toContMDiffMonoidMorphism (I := I) (I' := I'),
    φ.mfderiv_mulInvariantVectorField g Y, ← TauCeti.mulInvariantVectorFieldEquiv_apply,
    ← TauCeti.mulInvariantVectorFieldEquiv_apply] at h
  have hXY := (TauCeti.mulInvariantVectorFieldEquiv I' (φ g)).injective h
  rw [MonoidHom.groupLieAlgebraMap_apply, MonoidHom.groupLieAlgebraMap_apply,
    ContMDiffMonoidMorphism.coe_toMonoidHom, coe_toContMDiffMonoidMorphism] at hXY
  rw [h1 hXY.symm]

/-- **A continuous homomorphism with discrete kernel is an immersion.** It is smooth by automatic
smoothness (`TauCeti.Lie.contMDiff_of_continuous_monoidHom`), and its differential is injective at
every point (`ContinuousMonoidHom.injective_mfderiv_of_discreteTopology_ker`). -/
theorem isImmersion_of_discreteTopology_ker [I.Boundaryless] [I'.Boundaryless] (f : G →ₜ* G')
    [DiscreteTopology f.ker] : Manifold.IsImmersion I I' ∞ f :=
  (contMDiff_of_continuous_monoidHom f f.continuous).isImmersion_of_injective_mfderiv (by simp)
    (injective_mfderiv_of_discreteTopology_ker f)

/-- **An injective continuous homomorphism is an immersion**, since its kernel is trivial, hence
discrete (`ContinuousMonoidHom.isImmersion_of_discreteTopology_ker`). -/
theorem isImmersion_of_injective [I.Boundaryless] [I'.Boundaryless] (f : G →ₜ* G')
    (hf : Function.Injective f) : Manifold.IsImmersion I I' ∞ f := by
  have : DiscreteTopology f.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 hf]
    infer_instance
  exact isImmersion_of_discreteTopology_ker f

end ContinuousMonoidHom
