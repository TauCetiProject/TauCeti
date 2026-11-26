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

In particular an injective continuous homomorphism, whose kernel is trivial, has injective
differential at the identity, where the differential is the Lie map. Since `f (g * k) = f g * f k`,
left translations carry this to every point, so `f` is an immersion.

## Main results

* `ContinuousMonoidHom.lieMap_injective_of_discreteTopology_ker`: a continuous homomorphism with
  discrete kernel has injective Lie map.
* `ContinuousMonoidHom.injective_mfderiv_of_injective`,
  `ContinuousMonoidHom.isImmersion_of_injective`: an injective continuous homomorphism has
  injective differential at every point, so it is an immersion.

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

/-- **An injective continuous homomorphism has injective differential** at every point. Its kernel
is trivial, hence discrete, so its Lie map, which is its differential at the identity, is injective
(`ContinuousMonoidHom.lieMap_injective_of_discreteTopology_ker`). Left translation by `g` and by
`f g` carries this to the differential at `g`, since `f (g * k) = f g * f k`. -/
theorem injective_mfderiv_of_injective (f : G →ₜ* G') (hf : Function.Injective f) (g : G) :
    Function.Injective (mfderiv I I' f g) := by
  have : DiscreteTopology f.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 hf]
    infer_instance
  have hd := contMDiff_of_continuous_monoidHom (I := I) (I' := I') f f.continuous
  -- At the identity the differential is the Lie map, read through evaluation at the identity.
  have h1 : Function.Injective (mfderiv I I' f 1) := by
    let e := leftInvariantDerivationLieEquivGroupLieAlgebra
      (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))
    let e' := leftInvariantDerivationLieEquivGroupLieAlgebra
      (ContMDiffMul.isInteriorPoint (I := I') (n := ∞) (by simp) (1 : G'))
    intro v w hvw
    obtain ⟨X, rfl⟩ := e.surjective v
    obtain ⟨Y, rfl⟩ := e.surjective w
    have hX := leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap
      (f.toContMDiffMonoidMorphism I I') X
    have hY := leftInvariantDerivationLieEquivGroupLieAlgebra_lieMap
      (f.toContMDiffMonoidMorphism I I') Y
    rw [coe_toContMDiffMonoidMorphism, ← lieMap_def] at hX hY
    exact congrArg e (lieMap_injective_of_discreteTopology_ker (I := I) (I' := I') f
      (e'.injective (hX.trans (hvw.trans hY.symm))))
  -- Left translations carry the identity to `g`, and `f 1 = 1` to `f g`.
  have hcomp : (fun k ↦ f (g * k)) = (f g * ·) ∘ f := funext fun k ↦ map_mul f g k
  have hchain (w : TangentSpace I (1 : G)) :
      mfderiv I I' f g (mfderiv I I (g * ·) 1 w) =
        mfderiv I' I' (f g * ·) 1 (mfderiv I I' f 1 w) := by
    rw [← mfderiv_comp_apply_of_eq 1 (hd.mdifferentiableAt (by simp)) mdifferentiableAt_mul_left
      (mul_one g), ← mfderiv_comp_apply_of_eq 1 mdifferentiableAt_mul_left
      (hd.mdifferentiableAt (by simp)) (map_one f), Function.comp_def, hcomp]
  -- The differential of left translation at the identity is injective.
  have hinj : Function.Injective (mfderiv I' I' (f g * ·) 1) := fun a b hab ↦
    (TauCeti.mulInvariantVectorFieldEquiv I' (f g)).injective (by
      rwa [TauCeti.mulInvariantVectorFieldEquiv_apply, TauCeti.mulInvariantVectorFieldEquiv_apply,
        GroupLieAlgebra.mulInvariantVectorField_apply,
        GroupLieAlgebra.mulInvariantVectorField_apply])
  intro v w hvw
  obtain ⟨v, rfl⟩ := (TauCeti.mulInvariantVectorFieldEquiv I g).surjective v
  obtain ⟨w, rfl⟩ := (TauCeti.mulInvariantVectorFieldEquiv I g).surjective w
  rw [TauCeti.mulInvariantVectorFieldEquiv_apply, TauCeti.mulInvariantVectorFieldEquiv_apply,
    GroupLieAlgebra.mulInvariantVectorField_apply, GroupLieAlgebra.mulInvariantVectorField_apply,
    hchain, hchain] at hvw
  exact congrArg _ (h1 (hinj hvw))

/-- **An injective continuous homomorphism is an immersion.** It is smooth by automatic smoothness
(`TauCeti.Lie.contMDiff_of_continuous_monoidHom`), and its differential is injective at every point
(`ContinuousMonoidHom.injective_mfderiv_of_injective`). -/
theorem isImmersion_of_injective [I.Boundaryless] [I'.Boundaryless] (f : G →ₜ* G')
    (hf : Function.Injective f) : Manifold.IsImmersion I I' ∞ f :=
  (contMDiff_of_continuous_monoidHom f f.continuous).isImmersion_of_injective_mfderiv (by simp)
    (injective_mfderiv_of_injective f hf)

end ContinuousMonoidHom
