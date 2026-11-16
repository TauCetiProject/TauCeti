/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Functor
public import Mathlib.Algebra.Lie.Prod

/-!
# The Lie algebra of a product Lie group

For finite-dimensional real Lie groups, the two projection homomorphisms identify the native
Lie algebra of the product with the product of the native Lie algebras. The groups may have
arbitrary models with corners and independent model and carrier universes.

## Main results

* `TauCeti.Lie.prodLieEquiv`: the Lie-algebra equivalence induced by the two projections.
* `TauCeti.Lie.prodLieEquiv_apply`: its two components are the native Lie maps of the projections.
* `TauCeti.Lie.lieMap_fst_prodLieEquiv_symm` and
  `TauCeti.Lie.lieMap_snd_prodLieEquiv_symm`: the projections recover the two input derivations.

## References

* A. Kirillov Jr., *An Introduction to Lie Groups and Lie Algebras*, Cambridge Studies in
  Advanced Mathematics 113, Cambridge University Press (2008), Chapter 3, §3.8, proof of
  Theorem 3.41, p.42, for the product Lie-algebra identification.
-/

public noncomputable section

open scoped Manifold ContDiff

namespace TauCeti.Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G'] [LieGroup I' ∞ G']

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']

private def evalModel : LeftInvariantDerivation I G ≃ₗ[ℝ] E :=
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  leftInvariantDerivationLinearIsometryEquivModelVectorSpace.toLinearEquiv

private theorem eval_fst (D : LeftInvariantDerivation (I.prod I') (G × G')) :
    evalModel (lieMap (ContMDiffMonoidMorphism.fst (I := I) (I' := I')) D) =
      (evalModel D).1 := by
  have h := leftInvariantDerivationLinearIsometryEquivModelVectorSpace_lieMap
    (ContMDiffMonoidMorphism.fst (I := I) (I' := I')) D
  dsimp only at h
  rw [ContMDiffMonoidMorphism.coe_fst, mfderiv_fst] at h
  -- `evalModel` is the canonical isometry viewed as a linear equivalence. Its coercion and
  -- the tangent-space first projection reduce to the model-space functions in this goal.
  exact h

private theorem eval_snd (D : LeftInvariantDerivation (I.prod I') (G × G')) :
    evalModel (lieMap (ContMDiffMonoidMorphism.snd (I := I) (I' := I')) D) =
      (evalModel D).2 := by
  have h := leftInvariantDerivationLinearIsometryEquivModelVectorSpace_lieMap
    (ContMDiffMonoidMorphism.snd (I := I) (I' := I')) D
  dsimp only at h
  rw [ContMDiffMonoidMorphism.coe_snd, mfderiv_snd] at h
  -- The isometry's `toLinearEquiv` coercion and the tangent-space second projection are
  -- definitionally the model-space functions appearing in the goal.
  exact h

private def prodLieHom : LeftInvariantDerivation (I.prod I') (G × G') →ₗ⁅ℝ⁆
    LeftInvariantDerivation I G × LeftInvariantDerivation I' G' :=
  (lieMap ContMDiffMonoidMorphism.fst).prod (lieMap ContMDiffMonoidMorphism.snd)

private theorem prodLieHom_injective :
    Function.Injective (prodLieHom (I := I) (I' := I') (G := G) (G' := G')) := by
  intro D F h
  apply evalModel.injective
  apply Prod.ext
  · have h1 := congrArg (fun P ↦ evalModel (I := I) (G := G) P.1) h
    simpa only [prodLieHom, LieHom.prod_apply, eval_fst] using h1
  · have h2 := congrArg (fun P ↦ evalModel (I := I') (G := G') P.2) h
    simpa only [prodLieHom, LieHom.prod_apply, eval_snd] using h2

private theorem prodLieHom_surjective :
    Function.Surjective (prodLieHom (I := I) (I' := I') (G := G) (G' := G')) := by
  rintro ⟨X, Y⟩
  let Z := (evalModel (I := I.prod I') (G := G × G')).symm
    (evalModel X, evalModel Y)
  refine ⟨Z, Prod.ext ?_ ?_⟩
  · apply (evalModel (I := I) (G := G)).injective
    simp only [prodLieHom, LieHom.prod_apply, eval_fst, Z, LinearEquiv.apply_symm_apply]
  · apply (evalModel (I := I') (G := G')).injective
    simp only [prodLieHom, LieHom.prod_apply, eval_snd, Z, LinearEquiv.apply_symm_apply]

/-- The native Lie algebra of a product is the product of the two native Lie algebras. -/
def prodLieEquiv : LeftInvariantDerivation (I.prod I') (G × G') ≃ₗ⁅ℝ⁆
    LeftInvariantDerivation I G × LeftInvariantDerivation I' G' :=
  LieEquiv.ofBijective prodLieHom ⟨prodLieHom_injective, prodLieHom_surjective⟩

/-- The product Lie equivalence acts by the two projection Lie maps. -/
@[simp]
theorem prodLieEquiv_apply (D : LeftInvariantDerivation (I.prod I') (G × G')) :
    prodLieEquiv D =
      (lieMap ContMDiffMonoidMorphism.fst D, lieMap ContMDiffMonoidMorphism.snd D) := by
  rfl

/-- The first projection recovers the first component of the inverse product Lie equivalence. -/
@[simp]
theorem lieMap_fst_prodLieEquiv_symm
    (p : LeftInvariantDerivation I G × LeftInvariantDerivation I' G') :
    lieMap ContMDiffMonoidMorphism.fst (prodLieEquiv.symm p) = p.1 := by
  have h := congrArg Prod.fst
    ((prodLieEquiv (I := I) (I' := I') (G := G) (G' := G')).apply_symm_apply p)
  simpa only [prodLieEquiv_apply] using h

/-- The second projection recovers the second component of the inverse product Lie equivalence. -/
@[simp]
theorem lieMap_snd_prodLieEquiv_symm
    (p : LeftInvariantDerivation I G × LeftInvariantDerivation I' G') :
    lieMap ContMDiffMonoidMorphism.snd (prodLieEquiv.symm p) = p.2 := by
  have h := congrArg Prod.snd
    ((prodLieEquiv (I := I) (I' := I') (G := G) (G' := G')).apply_symm_apply p)
  simpa only [prodLieEquiv_apply] using h

end TauCeti.Lie
