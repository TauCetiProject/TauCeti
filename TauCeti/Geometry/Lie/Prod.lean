/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.ContinuousFunctor
public import Mathlib.Algebra.Lie.Prod
import TauCeti.Algebra.Lie.Basic
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Prod

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
* `TauCeti.Lie.prodLieEquiv_continuousMonoidHom_lieMap_prod`,
  `TauCeti.Lie.prodLieEquiv_continuousMonoidHom_lieMap_inl`,
  `TauCeti.Lie.prodLieEquiv_continuousMonoidHom_lieMap_inr`, and
  `TauCeti.Lie.prodLieEquiv_symm_eq_add`: evaluation on product homomorphisms and factor
  inclusions, and the additive formula for the inverse equivalence.
* `TauCeti.Lie.lieMap_inl_add_lieMap_inr`: a derivation of the product is the sum of the images of
  its components under the inclusions of the factors.
* `TauCeti.Lie.lieMap_noncommCoprod`: the Lie map of `(g, g') ↦ φ g * ψ g'` for commuting smooth
  homomorphisms `φ` and `ψ` is the sum of their Lie maps on the two components.

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
      (lieMap ContMDiffMonoidMorphism.fst D, lieMap ContMDiffMonoidMorphism.snd D) :=
  LieEquiv.ofBijective_apply _ _ D

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

/-- The first smooth projection Lie map applied to the Lie map of a continuous product
homomorphism recovers the first component's Lie map. -/
@[simp]
theorem lieMap_fst_continuousMonoidHom_lieMap_prod
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
    {K : Type*} [TopologicalSpace K] [ChartedSpace H'' K] [Group K] [LieGroup I'' ∞ K]
    (f : K →ₜ* G) (g : K →ₜ* G') (D : LeftInvariantDerivation I'' K) :
    lieMap (ContMDiffMonoidMorphism.fst (I := I) (I' := I') (G := G) (G' := G'))
      (ContinuousMonoidHom.lieMap (I := I'') (I' := I.prod I') (f.prod g) D) =
      ContinuousMonoidHom.lieMap (I := I'') (I' := I) f D := by
  have h := ContinuousMonoidHom.lieMap_comp_apply (I := I'') (I' := I.prod I') (I'' := I)
    (f.prod g) (ContinuousMonoidHom.fst G G') D
  rw [ContinuousMonoidHom.fst_comp_prod,
    ContinuousMonoidHom.lieMap_def (I := I.prod I') (I' := I) (ContinuousMonoidHom.fst G G'),
    ContinuousMonoidHom.toContMDiffMonoidMorphism_fst] at h
  exact h.symm

/-- The second smooth projection Lie map applied to the Lie map of a continuous product
homomorphism recovers the second component's Lie map. -/
@[simp]
theorem lieMap_snd_continuousMonoidHom_lieMap_prod
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
    {K : Type*} [TopologicalSpace K] [ChartedSpace H'' K] [Group K] [LieGroup I'' ∞ K]
    (f : K →ₜ* G) (g : K →ₜ* G') (D : LeftInvariantDerivation I'' K) :
    lieMap (ContMDiffMonoidMorphism.snd (I := I) (I' := I') (G := G) (G' := G'))
      (ContinuousMonoidHom.lieMap (I := I'') (I' := I.prod I') (f.prod g) D) =
      ContinuousMonoidHom.lieMap (I := I'') (I' := I') g D := by
  have h := ContinuousMonoidHom.lieMap_comp_apply (I := I'') (I' := I.prod I') (I'' := I')
    (f.prod g) (ContinuousMonoidHom.snd G G') D
  rw [ContinuousMonoidHom.snd_comp_prod,
    ContinuousMonoidHom.lieMap_def (I := I.prod I') (I' := I') (ContinuousMonoidHom.snd G G'),
    ContinuousMonoidHom.toContMDiffMonoidMorphism_snd] at h
  exact h.symm

/-- The first smooth projection Lie map undoes the continuous left factor inclusion on Lie
algebras. -/
@[simp]
theorem lieMap_fst_continuousMonoidHom_lieMap_inl (X : LeftInvariantDerivation I G) :
    lieMap (ContMDiffMonoidMorphism.fst (I := I) (I' := I') (G := G) (G' := G'))
      (ContinuousMonoidHom.lieMap (I := I) (I' := I.prod I')
        (ContinuousMonoidHom.inl G G') X) = X := by
  rw [ContinuousMonoidHom.inl, lieMap_fst_continuousMonoidHom_lieMap_prod,
    ContinuousMonoidHom.lieMap_id, one_apply_eq_self]

/-- The first smooth projection Lie map kills the continuous right factor inclusion on Lie
algebras. -/
@[simp]
theorem lieMap_fst_continuousMonoidHom_lieMap_inr (Y : LeftInvariantDerivation I' G') :
    lieMap (ContMDiffMonoidMorphism.fst (I := I) (I' := I') (G := G) (G' := G'))
      (ContinuousMonoidHom.lieMap (I := I') (I' := I.prod I')
        (ContinuousMonoidHom.inr G G') Y) = 0 := by
  rw [ContinuousMonoidHom.inr, lieMap_fst_continuousMonoidHom_lieMap_prod,
    ContinuousMonoidHom.lieMap_one, zero_apply]

/-- The second smooth projection Lie map kills the continuous left factor inclusion on Lie
algebras. -/
@[simp]
theorem lieMap_snd_continuousMonoidHom_lieMap_inl (X : LeftInvariantDerivation I G) :
    lieMap (ContMDiffMonoidMorphism.snd (I := I) (I' := I') (G := G) (G' := G'))
      (ContinuousMonoidHom.lieMap (I := I) (I' := I.prod I')
        (ContinuousMonoidHom.inl G G') X) = 0 := by
  rw [ContinuousMonoidHom.inl, lieMap_snd_continuousMonoidHom_lieMap_prod,
    ContinuousMonoidHom.lieMap_one, zero_apply]

/-- The second smooth projection Lie map undoes the continuous right factor inclusion on Lie
algebras. -/
@[simp]
theorem lieMap_snd_continuousMonoidHom_lieMap_inr (Y : LeftInvariantDerivation I' G') :
    lieMap (ContMDiffMonoidMorphism.snd (I := I) (I' := I') (G := G) (G' := G'))
      (ContinuousMonoidHom.lieMap (I := I') (I' := I.prod I')
        (ContinuousMonoidHom.inr G G') Y) = Y := by
  rw [ContinuousMonoidHom.inr, lieMap_snd_continuousMonoidHom_lieMap_prod,
    ContinuousMonoidHom.lieMap_id, one_apply_eq_self]

/-- In product Lie-algebra coordinates, the Lie map of a product of continuous homomorphisms
evaluates componentwise. -/
theorem prodLieEquiv_continuousMonoidHom_lieMap_prod
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
    {K : Type*} [TopologicalSpace K] [ChartedSpace H'' K] [Group K] [LieGroup I'' ∞ K]
    (f : K →ₜ* G) (g : K →ₜ* G') (D : LeftInvariantDerivation I'' K) :
    prodLieEquiv (ContinuousMonoidHom.lieMap (I := I'') (I' := I.prod I') (f.prod g) D) =
      (ContinuousMonoidHom.lieMap (I := I'') (I' := I) f D,
        ContinuousMonoidHom.lieMap (I := I'') (I' := I') g D) := by
  simp

/-- The left factor inclusion maps a derivation to the first summand of the product Lie algebra. -/
theorem prodLieEquiv_continuousMonoidHom_lieMap_inl (X : LeftInvariantDerivation I G) :
    prodLieEquiv
        (ContinuousMonoidHom.lieMap (I := I) (I' := I.prod I')
          (ContinuousMonoidHom.inl G G') X) =
      (X, 0) := by
  simp

/-- The right factor inclusion maps a derivation to the second summand of the product Lie
algebra. -/
theorem prodLieEquiv_continuousMonoidHom_lieMap_inr (Y : LeftInvariantDerivation I' G') :
    prodLieEquiv
        (ContinuousMonoidHom.lieMap (I := I') (I' := I.prod I')
          (ContinuousMonoidHom.inr G G') Y) =
      (0, Y) := by
  simp

/-- The inverse product Lie equivalence reconstructs a pair of derivations as the sum of their
images under the two factor inclusions. -/
theorem prodLieEquiv_symm_eq_add
    (p : LeftInvariantDerivation I G × LeftInvariantDerivation I' G') :
    prodLieEquiv.symm p =
      ContinuousMonoidHom.lieMap (I := I) (I' := I.prod I')
          (ContinuousMonoidHom.inl G G') p.1 +
        ContinuousMonoidHom.lieMap (I := I') (I' := I.prod I')
          (ContinuousMonoidHom.inr G G') p.2 := by
  apply EquivLike.injective prodLieEquiv
  rw [prodLieEquiv.apply_symm_apply, map_add, prodLieEquiv_continuousMonoidHom_lieMap_inl,
    prodLieEquiv_continuousMonoidHom_lieMap_inr]
  ext <;> simp

/-- Pushing the inverse product Lie equivalence forward along a continuous homomorphism out of
`G × G'` evaluates by adding the Lie maps of its restrictions to the two factors. -/
theorem lieMap_prodLieEquiv_symm
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
    {K : Type*} [TopologicalSpace K] [ChartedSpace H'' K] [Group K] [LieGroup I'' ∞ K]
    (f : G × G' →ₜ* K)
    (p : LeftInvariantDerivation I G × LeftInvariantDerivation I' G') :
    ContinuousMonoidHom.lieMap (I := I.prod I') (I' := I'') f (prodLieEquiv.symm p) =
      ContinuousMonoidHom.lieMap (I := I) (I' := I'')
          (f.comp (ContinuousMonoidHom.inl G G')) p.1 +
        ContinuousMonoidHom.lieMap (I := I') (I' := I'')
          (f.comp (ContinuousMonoidHom.inr G G')) p.2 := by
  rw [prodLieEquiv_symm_eq_add, map_add,
    ContinuousMonoidHom.lieMap_comp_apply (I := I) (I' := I.prod I') (I'' := I'')
      (ContinuousMonoidHom.inl G G') f p.1,
    ContinuousMonoidHom.lieMap_comp_apply (I := I') (I' := I.prod I') (I'' := I'')
      (ContinuousMonoidHom.inr G G') f p.2]

/-- If a continuous homomorphism out of `G × G'` has injective Lie map, so does its restriction to
the first factor. -/
theorem lieMap_comp_inl_injective
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
    {K : Type*} [TopologicalSpace K] [ChartedSpace H'' K] [Group K] [LieGroup I'' ∞ K]
    {f : G × G' →ₜ* K}
    (hf : Function.Injective (ContinuousMonoidHom.lieMap (I := I.prod I') (I' := I'') f)) :
    Function.Injective
      (ContinuousMonoidHom.lieMap (I := I) (I' := I'')
        (f.comp (ContinuousMonoidHom.inl G G'))) := by
  rw [ContinuousMonoidHom.lieMap_comp (I := I) (I' := I.prod I') (I'' := I'')
    (ContinuousMonoidHom.inl G G') f, LieHom.coe_comp]
  refine hf.comp fun X Y hXY ↦ ?_
  have h := congrArg (fun D ↦ (prodLieEquiv (I := I) (I' := I') (G := G) (G' := G') D).1) hXY
  simpa only [prodLieEquiv_continuousMonoidHom_lieMap_inl] using h

/-- If a continuous homomorphism out of `G × G'` has injective Lie map, so does its restriction to
the second factor. -/
theorem lieMap_comp_inr_injective
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
    {K : Type*} [TopologicalSpace K] [ChartedSpace H'' K] [Group K] [LieGroup I'' ∞ K]
    {f : G × G' →ₜ* K}
    (hf : Function.Injective (ContinuousMonoidHom.lieMap (I := I.prod I') (I' := I'') f)) :
    Function.Injective
      (ContinuousMonoidHom.lieMap (I := I') (I' := I'')
        (f.comp (ContinuousMonoidHom.inr G G'))) := by
  rw [ContinuousMonoidHom.lieMap_comp (I := I') (I' := I.prod I') (I'' := I'')
    (ContinuousMonoidHom.inr G G') f, LieHom.coe_comp]
  refine hf.comp fun X Y hXY ↦ ?_
  have h := congrArg (fun D ↦ (prodLieEquiv (I := I) (I' := I') (G := G) (G' := G') D).2) hXY
  simpa only [prodLieEquiv_continuousMonoidHom_lieMap_inr] using h

/-- The Lie map of a product homomorphism `f.prod g : K →ₜ* G × G'` is bijective if and only if the
paired Lie map `D ↦ (f.lieMap D, g.lieMap D)` is bijective. -/
theorem bijective_lieMap_prod_iff
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
    {K : Type*} [TopologicalSpace K] [ChartedSpace H'' K] [Group K] [LieGroup I'' ∞ K]
    (f : K →ₜ* G) (g : K →ₜ* G') :
    Function.Bijective (ContinuousMonoidHom.lieMap (I := I'') (I' := I.prod I') (f.prod g)) ↔
      Function.Bijective (fun D : LeftInvariantDerivation I'' K ↦
        (ContinuousMonoidHom.lieMap (I := I'') (I' := I) f D,
          ContinuousMonoidHom.lieMap (I := I'') (I' := I') g D)) := by
  have hcomp :
      (prodLieEquiv (I := I) (I' := I') (G := G) (G' := G') ∘
        ContinuousMonoidHom.lieMap (I := I'') (I' := I.prod I') (f.prod g)) =
        fun D ↦ (ContinuousMonoidHom.lieMap (I := I'') (I' := I) f D,
          ContinuousMonoidHom.lieMap (I := I'') (I' := I') g D) := by
    funext D
    exact prodLieEquiv_continuousMonoidHom_lieMap_prod f g D
  rw [← hcomp]
  exact ((prodLieEquiv (I := I) (I' := I') (G := G) (G' := G')).bijective.of_comp_iff' _).symm

/-- The first projection undoes the first inclusion on Lie algebras. -/
@[simp]
theorem lieMap_fst_lieMap_inl (X : LeftInvariantDerivation I G) :
    lieMap (ContMDiffMonoidMorphism.fst (I := I) (I' := I') (G := G) (G' := G'))
      (lieMap (ContMDiffMonoidMorphism.inl (I := I) (I' := I') (G := G) (G' := G')) X) = X := by
  rw [← LieHom.comp_apply, ← lieMap_comp, ContMDiffMonoidMorphism.fst_comp_inl, lieMap_id,
    one_apply_eq_self]

/-- The first projection kills the second inclusion on Lie algebras. -/
@[simp]
theorem lieMap_fst_lieMap_inr (Y : LeftInvariantDerivation I' G') :
    lieMap (ContMDiffMonoidMorphism.fst (I := I) (I' := I') (G := G) (G' := G'))
      (lieMap (ContMDiffMonoidMorphism.inr (I := I) (I' := I') (G := G) (G' := G')) Y) = 0 := by
  rw [← LieHom.comp_apply, ← lieMap_comp, ContMDiffMonoidMorphism.fst_comp_inr, lieMap_one,
    zero_apply]

/-- The second projection kills the first inclusion on Lie algebras. -/
@[simp]
theorem lieMap_snd_lieMap_inl (X : LeftInvariantDerivation I G) :
    lieMap (ContMDiffMonoidMorphism.snd (I := I) (I' := I') (G := G) (G' := G'))
      (lieMap (ContMDiffMonoidMorphism.inl (I := I) (I' := I') (G := G) (G' := G')) X) = 0 := by
  rw [← LieHom.comp_apply, ← lieMap_comp, ContMDiffMonoidMorphism.snd_comp_inl, lieMap_one,
    zero_apply]

/-- The second projection undoes the second inclusion on Lie algebras. -/
@[simp]
theorem lieMap_snd_lieMap_inr (Y : LeftInvariantDerivation I' G') :
    lieMap (ContMDiffMonoidMorphism.snd (I := I) (I' := I') (G := G) (G' := G'))
      (lieMap (ContMDiffMonoidMorphism.inr (I := I) (I' := I') (G := G) (G' := G')) Y) = Y := by
  rw [← LieHom.comp_apply, ← lieMap_comp, ContMDiffMonoidMorphism.snd_comp_inr, lieMap_id,
    one_apply_eq_self]

/-- A left-invariant derivation of a product is the sum of the images of its two components under
the inclusions of the factors. -/
theorem lieMap_inl_add_lieMap_inr (D : LeftInvariantDerivation (I.prod I') (G × G')) :
    lieMap ContMDiffMonoidMorphism.inl (lieMap ContMDiffMonoidMorphism.fst D) +
      lieMap ContMDiffMonoidMorphism.inr (lieMap ContMDiffMonoidMorphism.snd D) = D := by
  refine EquivLike.injective (prodLieEquiv (I := I) (I' := I') (G := G) (G' := G')) ?_
  simp

/-- The Lie map of the product `(g, g') ↦ φ g * ψ g'` of two smooth homomorphisms with commuting
images is the sum of their Lie maps on the two components. -/
@[simp]
theorem lieMap_noncommCoprod
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
    {G'' : Type*} [TopologicalSpace G''] [ChartedSpace H'' G''] [Group G''] [LieGroup I'' ∞ G'']
    (φ : ContMDiffMonoidMorphism I I'' ∞ G G'') (ψ : ContMDiffMonoidMorphism I' I'' ∞ G' G'')
    (h : ∀ g g', Commute (φ g) (ψ g')) (D : LeftInvariantDerivation (I.prod I') (G × G')) :
    lieMap (φ.noncommCoprod ψ h) D =
      lieMap φ (lieMap ContMDiffMonoidMorphism.fst D) +
        lieMap ψ (lieMap ContMDiffMonoidMorphism.snd D) := by
  conv_lhs => rw [← lieMap_inl_add_lieMap_inr D]
  rw [map_add]
  congr 1
  · rw [← LieHom.comp_apply, ← lieMap_comp, ContMDiffMonoidMorphism.noncommCoprod_comp_inl]
  · rw [← LieHom.comp_apply, ← lieMap_comp, ContMDiffMonoidMorphism.noncommCoprod_comp_inr]

end TauCeti.Lie
