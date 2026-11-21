/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.ContinuousFunctor
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
* `TauCeti.Lie.prodLieEquiv_continuousMonoidHom_lieMap_prod`,
  `TauCeti.Lie.prodLieEquiv_continuousMonoidHom_lieMap_inl`,
  `TauCeti.Lie.prodLieEquiv_continuousMonoidHom_lieMap_inr`, and
  `TauCeti.Lie.prodLieEquiv_symm_eq_add`: evaluation on product homomorphisms and factor
  inclusions, and the additive formula for the inverse equivalence.

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
  rw [prodLieEquiv_apply,
    ← ContinuousMonoidHom.toContMDiffMonoidMorphism_fst (I := I) (I' := I') (G := G) (G' := G'),
    ← ContinuousMonoidHom.toContMDiffMonoidMorphism_snd (I := I) (I' := I') (G := G) (G' := G'),
    ← ContinuousMonoidHom.lieMap_def, ← ContinuousMonoidHom.lieMap_def]
  have hfst : (ContinuousMonoidHom.fst G G').comp (f.prod g) = f := by
    apply ContinuousMonoidHom.ext; intro x; rfl
  have hsnd : (ContinuousMonoidHom.snd G G').comp (f.prod g) = g := by
    apply ContinuousMonoidHom.ext; intro x; rfl
  have h1 := LieHom.congr_fun
    (ContinuousMonoidHom.lieMap_comp (I := I'') (I' := I.prod I') (I'' := I)
      (f.prod g) (ContinuousMonoidHom.fst G G')) D
  have h2 := LieHom.congr_fun
    (ContinuousMonoidHom.lieMap_comp (I := I'') (I' := I.prod I') (I'' := I')
      (f.prod g) (ContinuousMonoidHom.snd G G')) D
  rw [hfst, LieHom.comp_apply] at h1
  rw [hsnd, LieHom.comp_apply] at h2
  exact Prod.ext h1.symm h2.symm

/-- The left factor inclusion maps a derivation to the first summand of the product Lie algebra. -/
theorem prodLieEquiv_continuousMonoidHom_lieMap_inl (X : LeftInvariantDerivation I G) :
    prodLieEquiv
        (ContinuousMonoidHom.lieMap (I := I) (I' := I.prod I')
          (ContinuousMonoidHom.inl G G') X) =
      (X, 0) := by
  have hinl : ContinuousMonoidHom.inl G G' = (ContinuousMonoidHom.id G).prod 1 := by
    apply ContinuousMonoidHom.ext; intro x; rfl
  rw [hinl, prodLieEquiv_continuousMonoidHom_lieMap_prod, ContinuousMonoidHom.lieMap_id,
    ContinuousMonoidHom.lieMap_one, one_apply_eq_self, zero_apply]

/-- The right factor inclusion maps a derivation to the second summand of the product Lie
algebra. -/
theorem prodLieEquiv_continuousMonoidHom_lieMap_inr (Y : LeftInvariantDerivation I' G') :
    prodLieEquiv
        (ContinuousMonoidHom.lieMap (I := I') (I' := I.prod I')
          (ContinuousMonoidHom.inr G G') Y) =
      (0, Y) := by
  have hinr : ContinuousMonoidHom.inr G G' =
      (1 : G' →ₜ* G).prod (ContinuousMonoidHom.id G') := by
    apply ContinuousMonoidHom.ext; intro y; rfl
  rw [hinr, prodLieEquiv_continuousMonoidHom_lieMap_prod, ContinuousMonoidHom.lieMap_one,
    ContinuousMonoidHom.lieMap_id, zero_apply, one_apply_eq_self]

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
  rw [prodLieEquiv_symm_eq_add, map_add]
  have h1 := LieHom.congr_fun
    (ContinuousMonoidHom.lieMap_comp (I := I) (I' := I.prod I') (I'' := I'')
      (ContinuousMonoidHom.inl G G') f) p.1
  have h2 := LieHom.congr_fun
    (ContinuousMonoidHom.lieMap_comp (I := I') (I' := I.prod I') (I'' := I'')
      (ContinuousMonoidHom.inr G G') f) p.2
  rw [LieHom.comp_apply] at h1 h2
  rw [← h1, ← h2]

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
  intro X Y hXY
  have h : ContinuousMonoidHom.lieMap (I := I.prod I') (I' := I'') f (prodLieEquiv.symm (X, 0)) =
      ContinuousMonoidHom.lieMap (I := I.prod I') (I' := I'') f (prodLieEquiv.symm (Y, 0)) := by
    rw [lieMap_prodLieEquiv_symm, lieMap_prodLieEquiv_symm, map_zero, add_zero, add_zero, hXY]
  exact (Prod.mk.inj (EquivLike.injective prodLieEquiv.symm (hf h))).1

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
  intro X Y hXY
  have h : ContinuousMonoidHom.lieMap (I := I.prod I') (I' := I'') f (prodLieEquiv.symm (0, X)) =
      ContinuousMonoidHom.lieMap (I := I.prod I') (I' := I'') f (prodLieEquiv.symm (0, Y)) := by
    rw [lieMap_prodLieEquiv_symm, lieMap_prodLieEquiv_symm, map_zero, zero_add, zero_add, hXY]
  exact (Prod.mk.inj (EquivLike.injective prodLieEquiv.symm (hf h))).2

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

end TauCeti.Lie
