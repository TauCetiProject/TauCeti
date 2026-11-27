/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FiniteHopfModuleCat.RightRigid

/-!
# Duals of small models of finite Hopf modules

A finite-dimensional module can have a carrier in a larger universe than its scalar field.
`ofShrink` replaces it by an isomorphic module in the scalar field's universe. This file
compares the contragredient of that small model with the small model of the original
contragredient. The comparison intertwines the Hopf algebra actions, is natural in module
maps, and preserves evaluation and coevaluation.

The tensor comparison `shrinkTensorEquiv` and its coherence laws are in
`FiniteHopfModuleCat/Monoidal.lean`, where only a bialgebra is required. The dual comparison is
precomposition with the inverse shrinking equivalence; it uses the antipode action on functionals.
Together these comparisons retain the tensor and right-dual data under universe reduction.

The construction specializes `BialgebraModule.dualCongr` and its coevaluation transport
`BialgebraModule.tensorMap_comp_dualCoeval`, which uses dinaturality of native coevaluation
(`LinearMap.rTensor_comp_coevaluation`).
-/

public noncomputable section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace TauCeti.FiniteHopfModuleCat

open BialgebraModule

universe u v w w'

variable (k : Type u) [Field k] (H : Type v) [Ring H]

section Hopf

variable [HopfAlgebra k H]
variable (V : Type w) [AddCommGroup V] [Module k V] [Module H V]
  [IsScalarTower k H V] [Module.Finite k V]

/-- The contragredient of the small model is the small model of the contragredient.
On functionals the comparison is precomposition with the inverse shrinking equivalence. -/
def shrinkDualEquiv : dual (ofShrink k H V) ≃ₗ[H] ofShrink k H (Dual k H V) :=
  (dualCongr k H (ofShrinkEquiv k H V).symm).trans
    (ofShrinkEquiv k H (Dual k H V)).symm

/-- On the original dual, shrinking comparison is the contragredient equivalence. -/
@[simp↓]
theorem ofShrinkEquiv_shrinkDualEquiv (φ : dual (ofShrink k H V)) :
    ofShrinkEquiv k H (Dual k H V) (shrinkDualEquiv k H V φ) =
      dualCongr k H (ofShrinkEquiv k H V).symm φ :=
  (ofShrinkEquiv k H (Dual k H V)).apply_symm_apply _

/-- On the original module, the transported functional is precomposition with the inverse
shrinking equivalence. -/
-- Simplify the composite before the primitive shrink map expands into carrier casts.
@[simp↓]
theorem dualEquiv_ofShrinkEquiv_shrinkDualEquiv_apply (φ : dual (ofShrink k H V)) (x : V) :
    dualEquiv k H V (ofShrinkEquiv k H (Dual k H V) (shrinkDualEquiv k H V φ)) x =
      dualEquiv k H (ofShrink k H V) φ ((ofShrinkEquiv k H V).symm x) := by
  rw [ofShrinkEquiv_shrinkDualEquiv]
  exact dualEquiv_dualCongr_apply k H (ofShrinkEquiv k H V).symm φ x

/-- The inverse dual comparison preserves evaluation on the small model. -/
@[simp]
theorem dualEquiv_shrinkDualEquiv_symm_apply (φ : ofShrink k H (Dual k H V))
    (x : ofShrink k H V) :
    dualEquiv k H (ofShrink k H V) ((shrinkDualEquiv k H V).symm φ) x =
      dualEquiv k H V (ofShrinkEquiv k H (Dual k H V) φ) (ofShrinkEquiv k H V x) := by
  simpa only [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] using
    (dualEquiv_ofShrinkEquiv_shrinkDualEquiv_apply k H V ((shrinkDualEquiv k H V).symm φ)
      (ofShrinkEquiv k H V x)).symm

/-- Shrinking commutes with dual evaluation, through the tensor and unit comparisons. -/
theorem shrinkDualEquiv_evaluation :
    (shrinkDualEquiv k H V).toFiniteHopfModuleCatIso.hom ▷ ofShrink k H V ≫
        (shrinkTensorEquiv k H (Dual k H V) V).toFiniteHopfModuleCatIso.hom ≫
          shrinkHom k H (dualEval k H V) =
      dualEvaluation (ofShrink k H V) ≫
        (ofShrinkEquiv k H (Trivial k H)).symm.toFiniteHopfModuleCatIso.hom := by
  ext φ x
  simp only [hom_hom_comp, shrinkHom_hom_hom,
    LinearEquiv.toFiniteHopfModuleCatIso_hom_hom, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, whiskerRight_tmul, shrinkTensorEquiv_tmul,
    LinearEquiv.apply_symm_apply, dualEval_tmul, dualEquiv_ofShrinkEquiv_shrinkDualEquiv_apply,
    LinearEquiv.symm_apply_apply, dualEvaluation_hom_hom]
  exact (congrArg (ofShrinkEquiv k H (Trivial k H)).symm
    (dualEval_tmul k H (ofShrink k H V) φ x)).symm

/-- Shrinking commutes with dual coevaluation, through the tensor and unit comparisons. -/
theorem shrinkDualEquiv_coevaluation :
    (ofShrinkEquiv k H (Trivial k H)).symm.toFiniteHopfModuleCatIso.hom ≫
        shrinkHom k H (dualCoeval k H V) =
      dualCoevaluation (ofShrink k H V) ≫
        ofShrink k H V ◁ (shrinkDualEquiv k H V).toFiniteHopfModuleCatIso.hom ≫
          (shrinkTensorEquiv k H V (Dual k H V)).toFiniteHopfModuleCatIso.hom := by
  ext r
  apply (ofShrinkEquiv k H (Tensor k H V (Dual k H V))).injective
  simp only [hom_hom_comp, shrinkHom_hom_hom,
    LinearEquiv.toFiniteHopfModuleCatIso_hom_hom, LinearMap.coe_comp,
    Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    dualCoevaluation_hom_hom, whiskerLeft_hom_hom]
  -- Composition is pointwise on the canonical coproduct tensor carrier.
  change dualCoeval k H V r = ofShrinkEquiv k H (Tensor k H V (Dual k H V))
    (shrinkTensorEquiv k H V (Dual k H V)
      (tensorMap k H LinearMap.id (shrinkDualEquiv k H V).toLinearMap
        (dualCoeval k H (ofShrink k H V) r)))
  rw [ofShrinkEquiv_shrinkTensorEquiv]
  have h := LinearMap.congr_fun (tensorMap_comp k H
    (LinearMap.id : ofShrink k H V →ₗ[H] ofShrink k H V) (ofShrinkEquiv k H V).toLinearMap
    (shrinkDualEquiv k H V).toLinearMap (ofShrinkEquiv k H (Dual k H V)).toLinearMap)
      (dualCoeval k H (ofShrink k H V) r)
  simp only [LinearMap.comp_id] at h
  have hd : (ofShrinkEquiv k H (Dual k H V)).toLinearMap ∘ₗ
      (shrinkDualEquiv k H V).toLinearMap =
        dualTranspose k H (ofShrinkEquiv k H V).symm.toLinearMap := by
    rw [← toLinearMap_dualCongr k H (ofShrinkEquiv k H V).symm]
    ext φ
    exact ofShrinkEquiv_shrinkDualEquiv k H V φ
  rw [hd] at h
  exact (LinearMap.congr_fun
    (tensorMap_comp_dualCoeval k H (ofShrink k H V) (ofShrinkEquiv k H V)) r).symm.trans h

variable {V}
variable {W : Type w'} [AddCommGroup W] [Module k W] [Module H W]
  [IsScalarTower k H W] [Module.Finite k W]

/-- The dual of a transported intertwiner is the transpose of the original intertwiner,
under the dual comparisons. -/
theorem shrinkDualEquiv_naturality_apply (f : V →ₗ[H] W)
    (φ : dual (ofShrink k H W)) (x : V) :
    dualEquiv k H V (ofShrinkEquiv k H (Dual k H V)
        (shrinkDualEquiv k H V (((shrinkHom k H f)ᘁ).hom.hom φ))) x =
      dualEquiv k H W (ofShrinkEquiv k H (Dual k H W) (shrinkDualEquiv k H W φ)) (f x) := by
  simp only [dualEquiv_ofShrinkEquiv_shrinkDualEquiv_apply, dualEquiv_rightAdjointMate_apply,
    shrinkHom_hom_hom, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply]

/-- The dual comparison intertwines categorical right mates with transported
module-level transposes. -/
theorem shrinkDualEquiv_naturality (f : V →ₗ[H] W) :
    (shrinkHom k H f)ᘁ ≫ (shrinkDualEquiv k H V).toFiniteHopfModuleCatIso.hom =
      (shrinkDualEquiv k H W).toFiniteHopfModuleCatIso.hom ≫
        shrinkHom k H (dualTranspose k H f) := by
  apply hom_ext
  apply LinearMap.ext
  intro φ
  apply (ofShrinkEquiv k H (Dual k H V)).injective
  apply (dualEquiv k H V).injective
  ext x
  simp only [hom_hom_comp, LinearMap.comp_apply,
    LinearEquiv.toFiniteHopfModuleCatIso_hom_hom,
    shrinkHom_hom_hom, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    dualEquiv_dualTranspose_apply]
  exact shrinkDualEquiv_naturality_apply k H f φ x

end Hopf

end TauCeti.FiniteHopfModuleCat
