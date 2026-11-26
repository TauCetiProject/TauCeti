/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FiniteHopfModuleCat.RightRigid

/-!
# Tensor products and duals of small models of finite Hopf modules

A finite-dimensional module can have a carrier in a larger universe than its scalar field.
`ofShrink` replaces it by an isomorphic module in the scalar field's universe. This file
compares the tensor products and contragredients of those small models with the small models
of the original tensor products and contragredients. The comparisons intertwine the Hopf
algebra actions, are natural in module maps, and preserve evaluation and coevaluation.

The tensor comparison already works for bialgebras. Under the forgetful functor it is the
ordinary tensor product of the scalar-linear shrinking equivalences. The dual comparison is
precomposition with the inverse shrinking equivalence; it uses the antipode action on functionals.
Thus universe reduction retains the tensor and dual data needed to regard finite modules
as objects of a single monoidal category.

The constructions use `BialgebraModule.tensorCongr`, native transposition of linear
equivalences, and dinaturality of coevaluation (`LinearMap.rTensor_comp_coevaluation`).
-/

public noncomputable section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace TauCeti.FiniteHopfModuleCat

open BialgebraModule

universe u v w w' w'' w'''

variable (k : Type u) [Field k] (H : Type v) [Ring H]

section Bialgebra

variable [Bialgebra k H]
variable (V : Type w) [AddCommGroup V] [Module k V] [Module H V]
  [IsScalarTower k H V] [Module.Finite k V]
variable (W : Type w') [AddCommGroup W] [Module k W] [Module H W]
  [IsScalarTower k H W] [Module.Finite k W]

/-- Tensoring the small models gives the small model of the coproduct tensor product.
The comparison sends `v ⊗ w` to the small representative of the corresponding original tensor. -/
def shrinkTensorEquiv :
    (ofShrink k H V ⊗ ofShrink k H W : FiniteHopfModuleCat k H) ≃ₗ[H]
      ofShrink k H (Tensor k H V W) :=
  (tensorCongr k H (ofShrinkEquiv k H V) (ofShrinkEquiv k H W)).trans
    (ofShrinkEquiv k H (Tensor k H V W)).symm

/-- The tensor comparison acts factorwise on pure tensors. -/
@[simp]
theorem shrinkTensorEquiv_tmul (x : ofShrink k H V) (y : ofShrink k H W) :
    shrinkTensorEquiv k H V W (tmul k H x y) =
      (ofShrinkEquiv k H (Tensor k H V W)).symm
        (tmul k H (ofShrinkEquiv k H V x) (ofShrinkEquiv k H W y)) := by
  exact congrArg (ofShrinkEquiv k H (Tensor k H V W)).symm
    (tensorCongr_tmul k H (ofShrinkEquiv k H V) (ofShrinkEquiv k H W) x y)

/-- On the original modules, tensor comparison is the coproduct tensor product of the
shrinking maps. -/
-- Simplify the composite before the primitive shrink map expands into carrier casts.
@[simp↓]
theorem ofShrinkEquiv_shrinkTensorEquiv
    (x : (ofShrink k H V ⊗ ofShrink k H W : FiniteHopfModuleCat k H)) :
    ofShrinkEquiv k H (Tensor k H V W) (shrinkTensorEquiv k H V W x) =
      tensorMap k H (ofShrinkEquiv k H V).toLinearMap (ofShrinkEquiv k H W).toLinearMap x := by
  calc
    _ = tensorCongr k H (ofShrinkEquiv k H V) (ofShrinkEquiv k H W) x :=
      (ofShrinkEquiv k H (Tensor k H V W)).apply_symm_apply _
    _ = _ := tensorCongr_apply k H _ _ x

/-- The inverse tensor comparison returns the tensor of the small representatives. -/
@[simp]
theorem shrinkTensorEquiv_symm_tmul (x : V) (y : W) :
    (shrinkTensorEquiv k H V W).symm
        ((ofShrinkEquiv k H (Tensor k H V W)).symm (tmul k H x y)) =
      tmul k H ((ofShrinkEquiv k H V).symm x) ((ofShrinkEquiv k H W).symm y) := by
  apply (shrinkTensorEquiv k H V W).injective
  simp only [LinearEquiv.apply_symm_apply, shrinkTensorEquiv_tmul]

/-- Forgetting the action identifies the tensor comparison with the tensor product of the
scalar-linear shrinking equivalences. -/
theorem ofShrinkLinearEquiv_shrinkTensorEquiv
    (x : (ofShrink k H V ⊗ ofShrink k H W : FiniteHopfModuleCat k H)) :
    tensorEquiv k H V W (ofShrinkLinearEquiv k H (Tensor k H V W)
      (shrinkTensorEquiv k H V W x)) =
      TensorProduct.congr (ofShrinkLinearEquiv k H V) (ofShrinkLinearEquiv k H W)
        (tensorEquiv k H (ofShrink k H V) (ofShrink k H W) x) := by
  induction x using Tensor.inductionOn with
  | htmul x y => simp
  | hadd x y hx hy => simp only [map_add, hx, hy]

variable {V W}
variable {V' : Type w''} [AddCommGroup V'] [Module k V'] [Module H V']
  [IsScalarTower k H V'] [Module.Finite k V']
variable {W' : Type w'''} [AddCommGroup W'] [Module k W'] [Module H W']
  [IsScalarTower k H W'] [Module.Finite k W']

/-- Tensor comparison commutes with the transport of intertwiners to small models. -/
theorem shrinkTensorEquiv_naturality (f : V →ₗ[H] V') (g : W →ₗ[H] W') :
    (shrinkHom k H f ⊗ₘ shrinkHom k H g) ≫
        (shrinkTensorEquiv k H V' W').toFiniteHopfModuleCatIso.hom =
      (shrinkTensorEquiv k H V W).toFiniteHopfModuleCatIso.hom ≫
        shrinkHom k H (tensorMap k H f g) := by
  ext x y
  simp

variable (V)

/-- Tensor comparison commutes with the left unitor, including the unit comparison. -/
theorem shrinkTensorEquiv_left_unitality :
    (ofShrinkEquiv k H (Trivial k H)).symm.toFiniteHopfModuleCatIso.hom ▷ ofShrink k H V ≫
        (shrinkTensorEquiv k H (Trivial k H) V).toFiniteHopfModuleCatIso.hom ≫
          shrinkHom k H (lid k H V).toLinearMap =
      (λ_ (ofShrink k H V)).hom := by
  ext r x
  simp [-ofShrinkEquiv_apply, ← ofShrinkLinearEquiv_apply, ← ofShrinkLinearEquiv_symm_apply]

/-- Tensor comparison commutes with the right unitor, including the unit comparison. -/
theorem shrinkTensorEquiv_right_unitality :
    ofShrink k H V ◁ (ofShrinkEquiv k H (Trivial k H)).symm.toFiniteHopfModuleCatIso.hom ≫
        (shrinkTensorEquiv k H V (Trivial k H)).toFiniteHopfModuleCatIso.hom ≫
          shrinkHom k H (rid k H V).toLinearMap =
      (ρ_ (ofShrink k H V)).hom := by
  ext x r
  simp [-ofShrinkEquiv_apply, ← ofShrinkLinearEquiv_apply, ← ofShrinkLinearEquiv_symm_apply]

variable (W)
variable (P : Type w'') [AddCommGroup P] [Module k P] [Module H P]
  [IsScalarTower k H P] [Module.Finite k P]

/-- The two ways of comparing a triple tensor product agree through the actual associator. -/
theorem shrinkTensorEquiv_associativity :
    (shrinkTensorEquiv k H V W).toFiniteHopfModuleCatIso.hom ▷ ofShrink k H P ≫
        (shrinkTensorEquiv k H (Tensor k H V W) P).toFiniteHopfModuleCatIso.hom ≫
          shrinkHom k H (assoc k H V W P).toLinearMap =
      (α_ (ofShrink k H V) (ofShrink k H W) (ofShrink k H P)).hom ≫
        ofShrink k H V ◁ (shrinkTensorEquiv k H W P).toFiniteHopfModuleCatIso.hom ≫
          (shrinkTensorEquiv k H V (Tensor k H W P)).toFiniteHopfModuleCatIso.hom := by
  apply hom_ext
  simp only [hom_hom_comp, whiskerRight_hom_hom, whiskerLeft_hom_hom,
    LinearEquiv.toFiniteHopfModuleCatIso_hom_hom, associator_hom_hom, shrinkHom_hom_hom]
  apply Tensor.ext
  intro xy z
  induction xy using Tensor.inductionOn with
  | htmul x y =>
      -- The categorical composites use the full-subcategory object instances; this
      -- identifies their functions with maps on the canonical module-level carriers.
      change (ofShrinkEquiv k H (Tensor k H V (Tensor k H W P))).symm
          (assoc k H V W P (ofShrinkEquiv k H (Tensor k H (Tensor k H V W) P)
            (shrinkTensorEquiv k H (Tensor k H V W) P
              (tensorMap k H (shrinkTensorEquiv k H V W).toLinearMap LinearMap.id
                (tmul k H (tmul k H x y) z))))) =
        shrinkTensorEquiv k H V (Tensor k H W P)
          (tensorMap k H LinearMap.id (shrinkTensorEquiv k H W P).toLinearMap
            (assoc k H (ofShrink k H V) (ofShrink k H W) (ofShrink k H P)
              (tmul k H (tmul k H x y) z)))
      simp only [tensorMap_tmul, LinearMap.id_apply, LinearEquiv.coe_coe,
        shrinkTensorEquiv_tmul, LinearEquiv.apply_symm_apply, assoc_tmul]
      have h := tensorMap_tmul k H
        (LinearMap.id : ofShrink k H V →ₗ[H] ofShrink k H V)
        (shrinkTensorEquiv k H W P).toLinearMap x
        (tmul k H y z : (ofShrink k H W ⊗ ofShrink k H P : FiniteHopfModuleCat k H))
      have h' := (congrArg (shrinkTensorEquiv k H V (Tensor k H W P)) h).symm
      simp only [LinearMap.id_apply, LinearEquiv.coe_coe, shrinkTensorEquiv_tmul,
        LinearEquiv.apply_symm_apply] at h'
      exact h'
  | hadd x y hx hy => simp only [add_tmul, map_add, hx, hy]

end Bialgebra

section Hopf

variable [HopfAlgebra k H]
variable (V : Type w) [AddCommGroup V] [Module k V] [Module H V]
  [IsScalarTower k H V] [Module.Finite k V]

/-- The contragredient of the small model is the small model of the contragredient.
On functionals the comparison is precomposition with the inverse shrinking equivalence. -/
def shrinkDualEquiv : dual (ofShrink k H V) ≃ₗ[H] ofShrink k H (Dual k H V) :=
  let e : Dual k H (ofShrink k H V) ≃ₗ[k] Dual k H V :=
    (dualEquiv k H (ofShrink k H V)).trans <|
      (ofShrinkLinearEquiv k H V).symm.dualMap.trans (dualEquiv k H V).symm
  have he (φ : Dual k H (ofShrink k H V)) (x : V) :
      dualEquiv k H V (e φ) x = dualEquiv k H (ofShrink k H V) φ
        ((ofShrinkLinearEquiv k H V).symm x) := by
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.dualMap_apply]
  let eH : Dual k H (ofShrink k H V) ≃ₗ[H] Dual k H V :=
    { e with
      map_smul' a φ := by
        apply (dualEquiv k H V).injective
        ext x
        -- The structure update retains the scalar-linear equivalence's function.
        change dualEquiv k H V (e (a • φ)) x = dualEquiv k H V (a • e φ) x
        rw [he, dualEquiv_smul_apply k H V, he, dualEquiv_smul_apply]
        apply congrArg (dualEquiv k H (ofShrink k H V) φ)
        simpa only [ofShrinkLinearEquiv_symm_apply] using
          ((ofShrinkEquiv k H V).symm.map_smul (HopfAlgebra.antipode k a) x).symm }
  eH.trans (ofShrinkEquiv k H (Dual k H V)).symm

/-- On the original module, the transported functional is precomposition with the inverse
shrinking equivalence. -/
-- Simplify the composite before the primitive shrink map expands into carrier casts.
@[simp↓]
theorem shrinkDualEquiv_apply (φ : dual (ofShrink k H V)) (x : V) :
    dualEquiv k H V (ofShrinkEquiv k H (Dual k H V) (shrinkDualEquiv k H V φ)) x =
      dualEquiv k H (ofShrink k H V) φ ((ofShrinkEquiv k H V).symm x) := by
  -- The H-linear structure update retains the transposition's underlying function.
  -- The categorical dual carrier is the module-level contragredient by construction.
  change dualEquiv k H V
      (ofShrinkEquiv k H (Dual k H V) ((ofShrinkEquiv k H (Dual k H V)).symm
        ((dualEquiv k H V).symm ((ofShrinkLinearEquiv k H V).symm.dualMap
          (dualEquiv k H (ofShrink k H V) φ))))) x = _
  simp only [LinearEquiv.apply_symm_apply, LinearEquiv.dualMap_apply,
    ofShrinkLinearEquiv_symm_apply]

/-- The inverse dual comparison preserves evaluation on the small model. -/
@[simp]
theorem shrinkDualEquiv_symm_apply (φ : ofShrink k H (Dual k H V))
    (x : ofShrink k H V) :
    dualEquiv k H (ofShrink k H V) ((shrinkDualEquiv k H V).symm φ) x =
      dualEquiv k H V (ofShrinkEquiv k H (Dual k H V) φ) (ofShrinkEquiv k H V x) := by
  simpa only [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] using
    (shrinkDualEquiv_apply k H V ((shrinkDualEquiv k H V).symm φ)
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
    LinearEquiv.apply_symm_apply, dualEval_tmul, shrinkDualEquiv_apply,
    LinearEquiv.symm_apply_apply, dualEvaluation_hom_hom]
  exact (congrArg (ofShrinkEquiv k H (Trivial k H)).symm
    (dualEval_tmul k H (ofShrink k H V) φ x)).symm

/-- The contragredient comparison carries the module-level coevaluation tensor to the
coevaluation tensor of the original module. -/
private theorem tensorMap_dualCoeval_shrink (r : Trivial k H) :
    tensorMap k H (ofShrinkEquiv k H V).toLinearMap
        ((ofShrinkEquiv k H (Dual k H V)).toLinearMap ∘ₗ (shrinkDualEquiv k H V).toLinearMap)
        (dualCoeval k H (ofShrink k H V) r) = dualCoeval k H V r := by
  let e := ofShrinkLinearEquiv k H V
  let d : Dual k H (ofShrink k H V) →ₗ[H] Dual k H V :=
    (ofShrinkEquiv k H (Dual k H V)).toLinearMap ∘ₗ (shrinkDualEquiv k H V).toLinearMap
  have hd : d.restrictScalars k ∘ₗ (dualEquiv k H (ofShrink k H V)).symm.toLinearMap =
      (dualEquiv k H V).symm.toLinearMap ∘ₗ e.symm.toLinearMap.dualMap := by
    apply LinearMap.ext
    intro φ
    apply (dualEquiv k H V).injective
    ext y
    -- The composition uses the categorical dual carrier, which is the contragredient.
    change dualEquiv k H V (ofShrinkEquiv k H (Dual k H V)
        (shrinkDualEquiv k H V ((dualEquiv k H (ofShrink k H V)).symm φ))) y =
      dualEquiv k H V ((dualEquiv k H V).symm (e.symm.toLinearMap.dualMap φ)) y
    simp only [LinearEquiv.apply_symm_apply, LinearMap.dualMap_apply,
      LinearEquiv.coe_coe, e, ofShrinkLinearEquiv_symm_apply]
    have h := shrinkDualEquiv_apply k H V
      ((dualEquiv k H (ofShrink k H V)).symm φ) y
    simp only [LinearEquiv.apply_symm_apply] at h
    exact h
  -- Give the tensor map the canonical contragredient carrier before applying its API.
  change tensorMap k H (ofShrinkEquiv k H V).toLinearMap d
    (dualCoeval k H (ofShrink k H V) r) = dualCoeval k H V r
  apply (tensorEquiv k H V (Dual k H V)).injective
  rw [tensorEquiv_tensorMap, dualCoeval_apply, dualCoeval_apply]
  simp only [LinearEquiv.apply_symm_apply]
  have he : (ofShrinkEquiv k H V).toLinearMap.restrictScalars k = e.toLinearMap := by
    ext x
    exact (ofShrinkLinearEquiv_apply k H V x).symm
  rw [he, TensorProduct.map_map, hd, LinearMap.comp_id]
  have hn := LinearMap.congr_fun (LinearMap.rTensor_comp_coevaluation e.toLinearMap)
    (trivialEquiv k H r)
  have hn' := congrArg (TensorProduct.map (LinearMap.id : V →ₗ[k] V)
    e.symm.toLinearMap.dualMap) hn
  have hco : TensorProduct.map e.toLinearMap e.symm.toLinearMap.dualMap
      (coevaluation k (ofShrink k H V) (trivialEquiv k H r)) =
        coevaluation k V (trivialEquiv k H r) := by
    simpa [LinearMap.rTensor, LinearMap.lTensor, TensorProduct.map_map,
      LinearMap.dualMap_comp_dualMap] using hn'
  have h := congrArg (TensorProduct.map (LinearMap.id : V →ₗ[k] V)
    (dualEquiv k H V).symm.toLinearMap) hco
  simpa only [TensorProduct.map_map, LinearMap.id_comp] using h

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
  exact (tensorMap_dualCoeval_shrink k H V r).symm.trans h

variable {V}
variable {W : Type w'} [AddCommGroup W] [Module k W] [Module H W]
  [IsScalarTower k H W] [Module.Finite k W]

/-- The dual of a transported intertwiner is the transpose of the original intertwiner,
under the dual comparisons. -/
theorem shrinkDualEquiv_naturality (f : V →ₗ[H] W)
    (φ : dual (ofShrink k H W)) (x : V) :
    dualEquiv k H V (ofShrinkEquiv k H (Dual k H V)
        (shrinkDualEquiv k H V (((shrinkHom k H f)ᘁ).hom.hom φ))) x =
      dualEquiv k H W (ofShrinkEquiv k H (Dual k H W) (shrinkDualEquiv k H W φ)) (f x) := by
  simp only [shrinkDualEquiv_apply, dualEquiv_rightAdjointMate_apply,
    shrinkHom_hom_hom, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply]

end Hopf

end TauCeti.FiniteHopfModuleCat
