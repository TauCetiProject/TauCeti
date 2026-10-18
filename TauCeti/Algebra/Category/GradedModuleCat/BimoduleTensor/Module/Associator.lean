/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Basic
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Grading.Associator
public import Mathlib.CategoryTheory.Functor.Trifunctor

/-!
# Associativity of the graded bimodule action on left modules

For graded algebras A, B, and C, tensor composition and the left-module action identify
`(M tensor_B N) tensor_C P` with `M tensor_B (N tensor_C P)`, where M and N are graded
bimodules and P is a graded left C-module. The comparison transports the existing balanced
carrier associator and preserves the output left A-action and total internal grading.

The graded construction adapts
`TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Associator` to left modules.
The degree-preservation argument reuses the homogeneous balanced associator in
`TauCeti.LinearAlgebra.TensorProduct.Balanced.Grading.Associator`.

Both directions compute on nested pure tensors, and reassociation is natural in all three
maps. The trifunctor comparison supplies the associator for complex totalization; any
cohomological Koszul signs come from totalization, rather than the internal grading.
-/

public section

noncomputable section
open CategoryTheory MulOpposite
open scoped TensorProduct
namespace TauCeti.GradedModuleCat

universe vM vN vP uk uA uB uC
variable {k : Type uk} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing k] [Ring A] [Ring B] [Ring C]
  [Algebra k A] [Algebra k B] [Algebra k C]
  (Γ : InternalGrading k A) (Δ : InternalGrading k B) (Θ : InternalGrading k C)
  [GradedAlgebra Γ.piece] [GradedAlgebra Δ.piece] [GradedAlgebra Θ.piece]
  (M : GradedModuleCat.{vM} (Γ.tensorProduct Δ.opposite).piece)
  (N : GradedModuleCat.{vN} (Δ.tensorProduct Θ.opposite).piece)
  (P : GradedModuleCat.{vP} Θ.piece)

private local instance moduleAssocLeftModule {S T : Type*} [Ring S] [Ring T]
    [Algebra k S] [Algebra k T] (G : InternalGrading k S) (H : InternalGrading k T)
    (X : GradedModuleCat (G.tensorProduct H.opposite).piece) : Module S X :=
  TauCeti.Algebra.TensorProduct.moduleLeft (k := k) (A := S) (B := Tᵐᵒᵖ) X
private local instance moduleAssocRightModule {S T : Type*} [Ring S] [Ring T]
    [Algebra k S] [Algebra k T] (G : InternalGrading k S) (H : InternalGrading k T)
    (X : GradedModuleCat (G.tensorProduct H.opposite).piece) : Module Tᵐᵒᵖ X :=
  TauCeti.Algebra.TensorProduct.moduleRight (k := k) (A := S) (B := Tᵐᵒᵖ) X
private local instance moduleAssocLeftTower {S T : Type*} [Ring S] [Ring T]
    [Algebra k S] [Algebra k T] (G : InternalGrading k S) (H : InternalGrading k T)
    (X : GradedModuleCat (G.tensorProduct H.opposite).piece) : IsScalarTower k S X :=
  TauCeti.Algebra.TensorProduct.moduleLeftIsScalarTower (k := k) (A := S) (B := Tᵐᵒᵖ) X
private local instance moduleAssocRightTower {S T : Type*} [Ring S] [Ring T]
    [Algebra k S] [Algebra k T] (G : InternalGrading k S) (H : InternalGrading k T)
    (X : GradedModuleCat (G.tensorProduct H.opposite).piece) : IsScalarTower k Tᵐᵒᵖ X :=
  TauCeti.Algebra.TensorProduct.moduleRightIsScalarTower (k := k) (A := S) (B := Tᵐᵒᵖ) X
private local instance moduleAssocComm {S T : Type*} [Ring S] [Ring T]
    [Algebra k S] [Algebra k T] (G : InternalGrading k S) (H : InternalGrading k T)
    (X : GradedModuleCat (G.tensorProduct H.opposite).piece) : SMulCommClass S Tᵐᵒᵖ X :=
  TauCeti.Algebra.TensorProduct.moduleSMulCommClass (k := k) (A := S) (B := Tᵐᵒᵖ) X

attribute [local instance 100] BalancedTensorProduct.leftModule BalancedTensorProduct.rightModule
  BalancedTensorProduct.leftSMulCommClass BalancedTensorProduct.rightSMulCommClass
  BalancedTensorProduct.outerSMulCommClass
attribute [local instance] leftGradedSMul rightGradedSMul
  BalancedTensorProduct.gradedSMul_left BalancedTensorProduct.gradedSMul_right

local notation "MN" => bimoduleTensorObj Γ Δ Θ M N
local notation "NP" => bimoduleModuleTensorObj Δ Θ N P
local notation "L" => bimoduleModuleTensorObj Γ Θ MN P
local notation "R" => bimoduleModuleTensorObj Γ Δ M NP

private theorem refl_smul {S X : Type*} [AddCommGroup X] [Module k X] [SMul S X]
    (a : S) (x : X) :
    (LinearEquiv.refl k X) (a • x) = a • (LinearEquiv.refl k X) x := by
  simp only [LinearEquiv.refl_apply]

private def leftUnderlying : L ≃ₗ[k]
    BalancedTensorProduct k C (BalancedTensorProduct k B M N) P :=
  (bimoduleModuleTensorUnderlyingEquiv Γ Θ MN P).trans
    (BalancedTensorProduct.congr (bimoduleTensorUnderlyingEquiv Γ Δ Θ M N)
      (LinearEquiv.refl k P) (fun c x ↦ bimoduleTensorUnderlyingEquiv_smul_right Γ Δ Θ M N (op c) x)
      (refl_smul (k := k)))

private def rightUnderlying : R ≃ₗ[k]
    BalancedTensorProduct k B M (BalancedTensorProduct k C N P) :=
  (bimoduleModuleTensorUnderlyingEquiv Γ Δ M NP).trans
    (BalancedTensorProduct.congr (LinearEquiv.refl k M)
      (bimoduleModuleTensorUnderlyingEquiv Δ Θ N P)
      (fun b x ↦ refl_smul (k := k) (op b) x)
      (fun b x ↦ bimoduleModuleTensorUnderlyingEquiv_smul Δ Θ N P b x))

private def assocCarrier : L ≃ₗ[k] R :=
  (leftUnderlying Γ Δ Θ M N P).trans
    (BalancedTensorProduct.assoc.trans (rightUnderlying Γ Δ Θ M N P).symm)

private theorem leftUnderlying_tmul (m : M) (n : N) (p : P) :
    leftUnderlying Γ Δ Θ M N P
      (bimoduleModuleTensorTmul Γ Θ MN P (bimoduleTensorTmul Γ Δ Θ M N m n) p) =
      BalancedTensorProduct.tmul k C (BalancedTensorProduct.tmul k B m n) p := by
  unfold leftUnderlying
  rw [LinearEquiv.trans_apply, bimoduleModuleTensorUnderlyingEquiv_tmul]
  have h := BalancedTensorProduct.congr_tmul
    (bimoduleTensorUnderlyingEquiv Γ Δ Θ M N) (LinearEquiv.refl k P)
    (fun c x ↦ bimoduleTensorUnderlyingEquiv_smul_right Γ Δ Θ M N (op c) x)
    (refl_smul (k := k))
    (bimoduleTensorTmul Γ Δ Θ M N m n) p
  simpa only [bimoduleTensorUnderlyingEquiv_tmul, LinearEquiv.refl_apply] using h

private theorem rightUnderlying_tmul (m : M) (n : N) (p : P) :
    rightUnderlying Γ Δ Θ M N P
      (bimoduleModuleTensorTmul Γ Δ M NP m (bimoduleModuleTensorTmul Δ Θ N P n p)) =
      BalancedTensorProduct.tmul k B m (BalancedTensorProduct.tmul k C n p) := by
  unfold rightUnderlying
  rw [LinearEquiv.trans_apply, bimoduleModuleTensorUnderlyingEquiv_tmul]
  have h := BalancedTensorProduct.congr_tmul (LinearEquiv.refl k M)
    (bimoduleModuleTensorUnderlyingEquiv Δ Θ N P)
    (fun b x ↦ refl_smul (k := k) (op b) x)
    (fun b x ↦ bimoduleModuleTensorUnderlyingEquiv_smul Δ Θ N P b x)
    m (bimoduleModuleTensorTmul Δ Θ N P n p)
  simpa only [bimoduleModuleTensorUnderlyingEquiv_tmul, LinearEquiv.refl_apply] using h

private theorem assocCarrier_tmul (m : M) (n : N) (p : P) :
    assocCarrier Γ Δ Θ M N P
      (bimoduleModuleTensorTmul Γ Θ MN P (bimoduleTensorTmul Γ Δ Θ M N m n) p) =
      bimoduleModuleTensorTmul Γ Δ M NP m (bimoduleModuleTensorTmul Δ Θ N P n p) := by
  apply (rightUnderlying Γ Δ Θ M N P).injective
  simp only [assocCarrier, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [leftUnderlying_tmul, rightUnderlying_tmul, BalancedTensorProduct.assoc_tmul]

private theorem leftUnderlying_smul (a : A) (x : L) :
    leftUnderlying Γ Δ Θ M N P (a • x) = a • leftUnderlying Γ Δ Θ M N P x := by
  simp only [leftUnderlying, LinearEquiv.trans_apply,
    bimoduleModuleTensorUnderlyingEquiv_smul]
  exact BalancedTensorProduct.congr_smul_left A
    (bimoduleTensorUnderlyingEquiv Γ Δ Θ M N) (LinearEquiv.refl k P)
    (fun c y ↦ bimoduleTensorUnderlyingEquiv_smul_right Γ Δ Θ M N (op c) y)
    (refl_smul (k := k)) (fun a y ↦ bimoduleTensorUnderlyingEquiv_smul_left Γ Δ Θ M N a y) a _

private theorem rightUnderlying_smul (a : A) (x : R) :
    rightUnderlying Γ Δ Θ M N P (a • x) = a • rightUnderlying Γ Δ Θ M N P x := by
  simp only [rightUnderlying, LinearEquiv.trans_apply,
    bimoduleModuleTensorUnderlyingEquiv_smul]
  exact BalancedTensorProduct.congr_smul_left A
    (LinearEquiv.refl k M) (bimoduleModuleTensorUnderlyingEquiv Δ Θ N P)
    (fun b x ↦ refl_smul (k := k) (op b) x)
      (fun b y ↦ bimoduleModuleTensorUnderlyingEquiv_smul Δ Θ N P b y)
    (refl_smul (k := k)) a _

private theorem assocCarrier_smul (a : A) (x : L) :
    assocCarrier Γ Δ Θ M N P (a • x) = a • assocCarrier Γ Δ Θ M N P x := by
  apply (rightUnderlying Γ Δ Θ M N P).injective
  rw [rightUnderlying_smul]
  simp only [assocCarrier, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [leftUnderlying_smul]
  exact BalancedTensorProduct.assoc_smul_left A a (leftUnderlying Γ Δ Θ M N P x)

private def assocLinear : L →ₗ[A] R where
  toAddHom := (assocCarrier Γ Δ Θ M N P).toAddHom
  map_smul' := assocCarrier_smul Γ Δ Θ M N P

private theorem assocLinear_apply (x : L) :
    assocLinear Γ Δ Θ M N P x = assocCarrier Γ Δ Θ M N P x := rfl

private def assocEquiv : L ≃ₗ[A] R :=
  LinearEquiv.ofBijective (assocLinear Γ Δ Θ M N P)
    (by
      have hf : (assocLinear Γ Δ Θ M N P : L → R) =
          assocCarrier Γ Δ Θ M N P := funext (assocLinear_apply Γ Δ Θ M N P)
      rw [hf]
      exact (assocCarrier Γ Δ Θ M N P).bijective)

private theorem assocEquiv_apply (x : L) :
    assocEquiv Γ Δ Θ M N P x = assocCarrier Γ Δ Θ M N P x := by
  simp only [assocEquiv, LinearEquiv.ofBijective_apply, assocLinear_apply]

private theorem leftUnderlying_homogeneous :
    LinearMap.IsHomogeneous (leftUnderlying Γ Δ Θ M N P).toLinearMap (L).grading.piece
      (BalancedTensorProduct.grading (𝒜 := Θ.piece)
        (BalancedTensorProduct.grading (𝒜 := Δ.piece) M.grading N.grading) P.grading).piece 0 := by
  have h := BalancedTensorProduct.isHomogeneous_map (𝒜 := Θ.piece) (MN).grading P.grading
    (BalancedTensorProduct.grading (𝒜 := Δ.piece) M.grading N.grading) P.grading
    (bimoduleTensorUnderlyingEquiv Γ Δ Θ M N).toLinearMap (LinearEquiv.refl k P).toLinearMap
    (fun c x ↦ bimoduleTensorUnderlyingEquiv_smul_right Γ Δ Θ M N (op c) x)
    (refl_smul (k := k)) (bimoduleTensorUnderlyingEquiv_isHomogeneous Γ Δ Θ M N)
    (by simpa only [LinearEquiv.refl_toLinearMap] using LinearMap.isHomogeneous_id P.grading.piece)
  simpa only [LinearMap.isHomogeneous_def, leftUnderlying, LinearEquiv.coe_coe,
    LinearEquiv.coe_trans, Function.comp_apply, BalancedTensorProduct.congr_apply,
    LinearMap.comp_apply, add_zero] using
    h.comp (bimoduleModuleTensorUnderlyingEquiv_isHomogeneous Γ Θ MN P)

private theorem rightUnderlying_homogeneous :
    LinearMap.IsHomogeneous (rightUnderlying Γ Δ Θ M N P).toLinearMap (R).grading.piece
      (BalancedTensorProduct.grading (𝒜 := Δ.piece) M.grading
        (BalancedTensorProduct.grading (𝒜 := Θ.piece) N.grading P.grading)).piece 0 := by
  have h := BalancedTensorProduct.isHomogeneous_map (𝒜 := Δ.piece) M.grading (NP).grading
    M.grading (BalancedTensorProduct.grading (𝒜 := Θ.piece) N.grading P.grading)
    (LinearEquiv.refl k M).toLinearMap (bimoduleModuleTensorUnderlyingEquiv Δ Θ N P).toLinearMap
    (fun b x ↦ refl_smul (k := k) (op b) x)
    (fun b x ↦ bimoduleModuleTensorUnderlyingEquiv_smul Δ Θ N P b x)
    (by simpa only [LinearEquiv.refl_toLinearMap] using LinearMap.isHomogeneous_id M.grading.piece)
    (bimoduleModuleTensorUnderlyingEquiv_isHomogeneous Δ Θ N P)
  simpa only [LinearMap.isHomogeneous_def, rightUnderlying, LinearEquiv.coe_coe,
    LinearEquiv.coe_trans, Function.comp_apply, BalancedTensorProduct.congr_apply,
    LinearMap.comp_apply, add_zero] using
    h.comp (bimoduleModuleTensorUnderlyingEquiv_isHomogeneous Γ Δ M NP)

private theorem assocCarrier_mem {r : ℤ} {x : L} (hx : x ∈ (L).grading.piece r) :
    assocCarrier Γ Δ Θ M N P x ∈ (R).grading.piece r := by
  have hl := (leftUnderlying_homogeneous Γ Δ Θ M N P).map_mem hx
  have ha := (BalancedTensorProduct.isHomogeneous_assoc (ℬ := Δ.piece) (𝒞 := Θ.piece)
    M.grading N.grading P.grading).map_mem hl
  have hr := (rightUnderlying_homogeneous Γ Δ Θ M N P).linearEquiv_symm.map_mem ha
  simpa only [assocCarrier, LinearEquiv.trans_apply, LinearEquiv.coe_coe,
    add_zero, neg_zero] using hr

private theorem assocEquiv_homogeneous :
    LinearMap.IsHomogeneous (assocEquiv Γ Δ Θ M N P).toLinearMap
      (L).grading.piece (R).grading.piece 0 :=
  LinearMap.isHomogeneous_def.2 fun r x hx ↦ by
    rw [add_zero, LinearEquiv.coe_coe, assocEquiv_apply]
    exact assocCarrier_mem Γ Δ Θ M N P hx

/-- Reassociate two graded bimodules acting on a graded left module. -/
def bimoduleModuleTensorAssociator : L ≅ R :=
  isoMk (assocEquiv Γ Δ Θ M N P) (fun r x ↦ ⟨
    fun hx ↦ by
      simpa only [add_zero, LinearEquiv.coe_coe] using
        (assocEquiv_homogeneous Γ Δ Θ M N P).map_mem hx,
    fun hx ↦ by
      have h := (assocEquiv_homogeneous Γ Δ Θ M N P).linearEquiv_symm.map_mem hx
      simpa only [add_zero, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using h⟩)

/-- Reassociation changes only the parentheses of a nested pure tensor. -/
@[simp]
theorem bimoduleModuleTensorAssociator_hom_tmul (m : M) (n : N) (p : P) :
    (bimoduleModuleTensorAssociator Γ Δ Θ M N P).hom.hom
      (bimoduleModuleTensorTmul Γ Θ MN P (bimoduleTensorTmul Γ Δ Θ M N m n) p) =
      bimoduleModuleTensorTmul Γ Δ M NP m (bimoduleModuleTensorTmul Δ Θ N P n p) := by
  simp only [bimoduleModuleTensorAssociator, isoMk_hom_hom, LinearEquiv.coe_coe,
    assocEquiv_apply, assocCarrier_tmul]

/-- The inverse associator restores the original nested pure tensor. -/
@[simp]
theorem bimoduleModuleTensorAssociator_inv_tmul (m : M) (n : N) (p : P) :
    (bimoduleModuleTensorAssociator Γ Δ Θ M N P).inv.hom
      (bimoduleModuleTensorTmul Γ Δ M NP m (bimoduleModuleTensorTmul Δ Θ N P n p)) =
      bimoduleModuleTensorTmul Γ Θ MN P (bimoduleTensorTmul Γ Δ Θ M N m n) p := by
  apply (assocEquiv Γ Δ Θ M N P).injective
  simp only [bimoduleModuleTensorAssociator, isoMk_inv_hom, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, assocEquiv_apply, assocCarrier_tmul]

/-- Reassociation is natural in each bimodule and the left module. -/
@[reassoc]
theorem bimoduleModuleTensorAssociator_naturality
    {M' : GradedModuleCat.{vM} (Γ.tensorProduct Δ.opposite).piece}
    {N' : GradedModuleCat.{vN} (Δ.tensorProduct Θ.opposite).piece}
    {P' : GradedModuleCat.{vP} Θ.piece}
    (f : M ⟶ M') (g : N ⟶ N') (h : P ⟶ P') :
    bimoduleModuleTensorMap Γ Θ (bimoduleTensorMap Γ Δ Θ f g) h ≫
      (bimoduleModuleTensorAssociator Γ Δ Θ M' N' P').hom =
    (bimoduleModuleTensorAssociator Γ Δ Θ M N P).hom ≫
      bimoduleModuleTensorMap Γ Δ f (bimoduleModuleTensorMap Δ Θ g h) := by
  apply bimoduleModuleTensor_hom_ext Γ Θ
  intro x p
  induction x using bimoduleTensor_induction_on Γ Δ Θ M N with
  | ht m n =>
    simp only [hom_comp, LinearMap.comp_apply, bimoduleTensorMap_tmul,
      bimoduleModuleTensorMap_tmul, bimoduleModuleTensorAssociator_hom_tmul]
  | ha x y hx hy =>
    simpa only [← bimoduleModuleTensorMk_apply, map_add, LinearMap.add_apply]
      using congrArg₂ (· + ·) hx hy

/-- The action associator as an isomorphism between the two tensor trifunctors. -/
def bimoduleModuleTensorAssociatorNatIso :
    (bifunctorComp₁₂ (bimoduleTensor.{vM, vN} Γ Δ Θ)
        (bimoduleModuleTensor.{max vM vN, vP} Γ Θ)) ≅
    (bifunctorComp₂₃ (bimoduleModuleTensor.{vM, max vN vP} Γ Δ)
        (bimoduleModuleTensor.{vN, vP} Δ Θ)) :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun N ↦
    NatIso.ofComponents (fun P ↦ bimoduleModuleTensorAssociator Γ Δ Θ M N P)
      (by
        intro P P' h
        simp only [bifunctorComp₁₂_obj, bifunctorComp₁₂Obj_obj_obj, bifunctorComp₁₂Obj_obj_map,
          bifunctorComp₂₃_obj, bifunctorComp₂₃Obj_obj_obj, bifunctorComp₂₃Obj_obj_map,
          bimoduleModuleTensor_obj_map, bimoduleTensor_obj_obj,
          eqToHom_refl, Category.id_comp, Category.comp_id]
        simpa only [bimoduleTensorMap_id] using
          bimoduleModuleTensorAssociator_naturality Γ Δ Θ M N P (𝟙 M) (𝟙 N) h))
    (by
      intro N N' g
      apply NatTrans.ext
      funext P
      simp only [NatTrans.comp_app, NatIso.ofComponents_hom_app,
        bifunctorComp₁₂_obj, bifunctorComp₁₂Obj_obj_obj, bifunctorComp₁₂Obj_map_app,
        bifunctorComp₂₃_obj, bifunctorComp₂₃Obj_obj_obj, bifunctorComp₂₃Obj_map_app,
        bimoduleTensor_obj_map, bimoduleModuleTensor_map_app, bimoduleModuleTensor_obj_map,
        bimoduleTensor_obj_obj,
        eqToHom_refl, Category.id_comp, Category.comp_id]
      exact bimoduleModuleTensorAssociator_naturality Γ Δ Θ M N P (𝟙 M) g (𝟙 P)))
    (by
      intro M M' f
      apply NatTrans.ext
      funext N
      apply NatTrans.ext
      funext P
      simp only [NatTrans.comp_app, NatIso.ofComponents_hom_app,
        bifunctorComp₁₂_obj, bifunctorComp₁₂Obj_obj_obj, bifunctorComp₁₂_map_app_app,
        bifunctorComp₂₃_obj, bifunctorComp₂₃Obj_obj_obj, bifunctorComp₂₃_map_app_app,
        bimoduleTensor_map_app, bimoduleModuleTensor_map_app,
        bimoduleTensor_obj_obj,
        eqToHom_refl, Category.id_comp, Category.comp_id]
      simpa only [bimoduleModuleTensor, bimoduleModuleTensorMap_id] using
        bimoduleModuleTensorAssociator_naturality Γ Δ Θ M N P f (𝟙 N) (𝟙 P))

/-- Each forward trifunctor component is the graded associator. -/
@[simp, reassoc]
theorem bimoduleModuleTensorAssociatorNatIso_hom_app :
    (((bimoduleModuleTensorAssociatorNatIso.{vM, vN, vP} Γ Δ Θ).hom.app M).app N).app P =
      (bimoduleModuleTensorAssociator Γ Δ Θ M N P).hom := by
  simp only [bimoduleModuleTensorAssociatorNatIso, NatIso.ofComponents_hom_app]

/-- Each reverse trifunctor component is the inverse graded associator. -/
@[simp, reassoc]
theorem bimoduleModuleTensorAssociatorNatIso_inv_app :
    (((bimoduleModuleTensorAssociatorNatIso.{vM, vN, vP} Γ Δ Θ).inv.app M).app N).app P =
      (bimoduleModuleTensorAssociator Γ Δ Θ M N P).inv := by
  simp only [bimoduleModuleTensorAssociatorNatIso, NatIso.ofComponents_inv_app]

end TauCeti.GradedModuleCat
