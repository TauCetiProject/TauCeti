/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Basic
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Associator
public import Mathlib.CategoryTheory.Functor.Trifunctor

/-!
# Associativity of graded bimodule tensor composition

For graded algebras A, B, C, and D, tensor composition identifies
`(M tensor_B N) tensor_C P` with `M tensor_B (N tensor_C P)` as graded
(A,D)-bimodules. The construction transports the balanced carrier associator
through the public underlying equivalences. Transport is equivariant for the
middle actions, and the output map respects both outer actions and the sum
internal grading.

The public associator and its inverse compute on pure tensors. Naturality in
all three factors packages the comparison as an isomorphism of trifunctors,
ready for Mathlib's totalization associator. No internal Koszul sign is
introduced; cohomological signs belong to the complex totalization.

-/

public section

noncomputable section
open CategoryTheory MulOpposite
open scoped TensorProduct
namespace TauCeti.GradedModuleCat

universe vM vN vP uk uA uB uC uD
variable {k : Type uk} {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
  [CommRing k] [Ring A] [Ring B] [Ring C] [Ring D]
  [Algebra k A] [Algebra k B] [Algebra k C] [Algebra k D]
  (Γ : InternalGrading k A) (Δ : InternalGrading k B)
  (Θ : InternalGrading k C) (Ψ : InternalGrading k D)
  [GradedAlgebra Γ.piece] [GradedAlgebra Δ.piece]
  [GradedAlgebra Θ.piece] [GradedAlgebra Ψ.piece]
  (M : GradedModuleCat.{vM} (Γ.tensorProduct Δ.opposite).piece)
  (N : GradedModuleCat.{vN} (Δ.tensorProduct Θ.opposite).piece)
  (P : GradedModuleCat.{vP} (Θ.tensorProduct Ψ.opposite).piece)

private local instance assocLeftModule {S T : Type*} [Ring S] [Ring T]
    [Algebra k S] [Algebra k T] (G : InternalGrading k S) (H : InternalGrading k T)
    (X : GradedModuleCat (G.tensorProduct H.opposite).piece) : Module S X :=
  TauCeti.Algebra.TensorProduct.moduleLeft (k := k) (A := S) (B := Tᵐᵒᵖ) X
private local instance assocRightModule {S T : Type*} [Ring S] [Ring T]
    [Algebra k S] [Algebra k T] (G : InternalGrading k S) (H : InternalGrading k T)
    (X : GradedModuleCat (G.tensorProduct H.opposite).piece) : Module Tᵐᵒᵖ X :=
  TauCeti.Algebra.TensorProduct.moduleRight (k := k) (A := S) (B := Tᵐᵒᵖ) X
private local instance assocLeftTower {S T : Type*} [Ring S] [Ring T]
    [Algebra k S] [Algebra k T] (G : InternalGrading k S) (H : InternalGrading k T)
    (X : GradedModuleCat (G.tensorProduct H.opposite).piece) : IsScalarTower k S X :=
  TauCeti.Algebra.TensorProduct.moduleLeftIsScalarTower (k := k) (A := S) (B := Tᵐᵒᵖ) X
private local instance assocRightTower {S T : Type*} [Ring S] [Ring T]
    [Algebra k S] [Algebra k T] (G : InternalGrading k S) (H : InternalGrading k T)
    (X : GradedModuleCat (G.tensorProduct H.opposite).piece) : IsScalarTower k Tᵐᵒᵖ X :=
  TauCeti.Algebra.TensorProduct.moduleRightIsScalarTower (k := k) (A := S) (B := Tᵐᵒᵖ) X
private local instance assocComm {S T : Type*} [Ring S] [Ring T]
    [Algebra k S] [Algebra k T] (G : InternalGrading k S) (H : InternalGrading k T)
    (X : GradedModuleCat (G.tensorProduct H.opposite).piece) : SMulCommClass S Tᵐᵒᵖ X :=
  TauCeti.Algebra.TensorProduct.moduleSMulCommClass (k := k) (A := S) (B := Tᵐᵒᵖ) X

attribute [local instance 100] BalancedTensorProduct.leftModule BalancedTensorProduct.rightModule
  BalancedTensorProduct.leftSMulCommClass BalancedTensorProduct.rightSMulCommClass
  BalancedTensorProduct.outerSMulCommClass

local notation "MN" => bimoduleTensorObj Γ Δ Θ M N
local notation "NP" => bimoduleTensorObj Δ Θ Ψ N P
local notation "L" => bimoduleTensorObj Γ Θ Ψ MN P
local notation "R" => bimoduleTensorObj Γ Δ Ψ M NP

private def leftUnderlying : L ≃ₗ[k]
    BalancedTensorProduct k C (BalancedTensorProduct k B M N) P :=
  (bimoduleTensorUnderlyingEquiv Γ Θ Ψ MN P).trans
    (BalancedTensorProduct.congr (bimoduleTensorUnderlyingEquiv Γ Δ Θ M N)
      (LinearEquiv.refl k P) (fun c x ↦ bimoduleTensorUnderlyingEquiv_smul_right Γ Δ Θ M N (op c) x)
      (fun _ _ ↦ rfl))

private def rightUnderlying : R ≃ₗ[k]
    BalancedTensorProduct k B M (BalancedTensorProduct k C N P) :=
  (bimoduleTensorUnderlyingEquiv Γ Δ Ψ M NP).trans
    (BalancedTensorProduct.congr (LinearEquiv.refl k M)
      (bimoduleTensorUnderlyingEquiv Δ Θ Ψ N P)
      (fun _ _ ↦ rfl) (fun b x ↦ bimoduleTensorUnderlyingEquiv_smul_left Δ Θ Ψ N P b x))

private def assocCarrier : L ≃ₗ[k] R :=
  (leftUnderlying Γ Δ Θ Ψ M N P).trans
    (BalancedTensorProduct.assoc.trans (rightUnderlying Γ Δ Θ Ψ M N P).symm)

private theorem leftUnderlying_tmul (m : M) (n : N) (p : P) :
    leftUnderlying Γ Δ Θ Ψ M N P
      (bimoduleTensorTmul Γ Θ Ψ MN P (bimoduleTensorTmul Γ Δ Θ M N m n) p) =
      BalancedTensorProduct.tmul k C (BalancedTensorProduct.tmul k B m n) p := by
  unfold leftUnderlying
  rw [LinearEquiv.trans_apply, bimoduleTensorUnderlyingEquiv_tmul]
  have h := BalancedTensorProduct.congr_tmul
    (bimoduleTensorUnderlyingEquiv Γ Δ Θ M N) (LinearEquiv.refl k P)
    (fun c x ↦ bimoduleTensorUnderlyingEquiv_smul_right Γ Δ Θ M N (op c) x) (fun _ _ ↦ rfl)
    (bimoduleTensorTmul Γ Δ Θ M N m n) p
  simpa only [bimoduleTensorUnderlyingEquiv_tmul, LinearEquiv.refl_apply] using h

private theorem rightUnderlying_tmul (m : M) (n : N) (p : P) :
    rightUnderlying Γ Δ Θ Ψ M N P
      (bimoduleTensorTmul Γ Δ Ψ M NP m (bimoduleTensorTmul Δ Θ Ψ N P n p)) =
      BalancedTensorProduct.tmul k B m (BalancedTensorProduct.tmul k C n p) := by
  unfold rightUnderlying
  rw [LinearEquiv.trans_apply, bimoduleTensorUnderlyingEquiv_tmul]
  have h := BalancedTensorProduct.congr_tmul (LinearEquiv.refl k M)
    (bimoduleTensorUnderlyingEquiv Δ Θ Ψ N P) (fun _ _ ↦ rfl)
    (fun b x ↦ bimoduleTensorUnderlyingEquiv_smul_left Δ Θ Ψ N P b x)
    m (bimoduleTensorTmul Δ Θ Ψ N P n p)
  simpa only [bimoduleTensorUnderlyingEquiv_tmul, LinearEquiv.refl_apply] using h

private theorem assocCarrier_tmul (m : M) (n : N) (p : P) :
    assocCarrier Γ Δ Θ Ψ M N P
      (bimoduleTensorTmul Γ Θ Ψ MN P (bimoduleTensorTmul Γ Δ Θ M N m n) p) =
      bimoduleTensorTmul Γ Δ Ψ M NP m (bimoduleTensorTmul Δ Θ Ψ N P n p) := by
  apply (rightUnderlying Γ Δ Θ Ψ M N P).injective
  simp only [assocCarrier, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [leftUnderlying_tmul, rightUnderlying_tmul, BalancedTensorProduct.assoc_tmul]

private theorem leftUnderlying_smul_left (a : A) (x : L) :
    leftUnderlying Γ Δ Θ Ψ M N P (a • x) = a • leftUnderlying Γ Δ Θ Ψ M N P x := by
  simp only [leftUnderlying, LinearEquiv.trans_apply,
    bimoduleTensorUnderlyingEquiv_smul_left]
  exact BalancedTensorProduct.congr_smul_left A
    (bimoduleTensorUnderlyingEquiv Γ Δ Θ M N) (LinearEquiv.refl k P)
    (fun c y ↦ bimoduleTensorUnderlyingEquiv_smul_right Γ Δ Θ M N (op c) y)
    (fun _ _ ↦ rfl) (fun a y ↦ bimoduleTensorUnderlyingEquiv_smul_left Γ Δ Θ M N a y) a _

private theorem leftUnderlying_smul_right (d : Dᵐᵒᵖ) (x : L) :
    leftUnderlying Γ Δ Θ Ψ M N P (d • x) = d • leftUnderlying Γ Δ Θ Ψ M N P x := by
  simp only [leftUnderlying, LinearEquiv.trans_apply,
    bimoduleTensorUnderlyingEquiv_smul_right]
  exact BalancedTensorProduct.congr_smul_right Dᵐᵒᵖ
    (bimoduleTensorUnderlyingEquiv Γ Δ Θ M N) (LinearEquiv.refl k P)
    (fun c y ↦ bimoduleTensorUnderlyingEquiv_smul_right Γ Δ Θ M N (op c) y)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) d _

private theorem rightUnderlying_smul_left (a : A) (x : R) :
    rightUnderlying Γ Δ Θ Ψ M N P (a • x) = a • rightUnderlying Γ Δ Θ Ψ M N P x := by
  simp only [rightUnderlying, LinearEquiv.trans_apply,
    bimoduleTensorUnderlyingEquiv_smul_left]
  exact BalancedTensorProduct.congr_smul_left A
    (LinearEquiv.refl k M) (bimoduleTensorUnderlyingEquiv Δ Θ Ψ N P)
    (fun _ _ ↦ rfl) (fun b y ↦ bimoduleTensorUnderlyingEquiv_smul_left Δ Θ Ψ N P b y)
    (fun _ _ ↦ rfl) a _

private theorem rightUnderlying_smul_right (d : Dᵐᵒᵖ) (x : R) :
    rightUnderlying Γ Δ Θ Ψ M N P (d • x) = d • rightUnderlying Γ Δ Θ Ψ M N P x := by
  simp only [rightUnderlying, LinearEquiv.trans_apply,
    bimoduleTensorUnderlyingEquiv_smul_right]
  exact BalancedTensorProduct.congr_smul_right Dᵐᵒᵖ
    (LinearEquiv.refl k M) (bimoduleTensorUnderlyingEquiv Δ Θ Ψ N P)
    (fun _ _ ↦ rfl) (fun b y ↦ bimoduleTensorUnderlyingEquiv_smul_left Δ Θ Ψ N P b y)
    (fun d y ↦ bimoduleTensorUnderlyingEquiv_smul_right Δ Θ Ψ N P d y) d _

private theorem assocCarrier_left (a : A) (x : L) :
    assocCarrier Γ Δ Θ Ψ M N P ((a ⊗ₜ[k] (1 : Dᵐᵒᵖ)) • x) =
      (a ⊗ₜ[k] (1 : Dᵐᵒᵖ)) • assocCarrier Γ Δ Θ Ψ M N P x := by
  rw [← TauCeti.Algebra.TensorProduct.smul_moduleLeft,
    ← TauCeti.Algebra.TensorProduct.smul_moduleLeft]
  apply (rightUnderlying Γ Δ Θ Ψ M N P).injective
  rw [rightUnderlying_smul_left]
  simp only [assocCarrier, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [leftUnderlying_smul_left]
  exact BalancedTensorProduct.assoc_smul_left A a (leftUnderlying Γ Δ Θ Ψ M N P x)

private theorem assocCarrier_right (d : Dᵐᵒᵖ) (x : L) :
    assocCarrier Γ Δ Θ Ψ M N P (((1 : A) ⊗ₜ[k] d) • x) =
      ((1 : A) ⊗ₜ[k] d) • assocCarrier Γ Δ Θ Ψ M N P x := by
  rw [← TauCeti.Algebra.TensorProduct.smul_moduleRight,
    ← TauCeti.Algebra.TensorProduct.smul_moduleRight]
  apply (rightUnderlying Γ Δ Θ Ψ M N P).injective
  rw [rightUnderlying_smul_right]
  simp only [assocCarrier, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [leftUnderlying_smul_right]
  exact BalancedTensorProduct.assoc_smul_right Dᵐᵒᵖ d (leftUnderlying Γ Δ Θ Ψ M N P x)

private def assocLinear : L →ₗ[A ⊗[k] Dᵐᵒᵖ] R :=
  TauCeti.Algebra.TensorProduct.linearMapOfFactors L
    (assocCarrier Γ Δ Θ Ψ M N P).toLinearMap
    (assocCarrier_left Γ Δ Θ Ψ M N P) (assocCarrier_right Γ Δ Θ Ψ M N P)

private theorem assocLinear_apply (x : L) :
    assocLinear Γ Δ Θ Ψ M N P x = assocCarrier Γ Δ Θ Ψ M N P x := by
  rw [assocLinear, TauCeti.Algebra.TensorProduct.linearMapOfFactors_apply, LinearEquiv.coe_coe]

private def assocEnvelopeEquiv : L ≃ₗ[A ⊗[k] Dᵐᵒᵖ] R :=
  LinearEquiv.ofBijective (assocLinear Γ Δ Θ Ψ M N P)
    (by
      have hf : (assocLinear Γ Δ Θ Ψ M N P : L → R) =
          assocCarrier Γ Δ Θ Ψ M N P := funext (assocLinear_apply Γ Δ Θ Ψ M N P)
      rw [hf]
      exact (assocCarrier Γ Δ Θ Ψ M N P).bijective)

private theorem assocEnvelopeEquiv_apply (x : L) :
    assocEnvelopeEquiv Γ Δ Θ Ψ M N P x = assocCarrier Γ Δ Θ Ψ M N P x := by
  simp only [assocEnvelopeEquiv, LinearEquiv.ofBijective_apply, assocLinear_apply]

private theorem assocCarrier_mem {r : ℤ} {x : L} (hx : x ∈ (L).grading.piece r) :
    assocCarrier Γ Δ Θ Ψ M N P x ∈ (R).grading.piece r := by
  -- Apply the public quotient grading's span description at both tensor stages.
  have h := bimoduleTensorObj_map_mem_of_tmul Γ Θ Ψ MN P (R).grading
    (assocCarrier Γ Δ Θ Ψ M N P).toLinearMap 0 (by
      intro s t y p hy hp
      let f : MN →ₗ[k] R :=
        { toFun y := assocCarrier Γ Δ Θ Ψ M N P (bimoduleTensorTmul Γ Θ Ψ MN P y p)
          map_add' y z := by simp only [bimoduleTensorTmul_add_left, map_add]
          map_smul' a y := by simp only [bimoduleTensorTmul_smul_left, map_smul, RingHom.id_apply] }
      have hinner := bimoduleTensorObj_map_mem_of_tmul Γ Δ Θ M N (R).grading f t (by
        intro a b m n hm hn
        dsimp only [f, LinearMap.coe_mk, AddHom.coe_mk]
        rw [assocCarrier_tmul]
        have ht := bimoduleTensorTmul_mem Γ Δ Ψ M NP hm
          (bimoduleTensorTmul_mem Δ Θ Ψ N P hn hp)
        simpa only [add_assoc] using ht) hy
      simpa only [f, LinearMap.coe_mk, AddHom.coe_mk, add_zero, LinearEquiv.coe_coe]
        using hinner) hx
  simpa only [add_zero, LinearEquiv.coe_coe] using h

private theorem assocEnvelopeEquiv_homogeneous :
    LinearMap.IsHomogeneous (assocEnvelopeEquiv Γ Δ Θ Ψ M N P).toLinearMap
      (L).grading.piece (R).grading.piece 0 :=
  LinearMap.isHomogeneous_def.2 fun r x hx ↦ by
    rw [add_zero, LinearEquiv.coe_coe, assocEnvelopeEquiv_apply]
    exact assocCarrier_mem Γ Δ Θ Ψ M N P hx

/-- Reassociation of graded bimodule tensors, balanced over the two middle algebras. -/
def bimoduleTensorAssociator : L ≅ R :=
  isoMk (assocEnvelopeEquiv Γ Δ Θ Ψ M N P) (fun r x ↦ ⟨
    fun hx ↦ by
      simpa only [add_zero, LinearEquiv.coe_coe] using
        (assocEnvelopeEquiv_homogeneous Γ Δ Θ Ψ M N P).map_mem hx,
    fun hx ↦ by
      have h := (assocEnvelopeEquiv_homogeneous Γ Δ Θ Ψ M N P).linearEquiv_symm.map_mem hx
      simpa only [add_zero, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using h⟩)

/-- The graded associator changes only the parentheses of a nested pure tensor. -/
@[simp]
theorem bimoduleTensorAssociator_hom_tmul (m : M) (n : N) (p : P) :
    (bimoduleTensorAssociator Γ Δ Θ Ψ M N P).hom.hom
      (bimoduleTensorTmul Γ Θ Ψ MN P (bimoduleTensorTmul Γ Δ Θ M N m n) p) =
      bimoduleTensorTmul Γ Δ Ψ M NP m (bimoduleTensorTmul Δ Θ Ψ N P n p) := by
  simp only [bimoduleTensorAssociator, isoMk_hom_hom, LinearEquiv.coe_coe,
    assocEnvelopeEquiv_apply, assocCarrier_tmul]

/-- The inverse graded associator restores the original nested pure tensor. -/
@[simp]
theorem bimoduleTensorAssociator_inv_tmul (m : M) (n : N) (p : P) :
    (bimoduleTensorAssociator Γ Δ Θ Ψ M N P).inv.hom
      (bimoduleTensorTmul Γ Δ Ψ M NP m (bimoduleTensorTmul Δ Θ Ψ N P n p)) =
      bimoduleTensorTmul Γ Θ Ψ MN P (bimoduleTensorTmul Γ Δ Θ M N m n) p := by
  apply (assocEnvelopeEquiv Γ Δ Θ Ψ M N P).injective
  simp only [bimoduleTensorAssociator, isoMk_inv_hom, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, assocEnvelopeEquiv_apply, assocCarrier_tmul]

/-- Reassociation is natural in each of the three bimodule maps. -/
@[reassoc]
theorem bimoduleTensorAssociator_naturality
    {M' : GradedModuleCat.{vM} (Γ.tensorProduct Δ.opposite).piece}
    {N' : GradedModuleCat.{vN} (Δ.tensorProduct Θ.opposite).piece}
    {P' : GradedModuleCat.{vP} (Θ.tensorProduct Ψ.opposite).piece}
    (f : M ⟶ M') (g : N ⟶ N') (h : P ⟶ P') :
    bimoduleTensorMap Γ Θ Ψ (bimoduleTensorMap Γ Δ Θ f g) h ≫
      (bimoduleTensorAssociator Γ Δ Θ Ψ M' N' P').hom =
    (bimoduleTensorAssociator Γ Δ Θ Ψ M N P).hom ≫
      bimoduleTensorMap Γ Δ Ψ f (bimoduleTensorMap Δ Θ Ψ g h) := by
  apply bimoduleTensor_hom_ext Γ Θ Ψ
  intro x p
  induction x using bimoduleTensor_induction_on Γ Δ Θ M N with
  | ht m n =>
    simp only [hom_comp, LinearMap.comp_apply, bimoduleTensorMap_tmul,
      bimoduleTensorAssociator_hom_tmul]
  | ha x y hx hy =>
    simp only [bimoduleTensorTmul_add_left, map_add, hx, hy]

/-- The graded associator as an isomorphism between the two tensor trifunctors. -/
def bimoduleTensorAssociatorNatIso :
    bifunctorComp₁₂ (bimoduleTensor.{vM, vN} Γ Δ Θ)
      (bimoduleTensor.{max vM vN, vP} Γ Θ Ψ) ≅
    bifunctorComp₂₃ (bimoduleTensor.{vM, max vN vP} Γ Δ Ψ)
      (bimoduleTensor.{vN, vP} Δ Θ Ψ) :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun N ↦
    NatIso.ofComponents (fun P ↦ bimoduleTensorAssociator Γ Δ Θ Ψ M N P)
      (by
        intro P P' h
        simp only [bifunctorComp₁₂_obj, bifunctorComp₁₂Obj_obj_obj, bifunctorComp₁₂Obj_obj_map,
          bifunctorComp₂₃_obj, bifunctorComp₂₃Obj_obj_obj, bifunctorComp₂₃Obj_obj_map,
          bimoduleTensor_obj_map,
          bimoduleTensor_obj_obj]
        simpa only [bimoduleTensorMap_id] using
          bimoduleTensorAssociator_naturality Γ Δ Θ Ψ M N P (𝟙 M) (𝟙 N) h))
    (by
      intro N N' g
      apply NatTrans.ext
      funext P
      simp only [NatTrans.comp_app]
      simp only [bifunctorComp₁₂_obj, bifunctorComp₁₂Obj_map_app,
        bifunctorComp₂₃_obj, bifunctorComp₂₃Obj_map_app, bimoduleTensor_obj_map,
        bimoduleTensor_map_app, bimoduleTensor_obj_obj]
      exact bimoduleTensorAssociator_naturality Γ Δ Θ Ψ M N P (𝟙 M) g (𝟙 P)))
    (by
      intro M M' f
      apply NatTrans.ext
      funext N
      simp only [NatTrans.comp_app]
      apply NatTrans.ext
      funext P
      simp only [NatTrans.comp_app, NatIso.ofComponents_hom_app]
      simp only [bifunctorComp₁₂_obj, bifunctorComp₁₂Obj_obj_obj,
        bifunctorComp₂₃_obj, bifunctorComp₂₃Obj_obj_obj,
        bifunctorComp₁₂_map_app_app, bifunctorComp₂₃_map_app_app,
        bimoduleTensor_map_app, bimoduleTensor_obj_obj]
      simpa only [bimoduleTensorMap_id] using
        bimoduleTensorAssociator_naturality Γ Δ Θ Ψ M N P f (𝟙 N) (𝟙 P))

/-- The forward trifunctor comparison has the graded associator as each component. -/
@[simp]
theorem bimoduleTensorAssociatorNatIso_hom_app :
    (((bimoduleTensorAssociatorNatIso.{vM, vN, vP} Γ Δ Θ Ψ).hom.app M).app N).app P =
      (bimoduleTensorAssociator Γ Δ Θ Ψ M N P).hom := by
  simp only [bimoduleTensorAssociatorNatIso, NatIso.ofComponents_hom_app]

/-- The reverse trifunctor comparison has the inverse graded associator as each component. -/
@[simp]
theorem bimoduleTensorAssociatorNatIso_inv_app :
    (((bimoduleTensorAssociatorNatIso.{vM, vN, vP} Γ Δ Θ Ψ).inv.app M).app N).app P =
      (bimoduleTensorAssociator Γ Δ Θ Ψ M N P).inv := by
  simp only [bimoduleTensorAssociatorNatIso, NatIso.ofComponents_inv_app]

end TauCeti.GradedModuleCat
