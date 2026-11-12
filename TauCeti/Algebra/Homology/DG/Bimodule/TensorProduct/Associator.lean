/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Bimodule.TensorProduct.Functor
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Associator
import TauCeti.Algebra.Homology.DG.Module.TensorProduct.Associator
import TauCeti.LinearAlgebra.TensorProduct.Balanced.Coherence

/-!
# Associativity of tensor products of DG bimodules

The ordinary balanced tensor product of DG bimodules is associative up to the canonical
isomorphism `DGBimoduleCat.tensorAssoc`. Reassociation preserves the two outer actions,
the total grading and the signed differential. It is natural in all three bimodules
and satisfies the pentagon identity, so iterated tensor composition has coherent
parenthesizations. No flatness hypotheses are needed for these underived products.

Algebra and module carriers may live in independent universes.

## References

* B. Keller, *Deriving DG categories*, Section 6.1.
-/

public section

noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti.DGBimoduleCat

universe uR uA uB uC uD uE uM uN uP uQ

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
  [CommRing R] [Ring A] [Ring B] [Ring C] [Ring D]
  [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  {𝒞 : ℤ → Submodule R C} {𝒟 : ℤ → Submodule R D}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞] [GradedAlgebra 𝒟]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {dC : C →ₗ[R] C} {dD : D →ₗ[R] D}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}
  {hC : IsDGAlgebra 𝒞 dC} {hD : IsDGAlgebra 𝒟 dD}

open BalancedTensorProduct

attribute [local instance 100] leftModule rightModule leftIsScalarTower rightIsScalarTower
  leftSMulCommClass rightSMulCommClass outerSMulCommClass

attribute [local instance] tensorGradedOuterLeft tensorGradedOuterRight

variable (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB)
  (N : DGBimoduleCat.{uR, uB, uC, uN} hB hC)
  (P : DGBimoduleCat.{uR, uC, uD, uP} hC hD)

-- Transport the graded actions through the characteristic equation of `ofDecomposition`.
local instance : SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece
    (InternalGrading.ofDecomposition M.grading).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

local instance : SetLike.GradedSMul ℬ (InternalGrading.ofDecomposition N.grading).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

local instance : SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒞).opposite.piece
    (InternalGrading.ofDecomposition N.grading).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

local instance : SetLike.GradedSMul 𝒞 (InternalGrading.ofDecomposition P.grading).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

local notation "G" => InternalGrading.ofDecomposition M.grading
local notation "H" => InternalGrading.ofDecomposition N.grading
local notation "I" => InternalGrading.ofDecomposition P.grading

/-- Reassociation of ordinary DG bimodule tensor products, preserving both outer actions. -/
def tensorAssoc : tensorObj (tensorObj M N) P ≅ tensorObj M (tensorObj N P) := by
  let e := assoc (k := R) (B := B) (C := C) (M := M) (N := N) (P := P)
  have hMN : InternalGrading.ofDecomposition (grading (𝒜 := ℬ) G H).piece =
      grading (𝒜 := ℬ) G H :=
    InternalGrading.ext fun p ↦ congrFun (InternalGrading.ofDecomposition_piece _) p
  have hNP : InternalGrading.ofDecomposition (grading (𝒜 := 𝒞) H I).piece =
      grading (𝒜 := 𝒞) H I :=
    InternalGrading.ext fun p ↦ congrFun (InternalGrading.ofDecomposition_piece _) p
  let f : tensorObj (tensorObj M N) P ⟶ tensorObj M (tensorObj N P) :=
    ⟨{ toLinearMap :=
        { toFun := e
          map_add' := e.map_add
          map_smul' := assoc_smul_right Dᵐᵒᵖ }
       map_mem' := fun {p z} hz ↦ by
         have hz' := (isHomogeneous_assoc G H I).map_mem
           (by simpa only [hMN] using hz)
         simpa only [add_zero, hNP, LinearEquiv.coe_coe, LinearMap.coe_mk,
           AddHom.coe_mk, e] using hz'
       map_d' := fun z ↦
         (assoc_differential M.isDGRightModule N.isDGBimodule P.isDGLeftModule z).symm },
      (mem_dgBimoduleHomSubmodule _ _ _).mpr (assoc_smul_left A)⟩
  let g : tensorObj M (tensorObj N P) ⟶ tensorObj (tensorObj M N) P :=
    ⟨{ toLinearMap :=
        { toFun := e.symm
          map_add' := e.symm.map_add
          map_smul' := fun d z ↦ e.injective (by
            rw [LinearEquiv.apply_symm_apply, assoc_smul_right,
              LinearEquiv.apply_symm_apply]
            rfl) }
       map_mem' := fun {p z} hz ↦ by
         have hz' := (isHomogeneous_assoc_symm G H I).map_mem
           (by simpa only [hNP] using hz)
         simpa only [add_zero, hMN, LinearEquiv.coe_coe, LinearMap.coe_mk,
           AddHom.coe_mk, e] using hz'
       map_d' := fun z ↦
         (assoc_symm_differential M.isDGRightModule N.isDGBimodule P.isDGLeftModule z).symm },
      (mem_dgBimoduleHomSubmodule _ _ _).mpr fun a z ↦ e.injective (by
        rw [DGRightModuleHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
          LinearEquiv.apply_symm_apply, assoc_smul_left, LinearEquiv.apply_symm_apply])⟩
  exact
    { hom := f
      inv := g
      hom_inv_id := hom_ext fun z ↦ by
        rw [comp_apply, id_apply]
        exact e.symm_apply_apply z
      inv_hom_id := hom_ext fun z ↦ by
        rw [comp_apply, id_apply]
        exact e.apply_symm_apply z }

/-- The ground-ring linear map of forward reassociation is the balanced associator. -/
theorem tensorAssoc_hom_toLinearMap :
    (tensorAssoc M N P).hom.val.toLinearMap.restrictScalars R =
      (BalancedTensorProduct.assoc (k := R) (B := B) (C := C)
        (M := M) (N := N) (P := P)).toLinearMap := (rfl)

/-- The ground-ring linear map of inverse reassociation is the inverse balanced associator. -/
theorem tensorAssoc_inv_toLinearMap :
    (tensorAssoc M N P).inv.val.toLinearMap.restrictScalars R =
      (BalancedTensorProduct.assoc (k := R) (B := B) (C := C)
        (M := M) (N := N) (P := P)).symm.toLinearMap := (rfl)

/-- Forward reassociation changes only parentheses on pure tensors. -/
@[simp↓]
theorem tensorAssoc_hom_tmul (m : M) (n : N) (p : P) :
    (tensorAssoc M N P).hom (tmul R C (tmul R B m n) p) =
      tmul R B m (tmul R C n p) := by
  simpa only [LinearMap.restrictScalars_apply, DGRightModuleHom.coe_toLinearMap,
    DGBimoduleHom.coe_val, LinearEquiv.coe_coe, assoc_tmul] using
    LinearMap.congr_fun (tensorAssoc_hom_toLinearMap M N P) (tmul R C (tmul R B m n) p)

/-- Inverse reassociation restores the original parentheses on pure tensors. -/
@[simp↓]
theorem tensorAssoc_inv_tmul (m : M) (n : N) (p : P) :
    (tensorAssoc M N P).inv (tmul R B m (tmul R C n p)) =
      tmul R C (tmul R B m n) p := by
  simpa only [LinearMap.restrictScalars_apply, DGRightModuleHom.coe_toLinearMap,
    DGBimoduleHom.coe_val, LinearEquiv.coe_coe, assoc_symm_tmul] using
    LinearMap.congr_fun (tensorAssoc_inv_toLinearMap M N P) (tmul R B m (tmul R C n p))

variable {M N P}
  {M' : DGBimoduleCat.{uR, uA, uB, uM} hA hB}
  {N' : DGBimoduleCat.{uR, uB, uC, uN} hB hC}
  {P' : DGBimoduleCat.{uR, uC, uD, uP} hC hD}

/-- Reassociation is natural in all three DG bimodules. -/
@[reassoc]
theorem tensorAssoc_naturality (f : M ⟶ M') (g : N ⟶ N') (h : P ⟶ P') :
    tensorMap (tensorMap f g) h ≫ (tensorAssoc M' N' P').hom =
      (tensorAssoc M N P).hom ≫ tensorMap f (tensorMap g h) := by
  have hnat := BalancedTensorProduct.map_map_comp_assoc_eq
    (f.val.toLinearMap.restrictScalars R) (g.val.toLinearMap.restrictScalars R)
    (h.val.toLinearMap.restrictScalars R)
    (fun b m ↦ map_smul f (op b) m) (fun b n ↦ map_smul_left g b n)
    (fun c n ↦ map_smul g (op c) n) (fun c p ↦ map_smul_left h c p)
  have hlin :
      (tensorMap f (tensorMap g h)).val.toLinearMap.restrictScalars R ∘ₗ
          (tensorAssoc M N P).hom.val.toLinearMap.restrictScalars R =
        (tensorAssoc M' N' P').hom.val.toLinearMap.restrictScalars R ∘ₗ
          (tensorMap (tensorMap f g) h).val.toLinearMap.restrictScalars R := by
    -- Specify each tensor map: the nested bundled carriers obstruct generic rewriting.
    simp_rw [tensorMap_toLinearMap f (tensorMap g h),
      tensorMap_toLinearMap (tensorMap f g) h, tensorMap_toLinearMap f g,
      tensorMap_toLinearMap g h, tensorAssoc_hom_toLinearMap M N P,
      tensorAssoc_hom_toLinearMap M' N' P']
    exact hnat
  apply hom_ext
  intro z
  simp only [comp_apply (tensorMap (tensorMap f g) h) (tensorAssoc M' N' P').hom,
    comp_apply (tensorAssoc M N P).hom (tensorMap f (tensorMap g h))]
  simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    DGRightModuleHom.coe_toLinearMap, DGBimoduleHom.coe_val]
    using (LinearMap.congr_fun hlin z).symm

variable {E : Type uE} [Ring E] [Algebra R E]
  {ℰ : ℤ → Submodule R E} [GradedAlgebra ℰ] {dE : E →ₗ[R] E}
  {hE : IsDGAlgebra ℰ dE}

/-- The two reassociation paths for four composable DG bimodules agree. -/
theorem tensorAssoc_pentagon (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB)
    (N : DGBimoduleCat.{uR, uB, uC, uN} hB hC)
    (P : DGBimoduleCat.{uR, uC, uD, uP} hC hD)
    (Q : DGBimoduleCat.{uR, uD, uE, uQ} hD hE) :
    tensorMap (tensorAssoc M N P).hom (𝟙 Q) ≫
        (tensorAssoc M (tensorObj N P) Q).hom ≫
        tensorMap (𝟙 M) (tensorAssoc N P Q).hom =
      (tensorAssoc (tensorObj M N) P Q).hom ≫
        (tensorAssoc M N (tensorObj P Q)).hom := by
  have hpent := BalancedTensorProduct.pentagon
    (k := R) (B := B) (C := C) (D := D) (M := M) (N := N) (P := P) (Q := Q)
  have hlin :
      (tensorMap (𝟙 M) (tensorAssoc N P Q).hom).val.toLinearMap.restrictScalars R ∘ₗ
        (tensorAssoc M (tensorObj N P) Q).hom.val.toLinearMap.restrictScalars R ∘ₗ
        (tensorMap (tensorAssoc M N P).hom (𝟙 Q)).val.toLinearMap.restrictScalars R =
      (tensorAssoc M N (tensorObj P Q)).hom.val.toLinearMap.restrictScalars R ∘ₗ
        (tensorAssoc (tensorObj M N) P Q).hom.val.toLinearMap.restrictScalars R := by
    have hMId : (𝟙 M : M ⟶ M).val.toLinearMap.restrictScalars R = LinearMap.id := by
      ext x
      exact id_apply M x
    have hQId : (𝟙 Q : Q ⟶ Q).val.toLinearMap.restrictScalars R = LinearMap.id := by
      ext x
      exact id_apply Q x
    -- Specify the objects to preserve the selected outer actions on nested tensors.
    simp_rw [tensorMap_toLinearMap (𝟙 M) (tensorAssoc N P Q).hom,
      tensorMap_toLinearMap (tensorAssoc M N P).hom (𝟙 Q),
      tensorAssoc_hom_toLinearMap N P Q,
      tensorAssoc_hom_toLinearMap M (tensorObj N P) Q,
      tensorAssoc_hom_toLinearMap M N P,
      tensorAssoc_hom_toLinearMap M N (tensorObj P Q),
      tensorAssoc_hom_toLinearMap (tensorObj M N) P Q, hMId, hQId]
    exact hpent
  apply hom_ext
  intro z
  rw [comp_apply, comp_apply, comp_apply]
  simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    DGRightModuleHom.coe_toLinearMap, DGBimoduleHom.coe_val]
    using LinearMap.congr_fun hlin z

end TauCeti.DGBimoduleCat
