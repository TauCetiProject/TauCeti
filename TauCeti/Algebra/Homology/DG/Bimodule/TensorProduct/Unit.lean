/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ULift
public import TauCeti.Algebra.Homology.DG.Bimodule.TensorProduct.Functor
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Grading.Unit

/-!
# Units for tensor products of DG bimodules

The regular DG bimodule is a two-sided unit for balanced tensor composition. Its carrier is
universe-lifted to the universe of the bimodule being tensored, while its grading and differential
are transported without a degree shift. The resulting unit isomorphisms evaluate the regular
factor by the appropriate action, and their inverses insert the algebra unit.

These are isomorphisms for the ordinary balanced tensor product. Derived tensor products still
require suitable resolutions.

## References

* B. Keller, *Deriving DG categories*, Section 6.1.
-/

public section

noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti.DGBimoduleCat

universe v uR uA uB

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : A →ₗ[R] A}

variable (hA : IsDGAlgebra 𝒜 dA)

/-- The universe-lifted regular DG bimodule of a DG algebra. -/
@[expose]
def tensorUnit : DGBimoduleCat.{uR, uA, uA, max v uA} hA hA := by
  let E := (ULift.moduleEquiv : ULift.{v} A ≃ₗ[R] A).symm
  let G₀ := InternalGrading.ofDecomposition 𝒜
  let G := G₀.map E
  have mem_G_iff (p : ℤ) (x : ULift.{v} A) : x ∈ G.piece p ↔ x.down ∈ 𝒜 p := by
    rw [G₀.mem_map_ulift_piece_iff, InternalGrading.ofDecomposition_piece]
  letI : SMulCommClass A Aᵐᵒᵖ (ULift.{v} A) :=
    ⟨fun a b x ↦ by
      apply ULift.ext
      simpa only [ULift.smul_down] using smul_comm a b x.down⟩
  letI : SetLike.GradedSMul 𝒜 G.piece :=
    ⟨fun {p q} {a x} ha hx ↦ by
      rw [mem_G_iff] at hx ⊢
      simpa only [ULift.smul_down, smul_eq_mul, vadd_eq_add] using
        SetLike.GradedMul.mul_mem ha hx⟩
  letI : SetLike.GradedSMul G₀.opposite.piece G.piece :=
    ⟨fun {p q} {a x} ha hx ↦ by
      rw [mem_G_iff] at hx ⊢
      have ha' : unop a ∈ 𝒜 p := by
        simpa only [G₀, InternalGrading.ofDecomposition_piece] using
          (G₀.mem_opposite_piece_iff p a).1 ha
      simpa only [ULift.smul_down, MulOpposite.smul_eq_mul_unop, add_comm, vadd_eq_add] using
        SetLike.GradedMul.mul_mem hx ha'⟩
  let dU : ULift.{v} A →ₗ[R] ULift.{v} A :=
    E.toLinearMap.comp (dA.comp E.symm.toLinearMap)
  refine of (ℳ := G.piece) (dM := dU) ?_
  refine
    { isHomogeneous := LinearMap.isHomogeneous_def.2 fun p x hx ↦ ?_
      sq_zero := fun x ↦ ?_
      leibniz := fun {p a} ha x ↦ ?_
      leibniz_right := fun {q x} hx a ↦ ?_ }
  · rw [mem_G_iff] at hx ⊢
    simpa only [E, dU, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_symm, ULift.moduleEquiv_apply,
      ULift.moduleEquiv_symm_apply, ULift.down_up] using
      hA.map_mem hx
  · apply ULift.ext
    simpa only [E, dU, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_symm, ULift.moduleEquiv_apply,
      ULift.moduleEquiv_symm_apply, ULift.down_up, ULift.zero_down] using
      hA.sq_zero x.down
  · apply ULift.ext
    simpa only [E, dU, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_symm, ULift.moduleEquiv_apply,
      ULift.moduleEquiv_symm_apply, ULift.down_up,
      ULift.smul_down, smul_eq_mul, ULift.add_down] using hA.leibniz ha x.down
  · rw [mem_G_iff] at hx
    apply ULift.ext
    simpa only [E, dU, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_symm, ULift.moduleEquiv_apply,
      ULift.moduleEquiv_symm_apply, ULift.down_up,
      ULift.smul_down, MulOpposite.smul_eq_mul_unop, unop_op, ULift.add_down] using
      hA.isDGRightModule.leibniz hx a

/-- The regular DG-bimodule carrier is linearly equivalent to the algebra. -/
def tensorUnitEquiv : A ≃ₗ[R] tensorUnit.{v} hA :=
  (ULift.moduleEquiv : ULift.{v} A ≃ₗ[R] A).symm

/-- The carrier equivalence sends an algebra element to its universe lift. -/
@[simp]
theorem tensorUnitEquiv_apply (a : A) :
    tensorUnitEquiv.{v} hA a = ULift.up a := by
  rw [tensorUnitEquiv]
  exact ULift.moduleEquiv_symm_apply a

/-- The inverse carrier equivalence lowers a regular-bimodule element. -/
@[simp]
theorem tensorUnitEquiv_symm_apply (x : tensorUnit.{v} hA) :
    (tensorUnitEquiv.{v} hA).symm x = x.down := by
  rw [LinearEquiv.symm_apply_eq, tensorUnitEquiv_apply]
  exact (ULift.up_down x).symm

/-- The grading of the regular DG bimodule is the transported algebra grading. -/
theorem tensorUnit_grading : (tensorUnit.{v} hA).grading =
    ((InternalGrading.ofDecomposition 𝒜).map
      ((ULift.moduleEquiv : ULift.{v} A ≃ₗ[R] A).symm)).piece := rfl

/-- Membership in a graded piece of the regular bimodule is detected after lowering. -/
@[simp]
theorem mem_tensorUnit_grading_iff (p : ℤ) (x : tensorUnit.{v} hA) :
    x ∈ (tensorUnit.{v} hA).grading p ↔ x.down ∈ 𝒜 p := by
  rw [tensorUnit_grading]
  exact ((InternalGrading.ofDecomposition 𝒜).mem_map_ulift_piece_iff p x).trans <| by
    rw [InternalGrading.ofDecomposition_piece]

/-- Lowering converts the regular bimodule's left action to multiplication. -/
@[simp]
theorem tensorUnit_smul_down (a : A) (x : tensorUnit.{v} hA) :
    (a • x).down = a * x.down := rfl

/-- Lowering converts the regular bimodule's right action to multiplication. -/
@[simp]
theorem tensorUnit_op_smul_down (b : A) (x : tensorUnit.{v} hA) :
    (op b • x).down = x.down * b := rfl

/-- The regular bimodule differential is the lifted algebra differential. -/
@[simp]
theorem tensorUnit_differential_apply (x : tensorUnit.{v} hA) :
    (tensorUnit.{v} hA).differential x = ULift.up (dA x.down) := rfl

/-- The carrier equivalence identifies the two-sided action with multiplication. -/
theorem tensorUnitEquiv_smul (a b x : A) :
    a • (op b • tensorUnitEquiv.{v} hA x) = tensorUnitEquiv.{v} hA (a * x * b) := by
  apply ULift.ext
  rw [tensorUnit_smul_down, tensorUnit_op_smul_down, tensorUnitEquiv_apply,
    tensorUnitEquiv_apply]
  simp only [mul_assoc]

/-- The lifted algebra unit has degree zero in the regular DG bimodule. -/
theorem tensorUnitEquiv_one_mem_grading_zero :
    tensorUnitEquiv.{v} hA 1 ∈ (tensorUnit.{v} hA).grading 0 := by
  rw [mem_tensorUnit_grading_iff, tensorUnitEquiv_apply, ULift.down_up]
  exact SetLike.one_mem_graded 𝒜

/-- The differential of the lifted algebra unit vanishes. -/
theorem tensorUnit_differential_one :
    (tensorUnit.{v} hA).differential (tensorUnitEquiv.{v} hA 1) = 0 := by
  rw [tensorUnit_differential_apply, tensorUnitEquiv_apply, hA.map_one_eq_zero]
  rfl

open BalancedTensorProduct

attribute [local instance 100] leftModule rightModule leftIsScalarTower rightIsScalarTower
  outerSMulCommClass

attribute [local instance] tensorGradedOuterLeft tensorGradedOuterRight

section LeftUnitor

variable {B : Type uB} [Ring B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B}
  (hB : IsDGAlgebra ℬ dB)
  (M : DGBimoduleCat.{uR, uA, uB, max v uA} hA hB)

local instance tensorLeftUnitorGradedSMulUnitRight : SetLike.GradedSMul
    (InternalGrading.ofDecomposition 𝒜).opposite.piece
    (InternalGrading.ofDecomposition (tensorUnit.{v} hA).grading).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

local instance tensorLeftUnitorGradedSMulModuleLeft : SetLike.GradedSMul 𝒜
    (InternalGrading.ofDecomposition M.grading).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

local instance tensorLeftUnitorGradedSMulAlgebraRight : SetLike.GradedSMul
    (InternalGrading.ofDecomposition 𝒜).opposite.piece
    (InternalGrading.ofDecomposition 𝒜).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

/-- Evaluate the regular left tensor factor by its action on the second factor. -/
def tensorLeftUnitorHom : tensorObj (tensorUnit.{v} hA) M ⟶ M := by
  let f := (tensorUnitEquiv.{v} hA).symm
  let g := LinearEquiv.refl R M
  have hf : ∀ (a : A) x, f (op a • x) = op a • f x := by
    intro a x
    simp only [f, tensorUnitEquiv_symm_apply, tensorUnit_op_smul_down,
      MulOpposite.smul_eq_mul_unop, unop_op]
  have hg : ∀ (a : A) m, g (a • m) = a • g m := fun _ _ ↦ rfl
  let c := BalancedTensorProduct.congr f g hf hg
  let e := c.trans (lid R A M)
  have he (z) :
      e z = (lid R A M) (BalancedTensorProduct.map f.toLinearMap g.toLinearMap hf hg z) := by
    rw [LinearEquiv.trans_apply, congr_apply]
  have hf₀ : LinearMap.IsHomogeneous f.toLinearMap (tensorUnit.{v} hA).grading 𝒜 0 :=
    LinearMap.isHomogeneous_def.2 fun q x hx ↦ by
      simpa only [f, LinearEquiv.coe_coe, tensorUnitEquiv_symm_apply, add_zero] using
        (mem_tensorUnit_grading_iff hA q x).1 hx
  let T : tensorObj (tensorUnit.{v} hA) M →ₗ[Bᵐᵒᵖ] M :=
    { toFun := e
      map_add' := map_add e
      map_smul' := fun b z ↦ by
        dsimp only [e, LinearEquiv.trans_apply]
        rw [RingHom.id_apply, congr_smul_right Bᵐᵒᵖ f g hf hg (fun _ _ ↦ rfl),
          lid_smul_right] }
  have hT (z) : T z = e z := rfl
  refine ⟨⟨T, ?_, ?_⟩, ?_⟩
  · intro p z hz
    have hf₀' : LinearMap.IsHomogeneous f.toLinearMap
        (InternalGrading.ofDecomposition (tensorUnit.{v} hA).grading).piece
        (InternalGrading.ofDecomposition 𝒜).piece 0 := by
      simpa only [InternalGrading.ofDecomposition_piece] using hf₀
    have hg₀ : LinearMap.IsHomogeneous g.toLinearMap
        (InternalGrading.ofDecomposition M.grading).piece
        (InternalGrading.ofDecomposition M.grading).piece 0 := by
      simpa only [g, LinearEquiv.refl_toLinearMap] using
        LinearMap.isHomogeneous_id (InternalGrading.ofDecomposition M.grading).piece
    have hc := (isHomogeneous_map
      (InternalGrading.ofDecomposition (tensorUnit.{v} hA).grading)
      (InternalGrading.ofDecomposition M.grading)
      (InternalGrading.ofDecomposition 𝒜)
      (InternalGrading.ofDecomposition M.grading)
      f.toLinearMap g.toLinearMap hf hg hf₀' hg₀).map_mem hz
    have hl := Submodule.mem_map_of_mem (f := (lid R A M).toLinearMap) (by
      simpa only [add_zero] using hc)
    rw [map_lid_grading_piece (𝒜 := 𝒜)
      (InternalGrading.ofDecomposition M.grading) p,
      InternalGrading.ofDecomposition_piece] at hl
    rw [hT, he]
    exact hl
  · intro z
    have hfd : dA ∘ₗ f.toLinearMap =
        f.toLinearMap ∘ₗ (tensorUnit.{v} hA).differential := by
      ext x
      calc
        dA x.down = ((tensorUnit.{v} hA).differential x).down := by
          rw [tensorUnit_differential_apply]
        _ = (tensorUnitEquiv.{v} hA).symm
            ((tensorUnit.{v} hA).differential x) :=
          (tensorUnitEquiv_symm_apply hA _).symm
    have hgd : M.differential ∘ₗ g.toLinearMap = g.toLinearMap ∘ₗ M.differential := by
      ext m
      simp only [LinearMap.comp_apply, g, LinearEquiv.coe_toLinearMap,
        LinearEquiv.refl_apply]
    have hc := LinearMap.congr_fun
      (differential_naturality (tensorUnit.{v} hA).isDGRightModule M.isDGLeftModule
        hA.isDGRightModule M.isDGLeftModule f.toLinearMap g.toLinearMap hf hg hf₀ hfd hgd) z
    have hl := LinearMap.congr_fun (lid_comp_differential hA M.isDGLeftModule)
      (BalancedTensorProduct.map f.toLinearMap g.toLinearMap hf hg z)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hc hl
    rw [hT, hT, he, he, ← hc, hl]
  · rw [mem_dgBimoduleHomSubmodule]
    intro a z
    rw [DGRightModuleHom.coe_mk, hT, hT]
    dsimp only [e, LinearEquiv.trans_apply]
    rw [congr_smul_left A f g hf hg (fun a x ↦ by
      simp only [f, tensorUnitEquiv_symm_apply, tensorUnit_smul_down, smul_eq_mul]),
      lid_smul_left]

/-- The left unitor evaluates a pure tensor by the left action. -/
@[simp]
theorem tensorLeftUnitorHom_tmul (x : tensorUnit.{v} hA) (m : M) :
    tensorLeftUnitorHom.{v} hA hB M (tmul R A x m) = x.down • m := by
  rw [← DGBimoduleHom.coe_val]
  dsimp only [tensorLeftUnitorHom, DGRightModuleHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  rw [LinearEquiv.trans_apply]
  refine (congrArg (lid R A M) (congr_tmul _ _ _ _ x m)).trans ?_
  rw [lid_tmul, LinearEquiv.refl_apply, tensorUnitEquiv_symm_apply]

/-- Insert `1` in the regular left tensor factor. -/
def tensorLeftUnitorInv : M ⟶ tensorObj (tensorUnit.{v} hA) M := by
  let f := (tensorUnitEquiv.{v} hA).symm
  let g := LinearEquiv.refl R M
  have hf : ∀ (a : A) x, f (op a • x) = op a • f x := by
    intro a x
    simp only [f, tensorUnitEquiv_symm_apply, tensorUnit_op_smul_down,
      MulOpposite.smul_eq_mul_unop, unop_op]
  have hg : ∀ (a : A) m, g (a • m) = a • g m := fun _ _ ↦ rfl
  let c := BalancedTensorProduct.congr f g hf hg
  let e := c.trans (lid R A M)
  have he_apply (m : M) : e.symm m = tmul R A (tensorUnitEquiv.{v} hA 1) m := by
    dsimp only [e, c, LinearEquiv.symm_trans_apply]
    rw [lid_symm_apply, congr_symm_tmul, LinearEquiv.refl_symm,
      LinearEquiv.refl_apply, LinearEquiv.symm_symm, tensorUnitEquiv_apply]
  let T : M →ₗ[Bᵐᵒᵖ] tensorObj (tensorUnit.{v} hA) M :=
    { toFun := e.symm
      map_add' := map_add e.symm
      map_smul' := fun b m ↦ by
        rw [he_apply, he_apply, RingHom.id_apply, smul_tmul_right] }
  have hT (m) : T m = tmul R A (tensorUnitEquiv.{v} hA 1) m := he_apply m
  refine ⟨⟨T, ?_, ?_⟩, ?_⟩
  · intro p m hm
    rw [hT]
    simpa only [zero_add] using
      tmul_mem_tensorObj_grading (M := tensorUnit.{v} hA) (N := M)
        (tensorUnitEquiv_one_mem_grading_zero hA) hm
  · intro m
    rw [hT, hT, tensorObj_differential_tmul (tensorUnitEquiv_one_mem_grading_zero hA) m,
      tensorUnit_differential_one]
    simp
  · rw [mem_dgBimoduleHomSubmodule]
    intro a m
    rw [DGRightModuleHom.coe_mk, hT, hT, smul_tmul_left]
    have h := balance R A a (tensorUnitEquiv.{v} hA 1) m
    have heq : op a • tensorUnitEquiv.{v} hA 1 =
        a • tensorUnitEquiv.{v} hA 1 := by
      apply ULift.ext
      rw [tensorUnit_op_smul_down, tensorUnit_smul_down, tensorUnitEquiv_apply]
      simp only [one_mul, mul_one]
    rw [heq] at h
    exact h.symm

/-- The inverse left unitor inserts the algebra unit. -/
@[simp]
theorem tensorLeftUnitorInv_apply (m : M) :
    tensorLeftUnitorInv.{v} hA hB M m =
      tmul R A (tensorUnitEquiv.{v} hA 1) m := by
  rw [← DGBimoduleHom.coe_val]
  dsimp only [tensorLeftUnitorInv, DGRightModuleHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  rw [LinearEquiv.symm_trans_apply, lid_symm_apply]
  refine (congr_symm_tmul _ _ _ _ (1 : A) m).trans ?_
  rw [LinearEquiv.symm_symm, LinearEquiv.refl_symm, LinearEquiv.refl_apply]

/-- The regular DG bimodule is a left unit for tensor composition. -/
def tensorLeftUnitor : tensorObj (tensorUnit.{v} hA) M ≅ M where
  hom := tensorLeftUnitorHom.{v} hA hB M
  inv := tensorLeftUnitorInv.{v} hA hB M
  hom_inv_id := by
    apply tensorObj_hom_ext
    intro x m
    rw [comp_apply, tensorLeftUnitorHom_tmul, tensorLeftUnitorInv_apply, id_apply]
    have h := balance R A x.down (tensorUnitEquiv.{v} hA 1) m
    have heq : op x.down • tensorUnitEquiv.{v} hA 1 = x := by
      apply ULift.ext
      rw [tensorUnit_op_smul_down, tensorUnitEquiv_apply]
      simp only [one_mul]
    rw [heq] at h
    exact h.symm
  inv_hom_id := by
    apply hom_ext
    intro m
    rw [comp_apply, tensorLeftUnitorInv_apply, tensorLeftUnitorHom_tmul, id_apply]
    simp only [tensorUnitEquiv_apply, ULift.down_up, one_smul]

/-- The left-unit isomorphism has the evaluation map as its forward morphism. -/
@[simp]
theorem tensorLeftUnitor_hom :
    (tensorLeftUnitor.{v} hA hB M).hom = tensorLeftUnitorHom.{v} hA hB M := (rfl)

/-- The left-unit isomorphism has the unit-insertion map as its inverse morphism. -/
@[simp]
theorem tensorLeftUnitor_inv :
    (tensorLeftUnitor.{v} hA hB M).inv = tensorLeftUnitorInv.{v} hA hB M := (rfl)

/-- The left unitor is natural in the DG bimodule. -/
@[reassoc (attr := simp)]
theorem tensorLeftUnitorHom_naturality
    {N : DGBimoduleCat.{uR, uA, uB, max v uA} hA hB} (f : M ⟶ N) :
    tensorMap (𝟙 (tensorUnit.{v} hA)) f ≫ tensorLeftUnitorHom.{v} hA hB N =
      tensorLeftUnitorHom.{v} hA hB M ≫ f := by
  apply tensorObj_hom_ext
  intro x m
  rw [comp_apply, comp_apply, tensorMap_tmul, id_apply,
    tensorLeftUnitorHom_tmul, tensorLeftUnitorHom_tmul, map_smul_left]

end LeftUnitor

section RightUnitor

variable {B : Type uB} [Ring B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B}
  (hB : IsDGAlgebra ℬ dB)
  (M : DGBimoduleCat.{uR, uA, uB, max v uB} hA hB)

local instance tensorRightUnitorGradedSMulModuleRight : SetLike.GradedSMul
    (InternalGrading.ofDecomposition ℬ).opposite.piece
    (InternalGrading.ofDecomposition M.grading).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

local instance tensorRightUnitorGradedSMulUnitLeft : SetLike.GradedSMul ℬ
    (InternalGrading.ofDecomposition (tensorUnit.{v} hB).grading).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

local instance tensorRightUnitorGradedSMulAlgebraLeft : SetLike.GradedSMul ℬ
    (InternalGrading.ofDecomposition ℬ).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

/-- Evaluate the regular right tensor factor by its action on the first factor. -/
def tensorRightUnitorHom : tensorObj M (tensorUnit.{v} hB) ⟶ M := by
  let f := LinearEquiv.refl R M
  let g := (tensorUnitEquiv.{v} hB).symm
  have hf : ∀ (b : B) m, f (op b • m) = op b • f m := fun _ _ ↦ rfl
  have hg : ∀ (b : B) x, g (b • x) = b • g x := by
    intro b x
    simp only [g, tensorUnitEquiv_symm_apply, tensorUnit_smul_down, smul_eq_mul]
  let c := BalancedTensorProduct.congr f g hf hg
  let e := c.trans (rid R B M)
  have he (z) :
      e z = (rid R B M) (BalancedTensorProduct.map f.toLinearMap g.toLinearMap hf hg z) := by
    rw [LinearEquiv.trans_apply, congr_apply]
  have hf₀ : LinearMap.IsHomogeneous f.toLinearMap M.grading M.grading 0 := by
    simpa only [f, LinearEquiv.refl_toLinearMap] using LinearMap.isHomogeneous_id M.grading
  have hg₀ : LinearMap.IsHomogeneous g.toLinearMap (tensorUnit.{v} hB).grading ℬ 0 :=
    LinearMap.isHomogeneous_def.2 fun q x hx ↦ by
      simpa only [g, LinearEquiv.coe_coe, tensorUnitEquiv_symm_apply, add_zero] using
        (mem_tensorUnit_grading_iff hB q x).1 hx
  let T : tensorObj M (tensorUnit.{v} hB) →ₗ[Bᵐᵒᵖ] M :=
    { toFun := e
      map_add' := map_add e
      map_smul' := fun b z ↦ by
        dsimp only [e, LinearEquiv.trans_apply]
        rw [RingHom.id_apply, congr_smul_right Bᵐᵒᵖ f g hf hg (fun b x ↦ by
          simp only [g, tensorUnitEquiv_symm_apply, MulOpposite.smul_eq_mul_unop]
          rw [← op_unop b, tensorUnit_op_smul_down]
          simp only [unop_op]), rid_smul_right] }
  have hT (z) : T z = e z := rfl
  refine ⟨⟨T, ?_, ?_⟩, ?_⟩
  · intro p z hz
    have hf₀' : LinearMap.IsHomogeneous f.toLinearMap
        (InternalGrading.ofDecomposition M.grading).piece
        (InternalGrading.ofDecomposition M.grading).piece 0 := by
      simpa only [InternalGrading.ofDecomposition_piece] using hf₀
    have hg₀' : LinearMap.IsHomogeneous g.toLinearMap
        (InternalGrading.ofDecomposition (tensorUnit.{v} hB).grading).piece
        (InternalGrading.ofDecomposition ℬ).piece 0 := by
      simpa only [InternalGrading.ofDecomposition_piece] using hg₀
    have hc := (isHomogeneous_map
      (InternalGrading.ofDecomposition M.grading)
      (InternalGrading.ofDecomposition (tensorUnit.{v} hB).grading)
      (InternalGrading.ofDecomposition M.grading)
      (InternalGrading.ofDecomposition ℬ)
      f.toLinearMap g.toLinearMap hf hg hf₀' hg₀').map_mem hz
    have hr := Submodule.mem_map_of_mem (f := (rid R B M).toLinearMap) (by
      simpa only [add_zero] using hc)
    rw [map_rid_grading_piece (𝒜 := ℬ)
      (InternalGrading.ofDecomposition M.grading) p,
      InternalGrading.ofDecomposition_piece] at hr
    rw [hT, he]
    exact hr
  · intro z
    have hfd : M.differential ∘ₗ f.toLinearMap = f.toLinearMap ∘ₗ M.differential := by
      ext m
      simp only [LinearMap.comp_apply, f, LinearEquiv.coe_toLinearMap,
        LinearEquiv.refl_apply]
    have hgd : dB ∘ₗ g.toLinearMap =
        g.toLinearMap ∘ₗ (tensorUnit.{v} hB).differential := by
      ext x
      calc
        dB x.down = ((tensorUnit.{v} hB).differential x).down := by
          rw [tensorUnit_differential_apply]
        _ = (tensorUnitEquiv.{v} hB).symm
            ((tensorUnit.{v} hB).differential x) :=
          (tensorUnitEquiv_symm_apply hB _).symm
    have hc := LinearMap.congr_fun
      (differential_naturality M.isDGRightModule (tensorUnit.{v} hB).isDGLeftModule
        M.isDGRightModule hB.isDGLeftModule f.toLinearMap g.toLinearMap hf hg hf₀ hfd hgd) z
    have hr := LinearMap.congr_fun (rid_comp_differential hB M.isDGRightModule)
      (BalancedTensorProduct.map f.toLinearMap g.toLinearMap hf hg z)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hc hr
    rw [hT, hT, he, he, ← hc, hr]
  · rw [mem_dgBimoduleHomSubmodule]
    intro a z
    rw [DGRightModuleHom.coe_mk, hT, hT]
    dsimp only [e, LinearEquiv.trans_apply]
    rw [congr_smul_left A f g hf hg (fun _ _ ↦ rfl), rid_smul_left]

/-- The right unitor evaluates a pure tensor by the right action. -/
@[simp]
theorem tensorRightUnitorHom_tmul (m : M) (x : tensorUnit.{v} hB) :
    tensorRightUnitorHom.{v} hA hB M (tmul R B m x) = op x.down • m := by
  rw [← DGBimoduleHom.coe_val]
  dsimp only [tensorRightUnitorHom, DGRightModuleHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  rw [LinearEquiv.trans_apply]
  refine (congrArg (rid R B M) (congr_tmul _ _ _ _ m x)).trans ?_
  rw [rid_tmul, LinearEquiv.refl_apply, tensorUnitEquiv_symm_apply]

/-- Insert `1` in the regular right tensor factor. -/
def tensorRightUnitorInv : M ⟶ tensorObj M (tensorUnit.{v} hB) := by
  let f := LinearEquiv.refl R M
  let g := (tensorUnitEquiv.{v} hB).symm
  have hf : ∀ (b : B) m, f (op b • m) = op b • f m := fun _ _ ↦ rfl
  have hg : ∀ (b : B) x, g (b • x) = b • g x := by
    intro b x
    simp only [g, tensorUnitEquiv_symm_apply, tensorUnit_smul_down, smul_eq_mul]
  let c := BalancedTensorProduct.congr f g hf hg
  let e := c.trans (rid R B M)
  have he_apply (m : M) : e.symm m = tmul R B m (tensorUnitEquiv.{v} hB 1) := by
    dsimp only [e, c, LinearEquiv.symm_trans_apply]
    rw [rid_symm_apply, congr_symm_tmul, LinearEquiv.refl_symm,
      LinearEquiv.refl_apply, LinearEquiv.symm_symm]
  let T : M →ₗ[Bᵐᵒᵖ] tensorObj M (tensorUnit.{v} hB) :=
    { toFun := e.symm
      map_add' := map_add e.symm
      map_smul' := fun b m ↦ by
        rw [he_apply, he_apply, RingHom.id_apply, smul_tmul_right]
        have h := balance R B (unop b) m (tensorUnitEquiv.{v} hB 1)
        have heq : unop b • tensorUnitEquiv.{v} hB 1 =
            b • tensorUnitEquiv.{v} hB 1 := by
          apply ULift.ext
          rw [tensorUnit_smul_down, ← op_unop b, tensorUnit_op_smul_down,
            tensorUnitEquiv_apply]
          simp only [mul_one, one_mul, unop_op]
        rw [heq] at h
        exact h }
  have hT (m) : T m = tmul R B m (tensorUnitEquiv.{v} hB 1) := he_apply m
  refine ⟨⟨T, ?_, ?_⟩, ?_⟩
  · intro p m hm
    rw [hT]
    simpa only [add_zero] using
      tmul_mem_tensorObj_grading (M := M) (N := tensorUnit.{v} hB) hm
        (tensorUnitEquiv_one_mem_grading_zero hB)
  · intro m
    rw [hT, hT]
    induction m using DirectSum.Decomposition.inductionOn M.grading with
    | zero => rw [zero_tmul, map_zero, map_zero, zero_tmul]
    | add m n hm hn => simp only [add_tmul, map_add, hm, hn]
    | @homogeneous p m =>
        rw [tensorObj_differential_tmul m.property (tensorUnitEquiv.{v} hB 1),
          tensorUnit_differential_one]
        simp
  · rw [mem_dgBimoduleHomSubmodule]
    intro a m
    rw [DGRightModuleHom.coe_mk, hT, hT, smul_tmul_left]

/-- The inverse right unitor inserts the algebra unit. -/
@[simp]
theorem tensorRightUnitorInv_apply (m : M) :
    tensorRightUnitorInv.{v} hA hB M m =
      tmul R B m (tensorUnitEquiv.{v} hB 1) := by
  rw [← DGBimoduleHom.coe_val]
  dsimp only [tensorRightUnitorInv, DGRightModuleHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  rw [LinearEquiv.symm_trans_apply, rid_symm_apply]
  refine (congr_symm_tmul _ _ _ _ m (1 : B)).trans ?_
  rw [LinearEquiv.symm_symm, LinearEquiv.refl_symm, LinearEquiv.refl_apply]

/-- The regular DG bimodule is a right unit for tensor composition. -/
def tensorRightUnitor : tensorObj M (tensorUnit.{v} hB) ≅ M where
  hom := tensorRightUnitorHom.{v} hA hB M
  inv := tensorRightUnitorInv.{v} hA hB M
  hom_inv_id := by
    apply tensorObj_hom_ext
    intro m x
    rw [comp_apply, tensorRightUnitorHom_tmul, tensorRightUnitorInv_apply, id_apply]
    have h := balance R B x.down m (tensorUnitEquiv.{v} hB 1)
    have heq : x.down • tensorUnitEquiv.{v} hB 1 = x := by
      apply ULift.ext
      rw [tensorUnit_smul_down, tensorUnitEquiv_apply]
      simp only [mul_one]
    rw [heq] at h
    exact h
  inv_hom_id := by
    apply hom_ext
    intro m
    rw [comp_apply, tensorRightUnitorInv_apply, tensorRightUnitorHom_tmul, id_apply]
    simp only [tensorUnitEquiv_apply, ULift.down_up, op_one, one_smul]

/-- The right-unit isomorphism has the evaluation map as its forward morphism. -/
@[simp]
theorem tensorRightUnitor_hom :
    (tensorRightUnitor.{v} hA hB M).hom = tensorRightUnitorHom.{v} hA hB M := (rfl)

/-- The right-unit isomorphism has the unit-insertion map as its inverse morphism. -/
@[simp]
theorem tensorRightUnitor_inv :
    (tensorRightUnitor.{v} hA hB M).inv = tensorRightUnitorInv.{v} hA hB M := (rfl)

/-- The right unitor is natural in the DG bimodule. -/
@[reassoc (attr := simp)]
theorem tensorRightUnitorHom_naturality
    {N : DGBimoduleCat.{uR, uA, uB, max v uB} hA hB} (f : M ⟶ N) :
    tensorMap f (𝟙 (tensorUnit.{v} hB)) ≫ tensorRightUnitorHom.{v} hA hB N =
      tensorRightUnitorHom.{v} hA hB M ≫ f := by
  apply tensorObj_hom_ext
  intro m x
  rw [comp_apply, comp_apply, tensorMap_tmul, id_apply,
    tensorRightUnitorHom_tmul, tensorRightUnitorHom_tmul]
  exact (map_smul f (op x.down) m).symm

end RightUnitor

/-- The left and right unitors agree on the tensor square of the regular DG bimodule. -/
theorem tensorUnitors_equal :
    tensorLeftUnitorHom.{v} hA hA (tensorUnit.{v} hA) =
      tensorRightUnitorHom.{v} hA hA (tensorUnit.{v} hA) := by
  apply tensorObj_hom_ext
  intro x y
  rw [tensorLeftUnitorHom_tmul, tensorRightUnitorHom_tmul]
  apply ULift.ext
  rw [tensorUnit_smul_down, tensorUnit_op_smul_down]

end TauCeti.DGBimoduleCat
