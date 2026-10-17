/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ULift
public import TauCeti.Algebra.Homology.DG.Bimodule.TensorProduct.Functor

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
  letI : SMulCommClass A Aᵐᵒᵖ (ULift.{v} A) :=
    ⟨fun a b x ↦ by apply ULift.ext; exact smul_comm a b x.down⟩
  letI : SetLike.GradedSMul 𝒜 G.piece :=
    ⟨fun {p q} {a x} ha hx ↦ by
      apply (G₀.mem_map_piece_iff E (p + q) _).2
      have hx' := (G₀.mem_map_piece_iff E q x).1 hx
      have hx'' : x.down ∈ 𝒜 q := by
        simpa only [E, G₀, LinearEquiv.symm_symm, ULift.moduleEquiv_apply,
          InternalGrading.ofDecomposition_piece] using hx'
      dsimp [E, G₀]
      rw [ULift.moduleEquiv_apply, InternalGrading.ofDecomposition_piece]
      change a * x.down ∈ 𝒜 (p + q)
      exact SetLike.GradedMul.mul_mem ha hx''⟩
  letI : SetLike.GradedSMul G₀.opposite.piece G.piece :=
    ⟨fun {p q} {a x} ha hx ↦ by
      apply (G₀.mem_map_piece_iff E (p + q) _).2
      have ha' : unop a ∈ 𝒜 p := by
        simpa only [G₀, InternalGrading.ofDecomposition_piece] using
          (G₀.mem_opposite_piece_iff p a).1 ha
      have hx' := (G₀.mem_map_piece_iff E q x).1 hx
      have hx'' : x.down ∈ 𝒜 q := by
        simpa only [E, G₀, LinearEquiv.symm_symm, ULift.moduleEquiv_apply,
          InternalGrading.ofDecomposition_piece] using hx'
      dsimp [E, G₀]
      rw [ULift.moduleEquiv_apply, InternalGrading.ofDecomposition_piece]
      change x.down * unop a ∈ 𝒜 (p + q)
      simpa only [add_comm] using SetLike.GradedMul.mul_mem hx'' ha'⟩
  let dU : ULift.{v} A →ₗ[R] ULift.{v} A :=
    E.toLinearMap.comp (dA.comp E.symm.toLinearMap)
  refine of (ℳ := G.piece) (dM := dU) ?_
  refine
    { isHomogeneous := LinearMap.isHomogeneous_def.2 fun p x hx ↦ ?_
      sq_zero := fun x ↦ ?_
      leibniz := fun {p a} ha x ↦ ?_
      leibniz_right := fun {q x} hx a ↦ ?_ }
  · apply (G₀.mem_map_piece_iff E (p + 1) _).2
    have hx' := (G₀.mem_map_piece_iff E p x).1 hx
    have hx'' : x.down ∈ 𝒜 p := by
      simpa only [E, G₀, LinearEquiv.symm_symm, ULift.moduleEquiv_apply,
        InternalGrading.ofDecomposition_piece] using hx'
    simpa only [E, G₀, dU, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_symm, ULift.moduleEquiv_apply,
      ULift.moduleEquiv_symm_apply, ULift.down_up,
      InternalGrading.ofDecomposition_piece] using hA.map_mem hx''
  · apply ULift.ext
    change dA (dA x.down) = 0
    exact hA.sq_zero x.down
  · apply ULift.ext
    change dA (a * x.down) = dA a * x.down + p.negOnePow • (a * dA x.down)
    exact hA.leibniz ha x.down
  · have hx' := (G₀.mem_map_piece_iff E q x).1 hx
    have hx'' : x.down ∈ 𝒜 q := by
      simpa only [E, G₀, LinearEquiv.symm_symm, ULift.moduleEquiv_apply,
        InternalGrading.ofDecomposition_piece] using hx'
    apply ULift.ext
    change dA (x.down * a) = dA x.down * a + q.negOnePow • (x.down * dA a)
    exact hA.isDGRightModule.leibniz hx'' a

/-- The regular DG-bimodule carrier is linearly equivalent to the algebra. -/
@[expose]
def tensorUnitEquiv : A ≃ₗ[R] tensorUnit.{v} hA :=
  (ULift.moduleEquiv : ULift.{v} A ≃ₗ[R] A).symm

@[simp]
theorem tensorUnitEquiv_apply (a : A) :
    tensorUnitEquiv.{v} hA a = ULift.up a := rfl

@[simp]
theorem tensorUnitEquiv_symm_apply (x : tensorUnit.{v} hA) :
    (tensorUnitEquiv.{v} hA).symm x = x.down := rfl

@[simp]
theorem mem_tensorUnit_grading_iff (p : ℤ) (x : tensorUnit.{v} hA) :
    x ∈ (tensorUnit.{v} hA).grading p ↔ x.down ∈ 𝒜 p := by
  change x ∈ ((InternalGrading.ofDecomposition 𝒜).map
    ((ULift.moduleEquiv : ULift.{v} A ≃ₗ[R] A).symm)).piece p ↔ _
  constructor
  · intro hx
    have h := ((InternalGrading.ofDecomposition 𝒜).mem_map_piece_iff
      ((ULift.moduleEquiv : ULift.{v} A ≃ₗ[R] A).symm) p x).1 hx
    change (tensorUnitEquiv.{v} hA).symm x ∈
      (InternalGrading.ofDecomposition 𝒜).piece p at h
    rw [tensorUnitEquiv_symm_apply, InternalGrading.ofDecomposition_piece] at h
    exact h
  · intro hx
    apply ((InternalGrading.ofDecomposition 𝒜).mem_map_piece_iff
      ((ULift.moduleEquiv : ULift.{v} A ≃ₗ[R] A).symm) p x).2
    change (tensorUnitEquiv.{v} hA).symm x ∈
      (InternalGrading.ofDecomposition 𝒜).piece p
    rw [tensorUnitEquiv_symm_apply, InternalGrading.ofDecomposition_piece]
    exact hx

@[simp]
theorem tensorUnit_differential_apply (x : tensorUnit.{v} hA) :
    (tensorUnit.{v} hA).differential x = ULift.up (dA x.down) := rfl

@[simp]
theorem tensorUnitEquiv_smul (a b x : A) :
    a • (op b • tensorUnitEquiv.{v} hA x) = tensorUnitEquiv.{v} hA (a * x * b) := by
  apply ULift.ext
  change a * (x * b) = (a * x) * b
  exact (mul_assoc a x b).symm

open BalancedTensorProduct

attribute [local instance 100] leftModule rightModule leftIsScalarTower rightIsScalarTower
  outerSMulCommClass

attribute [local instance] tensorGradedOuterLeft tensorGradedOuterRight

section LeftUnitor

variable {B : Type uB} [Ring B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B}
  (hB : IsDGAlgebra ℬ dB)
  (M : DGBimoduleCat.{uR, uA, uB, max v uA} hA hB)

private abbrev leftUnitAction : tensorUnit.{v} hA →ₗ[R] M →ₗ[R] M :=
  (Algebra.lsmul R R M (A := A)).toLinearMap.comp
    (tensorUnitEquiv.{v} hA).symm.toLinearMap

private theorem leftUnitAction_balanced (a : A) (x : tensorUnit.{v} hA) (m : M) :
    leftUnitAction.{v} hA hB M (op a • x) m =
      leftUnitAction.{v} hA hB M x (a • m) := by
  simp only [leftUnitAction, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    AlgHom.toLinearMap_apply, Algebra.lsmul_apply, tensorUnitEquiv_symm_apply]
  change (x.down * a) • m = x.down • a • m
  exact mul_smul x.down a m

private theorem leftUnitAction_degree {p q : ℤ} {x : tensorUnit.{v} hA} {m : M}
    (hx : x ∈ (tensorUnit.{v} hA).grading p) (hm : m ∈ M.grading q) :
    leftUnitAction.{v} hA hB M x m ∈ M.grading (p + q) := by
  simpa only [leftUnitAction, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    AlgHom.toLinearMap_apply, Algebra.lsmul_apply, tensorUnitEquiv_symm_apply,
    vadd_eq_add] using
    (SetLike.GradedSMul.smul_mem ((mem_tensorUnit_grading_iff hA p x).1 hx) hm :
      x.down • m ∈ M.grading (p + q))

local instance : SetLike.GradedSMul
    (InternalGrading.ofDecomposition 𝒜).opposite.piece
    (InternalGrading.ofDecomposition (tensorUnit.{v} hA).grading).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

local instance : SetLike.GradedSMul 𝒜
    (InternalGrading.ofDecomposition M.grading).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

/-- Evaluate the regular left tensor factor by its action on the second factor. -/
def tensorLeftUnitorHom : tensorObj (tensorUnit.{v} hA) M ⟶ M := by
  let F : tensorObj (tensorUnit.{v} hA) M →ₗ[R] M :=
    lift (leftUnitAction.{v} hA hB M) (leftUnitAction_balanced.{v} hA hB M)
  let T : tensorObj (tensorUnit.{v} hA) M →ₗ[Bᵐᵒᵖ] M :=
    { toFun := F
      map_add' := map_add F
      map_smul' := fun b z ↦ lift_smul_right Bᵐᵒᵖ
        (leftUnitAction.{v} hA hB M) (leftUnitAction_balanced.{v} hA hB M)
        (fun b x m ↦ by
          simp only [leftUnitAction, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
            AlgHom.toLinearMap_apply, Algebra.lsmul_apply]
          exact smul_comm _ b m) b z }
  refine ⟨⟨T, ?_, ?_⟩, ?_⟩
  · intro p z hz
    have hz' := (isHomogeneous_of_tmul
      (InternalGrading.ofDecomposition (tensorUnit.{v} hA).grading)
      (InternalGrading.ofDecomposition M.grading) M.grading F 0
      (fun hx hm ↦ by
        simpa only [F, lift_tmul, add_zero] using
          leftUnitAction_degree.{v} hA hB M
            (by simpa only [InternalGrading.ofDecomposition_piece] using hx)
            (by simpa only [InternalGrading.ofDecomposition_piece] using hm))).map_mem hz
    change F z ∈ M.grading p
    simpa only [add_zero] using hz'
  · intro z
    change M.differential (F z) = F ((tensorObj (tensorUnit.{v} hA) M).differential z)
    have hF (x : tensorUnit.{v} hA) (m : M) : F (tmul R A x m) = x.down • m := by
      dsimp [F]
      rw [lift_tmul]
      rfl
    induction z using induction_on with
    | ht x m =>
        induction x using DirectSum.Decomposition.inductionOn (tensorUnit.{v} hA).grading with
        | zero => simp [F]
        | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
        | @homogeneous p x =>
            rw [tensorObj_differential_tmul x.property m]
            simp only [map_add, Units.smul_def, map_zsmul, hF]
            rw [tensorUnit_differential_apply]
            change M.differential (x.val.down • m) =
              dA x.val.down • m + (p.negOnePow.val : ℤ) •
                (x.val.down • M.differential m)
            simpa only [Units.smul_def, Int.cast_smul_eq_zsmul] using
              M.isDGLeftModule.leibniz
                ((mem_tensorUnit_grading_iff hA p x).1 x.property) m
    | ha x y hx hy => simp only [map_add, hx, hy]
  · rw [mem_dgBimoduleHomSubmodule]
    intro a z
    exact lift_smul_left A (leftUnitAction.{v} hA hB M)
      (leftUnitAction_balanced.{v} hA hB M)
      (fun a x m ↦ by
        simp only [leftUnitAction, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
          AlgHom.toLinearMap_apply, Algebra.lsmul_apply, tensorUnitEquiv_symm_apply]
        change (a * x.down) • m = a • x.down • m
        exact mul_smul a x.down m) a z

@[simp]
theorem tensorLeftUnitorHom_tmul (x : tensorUnit.{v} hA) (m : M) :
    tensorLeftUnitorHom.{v} hA hB M (tmul R A x m) = x.down • m := by
  change (lift (leftUnitAction.{v} hA hB M)
    (leftUnitAction_balanced.{v} hA hB M)) (tmul R A x m) = _
  rw [lift_tmul]
  rfl

private abbrev leftUnitInsertBase :
    M →ₗ[R] tensorObj (tensorUnit.{v} hA) M where
  toFun m := tmul R A (tensorUnitEquiv.{v} hA 1) m
  map_add' m n := tmul_add R A (tensorUnitEquiv.{v} hA 1) m n
  map_smul' _ _ := tmul_smul _ _ _ _ _

private theorem leftUnitInsertBase_apply (m : M) :
    leftUnitInsertBase.{v} hA hB M m = tmul R A (tensorUnitEquiv.{v} hA 1) m := rfl

/-- Insert `1` in the regular left tensor factor. -/
def tensorLeftUnitorInv : M ⟶ tensorObj (tensorUnit.{v} hA) M := by
  let T : M →ₗ[Bᵐᵒᵖ] tensorObj (tensorUnit.{v} hA) M :=
    { toFun := leftUnitInsertBase.{v} hA hB M
      map_add' := map_add _
      map_smul' := fun b m ↦ by
        change tmul R A (tensorUnitEquiv.{v} hA 1) (b • m) =
          b • tmul R A (tensorUnitEquiv.{v} hA 1) m
        rw [smul_tmul_right] }
  refine ⟨⟨T, ?_, ?_⟩, ?_⟩
  · intro p m hm
    have h1 : tensorUnitEquiv.{v} hA 1 ∈ (tensorUnit.{v} hA).grading 0 :=
      (mem_tensorUnit_grading_iff hA 0 _).2 (by
        simpa only [tensorUnitEquiv_apply, ULift.down_up] using
          SetLike.one_mem_graded 𝒜)
    change tmul R A (tensorUnitEquiv.{v} hA 1) m ∈
      (tensorObj (tensorUnit.{v} hA) M).grading p
    simpa only [zero_add] using
      tmul_mem_tensorObj_grading (M := tensorUnit.{v} hA) (N := M) h1 hm
  · intro m
    have h1 : tensorUnitEquiv.{v} hA 1 ∈ (tensorUnit.{v} hA).grading 0 :=
      (mem_tensorUnit_grading_iff hA 0 _).2 (by
        simpa only [tensorUnitEquiv_apply, ULift.down_up] using
          SetLike.one_mem_graded 𝒜)
    change (tensorObj (tensorUnit.{v} hA) M).differential
      (tmul R A (tensorUnitEquiv.{v} hA 1) m) =
        tmul R A (tensorUnitEquiv.{v} hA 1) (M.differential m)
    have hd : (tensorUnit.{v} hA).differential (tensorUnitEquiv.{v} hA 1) = 0 := by
      rw [tensorUnit_differential_apply, tensorUnitEquiv_apply, hA.map_one_eq_zero]
      rfl
    rw [tensorObj_differential_tmul h1 m, hd]
    simp
  · rw [mem_dgBimoduleHomSubmodule]
    intro a m
    change tmul R A (tensorUnitEquiv.{v} hA 1) (a • m) =
      a • tmul R A (tensorUnitEquiv.{v} hA 1) m
    rw [smul_tmul_left]
    have h := balance R A a (tensorUnitEquiv.{v} hA 1) m
    have heq : op a • tensorUnitEquiv.{v} hA 1 =
        a • tensorUnitEquiv.{v} hA 1 := by
      apply ULift.ext
      simp only [tensorUnitEquiv_apply]
      change 1 * a = a * 1
      simp
    rw [heq] at h
    exact h.symm

@[simp]
theorem tensorLeftUnitorInv_apply (m : M) :
    tensorLeftUnitorInv.{v} hA hB M m =
      tmul R A (tensorUnitEquiv.{v} hA 1) m := by
  change leftUnitInsertBase.{v} hA hB M m = _
  rfl

/-- The regular DG bimodule is a left unit for tensor composition. -/
@[expose]
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
      change 1 * x.down = x.down
      exact one_mul x.down
    rw [heq] at h
    exact h.symm
  inv_hom_id := by
    apply hom_ext
    intro m
    rw [comp_apply, tensorLeftUnitorInv_apply, tensorLeftUnitorHom_tmul, id_apply]
    simp only [tensorUnitEquiv_apply, ULift.down_up, one_smul]

@[simp]
theorem tensorLeftUnitor_hom :
    (tensorLeftUnitor.{v} hA hB M).hom = tensorLeftUnitorHom.{v} hA hB M := rfl

@[simp]
theorem tensorLeftUnitor_inv :
    (tensorLeftUnitor.{v} hA hB M).inv = tensorLeftUnitorInv.{v} hA hB M := rfl

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

private abbrev rightUnitAction : M →ₗ[R] tensorUnit.{v} hB →ₗ[R] M :=
  ((Algebra.lsmul R R M (A := Bᵐᵒᵖ)).toLinearMap.comp
    ((tensorUnitEquiv.{v} hB).symm.trans (opLinearEquiv R)).toLinearMap).flip

private theorem rightUnitAction_balanced (b : B) (m : M) (x : tensorUnit.{v} hB) :
    rightUnitAction.{v} hA hB M (op b • m) x =
      rightUnitAction.{v} hA hB M m (b • x) := by
  simp only [rightUnitAction, LinearMap.flip_apply, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply, coe_opLinearEquiv,
    AlgHom.toLinearMap_apply, Algebra.lsmul_apply, tensorUnitEquiv_symm_apply]
  change op x.down • op b • m = op (b * x.down) • m
  rw [← mul_smul, op_mul]

private theorem rightUnitAction_degree {p q : ℤ} {m : M} {x : tensorUnit.{v} hB}
    (hm : m ∈ M.grading p) (hx : x ∈ (tensorUnit.{v} hB).grading q) :
    rightUnitAction.{v} hA hB M m x ∈ M.grading (p + q) := by
  have hx' : op x.down ∈ (InternalGrading.ofDecomposition ℬ).opposite.piece q :=
    ((InternalGrading.ofDecomposition ℬ).mem_opposite_piece_iff q _).2 (by
      simpa only [InternalGrading.ofDecomposition_piece, unop_op] using
        (mem_tensorUnit_grading_iff hB q x).1 hx)
  simpa only [rightUnitAction, LinearMap.flip_apply, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply, coe_opLinearEquiv,
    AlgHom.toLinearMap_apply, Algebra.lsmul_apply, tensorUnitEquiv_symm_apply,
    add_comm, vadd_eq_add] using SetLike.GradedSMul.smul_mem hx' hm

local instance : SetLike.GradedSMul
    (InternalGrading.ofDecomposition ℬ).opposite.piece
    (InternalGrading.ofDecomposition M.grading).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

local instance : SetLike.GradedSMul ℬ
    (InternalGrading.ofDecomposition (tensorUnit.{v} hB).grading).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

/-- Evaluate the regular right tensor factor by its action on the first factor. -/
def tensorRightUnitorHom : tensorObj M (tensorUnit.{v} hB) ⟶ M := by
  let F : tensorObj M (tensorUnit.{v} hB) →ₗ[R] M :=
    lift (rightUnitAction.{v} hA hB M) (rightUnitAction_balanced.{v} hA hB M)
  let T : tensorObj M (tensorUnit.{v} hB) →ₗ[Bᵐᵒᵖ] M :=
    { toFun := F
      map_add' := map_add F
      map_smul' := fun b z ↦ lift_smul_right Bᵐᵒᵖ
        (rightUnitAction.{v} hA hB M) (rightUnitAction_balanced.{v} hA hB M)
        (fun b m x ↦ by
          simp only [rightUnitAction, LinearMap.flip_apply, LinearMap.comp_apply,
            LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply, coe_opLinearEquiv,
            AlgHom.toLinearMap_apply, Algebra.lsmul_apply, tensorUnitEquiv_symm_apply]
          change op (x.down * unop b) • m = b • op x.down • m
          rw [← mul_smul, op_mul, op_unop]) b z }
  refine ⟨⟨T, ?_, ?_⟩, ?_⟩
  · intro p z hz
    have hz' := (isHomogeneous_of_tmul
      (InternalGrading.ofDecomposition M.grading)
      (InternalGrading.ofDecomposition (tensorUnit.{v} hB).grading) M.grading F 0
      (fun hm hx ↦ by
        simpa only [F, lift_tmul, add_zero] using
          rightUnitAction_degree.{v} hA hB M
            (by simpa only [InternalGrading.ofDecomposition_piece] using hm)
            (by simpa only [InternalGrading.ofDecomposition_piece] using hx))).map_mem hz
    change F z ∈ M.grading p
    simpa only [add_zero] using hz'
  · intro z
    change M.differential (F z) = F ((tensorObj M (tensorUnit.{v} hB)).differential z)
    have hF (m : M) (x : tensorUnit.{v} hB) : F (tmul R B m x) = op x.down • m := by
      dsimp [F]
      rw [lift_tmul]
      rfl
    induction z using induction_on with
    | ht m x =>
        induction m using DirectSum.Decomposition.inductionOn M.grading with
        | zero => simp [F]
        | add m n hm hn => simp only [add_tmul, map_add, hm, hn]
        | @homogeneous p m =>
            rw [tensorObj_differential_tmul m.property x]
            simp only [map_add, Units.smul_def, map_zsmul, hF]
            rw [tensorUnit_differential_apply]
            change M.differential (op x.down • m.val) =
              op x.down • M.differential m.val + (p.negOnePow.val : ℤ) •
                (op (dB x.down) • m.val)
            simpa only [Units.smul_def, Int.cast_smul_eq_zsmul] using
              M.isDGRightModule.leibniz m.property x.down
    | ha x y hx hy => simp only [map_add, hx, hy]
  · rw [mem_dgBimoduleHomSubmodule]
    intro a z
    exact lift_smul_left A (rightUnitAction.{v} hA hB M)
      (rightUnitAction_balanced.{v} hA hB M)
      (fun a m x ↦ by
        simp only [rightUnitAction, LinearMap.flip_apply, LinearMap.comp_apply,
          LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply, coe_opLinearEquiv,
          AlgHom.toLinearMap_apply, Algebra.lsmul_apply]
        exact (smul_comm a (op ((tensorUnitEquiv.{v} hB).symm x)) m).symm) a z

@[simp]
theorem tensorRightUnitorHom_tmul (m : M) (x : tensorUnit.{v} hB) :
    tensorRightUnitorHom.{v} hA hB M (tmul R B m x) = op x.down • m := by
  change (lift (rightUnitAction.{v} hA hB M)
    (rightUnitAction_balanced.{v} hA hB M)) (tmul R B m x) = _
  rw [lift_tmul]
  rfl

private abbrev rightUnitInsertBase :
    M →ₗ[R] tensorObj M (tensorUnit.{v} hB) where
  toFun m := tmul R B m (tensorUnitEquiv.{v} hB 1)
  map_add' m n := add_tmul R B m n (tensorUnitEquiv.{v} hB 1)
  map_smul' _ _ := smul_tmul _ _ _ _ _

/-- Insert `1` in the regular right tensor factor. -/
def tensorRightUnitorInv : M ⟶ tensorObj M (tensorUnit.{v} hB) := by
  let T : M →ₗ[Bᵐᵒᵖ] tensorObj M (tensorUnit.{v} hB) :=
    { toFun := rightUnitInsertBase.{v} hA hB M
      map_add' := map_add _
      map_smul' := fun b m ↦ by
        change tmul R B (b • m) (tensorUnitEquiv.{v} hB 1) =
          b • tmul R B m (tensorUnitEquiv.{v} hB 1)
        rw [smul_tmul_right]
        have h := balance R B (unop b) m (tensorUnitEquiv.{v} hB 1)
        have heq : unop b • tensorUnitEquiv.{v} hB 1 =
            b • tensorUnitEquiv.{v} hB 1 := by
          apply ULift.ext
          change unop b * 1 = 1 * unop b
          simp
        rw [heq] at h
        exact h }
  refine ⟨⟨T, ?_, ?_⟩, ?_⟩
  · intro p m hm
    have h1 : tensorUnitEquiv.{v} hB 1 ∈ (tensorUnit.{v} hB).grading 0 :=
      (mem_tensorUnit_grading_iff hB 0 _).2 (SetLike.one_mem_graded ℬ)
    change tmul R B m (tensorUnitEquiv.{v} hB 1) ∈
      (tensorObj M (tensorUnit.{v} hB)).grading p
    simpa only [add_zero] using
      tmul_mem_tensorObj_grading (M := M) (N := tensorUnit.{v} hB) hm h1
  · intro m
    have h1 : tensorUnitEquiv.{v} hB 1 ∈ (tensorUnit.{v} hB).grading 0 :=
      (mem_tensorUnit_grading_iff hB 0 _).2 (SetLike.one_mem_graded ℬ)
    have hd : (tensorUnit.{v} hB).differential (tensorUnitEquiv.{v} hB 1) = 0 := by
      rw [tensorUnit_differential_apply, tensorUnitEquiv_apply, hB.map_one_eq_zero]
      rfl
    change (tensorObj M (tensorUnit.{v} hB)).differential
      (tmul R B m (tensorUnitEquiv.{v} hB 1)) =
        tmul R B (M.differential m) (tensorUnitEquiv.{v} hB 1)
    induction m using DirectSum.Decomposition.inductionOn M.grading with
    | zero => rw [zero_tmul, map_zero, map_zero, zero_tmul]
    | add m n hm hn => simp only [add_tmul, map_add, hm, hn]
    | @homogeneous p m =>
        rw [tensorObj_differential_tmul m.property (tensorUnitEquiv.{v} hB 1), hd]
        simp
  · rw [mem_dgBimoduleHomSubmodule]
    intro a m
    change tmul R B (a • m) (tensorUnitEquiv.{v} hB 1) =
      a • tmul R B m (tensorUnitEquiv.{v} hB 1)
    rw [smul_tmul_left]

@[simp]
theorem tensorRightUnitorInv_apply (m : M) :
    tensorRightUnitorInv.{v} hA hB M m =
      tmul R B m (tensorUnitEquiv.{v} hB 1) := by
  change rightUnitInsertBase.{v} hA hB M m = _
  rfl

/-- The regular DG bimodule is a right unit for tensor composition. -/
@[expose]
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
      change x.down * 1 = x.down
      exact mul_one x.down
    rw [heq] at h
    exact h
  inv_hom_id := by
    apply hom_ext
    intro m
    rw [comp_apply, tensorRightUnitorInv_apply, tensorRightUnitorHom_tmul, id_apply]
    simp only [tensorUnitEquiv_apply, ULift.down_up, op_one, one_smul]

@[simp]
theorem tensorRightUnitor_hom :
    (tensorRightUnitor.{v} hA hB M).hom = tensorRightUnitorHom.{v} hA hB M := rfl

@[simp]
theorem tensorRightUnitor_inv :
    (tensorRightUnitor.{v} hA hB M).inv = tensorRightUnitorInv.{v} hA hB M := rfl

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

/-- Left and right evaluation agree on two regular DG bimodules. -/
theorem tensorUnitHom_eq :
    tensorLeftUnitorHom.{v} hA hA (tensorUnit.{v} hA) =
      tensorRightUnitorHom.{v} hA hA (tensorUnit.{v} hA) := by
  apply tensorObj_hom_ext
  intro x y
  rw [tensorLeftUnitorHom_tmul, tensorRightUnitorHom_tmul]
  apply ULift.ext
  rfl

end TauCeti.DGBimoduleCat
