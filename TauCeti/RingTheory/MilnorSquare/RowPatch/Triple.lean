/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MilnorSquare.RowPatch
public import TauCeti.RingTheory.Patching.PatchedModule

/-!
# Row coordinates on patched modules of free triples

The Milnor row patch is the free case of the patching-triple construction. The
scalar extension of a free module identifies the transition on the overlap with
right multiplication by its matrix, with the second endpoint as the source.
-/

public section

noncomputable section

open Matrix

namespace RingHom

variable {A₁ A₂ Q : Type*} [Ring A₁] [Ring A₂] [Ring Q]
  {π₁ : A₁ →+* Q} {π₂ : A₂ →+* Q}
  {n : Type*} [Fintype n] [DecidableEq n]

/-- The second-to-first transition on scalar extensions of free modules, in row coordinates. -/
def rowPatchTransition (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q) (a : GL n Q) :
    TauCeti.BalancedExtension π₂ (n → A₂) ≃ₗ[Q] TauCeti.BalancedExtension π₁ (n → A₁) :=
  let e : (n → Q) ≃ₗ[Q] (n → Q) :=
    LinearEquiv.ofLinearMap (a : Matrix n n Q).vecMulLinear
      (↑a⁻¹ : Matrix n n Q).vecMulLinear
      (LinearMap.ext fun v ↦ by simp) (LinearMap.ext fun v ↦ by simp)
  (TauCeti.BalancedExtension.piScalarRight π₂ n).trans
    (e.trans (TauCeti.BalancedExtension.piScalarRight π₁ n).symm)

/-- The matrix acts on the second endpoint after reducing coefficients to the overlap. -/
@[simp]
theorem piScalarRight_rowPatchTransition_tmul (a : GL n Q) (s : Q) (q : n → A₂) :
    TauCeti.BalancedExtension.piScalarRight π₁ n
      (rowPatchTransition π₁ π₂ a (TauCeti.BalancedExtension.tmul π₂ s q)) =
      (fun i ↦ s * π₂ (q i)) ᵥ* (a : Matrix n n Q) := by
  simp only [rowPatchTransition, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    TauCeti.BalancedExtension.piScalarRight_tmul, LinearEquiv.coe_ofLinearMap,
    Matrix.vecMulLinear_apply]

variable (π₁ π₂) in
/-- Row coordinates realize the free case of `TauCeti.PatchedModule`, with the triple
ordered from the second endpoint to the first. -/
def rowPatchEquivPatchedModule (a : GL n Q) :
    π₁.rowPatch π₂ a ≃ₗ[π₁.pullback π₂]
      TauCeti.PatchedModule (π₁.pullback_comm_sq π₂).symm
        (rowPatchTransition π₁ π₂ a).toLinearMap where
  toFun x := ⟨x.val.2, x.val.1, by
    apply (TauCeti.BalancedExtension.piScalarRight π₁ n).injective
    simpa only [LinearEquiv.coe_coe, piScalarRight_rowPatchTransition_tmul,
      TauCeti.BalancedExtension.piScalarRight_tmul, one_mul, Function.comp_def] using
      (mem_rowPatch.mp x.property).symm⟩
  invFun y := ⟨(y.snd, y.fst), by
    apply mem_rowPatch.mpr
    have hy := congrArg (TauCeti.BalancedExtension.piScalarRight π₁ n) y.apply_one_tmul_fst
    simpa only [LinearEquiv.coe_coe, piScalarRight_rowPatchTransition_tmul,
      TauCeti.BalancedExtension.piScalarRight_tmul, one_mul, Function.comp_def] using hy.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := TauCeti.PatchedModule.ext rfl rfl
  map_smul' d x := by
    apply TauCeti.PatchedModule.ext
    · simpa only [RingHom.id_apply, TauCeti.PatchedModule.fst_smul] using
        congrArg Prod.snd (rowPatch.coe_smul a d x)
    · simpa only [RingHom.id_apply, TauCeti.PatchedModule.snd_smul] using
        congrArg Prod.fst (rowPatch.coe_smul a d x)

/-- The first coordinate in the patching triple is the second endpoint row. -/
@[simp]
theorem rowPatchEquivPatchedModule_fst (a : GL n Q) (x : π₁.rowPatch π₂ a) :
    (rowPatchEquivPatchedModule π₁ π₂ a x).fst = x.val.2 :=
  (rfl)

/-- The second coordinate in the patching triple is the first endpoint row. -/
@[simp]
theorem rowPatchEquivPatchedModule_snd (a : GL n Q) (x : π₁.rowPatch π₂ a) :
    (rowPatchEquivPatchedModule π₁ π₂ a x).snd = x.val.1 :=
  (rfl)

/-- The inverse comparison restores the original order of the endpoints. -/
@[simp]
theorem coe_rowPatchEquivPatchedModule_symm_apply (a : GL n Q)
    (y : TauCeti.PatchedModule (π₁.pullback_comm_sq π₂).symm
      (rowPatchTransition π₁ π₂ a).toLinearMap) :
    ((rowPatchEquivPatchedModule π₁ π₂ a).symm y).val = (y.snd, y.fst) :=
  (rfl)

end RingHom
