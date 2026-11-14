/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Zero
public import TauCeti.LinearAlgebra.QuadraticForm.Prod

/-!
# Unit and grading-sign laws of the graded tensor product of Clifford modules

This file proves two structural laws of `AlgHom.cliffordProdTensor` over a commutative ring:

* **Reversing the grading sign**: when `δ : End_R F` anticommutes with every generating vector of
  `M₂`, `1 ⊗ δ` intertwines the graded tensor product for `γ` with that for `-γ`
  (`AlgHom.lTensor_comp_cliffordProdTensor`, `AlgHom.conjAlgEquiv_lTensor_cliffordProdTensor`).
* **Rank-zero units**: for a trivial left factor `M₁`, `TensorProduct.lid R F` intertwines the
  `1`-graded product with `ρ₂` (`AlgHom.conjAlgEquiv_lid_cliffordProdTensor_one`) and twists the
  `(-1)`-graded product by `CliffordAlgebra.involute`
  (`AlgHom.conjAlgEquiv_lid_cliffordProdTensor_neg_one`); for a trivial right factor `M₂`,
  `TensorProduct.rid R E` intertwines the product with `ρ₁` for any grading `γ`
  (`AlgHom.conjAlgEquiv_rid_cliffordProdTensor`).
-/

public section

open TensorProduct CliffordAlgebra

namespace AlgHom

variable {R M₁ M₂ E F : Type*} [CommRing R]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

section GradingNeg

variable (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R E) (γ : Module.End R E)
  (hγ : γ * γ = 1) (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
  (ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End R F)

/-- If `δ : End_R F` anticommutes with every generating vector of `M₂`, then `1 ⊗ δ` intertwines
the graded tensor product action for `γ` with that for `-γ`. -/
theorem lTensor_comp_cliffordProdTensor (δ : Module.End R F)
    (hδρ : ∀ w, δ * ρ₂ (ι Q₂ w) = -(ρ₂ (ι Q₂ w) * δ)) (a : CliffordAlgebra (Q₁.prod Q₂)) :
    δ.lTensor E ∘ₗ cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ a =
      cliffordProdTensor ρ₁ (-γ) (by rw [neg_mul_neg, hγ])
        (fun v ↦ by rw [neg_mul, mul_neg, hγρ, neg_neg]) ρ₂ a ∘ₗ δ.lTensor E := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => ext z; simp [Algebra.algebraMap_eq_smul_one]
  | ι x =>
    refine TensorProduct.ext' fun e f ↦ ?_
    have hx := LinearMap.congr_fun (hδρ x.2) f
    simp only [_root_.mul_apply_eq_comp, LinearMap.neg_apply] at hx
    simp [cliffordProdTensor_ι_tmul, hx, tmul_neg, neg_tmul]
  | add a b ha hb => simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, ha, hb]
  | mul a b ha hb =>
    simp only [map_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ha]
    rw [LinearMap.comp_assoc, hb, ← LinearMap.comp_assoc]

/-- When `δ` is an involutive grading of `F`, conjugating the graded tensor product action for `γ`
by `1 ⊗ δ` (`LinearEquiv.lTensor E (.ofInvolutive δ hδ)`) gives the action for `-γ`. -/
theorem conjAlgEquiv_lTensor_cliffordProdTensor (δ : Module.End R F)
    (hδ : Function.Involutive δ) (hδρ : ∀ w, δ * ρ₂ (ι Q₂ w) = -(ρ₂ (ι Q₂ w) * δ)) :
    (((LinearEquiv.ofInvolutive δ hδ).lTensor E).conjAlgEquiv R).toAlgHom.comp
        (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂) =
      cliffordProdTensor ρ₁ (-γ) (by rw [neg_mul_neg, hγ])
        (fun v ↦ by rw [neg_mul, mul_neg, hγρ, neg_neg]) ρ₂ := by
  refine CliffordAlgebra.hom_ext <| LinearMap.ext fun x ↦ TensorProduct.ext' fun e f ↦ ?_
  have hx := LinearMap.congr_fun (hδρ x.2) (δ f)
  simp only [_root_.mul_apply_eq_comp, LinearMap.neg_apply, hδ f] at hx
  have hsymm : (LinearEquiv.ofInvolutive δ hδ).symm f = δ f := rfl
  simp [LinearEquiv.conjAlgEquiv_apply, cliffordProdTensor_ι_tmul, hsymm, hδ f, hx,
    tmul_neg, neg_tmul]

end GradingNeg

section UnitLeft

variable [Unique M₁] (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R R)
  (ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End R F)

/-- **Left unit law of the graded tensor product**: for a trivial left quadratic module `M₁` and
the positive grading `1` on `R`, conjugating `cliffordProdTensor` by `TensorProduct.lid R F`
recovers `ρ₂` along `QuadraticMap.IsometryEquiv.uniqueProd`. -/
theorem conjAlgEquiv_lid_cliffordProdTensor_one :
    ((TensorProduct.lid R F).conjAlgEquiv R).toAlgHom.comp
        (cliffordProdTensor ρ₁ 1 (mul_one 1) (fun v ↦ by simp [ι_eq_zero_of_subsingleton]) ρ₂) =
      ρ₂.comp (equivOfIsometry (QuadraticMap.IsometryEquiv.uniqueProd Q₁ Q₂)).toAlgHom := by
  refine CliffordAlgebra.hom_ext <| LinearMap.ext fun x ↦ LinearMap.ext fun f ↦ ?_
  simp [LinearEquiv.conjAlgEquiv_apply, cliffordProdTensor_ι_tmul, ι_eq_zero_of_subsingleton]

/-- Applied form of `AlgHom.conjAlgEquiv_lid_cliffordProdTensor_one`: the left unitor `R ⊗ F ≃ F`
intertwines the `1`-graded tensor product action with `ρ₂`. -/
theorem lid_cliffordProdTensor_one (a : CliffordAlgebra (Q₁.prod Q₂)) (z : R ⊗[R] F) :
    TensorProduct.lid R F
        (cliffordProdTensor ρ₁ 1 (mul_one 1)
          (fun v ↦ by simp [ι_eq_zero_of_subsingleton]) ρ₂ a z) =
      ρ₂ (equivOfIsometry (QuadraticMap.IsometryEquiv.uniqueProd Q₁ Q₂) a)
        (TensorProduct.lid R F z) := by
  simpa [LinearEquiv.conjAlgEquiv_apply] using congrArg (fun g ↦ g a (TensorProduct.lid R F z))
    (conjAlgEquiv_lid_cliffordProdTensor_one ρ₁ ρ₂)

/-- For a trivial left quadratic module `M₁` and the negative grading `-1` on `R`, conjugating
`cliffordProdTensor` by `TensorProduct.lid R F` twists `ρ₂` by `CliffordAlgebra.involute`. -/
theorem conjAlgEquiv_lid_cliffordProdTensor_neg_one :
    ((TensorProduct.lid R F).conjAlgEquiv R).toAlgHom.comp
        (cliffordProdTensor ρ₁ (-1) (LinearMap.ext fun _ ↦ by simp)
          (fun v ↦ by simp [ι_eq_zero_of_subsingleton]) ρ₂) =
      (ρ₂.comp (CliffordAlgebra.involute : CliffordAlgebra Q₂ →ₐ[R] CliffordAlgebra Q₂)).comp
        (equivOfIsometry (QuadraticMap.IsometryEquiv.uniqueProd Q₁ Q₂)).toAlgHom := by
  refine CliffordAlgebra.hom_ext <| LinearMap.ext fun x ↦ LinearMap.ext fun f ↦ ?_
  simp [LinearEquiv.conjAlgEquiv_apply, cliffordProdTensor_ι_tmul, ι_eq_zero_of_subsingleton]

/-- Applied form of `AlgHom.conjAlgEquiv_lid_cliffordProdTensor_neg_one`. -/
theorem lid_cliffordProdTensor_neg_one (a : CliffordAlgebra (Q₁.prod Q₂)) (z : R ⊗[R] F) :
    TensorProduct.lid R F
        (cliffordProdTensor ρ₁ (-1) (LinearMap.ext fun _ ↦ by simp)
          (fun v ↦ by simp [ι_eq_zero_of_subsingleton]) ρ₂ a z) =
      ρ₂ (CliffordAlgebra.involute
        (equivOfIsometry (QuadraticMap.IsometryEquiv.uniqueProd Q₁ Q₂) a))
        (TensorProduct.lid R F z) := by
  simpa [LinearEquiv.conjAlgEquiv_apply] using congrArg (fun g ↦ g a (TensorProduct.lid R F z))
    (conjAlgEquiv_lid_cliffordProdTensor_neg_one ρ₁ ρ₂)

end UnitLeft

section UnitRight

variable [Unique M₂] (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R E) (γ : Module.End R E)
  (hγ : γ * γ = 1) (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
  (ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End R R)

/-- **Right unit law of the graded tensor product**: for a trivial right quadratic module `M₂`,
conjugating `cliffordProdTensor` by `TensorProduct.rid R E` recovers `ρ₁` along
`QuadraticMap.IsometryEquiv.prodUnique`, for any grading `γ` on `E`. -/
theorem conjAlgEquiv_rid_cliffordProdTensor :
    ((TensorProduct.rid R E).conjAlgEquiv R).toAlgHom.comp
        (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂) =
      ρ₁.comp (equivOfIsometry (QuadraticMap.IsometryEquiv.prodUnique Q₁ Q₂)).toAlgHom := by
  refine CliffordAlgebra.hom_ext <| LinearMap.ext fun x ↦ LinearMap.ext fun e ↦ ?_
  simp [LinearEquiv.conjAlgEquiv_apply, cliffordProdTensor_ι_tmul, ι_eq_zero_of_subsingleton]

/-- Applied form of `AlgHom.conjAlgEquiv_rid_cliffordProdTensor`. -/
theorem rid_cliffordProdTensor (a : CliffordAlgebra (Q₁.prod Q₂)) (z : E ⊗[R] R) :
    TensorProduct.rid R E (cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ a z) =
      ρ₁ (equivOfIsometry (QuadraticMap.IsometryEquiv.prodUnique Q₁ Q₂) a)
        (TensorProduct.rid R E z) := by
  simpa [LinearEquiv.conjAlgEquiv_apply] using congrArg (fun g ↦ g a (TensorProduct.rid R E z))
    (conjAlgEquiv_rid_cliffordProdTensor ρ₁ γ hγ hγρ ρ₂)

end UnitRight

end AlgHom
