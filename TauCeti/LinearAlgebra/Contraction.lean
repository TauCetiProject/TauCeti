/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction

/-!
# Rank-one induction for maps out of a finite projective module

For a finite projective module `M`, the map `dualTensorHom : Dual R M ⊗[R] N → (M →ₗ[R] N)` is
an isomorphism (`dualTensorHomEquiv`), so every linear map out of `M` is a finite sum of rank-one
maps `φ.smulRight n`; the identification of the rank-one forms is
`dualTensorHom_tmul_eq_smulRight`. This gives an induction principle,
`LinearMap.induction_on_smulRight`, for properties of such maps that are closed under addition.

The file also records how evaluating dual factors interacts with rearranging a fourfold tensor
product: `TensorProduct.map_lTensor_eval_tensorTensorTensorComm_tmul` evaluates the dual factors
of `tensorTensorTensorComm ((a ⊗ b) ⊗ ψ)` at `x` and `y`, giving `dualDistrib ψ (x ⊗ y) • (a ⊗ b)`.
-/

public section

open Module TensorProduct

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- `dualTensorHom` sends the pure tensor `φ ⊗ n` to the rank-one map `x ↦ φ x • n`.
This is not a simp lemma: rewriting `dualTensorHom` of a pure tensor would block Mathlib's simp
lemmas stated for `dualTensorHom`, such as `dualTensorHomEquiv_symm_dualTensorHom`. -/
theorem dualTensorHom_tmul_eq_smulRight (φ : Dual R M) (n : N) :
    dualTensorHom R M N (φ ⊗ₜ n) = φ.smulRight n := by
  ext
  simp

namespace LinearMap

variable [Module.Finite R M] [Module.Projective R M]

/-- Every linear map out of a finite projective module is a finite sum of rank-one maps
`φ.smulRight n`, so a property of linear maps out of `M` that is closed under `+` holds as soon
as it holds for these. -/
theorem induction_on_smulRight {P : (M →ₗ[R] N) → Prop} (f : M →ₗ[R] N)
    (smulRight : ∀ (φ : Dual R M) (n : N), P (φ.smulRight n))
    (add : ∀ f g, P f → P g → P (f + g)) : P f := by
  obtain ⟨x, rfl⟩ := (dualTensorHomEquiv R M N).surjective f
  induction x using TensorProduct.inductionOn with
  | tmul φ n =>
    rw [← LinearEquiv.coe_coe, toLinearMap_dualTensorHomEquiv, dualTensorHom_tmul_eq_smulRight]
    exact smulRight φ n
  | add x y hx hy => simpa using add _ _ hx hy

end LinearMap

namespace TensorProduct

/-- Evaluating the dual factors of `(a ⊗ b) ⊗ ψ`, rearranged by `tensorTensorTensorComm` to
`(a ⊗ _) ⊗ (b ⊗ _)`, at `x` and `y` multiplies `a ⊗ b` by the value of `dualDistrib ψ` at
`x ⊗ y`. -/
theorem map_lTensor_eval_tensorTensorTensorComm_tmul {A B X Y : Type*} [AddCommMonoid A]
    [Module R A] [AddCommMonoid B] [Module R B] [AddCommMonoid X] [Module R X] [AddCommMonoid Y]
    [Module R Y] (a : A) (b : B) (x : X) (y : Y) (ψ : Dual R X ⊗[R] Dual R Y) :
    map (TensorProduct.rid R A ∘ₗ (Dual.eval R X x).lTensor A)
        (TensorProduct.rid R B ∘ₗ (Dual.eval R Y y).lTensor B)
        (tensorTensorTensorComm R A B (Dual R X) (Dual R Y) ((a ⊗ₜ b) ⊗ₜ ψ)) =
      dualDistrib R X Y ψ (x ⊗ₜ y) • (a ⊗ₜ b) := by
  induction ψ using TensorProduct.inductionOn with
  | add ψ ψ' h h' => rw [tmul_add, map_add, map_add, h, h', map_add, LinearMap.add_apply, add_smul]
  | tmul φ φ' =>
    simp only [tensorTensorTensorComm_tmul, map_tmul, LinearMap.comp_apply, LinearMap.lTensor_tmul,
      Dual.eval_apply, LinearEquiv.coe_coe, rid_tmul, dualDistrib_apply, smul_tmul_smul]

end TensorProduct
