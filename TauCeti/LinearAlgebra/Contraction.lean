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
