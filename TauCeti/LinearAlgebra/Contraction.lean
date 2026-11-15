/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction

/-!
# The range of `dualTensorHom`

The range of `dualTensorHom : Dual R M ⊗[R] N → (M →ₗ[R] N)` consists of the linear maps of finite
rank in the strong sense: `mem_range_dualTensorHom_iff` identifies it with the maps that factor
through a finite free module `Rⁿ`. Since it is a submodule, such maps are closed under sums and
scalar multiples, which is not evident from the factorisations themselves.

For a finite projective module `M`, `dualTensorHom` is an isomorphism (`dualTensorHomEquiv`), so
every linear map out of `M` is a finite sum of rank-one maps `φ.smulRight n`; the identification of
the rank-one forms is `dualTensorHom_tmul_eq_smulRight`. This gives an induction principle,
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

/-- A linear map lies in the range of `dualTensorHom` if and only if it factors through a finite
free module `Rⁿ`. -/
theorem mem_range_dualTensorHom_iff {f : M →ₗ[R] N} :
    f ∈ LinearMap.range (dualTensorHom R M N) ↔
      ∃ (n : ℕ) (u : M →ₗ[R] Fin n → R) (v : (Fin n → R) →ₗ[R] N), v ∘ₗ u = f := by
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨s, rfl⟩ := TensorProduct.exists_finset t
    refine ⟨s.card, LinearMap.pi fun i ↦ (s.equivFin.symm i).1.1,
      Fintype.linearCombination R fun i ↦ (s.equivFin.symm i).1.2, LinearMap.ext fun x ↦ ?_⟩
    simp only [LinearMap.comp_apply, LinearMap.pi_apply, Fintype.linearCombination_apply,
      map_sum, LinearMap.sum_apply, dualTensorHom_apply]
    rw [← Finset.sum_coe_sort s]
    exact Fintype.sum_equiv s.equivFin.symm _ (fun i ↦ i.1.1 x • i.1.2) fun _ ↦ rfl
  · rintro ⟨n, u, v, rfl⟩
    refine ⟨∑ i, (LinearMap.proj i ∘ₗ u) ⊗ₜ v (Pi.single i 1), LinearMap.ext fun x ↦ ?_⟩
    rw [map_sum, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.pi_apply_eq_sum_univ v (u x)]
    simp_rw [dualTensorHom_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    congr! with i _ j
    simp [Pi.single_apply, eq_comm]

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
