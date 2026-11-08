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
