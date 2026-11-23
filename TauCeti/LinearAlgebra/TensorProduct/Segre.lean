/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace
import TauCeti.LinearAlgebra.TensorProduct.Dual
import TauCeti.LinearAlgebra.TensorProduct.Separation

/-!
# Segre minor criterion for pure tensors

A tensor `z : M ⊗[k] N` over a field `k` is a pure tensor `m ⊗ₜ n` iff all `2 × 2` minors
of its dual evaluation vanish:
`(φ₁ ⊗ ψ₁)(z) * (φ₂ ⊗ ψ₂)(z) = (φ₁ ⊗ ψ₂)(z) * (φ₂ ⊗ ψ₁)(z)`.

## Main results

* `TensorProduct.dualDistrib_tmul_mul_dualDistrib_tmul`: pure tensors satisfy the `2 × 2` Segre
  minor relations over any commutative semiring.
* `TensorProduct.eq_smul_rid_lTensor_tmul_lid_rTensor`: explicit pure-tensor factorization from an
  invertible dual pairing and the Segre minor relations.
* `TensorProduct.exists_eq_tmul_iff`: characterization of pure tensors over a field by the
  vanishing of all `2 × 2` dual minors.
-/

public section

open scoped TensorProduct

namespace TensorProduct

section Semiring

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- Every pure tensor satisfies the `2 × 2` Segre minor relations under `dualDistrib`. -/
theorem dualDistrib_tmul_mul_dualDistrib_tmul (m : M) (n : N)
    (φ₁ φ₂ : Module.Dual R M) (ψ₁ ψ₂ : Module.Dual R N) :
    dualDistrib R M N (φ₁ ⊗ₜ ψ₁) (m ⊗ₜ n) * dualDistrib R M N (φ₂ ⊗ₜ ψ₂) (m ⊗ₜ n) =
      dualDistrib R M N (φ₁ ⊗ₜ ψ₂) (m ⊗ₜ n) * dualDistrib R M N (φ₂ ⊗ₜ ψ₁) (m ⊗ₜ n) := by
  simp
  ring

end Semiring

section CommRing

variable {R M N : Type*} [CommRing R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [Module.Projective R N]

/-- If `z : M ⊗[R] N` satisfies the `2 × 2` Segre minor relations and pairs to a unit `u` with
`φ₀ ⊗ₜ ψ₀`, and duals separate points of `M` and `N`, then `z` factors explicitly as a pure tensor
formed from its partial contractions with `ψ₀` and `φ₀`. -/
theorem eq_smul_rid_lTensor_tmul_lid_rTensor (z : M ⊗[R] N)
    (hf : ∀ m : M, (∀ φ : Module.Dual R M, φ m = 0) → m = 0)
    (hg : ∀ n : N, (∀ ψ : Module.Dual R N, ψ n = 0) → n = 0)
    {φ₀ : Module.Dual R M} {ψ₀ : Module.Dual R N} {u : Rˣ}
    (hu : dualDistrib R M N (φ₀ ⊗ₜ ψ₀) z = u)
    (hsegre : ∀ (φ : Module.Dual R M) (ψ : Module.Dual R N),
      dualDistrib R M N (φ ⊗ₜ ψ) z * dualDistrib R M N (φ₀ ⊗ₜ ψ₀) z =
        dualDistrib R M N (φ ⊗ₜ ψ₀) z * dualDistrib R M N (φ₀ ⊗ₜ ψ) z) :
    z = (u⁻¹ • TensorProduct.rid R M (LinearMap.lTensor M ψ₀ z)) ⊗ₜ[R]
      TensorProduct.lid R N (LinearMap.rTensor N φ₀ z) := by
  let _ : AddCommGroup (M ⊗[R] N) := Module.addCommMonoidToAddCommGroup R
  set m := TensorProduct.rid R M (LinearMap.lTensor M ψ₀ z)
  set n := TensorProduct.lid R N (LinearMap.rTensor N φ₀ z)
  rw [← sub_eq_zero]
  refine TauCeti.tensor_eq_zero_of_forall_lid_map_eq_zero id id hf hg _ fun φ ψ ↦ ?_
  have hφm : φ m = dualDistrib R M N (φ ⊗ₜ ψ₀) z :=
    LinearMap.congr_fun (comp_rid_lTensor_eq_dualDistrib φ ψ₀) z
  have hψn : ψ n = dualDistrib R M N (φ₀ ⊗ₜ ψ) z :=
    LinearMap.congr_fun (comp_lid_rTensor_eq_dualDistrib φ₀ ψ) z
  have hmap := LinearMap.congr_fun (lid_comp_map_eq_dualDistrib φ ψ) (z - (u⁻¹ • m) ⊗ₜ[R] n)
  simp only [id_eq, LinearMap.comp_apply, LinearEquiv.coe_coe] at hmap ⊢
  rw [hmap, map_sub, dualDistrib_apply, Units.smul_def, map_smul, smul_eq_mul, hφm, hψn]
  have hmul := hsegre φ ψ
  rw [hu] at hmul
  rw [sub_eq_zero, mul_assoc, ← hmul, mul_comm _ (u : R), Units.inv_mul_cancel_left]

end CommRing

section Field

variable {k M N : Type*} [Field k] [AddCommMonoid M] [Module k M] [AddCommMonoid N] [Module k N]

/-- **Segre minor criterion for pure tensors.** Over a field `k`, an element `z : M ⊗[k] N` is a
pure tensor if and only if all `2 × 2` minors of its dual evaluation vanish. -/
theorem exists_eq_tmul_iff (z : M ⊗[k] N) :
    (∃ (m : M) (n : N), z = m ⊗ₜ[k] n) ↔
      ∀ (φ₁ φ₂ : Module.Dual k M) (ψ₁ ψ₂ : Module.Dual k N),
        dualDistrib k M N (φ₁ ⊗ₜ ψ₁) z * dualDistrib k M N (φ₂ ⊗ₜ ψ₂) z =
          dualDistrib k M N (φ₁ ⊗ₜ ψ₂) z * dualDistrib k M N (φ₂ ⊗ₜ ψ₁) z := by
  let _ := Module.addCommMonoidToAddCommGroup k (M := M)
  let _ := Module.addCommMonoidToAddCommGroup k (M := N)
  refine ⟨fun ⟨m, n, hmn⟩ φ₁ φ₂ ψ₁ ψ₂ ↦
    hmn ▸ dualDistrib_tmul_mul_dualDistrib_tmul m n φ₁ φ₂ ψ₁ ψ₂, fun h ↦ ?_⟩
  by_cases h0 : ∃ (φ₀ : Module.Dual k M) (ψ₀ : Module.Dual k N),
      dualDistrib k M N (φ₀ ⊗ₜ ψ₀) z ≠ 0
  · obtain ⟨φ₀, ψ₀, hne⟩ := h0
    refine ⟨_, _, eq_smul_rid_lTensor_tmul_lid_rTensor z
      (fun m hm ↦ (Module.forall_dual_apply_eq_zero_iff k m).mp hm)
      (fun n hn ↦ (Module.forall_dual_apply_eq_zero_iff k n).mp hn)
      (u := Units.mk0 _ hne) rfl (fun φ ψ ↦ h φ φ₀ ψ ψ₀)⟩
  · push Not at h0
    have hz : z = 0 := TauCeti.tensor_eq_zero_of_forall_lid_map_eq_zero id id
      (fun m hm ↦ (Module.forall_dual_apply_eq_zero_iff k m).mp hm)
      (fun n hn ↦ (Module.forall_dual_apply_eq_zero_iff k n).mp hn) z fun φ ψ ↦ by
        simpa [← LinearMap.congr_fun (lid_comp_map_eq_dualDistrib φ ψ) z] using h0 φ ψ
    exact ⟨0, 0, by simp [hz]⟩

end Field

end TensorProduct
