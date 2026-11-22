/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower

/-!
# Products of generators of the tensor algebra

Mathlib's `TensorAlgebra.tprod R M n x` is the product `ι (x 0) * ⋯ * ι (x (n - 1))` of `n`
generators of the tensor algebra.  This file records how such a product splits off its last
generator (`TensorAlgebra.tprod_succ`) or its first generator (`TensorAlgebra.tprod_succ_eq_ι_mul`,
`TensorAlgebra.tprod_cons`), the steps of inductions on the length of the product, together with
linear-map extensionality on pure tensors (`TensorAlgebra.linearMap_ext_tprod`), left
multiplication on tensor-power ranges (`TensorAlgebra.ι_mul_mem_range_toTensorAlgebra`), and
evaluation of `TensorAlgebra.ofDirectSum` on a single homogeneous summand
(`TensorAlgebra.ofDirectSum_of`).
-/

public section

namespace TensorAlgebra

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- A product of `n + 1` generators of the tensor algebra is the product of the first `n` of them
times the last one. -/
theorem tprod_succ {n : ℕ} (x : Fin (n + 1) → M) :
    tprod R M (n + 1) x = tprod R M n (fun i ↦ x i.castSucc) * ι R (x (Fin.last n)) := by
  rw [tprod_apply, tprod_apply, List.ofFn_succ', List.prod_concat]

/-- A product of `n + 1` generators of the tensor algebra is the first of them times the product
of the remaining `n`. -/
theorem tprod_succ_eq_ι_mul {n : ℕ} (x : Fin (n + 1) → M) :
    tprod R M (n + 1) x = ι R (x 0) * tprod R M n (fun i ↦ x i.succ) := by
  simp [tprod_apply, List.ofFn_succ]

/-- Prepending a generator to a pure tensor product multiplies on the left by `ι R c`. -/
theorem tprod_cons {n : ℕ} (c : M) (x : Fin n → M) :
    tprod R M (n + 1) (Fin.cons c x) = ι R c * tprod R M n x := by simp

/-- Evaluating `TensorAlgebra.ofDirectSum` on a single homogeneous summand recovers
`TensorPower.toTensorAlgebra`. -/
@[simp]
theorem ofDirectSum_of {n : ℕ} (x : TensorPower R n M) :
    ofDirectSum (DirectSum.of (fun m ↦ TensorPower R m M) n x) = TensorPower.toTensorAlgebra x :=
  DirectSum.toAddMonoid_of (fun _ ↦ LinearMap.toAddMonoidHom TensorPower.toTensorAlgebra) n x

/-- Two linear maps out of the tensor algebra agree if they agree on all pure tensor products. -/
theorem linearMap_ext_tprod {f g : TensorAlgebra R M →ₗ[R] N}
    (h : ∀ (n : ℕ) (x : Fin n → M), f (tprod R M n x) = g (tprod R M n x)) : f = g :=
  LinearMap.ext fun z ↦ by
    rw [← ofDirectSum_toDirectSum z]
    induction toDirectSum z using DirectSum.induction_on with
    | zero => simp
    | add _ _ hu hv => simp only [map_add, hu, hv]
    | of n t => induction t using PiTensorProduct.induction_on with
      | add _ _ hu hv => simp only [map_add, hu, hv]
      | smul_tprod _ x => simp only [DirectSum.of_smul, map_smul, ofDirectSum_of_tprod, h n x]

/-- Left multiplication by a generator raises tensor length by one. -/
theorem ι_mul_mem_range_toTensorAlgebra (c : M) {n : ℕ} {y : TensorAlgebra R M}
    (hy : y ∈ LinearMap.range (TensorPower.toTensorAlgebra (R := R) (M := M) (n := n))) :
    ι R c * y ∈ LinearMap.range (TensorPower.toTensorAlgebra (R := R) (M := M) (n := n + 1)) := by
  obtain ⟨t, rfl⟩ := hy; induction t using PiTensorProduct.induction_on with
  | add _ _ hu hv => simpa only [map_add, mul_add] using Submodule.add_mem _ hu hv
  | smul_tprod r x =>
    rw [map_smul, mul_smul_comm, TensorPower.toTensorAlgebra_tprod]
    exact Submodule.smul_mem _ r ⟨PiTensorProduct.tprod R (Fin.cons c x), by
      rw [TensorPower.toTensorAlgebra_tprod, tprod_cons]⟩

end TensorAlgebra
