/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower

/-!
# Basic lemmas for tensor algebras

General utilities for pure tensor products `TensorAlgebra.tprod` and `TensorPower.toTensorAlgebra`:
linear-map extensionality on pure tensors, splitting or prepending a generator, and left
multiplication on tensor-power ranges.
-/

public section

namespace TensorAlgebra

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

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

/-- Splitting off the first factor of a pure tensor product of length `n + 1`. -/
theorem tprod_succ (n : ℕ) (x : Fin (n + 1) → M) :
    tprod R M (n + 1) x = ι R (x 0) * tprod R M n (fun i ↦ x i.succ) := by
  simp [tprod_apply, List.ofFn_succ]

/-- Prepending a generator to a pure tensor product multiplies on the left by `ι R c`. -/
theorem tprod_cons {n : ℕ} (c : M) (x : Fin n → M) :
    tprod R M (n + 1) (Fin.cons c x) = ι R c * tprod R M n x := by simp

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
