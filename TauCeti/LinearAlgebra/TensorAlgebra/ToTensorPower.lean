/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower

/-!
# Tensor algebras and tensor powers

This file records `TensorAlgebra.toDirectSum_toTensorAlgebra`, `TensorAlgebra.ofDirectSum_of`,
and `TensorPower.toTensorAlgebra_mem_range_pow`, bridging `TensorPower.toTensorAlgebra` with
`TensorAlgebra.toDirectSum`, `TensorAlgebra.ofDirectSum`, and powers of `(TensorAlgebra.ι R).range`.
-/

public section

open scoped TensorProduct

namespace TensorAlgebra

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- `TensorAlgebra.ofDirectSum` sends a single component in degree `n` to
`TensorPower.toTensorAlgebra`. -/
@[simp]
theorem ofDirectSum_of {n : ℕ} (t : ⨂[R]^n M) :
    ofDirectSum (DirectSum.of (fun k ↦ ⨂[R]^k M) n t) = TensorPower.toTensorAlgebra t :=
  DirectSum.toAddMonoid_of (fun _ ↦ LinearMap.toAddMonoidHom TensorPower.toTensorAlgebra) n t

/-- `TensorAlgebra.toDirectSum` sends an element of the `n`-th tensor power to the `n`-th
component of the direct sum. -/
@[simp]
theorem toDirectSum_toTensorAlgebra {n : ℕ} (t : ⨂[R]^n M) :
    toDirectSum (TensorPower.toTensorAlgebra t) =
      DirectSum.of (fun k ↦ ⨂[R]^k M) n t := by
  rw [← ofDirectSum_of t, toDirectSum_ofDirectSum]

end TensorAlgebra

namespace TensorPower

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The image of `TensorPower.toTensorAlgebra` on the `n`-th tensor power lies in
`(TensorAlgebra.ι R).range ^ n`. -/
theorem toTensorAlgebra_mem_range_pow {n : ℕ} (t : ⨂[R]^n M) :
    TensorPower.toTensorAlgebra t ∈ (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M).range ^ n := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul]; refine Submodule.smul_mem _ r ?_
    rw [TensorPower.toTensorAlgebra_tprod, TensorAlgebra.tprod_apply]
    have hlen : ∀ l : List M, (l.map (TensorAlgebra.ι R)).prod ∈
        (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M).range ^ l.length := by
      intro l; induction l with
      | nil => simp
      | cons u l ih =>
        rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
        exact Submodule.mul_mem_mul ⟨u, rfl⟩ ih
    simpa [List.length_ofFn, List.map_ofFn, Function.comp_def] using hlen (List.ofFn x)
  | add _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

end TensorPower
