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
multiplication on tensor-power ranges (`TensorAlgebra.ι_mul_mem_range_toTensorAlgebra`),
identification of the `d`-th tensor-power range with the `d`-th graded piece
(`TensorAlgebra.tprod_mem_range_pow`, `TensorPower.toTensorAlgebra_mem_range_pow`,
`TensorPower.range_toTensorAlgebra`), and evaluation of `TensorAlgebra.ofDirectSum` on a single
homogeneous summand (`TensorAlgebra.ofDirectSum_of`).
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

/-- A pure tensor of length `d` lies in the `d`-th power of the range of `TensorAlgebra.ι R`. -/
theorem tprod_mem_range_pow (d : ℕ) (m : Fin d → M) :
    tprod R M d m ∈ LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) ^ d := by
  induction d with
  | zero =>
    rw [tprod_apply, List.ofFn_zero, List.prod_nil, pow_zero]
    exact Submodule.one_le.mp le_rfl
  | succ d ih =>
    rw [tprod_apply, List.ofFn_succ, List.prod_cons, pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ (m 0)) (ih (m ∘ Fin.succ))

end TensorAlgebra

namespace TensorPower

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Every element of the `d`-th tensor power embeds into the `d`-th graded piece of the tensor
algebra. -/
theorem toTensorAlgebra_mem_range_pow (d : ℕ) (x : TensorPower R d M) :
    toTensorAlgebra x ∈ LinearMap.range (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M) ^ d := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [map_smul, toTensorAlgebra_tprod]
    exact Submodule.smul_mem _ r (TensorAlgebra.tprod_mem_range_pow d m)
  | add x y hx hy =>
    rw [map_add]
    exact add_mem hx hy

/-- The image of the `d`-th tensor power inside the tensor algebra is the `d`-th graded piece
`(LinearMap.range (TensorAlgebra.ι R)) ^ d`. -/
theorem range_toTensorAlgebra (d : ℕ) :
    LinearMap.range (toTensorAlgebra (R := R) (M := M) (n := d)) =
      LinearMap.range (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M) ^ d := by
  refine le_antisymm ?_ fun x hx ↦ ?_
  · rintro _ ⟨x, rfl⟩
    exact toTensorAlgebra_mem_range_pow d x
  · induction hx using Submodule.pow_induction_on_left' with
    | algebraMap r =>
      exact ⟨DirectSum.GAlgebra.toFun (A := fun n ↦ TensorPower R n M) r,
        toTensorAlgebra_galgebra_toFun (M := M) r⟩
    | add x y _ _ _ hx hy => exact add_mem hx hy
    | mem_mul m hm i x _ ih =>
      rcases hm with ⟨v, rfl⟩
      exact TensorAlgebra.ι_mul_mem_range_toTensorAlgebra v ih

end TensorPower
