/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorAlgebra.Grading
public import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower

/-!
# Tensor powers inside the tensor algebra and its grading

Mathlib identifies the tensor algebra `TensorAlgebra R M` with the direct sum `⨁ n, ⨂[R]^n M` of
the tensor powers (`TensorAlgebra.toDirectSum`, `TensorAlgebra.ofDirectSum`), and separately
grades it by the powers `range ι ^ n` of the image of `TensorAlgebra.ι`
(`TensorAlgebra.gradedAlgebra`). This file records how the two descriptions match:
`TensorPower.toTensorAlgebra` lands in the `n`-th graded piece, it is the degree-`n` part of
`ofDirectSum`, and the homogeneous components of a tensor for `TensorAlgebra.gradedAlgebra` are
the components of `TensorAlgebra.toDirectSum`.

## Main results

* `TensorAlgebra.ofDirectSum_of`, `TensorAlgebra.toDirectSum_toTensorAlgebra`: the identification
  with the direct sum restricts to `TensorPower.toTensorAlgebra` in each degree.
* `TensorPower.toTensorAlgebra_mem_range_ι_pow`: a degree-`n` tensor lies in `range ι ^ n`.
* `TensorAlgebra.coe_decompose_eq_toTensorAlgebra_toDirectSum`: the degree-`n` component for
  `TensorAlgebra.gradedAlgebra` is the image of the degree-`n` component of `toDirectSum`.
-/

public section

open DirectSum
open scoped TensorProduct

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

namespace TensorAlgebra

/-- On the degree-`n` summand, `TensorAlgebra.ofDirectSum` is `TensorPower.toTensorAlgebra`. -/
@[simp]
theorem ofDirectSum_of {n : ℕ} (x : ⨂[R]^n M) :
    ofDirectSum (of _ n x) = TensorPower.toTensorAlgebra x :=
  DirectSum.toAddMonoid_of (fun _ ↦ LinearMap.toAddMonoidHom TensorPower.toTensorAlgebra) _ _

/-- A degree-`n` tensor, viewed in the tensor algebra, corresponds under
`TensorAlgebra.toDirectSum` to the degree-`n` summand. -/
@[simp]
theorem toDirectSum_toTensorAlgebra {n : ℕ} (x : ⨂[R]^n M) :
    toDirectSum (TensorPower.toTensorAlgebra x) = of _ n x := by
  rw [← ofDirectSum_of, toDirectSum_ofDirectSum]

end TensorAlgebra

open TensorAlgebra

/-- A degree-`n` tensor lies in the `n`-th piece `range ι ^ n` of the grading
`TensorAlgebra.gradedAlgebra` of the tensor algebra. -/
theorem TensorPower.toTensorAlgebra_mem_range_ι_pow {n : ℕ} (x : ⨂[R]^n M) :
    TensorPower.toTensorAlgebra x ∈ LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) ^ n := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r g =>
    rw [map_smul, TensorPower.toTensorAlgebra_tprod, TensorAlgebra.tprod_apply]
    refine Submodule.smul_mem _ r ?_
    simpa using SetLike.list_prod_ofFn_mem_graded
      (A := fun n : ℕ ↦ LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) ^ n) (fun _ ↦ 1)
      (fun k ↦ ι R (g k)) fun k ↦ by simp
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

namespace TensorAlgebra

/-- The homogeneous components of a tensor for the grading `TensorAlgebra.gradedAlgebra` are the
images in the tensor algebra of the components of `TensorAlgebra.toDirectSum`. -/
theorem coe_decompose_eq_toTensorAlgebra_toDirectSum (t : TensorAlgebra R M) (n : ℕ) :
    (decompose (fun n : ℕ ↦ LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) ^ n) t n :
      TensorAlgebra R M) = TensorPower.toTensorAlgebra (toDirectSum t n) := by
  classical
  conv_lhs => rw [← ofDirectSum_toDirectSum t, ← sum_support_of (toDirectSum t)]
  rw [map_sum, decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
  simp_rw [ofDirectSum_of]
  rw [Finset.sum_eq_single n
    (fun m _ hmn ↦ decompose_of_mem_ne _ (TensorPower.toTensorAlgebra_mem_range_ι_pow _) hmn)
    (fun hn ↦ by simp [DFinsupp.notMem_support_iff.1 hn])]
  exact decompose_of_mem_same _ (TensorPower.toTensorAlgebra_mem_range_ι_pow _)

end TensorAlgebra
