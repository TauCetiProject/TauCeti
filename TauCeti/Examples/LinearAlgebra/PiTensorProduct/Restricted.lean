/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.PiTensorProduct.Restricted

/-!
# Checks for restricted tensor products

* The empty finite stage is the ring of scalars, with the empty pure tensor as `1`
  (Mathlib's `PiTensorProduct.isEmptyEquiv`).
* A zero reference vector kills nonzero tensors: if `w j = 0`, the empty pure tensor, which is
  nonzero, has image `0` in the restricted tensor product, so the empty stage does not embed
  (`TauCeti.RestrictedTensor.not_injective_ofFinite_empty`). The nonzero-reference hypothesis of
  `TauCeti.RestrictedTensor.ofFinite_injective` cannot be dropped.
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace RestrictedTensor

variable {ι : Type*} {R : Type*} [CommSemiring R] {W : ι → Type*}
  [∀ i, AddCommMonoid (W i)] [∀ i, Module R (W i)]

-- The empty finite stage is the ring of scalars, with the empty pure tensor as `1`.
example (f : ∀ i : (∅ : Finset ι), W i) :
    PiTensorProduct.isEmptyEquiv (∅ : Finset ι) (PiTensorProduct.tprod R f) = 1 :=
  PiTensorProduct.isEmptyEquiv_apply_tprod _ f

variable [DecidableEq ι]

/-- If a reference vector is zero, the empty stage does not embed in the restricted tensor
product: its nonzero empty pure tensor is sent to `0`. -/
theorem not_injective_ofFinite_empty [Nontrivial R] {w : ∀ i, W i} {j : ι} (hj : w j = 0) :
    ¬ Function.Injective (ofFinite R W w ∅) := by
  intro hinj
  have h0 : ofFinite R W w ∅ (PiTensorProduct.tprod R fun i ↦ w i) = 0 := by
    rw [← tprod_ref, tprod_coord_zero w _ j hj]
  have hne : (PiTensorProduct.tprod R fun i : (∅ : Finset ι) ↦ w i) ≠ 0 := fun h ↦ by
    simpa [h] using PiTensorProduct.isEmptyEquiv_apply_tprod (R := R)
      (s := fun i : (∅ : Finset ι) ↦ W i) (∅ : Finset ι) fun i ↦ w i
  exact hne (hinj (h0.trans (map_zero _).symm))

end RestrictedTensor

end TauCeti
