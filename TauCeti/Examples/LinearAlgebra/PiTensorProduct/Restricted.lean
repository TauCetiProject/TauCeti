/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.PiTensorProduct.Restricted.Rescale

/-!
# Checks for restricted tensor products

* The empty finite stage is the ring of scalars, with the empty pure tensor as `1`
  (`TauCeti.RestrictedTensor.emptyStageEquiv_tprod`).
* A zero reference vector kills nonzero tensors: if `w j = 0`, the empty pure tensor, which is
  nonzero, has image `0` in the restricted tensor product, so the empty stage does not embed
  (`TauCeti.RestrictedTensor.not_injective_ofFinite_empty`). The nonzero-reference hypothesis of
  `TauCeti.RestrictedTensor.ofFinite_injective` cannot be dropped.
* Rescaling the references by units `c i` sends the pure tensor of the references to the pure
  tensor of the rescaled references (`TauCeti.RestrictedTensor.rescale_tprod_ref`).
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace RestrictedTensor

variable {ι : Type*} {R : Type*} [CommSemiring R] {W : ι → Type*}
  [∀ i, AddCommMonoid (W i)] [∀ i, Module R (W i)]

variable (R W) in
/-- The empty finite stage is the ring of scalars. -/
noncomputable def emptyStageEquiv : (⨂[R] i : (∅ : Finset ι), W i) ≃ₗ[R] R :=
  PiTensorProduct.isEmptyEquiv _

/-- The empty pure tensor corresponds to `1`. -/
theorem emptyStageEquiv_tprod (f : ∀ i : (∅ : Finset ι), W i) :
    emptyStageEquiv R W (PiTensorProduct.tprod R f) = 1 :=
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
    simpa [h] using emptyStageEquiv_tprod (R := R) (W := W) fun i ↦ w i
  exact hne (hinj (h0.trans (map_zero _).symm))

/-- Rescaling the references sends the pure tensor of the references to the pure tensor of the
rescaled references. -/
theorem rescale_tprod_ref {w w' : ∀ i, W i} (c : ι → Rˣ) (hw : ∀ i, w' i = (c i : R) • w i) :
    rescale w w' c hw (tprod R w w (by simp)) = tprod R w' w' (by simp) := by
  rw [rescale_tprod]
  simp_rw [← hw]

end RestrictedTensor

end TauCeti
