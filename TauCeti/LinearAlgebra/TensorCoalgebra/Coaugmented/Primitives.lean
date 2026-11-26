/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Basic
public import TauCeti.LinearAlgebra.TensorCoalgebra.Primitives

/-!
# Primitive elements of the coaugmented tensor coalgebra

An element `z` of the coaugmented tensor coalgebra `Tᶜ(M)` is primitive when
`Δ z = z ⊗ 1 + 1 ⊗ z`.  Applying the counit shows that a primitive element has no empty-word
component, so it is the inclusion of a reduced tensor word with vanishing reduced coproduct, that
is, of a single letter (`TauCeti.ReducedTensorWords.deconcatenation_eq_zero_iff`).

## Main results

* `TauCeti.TensorWords.eq_reducedInclusion_ofLetter_of_deconcatenation_eq`: the primitive elements
  are the letters.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.6.
-/

public section

open scoped TensorProduct

universe uR uM

namespace TauCeti

namespace TensorWords

variable {R : Type uR} {M : Type uM} [CommSemiring R] [IsCancelAdd R] [AddCommMonoid M]
  [Module R M]

/-- **The primitive elements of `Tᶜ(M)` are the letters.**  An element `z` with
`Δ z = z ⊗ 1 + 1 ⊗ z` is the one-letter word on its letter component. -/
theorem eq_reducedInclusion_ofLetter_of_deconcatenation_eq {z : TensorWords R M}
    (hz : deconcatenation R M z = z ⊗ₜ[R] 1 + 1 ⊗ₜ[R] z) :
    z = reducedInclusion R M (ReducedTensorWords.ofLetter R M
      (ReducedTensorWords.letter R M (reducedProjection R M z))) := by
  -- The counit of a primitive element vanishes: apply the counit to both tensor factors.
  have hε : counit R M z = 0 := by
    have h := congrArg (fun y ↦ counit R M (TensorProduct.lid R (TensorWords R M) y))
      (LinearMap.congr_fun (rTensor_counit_comp_deconcatenation R M) z)
    simp only [LinearMap.comp_apply, hz, map_add, LinearMap.rTensor_tmul, counit_one,
      TensorProduct.mk_apply, TensorProduct.lid_tmul, map_smul, one_smul, smul_eq_mul,
      mul_one] at h
    exact add_eq_right.1 h
  set u := reducedProjection R M z
  have hzu : z = reducedInclusion R M u := by
    simpa [hε] using (reducedInclusion_reducedProjection_add_algebraMap_counit R M z).symm
  -- The reduced coproduct of `u` vanishes.
  have hu : ReducedTensorWords.deconcatenation R M u = 0 := by
    rw [← map_reducedProjection_deconcatenation_reducedInclusion, ← hzu, hz]
    simp
  obtain ⟨x, hx⟩ := (ReducedTensorWords.deconcatenation_eq_zero_iff R M).1 hu
  rw [hzu, ← hx, ReducedTensorWords.letter_ofLetter]

end TensorWords

end TauCeti
