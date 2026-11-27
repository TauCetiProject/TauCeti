/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.TensorGeneration
import TauCeti.LinearAlgebra.Vandermonde

/-!
# Tensor multiplicities and character fibres

* `FDRep.forall_finrank_hom_tensorPower_add_eq_zero_iff` characterizes vanishing of a window of
  tensor multiplicities over the coefficient field by vanishing of the weighted character
  fibre sums. It uses `FDRep.finrank_hom_tensorPower_eq_sum_characterFiberSum` and
  `TauCeti.exists_lt_card_sum_mul_pow_ne_zero`, which packages Mathlib's
  `Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero` for finite sets.

At shift zero this gives the Vandermonde step of Burnside–Brauer. For a faithful complex
representation, `FDRep.characterFiberSum_finrank_of_injective` gives a nonzero identity-fibre
sum whenever the source has positive dimension.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Theorem 4.3.
* B. Steinberg, *On the Burnside–Brauer–Steinberg theorem*, arXiv:1409.7632, Theorem 6.
-/

public section

open CategoryTheory

namespace FDRep

variable {k G : Type*} [Field k] [Group G] [Fintype G] [Invertible (Nat.card G : k)]

/-- If the group order is invertible, a full window of tensor multiplicities, read in the
coefficient field, vanishes exactly when every character fibre weight multiplied by the
corresponding power at the start of the window vanishes. In particular, shift zero tests
all fibres, including the fibre over zero (Isaacs, Theorem 4.3). -/
theorem forall_finrank_hom_tensorPower_add_eq_zero_iff (V X : FDRep k G) (B : ℕ) :
    (∀ n < V.characterValueCount, (Module.finrank k (X ⟶ V.tensorPower (B + n)) : k) = 0) ↔
      ∀ a ∈ V.characterValues, V.characterFiberSum X a * a ^ B = 0 := by
  have hmoment (n : ℕ) :
      (Module.finrank k (X ⟶ V.tensorPower (B + n)) : k) = 0 ↔
        ∑ a ∈ V.characterValues, (V.characterFiberSum X a * a ^ B) * a ^ n = 0 := by
    rw [V.finrank_hom_tensorPower_eq_sum_characterFiberSum, mul_eq_zero]
    simp only [inv_ne_zero (Invertible.ne_zero (Nat.card G : k)), false_or, pow_add, mul_assoc]
  simp_rw [hmoment]
  constructor
  · intro h a ha
    by_contra hne
    obtain ⟨n, hn, hsum⟩ := TauCeti.exists_lt_card_sum_mul_pow_ne_zero
      (θ := id) (w := fun a ↦ V.characterFiberSum X a * a ^ B)
      Function.injective_id.injOn ⟨a, ha, hne⟩
    rw [V.card_characterValues] at hn
    exact hsum (h n hn)
  · intro h n _
    exact Finset.sum_eq_zero fun a ha ↦ by rw [h a ha, zero_mul]

end FDRep
