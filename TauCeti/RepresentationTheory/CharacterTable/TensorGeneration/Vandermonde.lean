/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.TensorGeneration
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Tensor multiplicities and character fibres

* `FDRep.finrank_hom_tensorPower_eq_sum_characterFiberSum` computes a tensor multiplicity by
  grouping the character pairing using `FDRep.sum_characterFiberSum_smul`.
* `FDRep.forall_finrank_hom_tensorPower_add_eq_zero_iff` characterizes vanishing of a window of
  tensor multiplicities over the coefficient field by vanishing of the weighted character
  fibre sums. It uses Mathlib's `Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero`.

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

/-- Over a field in which the group order is invertible, the dimension of the intertwiner space
into a tensor power is the normalized sum of the character fibre weights times the
corresponding powers of the character values. -/
theorem finrank_hom_tensorPower_eq_sum_characterFiberSum (V X : FDRep k G) (n : ℕ) :
    (Module.finrank k (X ⟶ V.tensorPower n) : k) =
      (Nat.card G : k)⁻¹ * ∑ a ∈ V.characterValues, V.characterFiberSum X a * a ^ n := by
  have hgroup :
      ∑ a ∈ V.characterValues, V.characterFiberSum X a * a ^ n =
        ∑ g : G, V.character g ^ n * X.character g⁻¹ := by
    simpa only [smul_eq_mul, mul_comm] using V.sum_characterFiberSum_smul X (fun a : k ↦ a ^ n)
  rw [hgroup, ← scalar_product_char_eq_finrank_equivariant X (V.tensorPower n)]
  simp only [char_tensorPower]

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
    let e := (V.characterValues.equivFinOfCardEq V.card_characterValues).symm
    have hzero : (fun i ↦ V.characterFiberSum X (e i) * (e i : k) ^ B) = 0 := by
      apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
        (Subtype.val_injective.comp e.injective)
      intro n
      let moment (a : k) := V.characterFiberSum X a * a ^ B * a ^ (n : ℕ)
      exact (e.sum_comp (fun a ↦ moment a)).trans
        ((Finset.sum_coe_sort V.characterValues moment).trans (h n n.isLt))
    have hvalue := congrFun hzero (e.symm ⟨a, ha⟩)
    simpa only [Equiv.apply_symm_apply, Pi.zero_apply] using hvalue
  · intro h n _
    exact Finset.sum_eq_zero fun a ha ↦ by rw [h a ha, zero_mul]

end FDRep
