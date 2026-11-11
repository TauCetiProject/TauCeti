/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.ClebschGordan
public import TauCeti.Algebra.Lie.Sl2.HighestWeight
public import TauCeti.Algebra.Lie.UniversalEnveloping.Multiplicity

/-!
# Isotypic multiplicities of `sl₂`-modules against their characters

For `L = sl (Fin 2) K` over an algebraically closed field of characteristic zero, with the diagonal
Cartan and the positive base selecting `e = E₀₁`, this file computes the isotypic decomposition of
the module

`M = (V(1) ⊗ V(1)) × V(0)`

in two independent ways and checks that they agree.

* **By Clebsch-Gordan.** `V(m) ⊗ V(n)` is the internal direct sum of copies of `V(m + n - 2k)`
  for `k ≤ min m n` (`TauCeti.Sl2Std.isInternal_cgSummand`), and `V(p)` is `L(p)`, so by Schur's
  lemma the multiplicity of `L(p)` in `V(m) ⊗ V(n)` counts the `k` with `m + n - 2k = p`
  (`TauCeti.Sl2Std.isotypicMultiplicity_tensor_irreducibleQuotient`). For `M` the multiplicities of
  `L(2)`, `L(1)`, `L(0)` are therefore `1`, `0`, `2`
  (`TauCeti.Sl2Std.isotypicMultiplicity_one_tensor_one_prod_zero`).
* **By characters.** The formal character of `M` is `e^{2} + 3 + e^{-2}`
  (`TauCeti.Sl2Std.formalCharacter_one_tensor_one_prod_zero`), and multiplying it by the Weyl
  denominator `1 - e^{-2}` leaves the coefficients `1`, `0`, `2` at the weights `2`, `1`, `0`
  (`TauCeti.Sl2Std.coeff_formalCharacter_one_tensor_one_prod_zero_mul_weylDenominator`). These are
  the multiplicities again, as Weyl-alternating inversion
  (`TauCeti.coeff_formalCharacter_mul_weylDenominator_eq_isotypicMultiplicity`) predicts. Read on
  characters the decomposition is `ch M = ch V(2) + 2 ch V(0)`
  (`TauCeti.Sl2Std.formalCharacter_one_tensor_one_prod_zero_eq_add`).

The isotypic components of `M` then have dimensions `3`, `0`, `2`, the multiplicity times
`dim L(p) = p + 1` (`TauCeti.Sl2Std.finrank_isotypicComponent_one_tensor_one_prod_zero`), and these
add up to `dim M = 5` (`TauCeti.Sl2Std.sum_finrank_isotypicComponent_one_tensor_one_prod_zero`).

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §7.2, §22.5 and
  §24.
-/

public section

open LieAlgebra LieModule Module

open scoped TensorProduct

namespace TauCeti

namespace Sl2Std

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Field K] [CharZero K]

/-! ### Multiplicities by Clebsch-Gordan -/

section Multiplicity

variable [IsAlgClosed K]

/-- **The Clebsch-Gordan multiplicities.** The multiplicity of `L(p)` in `V(m) ⊗ V(n)` is the
number of `k ≤ min m n` with `m + n - 2k = p`. -/
theorem isotypicMultiplicity_tensor_irreducibleQuotient (m n p : ℕ) :
    LieModule.isotypicMultiplicity K (SpecialLinear.sl (Fin 2) K) (Sl2Std K m ⊗[K] Sl2Std K n)
        (irreducibleQuotient (slTwoPositiveBase K) (slTwoWeight (p : K))) =
      (Finset.univ.filter fun k : Fin (min m n + 1) ↦ p = m + n - 2 * (k : ℕ)).card := by
  rw [LieModule.isotypicMultiplicity_eq_sum_of_isInternal _
    (isInternal_cgSummand (K := K) (m := m) (n := n)) fun _ ↦ inferInstance, Finset.card_filter]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  obtain ⟨e⟩ := nonempty_lieModuleEquiv_cgSummand (K := K) k
  rw [LieModule.isotypicMultiplicity_eq_of_lieModuleEquiv e,
    isotypicMultiplicity_irreducibleQuotient]
  simp only [slTwoWeight_inj, Nat.cast_inj]

/-- **The multiplicities of `(V(1) ⊗ V(1)) × V(0)`**, read off from Clebsch-Gordan:
`L(0)` occurs twice, `L(2)` once and every other `L(p)` not at all. -/
theorem isotypicMultiplicity_one_tensor_one_prod_zero (p : ℕ) :
    LieModule.isotypicMultiplicity K (SpecialLinear.sl (Fin 2) K)
        ((Sl2Std K 1 ⊗[K] Sl2Std K 1) × Sl2Std K 0)
        (irreducibleQuotient (slTwoPositiveBase K) (slTwoWeight (p : K))) =
      if p = 0 then 2 else if p = 2 then 1 else 0 := by
  rw [LieModule.isotypicMultiplicity_prod _ inferInstance inferInstance,
    isotypicMultiplicity_tensor_irreducibleQuotient, isotypicMultiplicity_irreducibleQuotient]
  simp only [slTwoWeight_inj, Nat.cast_inj]
  split_ifs with h0 h2
  · subst h0
    decide
  · subst h2
    decide
  · rw [add_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro k _
    have := k.isLt
    omega

end Multiplicity

/-! ### Multiplicities by characters -/

section Character

/-- **The formal character of `(V(1) ⊗ V(1)) × V(0)`** is `e^{2} + 3 + e^{-2}`. -/
theorem formalCharacter_one_tensor_one_prod_zero :
    formalCharacter K (slTwoDiagonalCartan K) ((Sl2Std K 1 ⊗[K] Sl2Std K 1) × Sl2Std K 0) =
      AddMonoidAlgebra.single (slTwoWeight (2 : K)) 1 +
        AddMonoidAlgebra.single (slTwoWeight (0 : K)) 3 +
          AddMonoidAlgebra.single (slTwoWeight (-2 : K)) 1 := by
  -- The Cartan acts on `V(1) ⊗ V(1)` by restricting the action of `sl₂`; this agrees with the
  -- tensor product of the restricted actions, which `formalCharacter_tensor` is stated for, only
  -- after unfolding, so the tensor-product step is elaborated against the restricted action.
  have htensor : formalCharacter K (slTwoDiagonalCartan K) (Sl2Std K 1 ⊗[K] Sl2Std K 1) =
      formalCharacter K (slTwoDiagonalCartan K) (Sl2Std K 1) *
        formalCharacter K (slTwoDiagonalCartan K) (Sl2Std K 1) :=
    formalCharacter_tensor
  rw [formalCharacter_prod, htensor, formalCharacter_eq_sum, formalCharacter_eq_sum,
    show (3 : ℤ) = 1 + 1 + 1 by norm_num, AddMonoidAlgebra.single_add,
    AddMonoidAlgebra.single_add]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_mul, mul_add, add_zero,
    AddMonoidAlgebra.single_mul_single, ← slTwoWeight_add, mul_one]
  norm_num only [Fin.val_zero, Fin.val_succ]
  abel

/-- **The character of `(V(1) ⊗ V(1)) × V(0)` is `ch V(2) + 2 ch V(0)`**, the Clebsch-Gordan
decomposition read on characters. -/
theorem formalCharacter_one_tensor_one_prod_zero_eq_add :
    formalCharacter K (slTwoDiagonalCartan K) ((Sl2Std K 1 ⊗[K] Sl2Std K 1) × Sl2Std K 0) =
      formalCharacter K (slTwoDiagonalCartan K) (Sl2Std K 2) +
        2 • formalCharacter K (slTwoDiagonalCartan K) (Sl2Std K 0) := by
  rw [formalCharacter_one_tensor_one_prod_zero, formalCharacter_eq_sum, formalCharacter_eq_sum,
    show (3 : ℤ) = 1 + 1 + 1 by norm_num, AddMonoidAlgebra.single_add,
    AddMonoidAlgebra.single_add]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  norm_num only [Fin.val_zero, Fin.val_succ]
  abel

/-- **The multiplicities of `(V(1) ⊗ V(1)) × V(0)` read off its character.** Multiplying the
character by the Weyl denominator `1 - e^{-2}` gives `e^{2} + 2 - 2e^{-2} - e^{-4}`, whose
coefficients at the dominant weights `p = 0, 1, 2, …` are the multiplicities `2, 0, 1, 0, …` of
`TauCeti.Sl2Std.isotypicMultiplicity_one_tensor_one_prod_zero`. -/
theorem coeff_formalCharacter_one_tensor_one_prod_zero_mul_weylDenominator (p : ℕ) :
    (formalCharacter K (slTwoDiagonalCartan K) ((Sl2Std K 1 ⊗[K] Sl2Std K 1) × Sl2Std K 0) *
        weylDenominator (IsKilling.rootSystem (slTwoDiagonalCartan K))
          (slTwoPositiveBase K)).coeff (slTwoWeight (p : K)) =
      if p = 0 then 2 else if p = 2 then 1 else 0 := by
  classical
  -- Every weight that occurs is `slTwoWeight` of an integer, and such weights compare in `ℤ`.
  have hch : formalCharacter K (slTwoDiagonalCartan K)
      ((Sl2Std K 1 ⊗[K] Sl2Std K 1) × Sl2Std K 0) =
        AddMonoidAlgebra.single (slTwoWeight ((2 : ℤ) : K)) 1 +
          AddMonoidAlgebra.single (slTwoWeight ((0 : ℤ) : K)) 3 +
            AddMonoidAlgebra.single (slTwoWeight ((-2 : ℤ) : K)) 1 := by
    push_cast
    exact formalCharacter_one_tensor_one_prod_zero
  have hΔ : weylDenominator (IsKilling.rootSystem (slTwoDiagonalCartan K)) (slTwoPositiveBase K) =
      1 - AddMonoidAlgebra.single (slTwoWeight ((-2 : ℤ) : K)) 1 := by
    push_cast
    exact weylDenominator_slTwoPositiveBase
  rw [hch, hΔ, ← Int.cast_natCast, mul_sub, mul_one, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    AddMonoidAlgebra.coeff_mul_single_apply, ← sub_eq_add_neg, ← slTwoWeight_sub, ← Int.cast_sub]
  simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_single, Finsupp.add_apply,
    Finsupp.single_apply, slTwoWeight_inj, Int.cast_inj]
  grind

end Character

/-! ### The dimensions of the isotypic components -/

section IsotypicComponent

variable [IsAlgClosed K]

/-- **The isotypic components of `(V(1) ⊗ V(1)) × V(0)`**: the `L(0)`-component has dimension `2`,
the `L(2)`-component dimension `3`, and all others are zero. Each is the multiplicity times
`dim L(p) = p + 1`. -/
theorem finrank_isotypicComponent_one_tensor_one_prod_zero (p : ℕ) :
    finrank K (LieModule.isotypicComponent K (SpecialLinear.sl (Fin 2) K)
        ((Sl2Std K 1 ⊗[K] Sl2Std K 1) × Sl2Std K 0)
        (irreducibleQuotient (slTwoPositiveBase K) (slTwoWeight (p : K)))) =
      if p = 0 then 2 else if p = 2 then 3 else 0 := by
  rw [LieModule.finrank_isotypicComponent, isotypicMultiplicity_one_tensor_one_prod_zero,
    finrank_irreducibleQuotient_slTwoWeight]
  rcases p with _ | _ | _ | p <;> simp

/-- **The dimensions of the isotypic components of `M = (V(1) ⊗ V(1)) × V(0)` add up to
`dim M`**: `3 + 0 + 2 = 5` at the weights `2`, `1`, `0`. -/
theorem sum_finrank_isotypicComponent_one_tensor_one_prod_zero :
    ∑ p ∈ Finset.range 3, finrank K (LieModule.isotypicComponent K (SpecialLinear.sl (Fin 2) K)
        ((Sl2Std K 1 ⊗[K] Sl2Std K 1) × Sl2Std K 0)
        (irreducibleQuotient (slTwoPositiveBase K) (slTwoWeight (p : K)))) =
      finrank K ((Sl2Std K 1 ⊗[K] Sl2Std K 1) × Sl2Std K 0) := by
  simp only [finrank_isotypicComponent_one_tensor_one_prod_zero, Finset.sum_range_succ,
    Finset.sum_range_zero, finrank_prod, finrank_tensorProduct, finrank_eq]
  norm_num

end IsotypicComponent

end Sl2Std

end TauCeti
