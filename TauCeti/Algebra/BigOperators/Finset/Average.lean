/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Group.Action.Basic

/-!
# Algebra of finite averages

Over a ring in which the number of terms is invertible, the average `⅟#s • ∑ i ∈ s, f i` of a
family is the usual normalised sum. Averaging a constant family returns the constant. This is the
step that closes averaging arguments (Reynolds operators, Bochner averages, Maschke-type
projections) once the averaged terms have been shown to coincide.

The squared deviation from an average also expands into the double sum of centered products.
This identity is useful for second-moment calculations without any independence assumptions.

## Main results

* `Finset.invOf_card_smul_sum_const`: `⅟#s • ∑ _i ∈ s, v = v`.
* `Fintype.invOf_card_smul_sum_const`: the same over all of a finite type.
* `TauCeti.average_sub_sq_eq_sum_sum`: the squared deviation as a double sum.
-/

public section

open scoped BigOperators

variable {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- Averaging a constant over a finset returns it. -/
theorem Finset.invOf_card_smul_sum_const (s : Finset ι) [Invertible (s.card : R)] (v : M) :
    ⅟(s.card : R) • ∑ _i ∈ s, v = v := by
  rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul R, invOf_smul_smul]

/-- Averaging a constant over a finite type returns it. -/
theorem Fintype.invOf_card_smul_sum_const [Fintype ι] [Invertible (Fintype.card ι : R)] (v : M) :
    ⅟(Fintype.card ι : R) • ∑ _i : ι, v = v := by
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul R, invOf_smul_smul]

namespace TauCeti

/-- **The squared deviation of an average, as a double sum.** For a nonempty finite index set `s`,
the square of `(#s)⁻¹ * ∑ i ∈ s, a i - b` is `(#s)⁻¹ ^ 2` times the double sum of
`(a i - b) * (a j - b)` over `s × s`. -/
theorem average_sub_sq_eq_sum_sum {ι R : Type*} [Field R] [CharZero R] {s : Finset ι}
    (hs : s.Nonempty) (a : ι → R) (b : R) :
    ((s.card : R)⁻¹ * (∑ i ∈ s, a i) - b) ^ 2
      = (s.card : R)⁻¹ ^ 2 * ∑ i ∈ s, ∑ j ∈ s, (a i - b) * (a j - b) := by
  -- both normalised sums are expectations, where subtracting a constant is `expect_const`
  have hexp : ∀ f : ι → R, (s.card : R)⁻¹ * (∑ i ∈ s, f i) = 𝔼 i ∈ s, f i := fun f => by
    rw [Finset.expect_eq_sum_div_card, div_eq_inv_mul]
  have h1 : (s.card : R)⁻¹ * (∑ i ∈ s, a i) - b = (s.card : R)⁻¹ * ∑ i ∈ s, (a i - b) := by
    rw [hexp, hexp, Finset.expect_sub_distrib, Finset.expect_const hs]
  rw [h1, mul_pow, sq (∑ i ∈ s, (a i - b)), Finset.sum_mul_sum]

end TauCeti
