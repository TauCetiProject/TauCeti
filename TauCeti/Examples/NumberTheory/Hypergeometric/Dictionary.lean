/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Hypergeometric.Dictionary
import Mathlib.Tactic.NormNum

/-!
# Examples of the dictionary between cyclotomic data and parameter pairs

* `A = {4}` gives `α = {1/4, 3/4}`, the arguments of the roots of `Φ_4 = X² + 1`, and not the
  four classes `{1/4, 1/2, 3/4, 1}` of the roots of `X⁴ - 1`. `A = {1}` gives `α = {1}`, the
  class of `0`.
* The pair `α = {1/6}`, `β = {1/3}` is not Galois stable: in the pair of a cyclotomic datum a
  class of order `6` comes with all `φ(6) = 2` classes of that order.
* `A = {10, 6, 3, 2}`, `B = {14, 1, 1, 1}` has degree `9 = 4 + 2 + 2 + 1 = 6 + 1 + 1 + 1` and
  common denominator `lcm = 210`.
-/

public section

open TauCeti.Hypergeometric

namespace TauCeti.Hypergeometric.Examples

example : primitiveClasses {4} =
    {((1 / 4 : ℚ) : AddCircle (1 : ℚ)), ((3 / 4 : ℚ) : AddCircle (1 : ℚ))} := by
  rw [primitiveClasses_singleton, show (Finset.Icc 1 4).filter (Nat.Coprime 4) = {1, 3} by decide]
  norm_num

example : primitiveClasses {1} = {0} := by
  rw [primitiveClasses_singleton, show (Finset.Icc 1 1).filter (Nat.Coprime 1) = {1} by decide]
  simp [AddCircle.coe_period]

/-- The pair `α = {1/6}`, `β = {1/3}`. -/
noncomputable def sixthThird : Parameters where
  α := {((1 / 6 : ℚ) : AddCircle (1 : ℚ))}
  β := {((1 / 3 : ℚ) : AddCircle (1 : ℚ))}
  card_eq := rfl
  disjoint := by
    simp only [Multiset.disjoint_iff_ne, Multiset.mem_singleton]
    rintro _ rfl _ rfl
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc (a := 0) (by norm_num) (by norm_num)).not.2
        (by norm_num)

-- A datum whose `α` is `{1/6}` would have `6 ∈ A`, hence at least `φ(6) = 2` classes in `α`.
example : ¬ sixthThird.IsGaloisStable := by
  intro h
  obtain ⟨D, hD⟩ := (CyclotomicData.existsUnique_toParameters_eq h).exists
  have h6 : 6 ∈ D.A := by
    have hmem : ((1 / 6 : ℚ) : AddCircle (1 : ℚ)) ∈ D.toParameters.α := by simp [hD, sixthThird]
    rwa [CyclotomicData.toParameters_α, mem_primitiveClasses,
      show (1 / 6 : ℚ) = 1 / (6 : ℕ) by norm_num,
      AddCircle.addOrderOf_period_div (by norm_num)] at hmem
  have hcard : Multiset.card D.toParameters.α = 1 := by
    simp [hD, sixthThird]
  rw [CyclotomicData.toParameters_α, card_primitiveClasses] at hcard
  have hle : Nat.totient 6 ≤ (D.A.map Nat.totient).sum :=
    Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ h6)
  have h2 : Nat.totient 6 = 2 := by decide
  omega

/-- The datum `A = {10, 6, 3, 2}`, `B = {14, 1, 1, 1}`. -/
def tenSixThreeTwo : CyclotomicData where
  A := {10, 6, 3, 2}
  B := {14, 1, 1, 1}
  pos := by decide
  disjoint := Multiset.disjoint_left.2 (by simp)
  totient_sum_eq := by decide

example : tenSixThreeTwo.toParameters.degree = 9 := by
  rw [CyclotomicData.degree_toParameters, ← CyclotomicData.sum_map_totient_A]
  decide

example : tenSixThreeTwo.toParameters.denominator = 210 := by
  rw [CyclotomicData.denominator_toParameters]
  decide

end TauCeti.Hypergeometric.Examples
