/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Algebra.Polynomial.CardBoundedCoeff
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Counting integer polynomials of bounded degree and height

For natural numbers `D` and `C`, the set of integer polynomials of degree at most `D` whose
coefficients are all bounded in absolute value by `C` is finite, with at most

`(2·C + 1)^(D + 1)`

elements. Indeed such a polynomial is determined by its `D + 1` coefficients of index `0, …, D`
(every higher coefficient vanishes), each of which lies in the integer interval `[-C, C]` of
size `2·C + 1`; counting the coefficient vectors gives the bound.

This is the elementary counting step that the **Layer 2** summit of the effective-bounds
roadmap needs. Mathlib's qualitative Hermite–Minkowski theorem
(`NumberField.finite_of_discr_bdd`) already bounds the degree and the coefficients of a
generating polynomial of each number field of bounded discriminant, but it only concludes
*finiteness* of the resulting polynomial family (through `Polynomial.bUnion_roots_finite` over a
finite coefficient box); it never counts it. The explicit count below is what turns that
finiteness into an explicit upper bound on the number of fields.

## Main results

* `TauCeti.NumberField.card_intPolynomial_degree_height_le`: the explicit count
  `#{p : ℤ[X] | p.natDegree ≤ D ∧ ∀ i, |p.coeff i| ≤ C} ≤ (2·C + 1)^(D + 1)`.
* `TauCeti.NumberField.finite_intPolynomial_degree_height`: the same family is finite.
-/

open Polynomial

namespace TauCeti.NumberField

variable (D C : ℕ)

/-- The family of integer polynomials of degree at most `D` whose coefficients are all bounded in
absolute value by `C`. This is the polynomial box that the effective Hermite–Minkowski count
ranges over. -/
def intPolynomialBox : Set ℤ[X] :=
  {p | p.natDegree ≤ D ∧ ∀ i, (p.coeff i).natAbs ≤ C}

/-- A polynomial in `intPolynomialBox D C` has each of its first `D + 1` coefficients in the finite
integer interval `[-C, C]`. -/
theorem coeff_mem_Icc_of_mem_intPolynomialBox {p : ℤ[X]} (hp : p ∈ intPolynomialBox D C)
    (i : Fin (D + 1)) : p.coeff i ∈ Finset.Icc (-(C : ℤ)) (C : ℤ) := by
  have h : |p.coeff i| ≤ (C : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hp.2 i
  exact Finset.mem_Icc.mpr (abs_le.mp h)

/-- Sending a polynomial to its coefficient vector `(c₀, …, c_D) ∈ [-C, C]^{D+1}` is injective on
`intPolynomialBox D C`: a polynomial of degree at most `D` is determined by those coefficients,
since all higher coefficients vanish. -/
theorem coeffVec_injOn :
    Set.InjOn (fun p : ℤ[X] => fun i : Fin (D + 1) => p.coeff i) (intPolynomialBox D C) := by
  intro p hp q hq hpq
  refine Polynomial.ext fun n => ?_
  by_cases hn : n ≤ D
  · exact congr_fun hpq ⟨n, by omega⟩
  · have hn' : D < n := not_le.mp hn
    rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp.1 hn'),
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hq.1 hn')]

/-- **Counting integer polynomials of bounded degree and height.** There are at most
`(2·C + 1)^(D + 1)` integer polynomials of degree at most `D` whose coefficients are all bounded in
absolute value by `C`. -/
theorem card_intPolynomial_degree_height_le :
    (intPolynomialBox D C).ncard ≤ (2 * C + 1) ^ (D + 1) := by
  have hbox : intPolynomialBox D C =
      {p : ℤ[X] | p.natDegree ≤ D ∧ ∀ i, |p.coeff i| ≤ (C : ℤ)} := by
    ext p
    constructor
    · intro hp
      refine ⟨hp.1, fun i => ?_⟩
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hp.2 i
    · intro hp
      refine ⟨hp.1, fun i => ?_⟩
      have hcoeff : |p.coeff i| ≤ (C : ℤ) := hp.2 i
      rw [Int.abs_eq_natAbs] at hcoeff
      exact_mod_cast hcoeff
  rw [hbox]
  exact TauCeti.Polynomial.ncard_natDegree_le_abs_intCoeff_le D C

/-- The family of integer polynomials of degree at most `D` with coefficients bounded by `C` is
finite. (The explicit count above bounds its cardinality; this records finiteness on its own, since
`Set.ncard` carries no finiteness information for an a priori possibly-infinite set.) -/
theorem finite_intPolynomial_degree_height : (intPolynomialBox D C).Finite := by
  classical
  let T : Finset ℤ := Finset.Icc (-(C : ℤ)) (C : ℤ)
  let f : intPolynomialBox D C → (Fin (D + 1) → T) :=
    fun p i => ⟨(p : ℤ[X]).coeff i, coeff_mem_Icc_of_mem_intPolynomialBox D C p.2 i⟩
  have hf : Function.Injective f := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ hpq
    refine Subtype.ext (coeffVec_injOn D C hp hq (funext fun i => ?_))
    exact congr_arg Subtype.val (congr_fun hpq i)
  exact Set.finite_coe_iff.mp (Finite.of_injective f hf)

end TauCeti.NumberField
