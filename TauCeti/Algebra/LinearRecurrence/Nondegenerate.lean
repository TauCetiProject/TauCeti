/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.LinearRecurrence
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Nondegenerate linear recurrences

A recurrence is nondegenerate when its characteristic polynomial has nonzero constant
coefficient and no quotient of distinct characteristic roots is a root of unity.
Roots are taken in the algebraic closure of the coefficient field, not just in that field:
in particular, irreducible characteristic polynomials do not satisfy the condition vacuously.
Repeated roots are allowed.

The power characterization says precisely that distinct roots remain distinct on every
positive-step arithmetic progression. Nondegeneracy passes to characteristic-polynomial
divisors, as needed when replacing an annihilating recurrence by a minimal one.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), Chapter 8,
  §8.4, pp. 172–175.
-/

public section

open Polynomial

namespace LinearRecurrence

variable {K : Type*} [Field K]

/-- A recurrence is nondegenerate if its characteristic roots are nonzero and no quotient
of distinct roots in the algebraic closure is a root of unity. This does not require the
characteristic polynomial to be squarefree. -/
def IsNondegenerate (E : LinearRecurrence K) : Prop :=
  E.charPoly.coeff 0 ≠ 0 ∧
    ∀ ⦃θ θ' : AlgebraicClosure K⦄,
      θ ∈ E.charPoly.rootSet (AlgebraicClosure K) →
      θ' ∈ E.charPoly.rootSet (AlgebraicClosure K) →
      θ ≠ θ' → ¬IsOfFinOrder (θ / θ')

/-- Nondegeneracy is equivalent to a nonzero constant characteristic coefficient and
infinite multiplicative order of every quotient of distinct characteristic roots. -/
theorem isNondegenerate_def (E : LinearRecurrence K) :
    E.IsNondegenerate ↔ E.charPoly.coeff 0 ≠ 0 ∧
      ∀ ⦃θ θ' : AlgebraicClosure K⦄,
        θ ∈ E.charPoly.rootSet (AlgebraicClosure K) →
        θ' ∈ E.charPoly.rootSet (AlgebraicClosure K) →
        θ ≠ θ' → ¬IsOfFinOrder (θ / θ') :=
  Iff.rfl

variable {E E' : LinearRecurrence K}

/-- The constant characteristic coefficient of a nondegenerate recurrence is nonzero. -/
theorem IsNondegenerate.coeff_zero_ne_zero (h : E.IsNondegenerate) :
    E.charPoly.coeff 0 ≠ 0 :=
  h.1

/-- Every characteristic root of a nondegenerate recurrence is nonzero. -/
theorem IsNondegenerate.root_ne_zero (h : E.IsNondegenerate)
    {θ : AlgebraicClosure K} (hθ : θ ∈ E.charPoly.rootSet (AlgebraicClosure K)) : θ ≠ 0 := by
  intro hzero
  have hz := aeval_eq_zero_of_mem_rootSet hθ
  have hz' : algebraMap K (AlgebraicClosure K) (E.charPoly.coeff 0) = 0 := by
    simpa only [hzero, ← coeff_zero_eq_aeval_zero'] using hz
  exact h.1 ((algebraMap K (AlgebraicClosure K)).injective (hz'.trans (map_zero _).symm))

/-- Distinct characteristic roots of a nondegenerate recurrence have a quotient of
infinite multiplicative order. -/
theorem IsNondegenerate.not_isOfFinOrder_div (h : E.IsNondegenerate)
    {θ θ' : AlgebraicClosure K}
    (hθ : θ ∈ E.charPoly.rootSet (AlgebraicClosure K))
    (hθ' : θ' ∈ E.charPoly.rootSet (AlgebraicClosure K)) (hne : θ ≠ θ') :
    ¬IsOfFinOrder (θ / θ') :=
  h.2 hθ hθ' hne

/-- Nondegeneracy is equivalent to the nonzero constant coefficient condition together
with separation of all distinct characteristic roots by every positive natural power. -/
theorem isNondegenerate_iff_pow (E : LinearRecurrence K) :
    E.IsNondegenerate ↔ E.charPoly.coeff 0 ≠ 0 ∧
      ∀ ⦃θ θ' : AlgebraicClosure K⦄,
        θ ∈ E.charPoly.rootSet (AlgebraicClosure K) →
        θ' ∈ E.charPoly.rootSet (AlgebraicClosure K) →
        θ ≠ θ' → ∀ n : ℕ, 0 < n → θ ^ n ≠ θ' ^ n := by
  constructor
  · intro h
    refine ⟨h.1, fun {_ _} hθ hθ' hne n hn heq ↦ ?_⟩
    apply h.2 hθ hθ' hne
    exact isOfFinOrder_iff_pow_eq_one.mpr
      ⟨n, hn, by rw [div_pow, heq, div_self (pow_ne_zero _ (h.root_ne_zero hθ'))]⟩
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun {θ θ'} hθ hθ' hne hfin ↦ ?_⟩
    obtain ⟨n, hn, heq⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
    rw [div_pow] at heq
    have hden : θ' ^ n ≠ (0 : AlgebraicClosure K) := by
      intro hz
      simp [hz] at heq
    exact h hθ hθ' hne n hn ((div_eq_one_iff_eq hden).mp heq)

/-- When the characteristic polynomial splits over the coefficient field, nondegeneracy
can be checked there. In particular this applies over an algebraically closed field without
transporting the roots of a closed-form solution into a second algebraic closure. -/
theorem isNondegenerate_iff_pow_of_splits (E : LinearRecurrence K)
    (hsplit : E.charPoly.Splits) :
    E.IsNondegenerate ↔ E.charPoly.coeff 0 ≠ 0 ∧
      ∀ ⦃θ θ' : K⦄, θ ∈ E.charPoly.rootSet K → θ' ∈ E.charPoly.rootSet K →
        θ ≠ θ' → ∀ n : ℕ, 0 < n → θ ^ n ≠ θ' ^ n := by
  have himage : (algebraMap K (AlgebraicClosure K)) '' E.charPoly.rootSet K =
      E.charPoly.rootSet (AlgebraicClosure K) := by
    apply Splits.image_rootSet_algebraMap
    simpa using hsplit
  rw [isNondegenerate_iff_pow]
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun {θ θ'} hθ hθ' hne n hn heq ↦ ?_⟩
    have hr {x : K} (hx : x ∈ E.charPoly.rootSet K) :
        algebraMap K (AlgebraicClosure K) x ∈ E.charPoly.rootSet (AlgebraicClosure K) := by
      rw [← himage]
      exact Set.mem_image_of_mem _ hx
    apply h (hr hθ) (hr hθ') ((algebraMap K (AlgebraicClosure K)).injective.ne hne) n hn
    simpa only [map_pow] using congrArg (algebraMap K (AlgebraicClosure K)) heq
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun {θ θ'} hθ hθ' hne n hn heq ↦ ?_⟩
    rw [← himage] at hθ hθ'
    obtain ⟨x, hx, rfl⟩ := hθ
    obtain ⟨y, hy, rfl⟩ := hθ'
    apply h hx hy (fun hxy ↦ hne (congrArg _ hxy)) n hn
    exact (algebraMap K (AlgebraicClosure K)).injective (by simpa only [map_pow] using heq)

/-- Passing to a divisor of the characteristic polynomial preserves nondegeneracy. -/
theorem IsNondegenerate.of_dvd (h : E.IsNondegenerate) (hdvd : E'.charPoly ∣ E.charPoly) :
    E'.IsNondegenerate := by
  obtain ⟨q, hq⟩ := hdvd
  have h0 : E'.charPoly.coeff 0 ≠ 0 := by
    intro hz
    apply h.1
    simp [hq, mul_coeff_zero, hz]
  have hroot {θ : AlgebraicClosure K}
      (hθ : θ ∈ E'.charPoly.rootSet (AlgebraicClosure K)) :
      θ ∈ E.charPoly.rootSet (AlgebraicClosure K) := by
    rw [E.charPoly_monic.mem_rootSet]
    simp [hq, aeval_eq_zero_of_mem_rootSet hθ]
  exact ⟨h0, fun {_ _} hθ hθ' hne ↦ h.2 (hroot hθ) (hroot hθ') hne⟩

/-- A recurrence of order at most one with nonzero constant characteristic coefficient
is nondegenerate. -/
theorem isNondegenerate_of_order_le_one (E : LinearRecurrence K) (horder : E.order ≤ 1)
    (h0 : E.charPoly.coeff 0 ≠ 0) : E.IsNondegenerate := by
  refine ⟨h0, fun {_ _} hθ hθ' hne ↦ False.elim (hne ?_)⟩
  have hcard : (E.charPoly.rootSet (AlgebraicClosure K)).ncard ≤ 1 :=
    (ncard_rootSet_le _ _).trans (by
      rwa [natDegree_eq_of_degree_eq_some E.charPoly_degree_eq_order])
  exact ((Set.ncard_le_one_iff (E.charPoly.rootSet_finite _)).mp hcard) hθ hθ'

/-! ### Examples: repeated roots are permitted, root-of-unity quotients are not -/

/-- The recurrence `u(n+2) = 2u(n+1) - u(n)` is nondegenerate, despite its double
characteristic root `1`. -/
example : (⟨2, ![(-1 : ℚ), 2]⟩ : LinearRecurrence ℚ).IsNondegenerate := by
  let E : LinearRecurrence ℚ := ⟨2, ![-1, 2]⟩
  have hp : E.charPoly = (X - 1) ^ 2 := by
    simp [E, charPoly, Fin.sum_univ_two, ← C_mul_X_pow_eq_monomial, C_ofNat]
    ring
  have h0 : E.charPoly.coeff 0 ≠ 0 := by simp [hp, pow_two, mul_coeff_zero]
  refine ⟨h0, fun {θ θ'} hθ hθ' hne ↦ False.elim (hne ?_)⟩
  have hθ1 : θ = (1 : AlgebraicClosure ℚ) := by
    have hz : aeval θ E.charPoly = 0 := aeval_eq_zero_of_mem_rootSet hθ
    simpa [hp, sub_eq_zero] using hz
  have hθ'1 : θ' = (1 : AlgebraicClosure ℚ) := by
    have hz : aeval θ' E.charPoly = 0 := aeval_eq_zero_of_mem_rootSet hθ'
    simpa [hp, sub_eq_zero] using hz
  exact hθ1.trans hθ'1.symm

/-- The recurrence `u(n+2) = -u(n)` is degenerate even over `ℚ`, where its
characteristic polynomial has no roots. In the algebraic closure its opposite roots
have equal squares. -/
example : ¬(⟨2, ![(-1 : ℚ), 0]⟩ : LinearRecurrence ℚ).IsNondegenerate := by
  intro h
  have hp : (⟨2, ![(-1 : ℚ), 0]⟩ : LinearRecurrence ℚ).charPoly = X ^ 2 + 1 := by
    simp [charPoly, Fin.sum_univ_two, ← C_mul_X_pow_eq_monomial]
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : AlgebraicClosure ℚ)
    (by decide : 0 < (2 : ℕ))
  have hi0 : i ≠ 0 := by
    intro hz
    simp [hz] at hi
  have hne : i ≠ -i := by
    intro heq
    exact hi0 (self_eq_neg.mp heq)
  have hr (x : AlgebraicClosure ℚ) (hx : x ^ 2 = -1) :
      x ∈ (⟨2, ![(-1 : ℚ), 0]⟩ : LinearRecurrence ℚ).charPoly.rootSet (AlgebraicClosure ℚ) := by
    rw [(charPoly_monic _).mem_rootSet, hp]
    simp [hx]
  exact (isNondegenerate_iff_pow _).mp h |>.2 (hr i hi)
    (hr (-i) (by simpa using hi)) hne 2 (by decide) (by simp)

/-- A first-order recurrence with multiplier `2` is nondegenerate. -/
example : (⟨1, ![(2 : ℚ)]⟩ : LinearRecurrence ℚ).IsNondegenerate := by
  apply isNondegenerate_of_order_le_one _ le_rfl
  norm_num [charPoly, Fin.sum_univ_one, ← C_mul_X_pow_eq_monomial]

/-- The order-zero recurrence is nondegenerate; its characteristic polynomial is `1`. -/
example : (⟨0, Fin.elim0⟩ : LinearRecurrence ℚ).IsNondegenerate := by
  apply isNondegenerate_of_order_le_one _ (by decide)
  simp [charPoly]

end LinearRecurrence
