/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import TauCeti.Algebra.Cluster.ExchangePolynomial.Basic

import Mathlib.Algebra.BigOperators.Intervals

/-!
# Endpoint-one exchange polynomials and coefficient sums

This file supplements `TauCeti.ExchangePolynomial` with the API used by coefficient systems and
exchange data: free unit scaling (`scale_right_injective`), polynomials with both endpoint
coefficients equal to `1` (`IsEndpointOne`), and sums of coefficients `∑_{l=0}^r g(h_l)` over the
specified degree `r`. Such a sum is invariant under reversal (`sum_reverse_coeff`), and over a
nontrivial commutative semiring with trivial additive units the plain coefficient sum `H(1)` is
nonzero (`sum_coeff_ne_zero`).

## References

* L. Chekhov and M. Shapiro, *Teichmüller spaces of Riemann surfaces with orbifold points of
  arbitrary order and cluster variables*, Int. Math. Res. Not. 2014 (2014), §2.
* T. Nakanishi, *Structure of seeds in generalized cluster algebras*, Pacific J. Math. 277 (2015),
  §2.
-/

public section

namespace TauCeti

namespace ExchangePolynomial

variable {𝕂 : Type*} [CommMonoidWithZero 𝕂]

/-- Unit scaling acts freely on exchange polynomials because the constant coefficient is a unit. -/
theorem scale_right_injective (H : ExchangePolynomial 𝕂) : Function.Injective H.scale :=
  fun _ _ h ↦ H.scale_right_inj.mp h

/-! ### Endpoint-one polynomials -/

/-- An exchange polynomial has endpoint coefficients equal to `1` when `h_0 = 1` and `h_r = 1`. -/
def IsEndpointOne (H : ExchangePolynomial 𝕂) : Prop :=
  H.coeff 0 = 1 ∧ H.coeff H.degree = 1

theorem isEndpointOne_iff {H : ExchangePolynomial 𝕂} :
    H.IsEndpointOne ↔ H.coeff 0 = 1 ∧ H.coeff H.degree = 1 := Iff.rfl

protected theorem IsEndpointOne.coeff_zero {H : ExchangePolynomial 𝕂} (h : H.IsEndpointOne) :
    H.coeff 0 = 1 := h.1

protected theorem IsEndpointOne.coeff_degree {H : ExchangePolynomial 𝕂} (h : H.IsEndpointOne) :
    H.coeff H.degree = 1 := h.2

protected theorem IsEndpointOne.reverse {H : ExchangePolynomial 𝕂} (h : H.IsEndpointOne) :
    H.reverse.IsEndpointOne := ⟨by simp [h.2], by simp [h.1]⟩

@[simp]
theorem isEndpointOne_reverse_iff {H : ExchangePolynomial 𝕂} :
    H.reverse.IsEndpointOne ↔ H.IsEndpointOne :=
  ⟨fun h ↦ by simpa using h.reverse, fun h ↦ h.reverse⟩

protected theorem IsEndpointOne.dilationFactor {H : ExchangePolynomial 𝕂} (h : H.IsEndpointOne)
    (b : ℤ) : H.dilationFactor b = 1 :=
  H.dilationFactor_eq_one h.1 h.2 b

@[simp] theorem isEndpointOne_binary : (binary : ExchangePolynomial 𝕂).IsEndpointOne :=
  ⟨by simp, by simp⟩

/-! ### Coefficient sums -/

/-- Reversal permutes the coefficients `h_0, …, h_r`, so it preserves every coefficient sum. -/
theorem sum_reverse_coeff {M : Type*} [AddCommMonoid M] (H : ExchangePolynomial 𝕂) (g : 𝕂 → M) :
    ∑ l ∈ Finset.range (H.degree + 1), g (H.reverse.coeff l) =
      ∑ l ∈ Finset.range (H.degree + 1), g (H.coeff l) := by
  rw [← Finset.sum_range_reflect (fun l ↦ g (H.coeff l))]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  have hl : l ≤ H.degree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  simp [hl]

/-- Over a nontrivial commutative semiring with trivial additive units, the sum of all
coefficients of an exchange polynomial is nonzero because its constant coefficient is a unit. -/
theorem sum_coeff_ne_zero {S : Type*} [CommSemiring S] [Nontrivial S]
    [Subsingleton (AddUnits S)] (H : ExchangePolynomial S) :
    ∑ l ∈ Finset.range (H.degree + 1), H.coeff l ≠ 0 := fun hsum ↦
  H.coeff_zero_ne_zero ((Finset.sum_eq_zero_iff.mp hsum) 0 (by simp))

end ExchangePolynomial

end TauCeti
