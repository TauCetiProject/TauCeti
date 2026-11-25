/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.IsAlgClosed.Frobenius
public import TauCeti.RingTheory.PowerSeries.Basic

/-!
# Difference equations for coefficient Frobenius on power series

A twisted polynomial in positive coefficient Frobenius acts surjectively on power series over
an algebraically closed field if at least one of its operator coefficients has nonzero constant
term. Normalizing Laurent-series operator coefficients by a common power of `X` produces
a power-series equation with this nonzero reduction. Each successive coefficient is obtained
by solving a nonconstant residue polynomial.

## References

* K. S. Kedlaya, *A p-adic local monodromy theorem*, Ann. of Math. 160 (2004),
  Proposition 3.17, for the reduction to a polynomial over the residue field.
-/

public section

open scoped PowerSeries

namespace TauCeti.PowerSeries

variable {p : ℕ} {k : Type*} [Field k] [Fact p.Prime] [CharP k p] [IsAlgClosed k]

/-- A twisted polynomial in positive coefficient Frobenius with nonzero reduction modulo
`X` takes every value on power series over an algebraically closed field. -/
theorem exists_sum_mul_map_iterateFrobenius_eq (s : Finset ℕ) (a : ℕ → k⟦X⟧)
    {f : ℕ} (hf : 0 < f) (ha : ∃ i ∈ s, PowerSeries.constantCoeff (a i) ≠ 0) (b : k⟦X⟧) :
    ∃ x : k⟦X⟧, ∑ i ∈ s, a i * PowerSeries.map (iterateFrobenius k p (f * i)) x = b := by
  exact surjective_sum_mul_map_of_surjective_constantCoeff s a _
    (surjective_sum_mul_iterateFrobenius s (fun i => PowerSeries.constantCoeff (a i)) hf ha) b

end TauCeti.PowerSeries
