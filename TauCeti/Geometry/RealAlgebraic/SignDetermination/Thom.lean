/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Algebra.Polynomial.Thom.Basic
public import TauCeti.Geometry.RealAlgebraic.SignDetermination.Roots

/-! # Recovering Thom encodings from sign sums

`signCount_iterate_derivative` counts each realized Thom encoding exactly once in a
finite set of distinct roots. `fullInverse_mulVec_thomEncoding` applies the full sign-moment inverse
to Tarski queries of derivative products, recovering zero or one for each encoding.
The polynomial may have multiple roots.

The `_of_natDegree_le` forms record the signs of the derivatives of orders `1, …, N` for any
`N` at least the degree. Derivatives above the degree vanish, so the extra coordinates are zero.
A formal degree bound of this kind is what a polynomial family provides uniformly, while the
actual degree may drop after specialization.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Chapter 10, for recovering sign conditions from Tarski queries.
-/

public section

open TauCeti (PolynomialRolle)

open Polynomial SignType Finset TauCeti.SignDetermination
open scoped Matrix

namespace Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Each sign condition on the derivatives of orders `1, …, N`, for `N` at least the degree, is
realized by at most one point in a set of roots. -/
theorem signCount_iterate_derivative_of_natDegree_le (p : R[X]) (hrolle : PolynomialRolle R)
    (hp : p ≠ 0) (Z : Finset R) (hZ : ∀ x ∈ Z, p.eval x = 0) {N : ℕ} (hN : p.natDegree ≤ N)
    (σ : Fin N → SignType) :
    signCount Z (fun j : Fin N => derivative^[j.val + 1] p) σ =
      if ∃ x ∈ Z, ∀ j : Fin N, sign ((derivative^[j.val + 1] p).eval x) = σ j then 1 else 0 := by
  classical
  rw [signCount_eq_occCount, Function.occCount_of_injective]
  · simp only [funext_iff, Subtype.exists, exists_prop]
  · intro a b heq
    apply Subtype.ext
    refine eq_of_derivativeSign_eq p hrolle hp (hZ a.val a.property) (hZ b.val b.property)
      fun k hk => ?_
    rcases le_or_gt k N with hkN | hkN
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk.ne'
      simpa only [derivativeSign_def] using congrFun heq ⟨j, by omega⟩
    · exact derivativeSign_const p _ _ (by omega)

/-- Each derivative sign condition is realized by at most one point in a set of roots. -/
theorem signCount_iterate_derivative (p : R[X]) (hrolle : PolynomialRolle R) (hp : p ≠ 0)
    (Z : Finset R) (hZ : ∀ x ∈ Z, p.eval x = 0) (σ : Fin p.natDegree → SignType) :
    signCount Z (fun j : Fin p.natDegree => derivative^[j.val + 1] p) σ =
      if ∃ x ∈ Z, thomEncoding p x = σ then 1 else 0 := by
  simp only [signCount_iterate_derivative_of_natDegree_le p hrolle hp Z hZ le_rfl,
    thomEncoding_def, funext_iff]

open scoped Classical in
/-- Tarski queries of products of the derivatives of orders `1, …, N`, for `N` at least the
degree, recover exactly the realized sign conditions on those derivatives at the roots. -/
theorem fullInverse_mulVec_iterate_derivative_of_natDegree_le (p : R[X])
    (hrolle : PolynomialRolle R) (hp : p ≠ 0) {N : ℕ} (hN : p.natDegree ≤ N)
    (σ : Fin N → SignType) :
    (fullInverse (Fin N) *ᵥ (fun e =>
      (tarskiQuery p (∏ j : Fin N, (derivative^[j.val + 1] p) ^ (e j).val) : ℚ))) σ =
      if ∃ x, p.eval x = 0 ∧ ∀ j : Fin N, sign ((derivative^[j.val + 1] p).eval x) = σ j
      then 1 else 0 := by
  simp only [fullInverse_mulVec_tarskiQuery]
  rw [signCount_iterate_derivative_of_natDegree_le p hrolle hp p.roots.toFinset
    (fun x hx => isRoot_of_mem_roots (Multiset.mem_toFinset.mp hx)) hN]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Multiset.mem_toFinset,
    mem_roots hp, IsRoot.def]

open scoped Classical in
/-- Tarski queries of derivative products recover exactly the realized root encodings. -/
theorem fullInverse_mulVec_thomEncoding (p : R[X]) (hrolle : PolynomialRolle R) (hp : p ≠ 0)
    (σ : Fin p.natDegree → SignType) :
    (fullInverse (Fin p.natDegree) *ᵥ (fun e =>
      (tarskiQuery p (∏ j : Fin p.natDegree,
        (derivative^[j.val + 1] p) ^ (e j).val) : ℚ))) σ =
      if ∃ x, p.eval x = 0 ∧ thomEncoding p x = σ then 1 else 0 := by
  rw [fullInverse_mulVec_iterate_derivative_of_natDegree_le p hrolle hp le_rfl]
  simp only [thomEncoding_def, funext_iff]

end Polynomial
