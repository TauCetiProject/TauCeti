/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Algebra.Polynomial.Thom
public import TauCeti.Geometry.RealAlgebraic.SignDetermination.Roots

/-! # Recovering Thom encodings from sign sums

`signCount_iterate_derivative` counts each realized Thom encoding exactly once in a
finite set of distinct roots. `fullInverse_mulVec_thomEncoding` applies the full sign-moment inverse
to Tarski queries of derivative products, recovering zero or one for each encoding.
The polynomial may have multiple roots.

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

/-- Each derivative sign condition is realized by at most one point in a set of roots. -/
theorem signCount_iterate_derivative (p : R[X]) (hrolle : PolynomialRolle R) (hp : p ≠ 0)
    (Z : Finset R) (hZ : ∀ x ∈ Z, p.eval x = 0) (σ : Fin p.natDegree → SignType) :
    signCount Z (fun j : Fin p.natDegree => derivative^[j.val + 1] p) σ =
      if ∃ x ∈ Z, thomEncoding p x = σ then 1 else 0 := by
  classical
  rw [signCount_eq_occCount, Function.occCount_of_injective]
  · simp only [thomEncoding_def, Subtype.exists, exists_prop]
  · intro a b heq
    apply Subtype.ext
    apply thomEncoding_injOn p hrolle hp (hZ a.val a.property) (hZ b.val b.property)
    simpa only [thomEncoding_def] using heq

open scoped Classical in
/-- Tarski queries of derivative products recover exactly the realized root encodings. -/
theorem fullInverse_mulVec_thomEncoding (p : R[X]) (hrolle : PolynomialRolle R) (hp : p ≠ 0)
    (σ : Fin p.natDegree → SignType) :
    (fullInverse (Fin p.natDegree) *ᵥ (fun e =>
      (tarskiQuery p (∏ j : Fin p.natDegree,
        (derivative^[j.val + 1] p) ^ (e j).val) : ℚ))) σ =
      if ∃ x, p.eval x = 0 ∧ thomEncoding p x = σ then 1 else 0 := by
  simp only [fullInverse_mulVec_tarskiQuery]
  rw [signCount_iterate_derivative p hrolle hp p.roots.toFinset
    (fun x hx => isRoot_of_mem_roots (Multiset.mem_toFinset.mp hx))]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Multiset.mem_toFinset,
    mem_roots hp, IsRoot.def]

end Polynomial
