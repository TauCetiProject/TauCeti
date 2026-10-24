/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Sturm.Sequence
public import TauCeti.Algebra.Polynomial.Sturm.Infinity

/-!
# Transport of Sturm variations along ordered embeddings

Strictly monotone ring homomorphisms preserve the variation counts of polynomial lists at
finite points, on either side of a point, and at both infinities. Together with
`Polynomial.sturmSeq_map`, these laws transport the endpoint computations in Sturm–Tarski
formulas from an ordered field to an ordered extension, including an ordered real closure.
No real closedness hypothesis is needed for transport. Entries may be zero, and finite
endpoints may be roots.

The proofs reuse the coefficient-map laws for evaluation, one-sided signs, leading
coefficients, and degree, and Mathlib's sign-preserving list transport.

## References

S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*,
second edition, §2.2.2 and Chapter 10.
-/

public section

namespace TauCeti.Sturm

open Polynomial

section Semiring

variable {R S : Type*} [Semiring R] [LinearOrder R] [Semiring S] [LinearOrder S]

/-- Ordered coefficient embeddings preserve variations at the corresponding evaluation point. -/
@[simp]
theorem signVariationsAt_map (cs : List R[X]) (f : R →+* S) (hf : StrictMono f) (x : R) :
    signVariationsAt (cs.map (Polynomial.map f)) (f x) = signVariationsAt cs x := by
  rw [signVariationsAt_def, signVariationsAt_def]
  apply List.signVariations_congr
  simp only [List.map_map, Function.comp_def]
  exact List.map_congr_left fun p _ ↦ p.sign_eval_map f hf x

/-- Ordered coefficient embeddings preserve variations at positive infinity. -/
@[simp]
theorem signVariationsAtTop_map (cs : List R[X]) (f : R →+* S) (hf : StrictMono f) :
    signVariationsAtTop (cs.map (Polynomial.map f)) = signVariationsAtTop cs := by
  rw [signVariationsAtTop_def, signVariationsAtTop_def]
  apply List.signVariations_congr
  simp only [List.map_map, Function.comp_def]
  exact List.map_congr_left fun p _ ↦ by
    rw [leadingCoeff_map_of_injective hf.injective]
    exact hf.sign_comp _

end Semiring

section CommRing

variable {R S : Type*} [CommRing R] [LinearOrder R] [CommRing S] [LinearOrder S]

/-- Ordered coefficient embeddings preserve variations immediately to the right of a point. -/
@[simp]
theorem signVariationsRight_map (cs : List R[X]) (f : R →+* S) (hf : StrictMono f) (x : R) :
    signVariationsRight (cs.map (Polynomial.map f)) (f x) = signVariationsRight cs x := by
  simp only [signVariationsRight_def, List.map_map, Function.comp_def, derivSignRight_map _ f hf]

/-- Ordered coefficient embeddings preserve variations immediately to the left of a point. -/
@[simp]
theorem signVariationsLeft_map (cs : List R[X]) (f : R →+* S) (hf : StrictMono f) (x : R) :
    signVariationsLeft (cs.map (Polynomial.map f)) (f x) = signVariationsLeft cs x := by
  simp only [signVariationsLeft_def, List.map_map, Function.comp_def, derivSignLeft_map _ f hf]

end CommRing

section Ring

variable {R S : Type*} [Ring R] [LinearOrder R] [Ring S] [LinearOrder S]

/-- Ordered coefficient embeddings preserve variations at negative infinity. -/
@[simp]
theorem signVariationsAtBot_map (cs : List R[X]) (f : R →+* S) (hf : StrictMono f) :
    signVariationsAtBot (cs.map (Polynomial.map f)) = signVariationsAtBot cs := by
  rw [signVariationsAtBot_def, signVariationsAtBot_def]
  apply List.signVariations_congr
  simp only [List.map_map, Function.comp_def]
  exact List.map_congr_left fun p _ ↦ by
    rw [leadingCoeff_map_of_injective hf.injective, natDegree_map_eq_of_injective hf.injective]
    simpa only [map_mul, map_pow, map_neg, map_one] using
      hf.sign_comp (p.leadingCoeff * (-1) ^ p.natDegree)

end Ring

end TauCeti.Sturm
