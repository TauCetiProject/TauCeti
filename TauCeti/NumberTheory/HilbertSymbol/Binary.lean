/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Quaternion.Binary
public import TauCeti.NumberTheory.HilbertSymbol.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Binary
import TauCeti.NumberTheory.HilbertSymbol.NormSubgroup

/-!
# Hilbert symbols of binary forms

Isometric regular binary diagonal forms have the same norm-equation Hilbert symbol. This is the
binary-step input for descending the pairwise product of Hilbert symbols along a diagonal chain,
and hence for defining the local Hasse invariant on isometry classes. That assertion holds over
any field in which two is invertible.

Over an arbitrary field, the norm-equation symbol also describes the scalar multiples of the
binary form `⟨1, -b⟩`, the norm form of the quadratic algebra `K[√b] = QuadraticAlgebra K b 0`
(the field `K(√b)` only when `b` is not a square): the multiple `⟨a, -ab⟩` is isometric to it
exactly when `(b, a) = 1`, that is, when `a` is a value of `⟨1, -b⟩`. Since the two planes always
have the same dimension and discriminant, this makes the substitution of `⟨a, -ab⟩` for `⟨1, -b⟩`
a controlled change of isometry class: read over the completions of a global field, it changes
the local class exactly at the places where the symbol `(b, a)` is `-1`.

## Main results

* `TauCeti.hilbertSymbol_eq_of_equivalent_binary`: isometric binary diagonal forms have the same
  Hilbert symbol.
* `TauCeti.equivalent_binary_one_neg_iff_hilbertSymbol_eq_one`: `⟨1, -b⟩ ≅ ⟨a, -ab⟩` exactly
  when `(b, a) = 1`.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter V, Proposition 3.18.
* J.-P. Serre, *A Course in Arithmetic*, Chapter IV, §2.1.
* O. T. O'Meara, *Introduction to Quadratic Forms*, 72:1, for the substitution of `⟨a, -ab⟩` for
  `⟨1, -b⟩`.
-/

public section

open QuadraticMap

namespace TauCeti

variable {K : Type*} [Field K]

/-- Isometric regular binary diagonal forms have the same norm-equation Hilbert symbol. -/
theorem hilbertSymbol_eq_of_equivalent_binary [Invertible (2 : K)] {a b c d : Kˣ}
    (h : (weightedSumSquares K ![(a : K), b]).Equivalent
      (weightedSumSquares K ![(c : K), d])) :
    hilbertSymbol a b = hilbertSymbol c d :=
  hilbertSymbol_eq_of_nonempty_algEquiv
    (QuaternionAlgebra.nonempty_algEquiv_of_equivalent_binary (a : K) b c d h)

/-- **Scaling the norm form.** The binary forms `⟨1, -b⟩` and `⟨a, -ab⟩ = a⟨1, -b⟩` are isometric
exactly when the Hilbert symbol `(b, a)` is `1`, that is, when `a` is a value of `⟨1, -b⟩`. The
two forms always have the same discriminant `-b` modulo squares. -/
theorem equivalent_binary_one_neg_iff_hilbertSymbol_eq_one (a b : Kˣ) :
    (weightedSumSquares K ![1, -(b : K)]).Equivalent
        (weightedSumSquares K ![(a : K), -(a * b : K)]) ↔
      hilbertSymbol b a = 1 := by
  rw [← mem_unitValueSet_binary_one_neg_iff_hilbertSymbol_eq_one]
  refine ⟨fun h => h.unitValueSet_eq ▸ mem_unitValueSet_binary_left a _, fun h => ?_⟩
  -- Both forms represent `a`, and their discriminants `-b` and `-a²b` agree modulo squares.
  have hdisc : IsSquare ((1 : Kˣ) * -b * (a * -(a * b))) :=
    ⟨a * b, by simp only [one_mul, mul_neg, neg_mul, neg_neg]; ac_rfl⟩
  simpa using equivalent_binary_of_isSquare_of_mem_unitValueSet hdisc (by simpa using h)
    (mem_unitValueSet_binary_left a _)

end TauCeti
