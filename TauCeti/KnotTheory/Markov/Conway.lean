/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.SeifertMatrix.Polynomial.Conway
public import TauCeti.KnotTheory.Markov.Basic

/-!
# The Seifert-matrix Conway polynomial is a Markov invariant

Compute the Conway polynomial of a closed braid by Seifert's algorithm on any representing
word. The word algorithm includes the zero value for a disconnected Seifert surface.
Word independence allows it to descend to braids. Cyclic rotation gives conjugation invariance,
and either sign of stabilization preserves the polynomial. Thus Markov-equivalent braids have
equal Conway polynomials.

This is the Seifert-matrix algorithm on the braid presentation. No geometric correspondence
between braid closures and smooth links is assumed.

The word-invariant descent uses `TauCeti.MarkovBraid.liftWord` from
`TauCeti.KnotTheory.Markov.Basic`.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Chapters 6 and 8.
* J. Birman, *Braids, Links, and Mapping Class Groups*, Chapters 1 and 3.
-/

public noncomputable section

open scoped Polynomial

namespace TauCeti

open BraidGroup BraidWord

namespace MarkovBraid

/-- The Seifert-matrix Conway polynomial of a closed braid, normalized by `∇(unknot) = 1`
and with variable `z = s⁻¹ - s`. Any word representing the braid gives the same value. -/
def conwayPolynomial (β : MarkovBraid) : ℤ[X] :=
  liftWord BraidWord.conwayPolynomial β

/-- Any representing word computes the braid's Conway polynomial. -/
theorem conwayPolynomial_eq_of_toBraid_eq {β : MarkovBraid}
    {w : BraidWord (β.predStrands + 1)} (hw : w.toBraid = β.braid) :
    β.conwayPolynomial = w.conwayPolynomial :=
  liftWord_eq_of_toBraid_eq _ BraidWord.conwayPolynomial_eq_of_toBraid_eq hw

/-- The braid represented by a word has that word's Conway polynomial. -/
@[simp]
theorem conwayPolynomial_mk {n : ℕ} (w : BraidWord (n + 1)) :
    conwayPolynomial ⟨n, w.toBraid⟩ = w.conwayPolynomial :=
  conwayPolynomial_eq_of_toBraid_eq rfl

end MarkovBraid

/-- A single Markov move preserves the Seifert-matrix Conway polynomial. -/
theorem IsMarkovMove.conwayPolynomial_eq {β γ : MarkovBraid} (h : IsMarkovMove β γ) :
    β.conwayPolynomial = γ.conwayPolynomial :=
  h.liftWord_eq BraidWord.conwayPolynomial BraidWord.conwayPolynomial_eq_of_toBraid_eq
    conwayPolynomial_rotate conwayPolynomial_stabilize

/-- Markov-equivalent braids have equal Seifert-matrix Conway polynomials. -/
theorem MarkovEquiv.conwayPolynomial_eq {β γ : MarkovBraid} (h : MarkovEquiv β γ) :
    β.conwayPolynomial = γ.conwayPolynomial :=
  h.liftWord_eq BraidWord.conwayPolynomial BraidWord.conwayPolynomial_eq_of_toBraid_eq
    conwayPolynomial_rotate conwayPolynomial_stabilize

namespace MarkovBraid

/-- The identity braid closes to an unknot on one strand and a split unlink on more strands. -/
@[simp]
theorem conwayPolynomial_one (n : ℕ) :
    conwayPolynomial ⟨n, 1⟩ = if n = 0 then 1 else 0 := by
  rw [conwayPolynomial_eq_of_toBraid_eq (w := []) (toBraid_nil (n := n + 1)), conwayPolynomial_nil]

/-- The right-handed trefoil has Conway polynomial `1 + X²`. -/
@[simp]
theorem conwayPolynomial_sigma_pow_three :
    conwayPolynomial ⟨1, sigma 0 ^ 3⟩ = 1 + Polynomial.X ^ 2 := by
  have hw : toBraid (n := 2) [(0, 1), (0, 1), (0, 1)] = sigma 0 ^ 3 := by
    simp [toBraid_cons (n := 2), toBraid_nil (n := 2), pow_succ, mul_assoc]
  rw [conwayPolynomial_eq_of_toBraid_eq hw, BraidWord.conwayPolynomial_trefoil]

end MarkovBraid

end TauCeti
