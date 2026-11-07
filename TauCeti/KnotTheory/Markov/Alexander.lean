/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Burau.Normalization
public import TauCeti.KnotTheory.Markov.Conway
import TauCeti.KnotTheory.Burau.Skein
import TauCeti.KnotTheory.Markov.Skein

/-!
# The Seifert and Burau routes to the Alexander polynomial of a closed braid agree

There are two classical ways to compute the Conway-normalized Alexander polynomial of the closure of
a braid, written in the square root `s` of the Alexander variable `t`.

* **From a Seifert surface.** Seifert's algorithm on the closure of a word representing the braid
  gives the canonical Seifert surface, and its Seifert matrix gives the Conway polynomial in
  `z = s⁻¹ - s`, or `0` when the surface is disconnected and the closure is split
  (`TauCeti.MarkovBraid.conwayPolynomial`).
* **From the Burau representation.** The corner minor of `burau β - 1`, evaluated at `t = s²` and
  multiplied by the exact Markov normalization `(-1)^p s^(-e-p)`, for `p + 1` strands and exponent
  sum `e` (`TauCeti.MarkovBraid.normalizedBurauAlexander`).

Both routes are Markov invariants, satisfy the Conway skein relation `Δ₊ - Δ₋ = (s⁻¹ - s) Δ₀`,
vanish on braids with an uncrossed strand, whose closures are split, and take the value `1` on the
trivial braid on one strand, whose closure is the unknot. A Markov invariant with these properties
is determined (`TauCeti.MarkovBraid.eq_of_skein`), so the two routes agree for every braid and
every unit `s` of every commutative ring
(`TauCeti.MarkovBraid.normalizedBurauAlexander_eq_eval₂_conwayPolynomial`).

## Main results

* `TauCeti.MarkovBraid.normalizedBurauAlexander_eq_eval₂_conwayPolynomial`: **the Seifert-matrix
  and Burau routes to the Alexander polynomial of a closed braid agree.**

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 6
  (Seifert matrices) and Chapter 8, Theorem 8.6 (the Conway-normalized skein characterization).
* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82 (1974),
  Chapter 3 (the Burau representation and the Alexander polynomial of a closed braid).
-/

public section

namespace TauCeti

namespace MarkovBraid

/-- **The Seifert-matrix and Burau routes to the Alexander polynomial of a closed braid agree.**
For every braid `β` and every unit `s` of a commutative ring, the normalized Burau invariant at `s`
is the Seifert-matrix Conway polynomial evaluated at `z = s⁻¹ - s`. -/
theorem normalizedBurauAlexander_eq_eval₂_conwayPolynomial {R : Type*} [CommRing R]
    (β : MarkovBraid) (s : Rˣ) :
    β.normalizedBurauAlexander s =
      Polynomial.eval₂ (Int.castRingHom R) (((s⁻¹ : Rˣ) : R) - s) β.conwayPolynomial := by
  refine congrFun (eq_of_skein (R := R) (M := R) 1 (((s⁻¹ : Rˣ) : R) - s) 0
    (F := fun β ↦ β.normalizedBurauAlexander s)
    (G := fun β ↦ Polynomial.eval₂ (Int.castRingHom R) (((s⁻¹ : Rˣ) : R) - s) β.conwayPolynomial)
    (fun _ _ h ↦ h.normalizedBurauAlexander_eq s)
    (fun _ _ h ↦ by rw [h.conwayPolynomial_eq]) (fun n c i ↦ ?_) (fun n c i ↦ ?_)
    (fun n b ↦ by simp) (fun n b ↦ by simp) (by simp)) β
  · simpa using normalizedBurauAlexander_skein 1 c i s
  · have h := congrArg (Polynomial.eval₂ (Int.castRingHom R) (((s⁻¹ : Rˣ) : R) - s))
      (conwayPolynomial_skein 1 c i)
    simp only [one_mul, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X] at h
    simpa using h

end MarkovBraid

end TauCeti
