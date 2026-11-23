/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.RingTheory.Polynomial.Resultant.Recognition

/-!
# Resultant recognition over `ℤ_[p]`

Specialization of `Polynomial.resultantRecognition` to the `p`-adic integers `ℤ_[p]` with
integer test polynomials `ψ : ℤ[X]`. Using `PadicInt.appr_spec`, the integers `ℤ` are
`p`-adically dense in `ℤ_[p]`, and `PadicInt.addVal_eq_coe_valuation` identifies
`IsDiscreteValuationRing.addVal ℤ_[p] x` with `(x.valuation : ℕ∞)` for nonzero `x : ℤ_[p]`.

## Main results

* `PadicInt.resultantRecognition`: monic polynomials over `ℤ_[p]` are uniquely determined by the
  `p`-adic valuations of their nonzero resultants with monic integer polynomials.

## References

* J. S. Milne, *The Tate-Šafarevič group of a constant abelian variety*, Invent. Math. 6 (1968),
  §1, p. 65 ([1968a](https://jmilne.org/math/articles/1968a.pdf)).
-/

public section

open Polynomial

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- **Integer tests for a `p`-adic polynomial.** If monic polynomials `P, Q : ℤ_[p][X]` have equal
`p`-adic valuations of their resultants with every monic `ψ : ℤ[X]` for which both resultants are
nonzero, then `P = Q`. -/
theorem resultantRecognition {P Q : ℤ_[p][X]} (hP : P.Monic) (hQ : Q.Monic)
    (h : ∀ ψ : ℤ[X], ψ.Monic →
      P.resultant (ψ.map (Int.castRingHom ℤ_[p])) ≠ 0 →
      Q.resultant (ψ.map (Int.castRingHom ℤ_[p])) ≠ 0 →
      (P.resultant (ψ.map (Int.castRingHom ℤ_[p]))).valuation =
        (Q.resultant (ψ.map (Int.castRingHom ℤ_[p]))).valuation) :
    P = Q := by
  refine Polynomial.resultantRecognition (Int.castRingHom ℤ_[p]) (p : ℤ_[p]) irreducible_p
    (fun N o ↦ ⟨(o.appr N : ℤ), by simpa using PadicInt.appr_spec N o⟩) P Q hP hQ ?_
  intro ψ hψ hPψ hQψ
  rw [addVal_eq_coe_valuation hPψ, addVal_eq_coe_valuation hQψ, h ψ hψ hPψ hQψ]

end PadicInt
