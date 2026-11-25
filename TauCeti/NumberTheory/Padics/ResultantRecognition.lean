/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.RingHoms
public import TauCeti.RingTheory.Polynomial.Resultant.Recognition

/-!
# Integer resultant tests for `p`-adic polynomials

A monic polynomial over `ℤ_[p]` is determined by the `p`-adic valuations of its resultants with
monic integer polynomials: if monic `P, Q ∈ ℤ_[p][X]` have `v_p Res(P, ψ) = v_p Res(Q, ψ)` for
every monic `ψ ∈ ℤ[X]` with both resultants nonzero, then `P = Q`. This is the form in which
Milne's criterion identifies the characteristic polynomial of an endomorphism on a Dieudonné
module with its integral characteristic polynomial.

It is the case `D = ℤ`, `O = ℤ_[p]`, `π = p` of
`Polynomial.Monic.eq_of_forall_addVal_resultant_eq`; the density of `ℤ` modulo every power of `p`
is `PadicInt.appr_spec`. Mathlib's `PadicInt.valuation` sends `0` to `0`, so the tests with a
vanishing resultant are excluded.

## Main results

* `Polynomial.Monic.eq_of_forall_valuation_resultant_eq`: monic polynomials over `ℤ_[p]` with equal
  `p`-adic valuations of all common nonzero resultants against monic integer polynomials are
  equal.

## References

* J. S. Milne, *Extensions of abelian varieties defined over a finite field*, Invent. Math. 5
  (1968), 63–84, §1.
-/

public section

namespace Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- **Integer tests for a `p`-adic polynomial.** Monic `P, Q ∈ ℤ_[p][X]` with
`v_p Res(P, ψ) = v_p Res(Q, ψ)` for every monic `ψ ∈ ℤ[X]` for which both resultants are nonzero
are equal. -/
theorem Monic.eq_of_forall_valuation_resultant_eq {P Q : ℤ_[p][X]} (hP : P.Monic) (hQ : Q.Monic)
    (h : ∀ ψ : ℤ[X], ψ.Monic → P.resultant (ψ.map (Int.castRingHom ℤ_[p])) ≠ 0 →
      Q.resultant (ψ.map (Int.castRingHom ℤ_[p])) ≠ 0 →
        (P.resultant (ψ.map (Int.castRingHom ℤ_[p]))).valuation =
          (Q.resultant (ψ.map (Int.castRingHom ℤ_[p]))).valuation) :
    P = Q :=
  hP.eq_of_forall_addVal_resultant_eq hQ (Int.castRingHom ℤ_[p]) PadicInt.irreducible_p
    (fun N o ↦ ⟨o.appr N, by simpa using PadicInt.appr_spec N o⟩) fun ψ hψ hP0 hQ0 ↦ by
      rw [PadicInt.addVal_eq_valuation hP0, PadicInt.addVal_eq_valuation hQ0, h ψ hψ hP0 hQ0]

end Polynomial
