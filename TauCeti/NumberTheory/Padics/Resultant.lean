/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.Polynomial.Resultant.Recognition

/-!
# Resultant recognition over `ℤ_[p]`

Specialization of `Polynomial.resultantRecognition` to the `p`-adic integers `ℤ_[p]` with
integer test polynomials `ψ : ℤ[X]`. Using `PadicInt.appr_spec`, the integers `ℤ` are
`p`-adically dense in `ℤ_[p]`, and for nonzero `x : ℤ_[p]` the discrete-valuation-ring additive
valuation `IsDiscreteValuationRing.addVal ℤ_[p] x` agrees with `x.valuation`.

## Main results

* `PadicInt.addVal_eq_coe_valuation`: for nonzero `x : ℤ_[p]`,
  `IsDiscreteValuationRing.addVal ℤ_[p] x = (x.valuation : ℕ∞)`.
* `PadicInt.resultantRecognition`: monic polynomials over `ℤ_[p]` are uniquely determined by the
  `p`-adic valuations of their nonzero resultants with monic integer polynomials.
-/

public section

open Polynomial

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- For nonzero `x : ℤ_[p]`, the DVR additive valuation agrees with `PadicInt.valuation`. -/
theorem addVal_eq_coe_valuation {x : ℤ_[p]} (hx : x ≠ 0) :
    IsDiscreteValuationRing.addVal ℤ_[p] x = (x.valuation : ℕ∞) :=
  IsDiscreteValuationRing.addVal_def x (unitCoeff hx) irreducible_p x.valuation
    (unitCoeff_spec hx)

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
