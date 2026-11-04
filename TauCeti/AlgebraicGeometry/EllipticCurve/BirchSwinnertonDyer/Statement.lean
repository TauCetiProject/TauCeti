/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.BirchSwinnertonDyer.Quotient
public import TauCeti.AlgebraicGeometry.EllipticCurve.LFunction

/-!
# The statement of the Birch–Swinnerton-Dyer conjecture over `ℚ`

For an elliptic curve `E` over `ℚ` with `L`-series `L(E, s) = ∑ aₙ n⁻ˢ` (Mathlib's
`WeierstrassCurve.LSeries`, the Dirichlet series of the Euler product `WeierstrassCurve.LFunction`
of the local factors at all primes), the Birch–Swinnerton-Dyer conjecture asserts that

* the order of vanishing `r` of `L(E, s)` at `s = 1` is the rank of the Mordell–Weil group `E(ℚ)`;
* when `Sha(E/ℚ)` is finite, the leading Taylor coefficient `L^{(r)}(E, 1) / r!` is the
  Birch–Swinnerton-Dyer quotient `Ω(E) · Reg(E/ℚ) · #Sha(E/ℚ) · ∏_p c_p / #E(ℚ)_tors²`
  (`WeierstrassCurve.bsdQuotient`).

The series converges absolutely only on a right half-plane not containing `s = 1`, so the values at
`s = 1` are those of an analytic continuation. This file states the conjecture against every
continuation of the actual Dirichlet series to a connected open set containing `s = 1`
(`LSeries.IsContinuationOn`): an analytic function there, agreeing with the series on the part of
the half-plane of absolute convergence it meets. Each such continuation has finite order of
vanishing at `s = 1` (`WeierstrassCurve.analyticOrderAt_ne_top_of_isContinuationOn`). By the
modularity theorem `L(E, s)` extends to an entire function, with which every continuation agrees
on its domain (`LSeries.IsContinuationOn.eqOn_of_subset`), so the statement is the classical
conjecture. The conjecture itself is not proved here.

## Main definitions

* `WeierstrassCurve.BirchSwinnertonDyer E`: the Birch–Swinnerton-Dyer conjecture for `E`.
* `TauCeti.BirchSwinnertonDyerConjecture`: the conjecture for every elliptic curve over `ℚ`.

## Main results

* `WeierstrassCurve.BirchSwinnertonDyer.iteratedDeriv_finrank_div_factorial`: the leading
  coefficient identity, with the order of vanishing replaced by the rank.
* `WeierstrassCurve.BirchSwinnertonDyer.apply_one_ne_zero_iff`: the `L`-function does not vanish
  at `s = 1` exactly when `E(ℚ)` has rank zero.
* `WeierstrassCurve.BirchSwinnertonDyer.apply_one_eq_bsdQuotient`: in rank zero, `L(E, 1)` is the
  Birch–Swinnerton-Dyer quotient.

## References

* B. J. Birch and H. P. F. Swinnerton-Dyer, *Notes on elliptic curves. II*, J. Reine Angew. Math.
  218 (1965), 79–108.
* J. Tate, *On the conjectures of Birch and Swinnerton-Dyer and a geometric analog*, Séminaire
  Bourbaki 306 (1966).
* A. Wiles, *The Birch and Swinnerton-Dyer conjecture*, in *The Millennium Prize Problems*, Clay
  Mathematics Institute, 2006.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Appendix C, §16.
-/

public section

namespace WeierstrassCurve

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- **The Birch–Swinnerton-Dyer conjecture** for an elliptic curve `E` over `ℚ`. For every analytic
continuation `F` of the `L`-series `∑ aₙ n⁻ˢ` of `E` to a connected open set `U` containing
`s = 1` (`LSeries.IsContinuationOn`):

* the order of vanishing of `F` at `s = 1` is the rank of `E(ℚ)`;
* if `Sha(E/ℚ)` is finite, the leading Taylor coefficient `F^{(r)}(1) / r!` of `F` at `s = 1`,
  `r` being its order of vanishing there, is the Birch–Swinnerton-Dyer quotient
  `WeierstrassCurve.bsdQuotient E`. -/
structure BirchSwinnertonDyer : Prop where
  /-- The order of vanishing of the `L`-function at `s = 1` is the rank of `E(ℚ)`. -/
  analyticOrderAt_eq_finrank : ∀ ⦃F : ℂ → ℂ⦄ ⦃U : Set ℂ⦄,
    LSeries.IsContinuationOn ((↑) ∘ E.LFunction) F U → 1 ∈ U →
      analyticOrderAt F 1 = Module.finrank ℤ E.toAffine.Point
  /-- If `Sha(E/ℚ)` is finite, the leading Taylor coefficient of the `L`-function at `s = 1` is
  the Birch–Swinnerton-Dyer quotient. -/
  leadingCoeff_eq_bsdQuotient : ∀ [Finite E.sha] ⦃F : ℂ → ℂ⦄ ⦃U : Set ℂ⦄,
    LSeries.IsContinuationOn ((↑) ∘ E.LFunction) F U → 1 ∈ U →
      iteratedDeriv (analyticOrderNatAt F 1) F 1 / (analyticOrderNatAt F 1).factorial =
        E.bsdQuotient

namespace BirchSwinnertonDyer

variable {E} {F : ℂ → ℂ} {U : Set ℂ}

/-- Under the Birch–Swinnerton-Dyer conjecture, the order of vanishing at `s = 1`, as a natural
number, is the rank of `E(ℚ)`. -/
theorem analyticOrderNatAt_eq_finrank (h : E.BirchSwinnertonDyer)
    (hF : LSeries.IsContinuationOn ((↑) ∘ E.LFunction) F U) (h₁ : 1 ∈ U) :
    analyticOrderNatAt F 1 = Module.finrank ℤ E.toAffine.Point := by
  rw [analyticOrderNatAt, h.analyticOrderAt_eq_finrank hF h₁, ENat.toNat_natCast]

/-- **The leading coefficient identity at the rank**: under the Birch–Swinnerton-Dyer conjecture
and for `Sha(E/ℚ)` finite, `F^{(r)}(1) / r! = Ω(E) · Reg(E/ℚ) · #Sha(E/ℚ) · ∏_p c_p / #E(ℚ)_tors²`
with `r` the rank of `E(ℚ)`. -/
theorem iteratedDeriv_finrank_div_factorial (h : E.BirchSwinnertonDyer) [Finite E.sha]
    (hF : LSeries.IsContinuationOn ((↑) ∘ E.LFunction) F U) (h₁ : 1 ∈ U) :
    iteratedDeriv (Module.finrank ℤ E.toAffine.Point) F 1 /
        (Module.finrank ℤ E.toAffine.Point).factorial = E.bsdQuotient := by
  rw [← h.analyticOrderNatAt_eq_finrank hF h₁]
  exact h.leadingCoeff_eq_bsdQuotient hF h₁

/-- Under the Birch–Swinnerton-Dyer conjecture, the `L`-function does not vanish at `s = 1`
exactly when `E(ℚ)` has rank zero. -/
theorem apply_one_ne_zero_iff (h : E.BirchSwinnertonDyer)
    (hF : LSeries.IsContinuationOn ((↑) ∘ E.LFunction) F U) (h₁ : 1 ∈ U) :
    F 1 ≠ 0 ↔ Module.finrank ℤ E.toAffine.Point = 0 := by
  rw [← Nat.cast_eq_zero (R := ℕ∞), ← h.analyticOrderAt_eq_finrank hF h₁,
    (hF.analyticOnNhd 1 h₁).analyticOrderAt_eq_zero]

/-- **The rank-zero case**: under the Birch–Swinnerton-Dyer conjecture, if `E(ℚ)` has rank zero and
`Sha(E/ℚ)` is finite, then `L(E, 1)` is the Birch–Swinnerton-Dyer quotient. -/
theorem apply_one_eq_bsdQuotient (h : E.BirchSwinnertonDyer) [Finite E.sha]
    (hF : LSeries.IsContinuationOn ((↑) ∘ E.LFunction) F U) (h₁ : 1 ∈ U)
    (h₀ : Module.finrank ℤ E.toAffine.Point = 0) : F 1 = E.bsdQuotient := by
  simpa [h₀] using h.iteratedDeriv_finrank_div_factorial hF h₁

end BirchSwinnertonDyer

end WeierstrassCurve

namespace TauCeti

/-- **The Birch–Swinnerton-Dyer conjecture over `ℚ`**: every elliptic curve over `ℚ` satisfies
`WeierstrassCurve.BirchSwinnertonDyer`. -/
def BirchSwinnertonDyerConjecture : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], E.BirchSwinnertonDyer

/-- The defining characterization of `TauCeti.BirchSwinnertonDyerConjecture`. This is the
interface to it outside its defining module. -/
theorem birchSwinnertonDyerConjecture_iff :
    BirchSwinnertonDyerConjecture ↔ ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
      E.BirchSwinnertonDyer :=
  Iff.rfl

end TauCeti
