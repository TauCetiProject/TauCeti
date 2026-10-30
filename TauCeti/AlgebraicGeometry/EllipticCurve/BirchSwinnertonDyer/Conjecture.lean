/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
public import Mathlib.Analysis.Analytic.Order
public import TauCeti.AlgebraicGeometry.EllipticCurve.BirchSwinnertonDyer.Quotient
public import TauCeti.NumberTheory.LSeries.AnalyticContinuation
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite

/-!
# The statement of the Birch–Swinnerton-Dyer conjecture over `ℚ`

The Birch–Swinnerton-Dyer conjecture relates the `L`-function `L(E, s)` of an elliptic curve `E`
over `ℚ` to its arithmetic: the order of vanishing of `L(E, s)` at `s = 1` is the rank `r` of
`E(ℚ)`, and the leading coefficient `L^{(r)}(E, 1) / r!` of its Taylor expansion there is the
Birch–Swinnerton-Dyer quotient `Ω(E) · Reg(E/ℚ) · #Sha(E/ℚ) · ∏_p c_p / #E(ℚ)_tors²`
(`WeierstrassCurve.bsdQuotient`).

The Dirichlet series `WeierstrassCurve.LSeries E`, by definition `LSeries ((↑) ∘ E.LFunction)`,
converges absolutely only for `re s > 3 / 2`, so the conjecture is about an analytic continuation
to `s = 1`. The existence of one is a deep theorem (it follows from the modularity of `E`), and
neither it nor the convergence of the series is proved here. This file therefore states the
conjecture *relative to* a continuation: for every analytic function `f` on a connected open set
`U ∋ 1` that agrees with the Dirichlet series on the part of its half-plane of absolute
convergence inside `U` (`LSeries.IsAnalyticContinuation`), the order of vanishing of `f` at `1` is
the rank and its leading coefficient there is the quotient. Two such continuations on the same `U`
agree on `U` (`LSeries.IsAnalyticContinuation.eqOn`), so for a given `U` the order and the
coefficient do not depend on the choice of `f`; asking only for a function analytic near `s = 1`
would admit an unrelated germ and state nothing.

The quotient is defined only when `Sha(E/ℚ)` is finite, and that finiteness, itself part of the
conjecture, is taken as a hypothesis.

## Main definitions

* `WeierstrassCurve.BirchSwinnertonDyerConjecture E`: the Birch–Swinnerton-Dyer conjecture for
  the elliptic curve `E` over `ℚ`.

## Main results

* `WeierstrassCurve.BirchSwinnertonDyerConjecture.analyticOrderAt_eq`: the rank part.
* `WeierstrassCurve.BirchSwinnertonDyerConjecture.iteratedDeriv_div_factorial_eq`: the
  leading-coefficient part.
* `WeierstrassCurve.BirchSwinnertonDyerConjecture.apply_one_ne_zero_iff`: under the conjecture,
  `L(E, 1) ≠ 0` exactly when `E(ℚ)` is finite.
* `WeierstrassCurve.BirchSwinnertonDyerConjecture.apply_one_eq_bsdQuotient`: under the
  conjecture, if `E(ℚ)` is finite then `L(E, 1)` is the quotient.

## References

* B. J. Birch and H. P. F. Swinnerton-Dyer, *Notes on elliptic curves. II*, J. Reine Angew. Math.
  218 (1965), 79–108.
* J. Tate, *On the conjectures of Birch and Swinnerton-Dyer and a geometric analog*, Séminaire
  Bourbaki 306 (1966).
* A. Wiles, *The Birch and Swinnerton-Dyer conjecture*, in *The Millennium Prize Problems*,
  Clay Mathematics Institute, 2006, 31–41.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Appendix C, §16.
-/

public section

namespace WeierstrassCurve

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- **The Birch–Swinnerton-Dyer conjecture** for an elliptic curve `E` over `ℚ` with finite
Shafarevich–Tate group. Let `r` be the rank of `E(ℚ)`. For every analytic continuation `f` of the
`L`-series `WeierstrassCurve.LSeries E` to a connected open set containing `1`, in the sense of
`LSeries.IsAnalyticContinuation`, the order of vanishing of `f` at `1` is `r` and the leading
coefficient `f^{(r)}(1) / r!` of its Taylor expansion at `1` is `WeierstrassCurve.bsdQuotient E`.
-/
def BirchSwinnertonDyerConjecture : Prop :=
  ∀ [Finite E.sha] (f : ℂ → ℂ) (U : Set ℂ),
    LSeries.IsAnalyticContinuation ((↑) ∘ E.LFunction) f U → 1 ∈ U →
      analyticOrderAt f 1 = Module.finrank ℤ E.toAffine.Point ∧
        iteratedDeriv (Module.finrank ℤ E.toAffine.Point) f 1 /
          (Module.finrank ℤ E.toAffine.Point).factorial = E.bsdQuotient

/-- The defining characterization of `WeierstrassCurve.BirchSwinnertonDyerConjecture`. This is
the interface to it outside its defining module. -/
theorem birchSwinnertonDyerConjecture_iff :
    E.BirchSwinnertonDyerConjecture ↔
      ∀ [Finite E.sha] (f : ℂ → ℂ) (U : Set ℂ),
        LSeries.IsAnalyticContinuation ((↑) ∘ E.LFunction) f U → 1 ∈ U →
          analyticOrderAt f 1 = Module.finrank ℤ E.toAffine.Point ∧
            iteratedDeriv (Module.finrank ℤ E.toAffine.Point) f 1 /
              (Module.finrank ℤ E.toAffine.Point).factorial = E.bsdQuotient :=
  Iff.rfl

namespace BirchSwinnertonDyerConjecture

variable {E} [Finite E.sha] {f : ℂ → ℂ} {U : Set ℂ}

/-- **The rank part of the Birch–Swinnerton-Dyer conjecture**: the order of vanishing at `1` of
a continuation of `L(E, s)` is the rank of `E(ℚ)`. -/
theorem analyticOrderAt_eq (h : E.BirchSwinnertonDyerConjecture)
    (hf : LSeries.IsAnalyticContinuation ((↑) ∘ E.LFunction) f U) (h1 : 1 ∈ U) :
    analyticOrderAt f 1 = Module.finrank ℤ E.toAffine.Point :=
  (h f U hf h1).1

/-- **The leading-coefficient part of the Birch–Swinnerton-Dyer conjecture**: if `r` is the rank
of `E(ℚ)`, the coefficient `f^{(r)}(1) / r!` of a continuation `f` of `L(E, s)` is the
Birch–Swinnerton-Dyer quotient. -/
theorem iteratedDeriv_div_factorial_eq (h : E.BirchSwinnertonDyerConjecture)
    (hf : LSeries.IsAnalyticContinuation ((↑) ∘ E.LFunction) f U) (h1 : 1 ∈ U) :
    iteratedDeriv (Module.finrank ℤ E.toAffine.Point) f 1 /
      (Module.finrank ℤ E.toAffine.Point).factorial = E.bsdQuotient :=
  (h f U hf h1).2

/-- Under the Birch–Swinnerton-Dyer conjecture, a continuation of `L(E, s)` is nonzero at `1`
exactly when `E(ℚ)` is finite. -/
theorem apply_one_ne_zero_iff (h : E.BirchSwinnertonDyerConjecture)
    (hf : LSeries.IsAnalyticContinuation ((↑) ∘ E.LFunction) f U) (h1 : 1 ∈ U) :
    f 1 ≠ 0 ↔ Finite E.toAffine.Point := by
  rw [← (hf.analyticAt h1).analyticOrderAt_eq_zero, h.analyticOrderAt_eq hf h1,
    Nat.cast_eq_zero, Module.finrank_eq_zero_iff_isTorsion]
  exact ⟨Module.finite_of_fg_torsion _,
    fun _ ↦ isAddTorsion_iff_isTorsion_int.mp isAddTorsion_of_finite⟩

/-- Under the Birch–Swinnerton-Dyer conjecture, if `E(ℚ)` is finite then the value at `1` of a
continuation of `L(E, s)` is the Birch–Swinnerton-Dyer quotient. -/
theorem apply_one_eq_bsdQuotient [Finite E.toAffine.Point] (h : E.BirchSwinnertonDyerConjecture)
    (hf : LSeries.IsAnalyticContinuation ((↑) ∘ E.LFunction) f U) (h1 : 1 ∈ U) :
    f 1 = E.bsdQuotient := by
  have h0 : Module.finrank ℤ E.toAffine.Point = 0 :=
    Module.IsTorsion.finrank_eq_zero (isAddTorsion_iff_isTorsion_int.mp isAddTorsion_of_finite)
  simpa [h0] using h.iteratedDeriv_div_factorial_eq hf h1

end BirchSwinnertonDyerConjecture

end WeierstrassCurve
