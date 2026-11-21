/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Trivial
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Basic
public import TauCeti.NumberTheory.LFunctions.Hecke.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.CriticalLine
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Weight

/-!
# The extended and generalized Riemann hypotheses over a number field

This file states the two Riemann hypotheses attached to a number field `K` as propositions about
the continued functions of the LFunctions layers, following `AnalyticNumberTheoryPartI` §2.42 and
`ClassicalArithmeticCompletion` §5.0.

* `TauCeti.DedekindERH K`: the **extended Riemann hypothesis** for `K` — every zero of the
  continued Dedekind zeta function `TauCeti.LFunctions.dedekindZetaC K` in the open critical
  strip `0 < re s < 1` has real part `1/2`.
* `TauCeti.HeckeGRH χ`: the **generalized Riemann hypothesis** for a ray class character `χ` —
  the same statement for the continued Hecke L-function `TauCeti.LFunctions.heckeLFunctionC χ`.

Both are read through the divisor of the continued function on the plane
(`MeromorphicOn.divisor`), so the trivial zeros in `re s ≤ 0` and the pole of the trivial
character at `1` are not exceptions to list: the strip condition removes the trivial zeros, the
pole contributes no zero, and the strip excludes them by condition rather than by case. These
are propositions about the specified functions, not assumptions on arbitrary continuations, and
neither is asserted to hold.

The trivial character of modulus `1` is the bridge between the two statements
(`TauCeti.heckeGRH_one`): its Hecke L-function is the Dedekind zeta function, so
`TauCeti.DedekindERH K` is precisely the trivial-character case of `TauCeti.HeckeGRH`.

## Main definitions

* `TauCeti.DedekindERH`
* `TauCeti.HeckeGRH`

## Main results

* `TauCeti.heckeGRH_one`

## References

* `AnalyticNumberTheoryPartI` §2.42 and `ClassicalArithmeticCompletion` §5.0 of the Tau Ceti
  roadmap
* P. Belabas, M. Diaz y Diaz, D. A. Friedman, §2, pp. 1187-1188, as cited by
  `ClassicalArithmeticCompletion` §5.0; E. Bach, §3, p. 360, for the identification with
  absence of zeros off the line
-/

public section

namespace TauCeti

open Set Complex
open scoped NumberField
open GlobalNumberFields
open RayClassCharacter

/-- The **extended Riemann hypothesis** for the number field `K`: every zero of the continued
Dedekind zeta function `TauCeti.LFunctions.dedekindZetaC K` in the open critical strip
`0 < re s < 1` lies on the critical line `re s = 1/2`. Zeros are read through the divisor on the
plane, so the trivial zeros and the pole at `1` are excluded by the strip condition, and zeros
with `re s ≥ 1` do not occur once line-one nonvanishing is established. -/
def DedekindERH (K : Type*) [Field K] [NumberField K] : Prop :=
  LFunctions.AllOnCriticalLine (LFunctions.dedekindZetaC K) univ
    (Ioo (0 : ℝ) 1 ×ℂ univ)

/-- Unfolding `TauCeti.DedekindERH`: the hypothesis quantifies over the points of the open
critical strip where the divisor of the continued Dedekind zeta function is positive. -/
theorem dedekindERH_def (K : Type*) [Field K] [NumberField K] :
    DedekindERH K ↔
      ∀ ρ ∈ Ioo (0 : ℝ) 1 ×ℂ univ,
        0 < MeromorphicOn.divisor (LFunctions.dedekindZetaC K) univ ρ → ρ.re = 1 / 2 :=
  LFunctions.allOnCriticalLine_iff

/-- The **generalized Riemann hypothesis** for the ray class character `χ`: every zero of the
continued Hecke L-function `TauCeti.LFunctions.heckeLFunctionC χ` in the open critical strip
`0 < re s < 1` lies on the critical line `re s = 1/2`. For a character of modulus `1` this is
the assertion for a character of the class group as in `ClassicalArithmeticCompletion` §5.0; for
a primitive `χ` it is `GRH(χ)` of `AnalyticNumberTheoryPartI` §2.42. Ray class characters have
finite order, being characters of the finite ray class group. -/
def HeckeGRH {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}
    (χ : RayClassCharacter 𝔪) : Prop :=
  LFunctions.AllOnCriticalLine (LFunctions.heckeLFunctionC χ) univ
    (Ioo (0 : ℝ) 1 ×ℂ univ)

theorem heckeGRH_def {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}
    (χ : RayClassCharacter 𝔪) :
    HeckeGRH χ ↔
      ∀ ρ ∈ Ioo (0 : ℝ) 1 ×ℂ univ,
        0 < MeromorphicOn.divisor (LFunctions.heckeLFunctionC χ) univ ρ → ρ.re = 1 / 2 :=
  LFunctions.allOnCriticalLine_iff

section NumberFieldRiemannHypotheses

variable (K : Type*) [Field K] [NumberField K]

/-- `TauCeti.DedekindERH K` is precisely the trivial-character case of `TauCeti.HeckeGRH`: the
class-group character `1` of modulus `1` generalizes to the Hecke statement exactly as the
Dedekind zeta function generalizes the Dirichlet L-series. The proof turns on the trivial weight
of modulus `1` regenerating the ideal-counting coefficients of `NumberField.dedekindZeta`, so the
presented Hecke L-function of the trivial character of modulus `1` is the continued Dedekind zeta
function; that identity is proved here inline rather than exported. -/
theorem heckeGRH_one :
    HeckeGRH (1 : RayClassCharacter (Modulus.one K)) ↔ DedekindERH K := by
  have hc1 : LFunctions.heckeLFunctionC (1 : RayClassCharacter (Modulus.one K)) =
      LFunctions.dedekindZetaC K := by
    have hc :
        ((1 : RayClassCharacter (Modulus.one K))).toUnitaryIdealWeight.toIdealArithmeticFunction =
          (1 : IdealArithmeticFunction K) := by
      ext J
      obtain ⟨P, hP⟩ := J
      simp only [UnitaryIdealWeight.toIdealArithmeticFunction_apply, val_toUnitaryIdealWeight,
        toMultiplicativeIdealWeight_one]
      rw [Modulus.support_one]
      simp [show (P : Ideal (𝓞 K)) ≠ ⊥ from fun h ↦ by
        rw [h] at hP
        exact zero_notMem_nonZeroDivisorsLeft
          ((mem_nonZeroDivisors_iff' (M₀ := Ideal (𝓞 K))).mp hP).1]
    rw [LFunctions.heckeLFunctionC_def, hc, LFunctions.dedekindZetaC_def]
    exact congrArg (meromorphicContinuation 1)
      (funext fun s ↦ (dedekindZeta_eq_LSeries_normCoeff_one K s).symm)
  rw [heckeGRH_def, dedekindERH_def, hc1]

end NumberFieldRiemannHypotheses

end TauCeti
