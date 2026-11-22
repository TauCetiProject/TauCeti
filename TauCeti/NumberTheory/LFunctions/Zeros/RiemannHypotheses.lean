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

/-!
# The extended and generalized Riemann hypotheses over a number field

This file states the two Riemann hypotheses attached to a number field `K` as propositions about
the continued functions of the LFunctions layers.

* `TauCeti.DedekindERH K`: the **extended Riemann hypothesis** for `K` — every zero of the
  continued Dedekind zeta function `TauCeti.LFunctions.dedekindZetaC K` in the open critical
  strip `0 < re s < 1` has real part `1/2`.
* `TauCeti.HeckeGRH χ`: the **generalized Riemann hypothesis** for a ray class character `χ` —
  the same statement for the continued Hecke L-function `TauCeti.LFunctions.heckeLFunctionC χ`.

Both are read through the divisor of the continued function on the plane
(`MeromorphicOn.divisor`), so the trivial zeros in `re s ≤ 0` and the pole of the trivial
character at `1` are not exceptions to list: the strip condition removes the trivial zeros and
excludes the pole, which contributes no zero. Because `TauCeti.LFunctions.dedekindZetaC` and
`TauCeti.LFunctions.heckeLFunctionC` are defined via `TauCeti.meromorphicContinuation 1`, which
falls back to `0` when no whole-plane meromorphic continuation exists (and the zero function has
divisor `0`), each predicate holds trivially on that fallback and only carries its intended
meaning once whole-plane meromorphic continuation of `ζ_K` or `L(s, χ)` is established. Neither
predicate is asserted to hold.

The trivial character of modulus `1` is the bridge between the two statements
(`TauCeti.heckeGRH_one_iff_dedekindERH`): its continued Hecke L-function is
`TauCeti.LFunctions.dedekindZetaC K`, so `TauCeti.DedekindERH K` is equivalent to
`TauCeti.HeckeGRH` for the trivial character of modulus `1`.

## Main definitions

* `TauCeti.DedekindERH`
* `TauCeti.HeckeGRH`

## Main results

* `TauCeti.heckeGRH_one_iff_dedekindERH`

## References

* E. Bach, *Explicit bounds for primality testing and related problems*, Math. Comp. 55 (1990),
  no. 191, 355–380, doi:10.1090/S0025-5718-1990-1023756-8, §3, p. 360.
* K. Belabas, F. Diaz y Diaz, E. Friedman, *Small generators of the ideal class group*,
  Math. Comp. 77 (2008), §2, pp. 1187–1188.
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
plane, so the trivial zeros and the pole at `1` are excluded by the strip condition. The
predicate only has its intended meaning once `TauCeti.LFunctions.dedekindZetaC K` is known to
continue `ζ_K` to the whole plane; otherwise the `TauCeti.meromorphicContinuation` zero fallback
has divisor `0` and makes it hold trivially. -/
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
the statement for a character of the ideal class group; for a primitive `χ` it is the statement
for a primitive finite-order Hecke character. The predicate only has its intended meaning once
`TauCeti.LFunctions.heckeLFunctionC χ` is known to continue `L(s, χ)` to the whole plane;
otherwise the `TauCeti.meromorphicContinuation` zero fallback has divisor `0` and makes it hold
trivially. -/
def HeckeGRH {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}
    (χ : RayClassCharacter 𝔪) : Prop :=
  LFunctions.AllOnCriticalLine (LFunctions.heckeLFunctionC χ) univ
    (Ioo (0 : ℝ) 1 ×ℂ univ)

/-- Unfolding `TauCeti.HeckeGRH`: the hypothesis quantifies over the points of the open
critical strip where the divisor of the continued Hecke L-function is positive. -/
theorem heckeGRH_def {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}
    (χ : RayClassCharacter 𝔪) :
    HeckeGRH χ ↔
      ∀ ρ ∈ Ioo (0 : ℝ) 1 ×ℂ univ,
        0 < MeromorphicOn.divisor (LFunctions.heckeLFunctionC χ) univ ρ → ρ.re = 1 / 2 :=
  LFunctions.allOnCriticalLine_iff

section NumberFieldRiemannHypotheses

variable (K : Type*) [Field K] [NumberField K]

/-- `TauCeti.HeckeGRH` of the trivial ray class character of modulus `1` is equivalent to
`TauCeti.DedekindERH K`, because its continued Hecke L-function is
`TauCeti.LFunctions.dedekindZetaC K`. -/
theorem heckeGRH_one_iff_dedekindERH :
    HeckeGRH (1 : RayClassCharacter (Modulus.one K)) ↔ DedekindERH K := by
  have hc1 : LFunctions.heckeLFunctionC (1 : RayClassCharacter (Modulus.one K)) =
      LFunctions.dedekindZetaC K := by
    rw [LFunctions.heckeLFunctionC_def, toUnitaryIdealWeight_one,
      UnitaryIdealWeight.toIdealArithmeticFunction_one, LFunctions.dedekindZetaC_def]
    exact congrArg (meromorphicContinuation 1)
      (funext fun s ↦ (dedekindZeta_eq_LSeries_normCoeff_one K s).symm)
  rw [heckeGRH_def, dedekindERH_def, hc1]

end NumberFieldRiemannHypotheses

end TauCeti
