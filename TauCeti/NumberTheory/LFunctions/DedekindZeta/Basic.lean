/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Continuation
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates

/-!
# The continued Dedekind zeta function

Mathlib's `NumberField.dedekindZeta K` is the Dirichlet series `∑_𝔞 N𝔞 ^ (-s)` over the nonzero
integral ideals of `𝓞 K`, and its values are only meaningful on `Re s > 1`, where the series
converges. `TauCeti.LFunctions.dedekindZetaC K` is its canonical meromorphic continuation
(`TauCeti.meromorphicContinuation`): the function in meromorphic normal form on the whole plane
that agrees with `ζ_K` on `Re s > 1`, and `0` if there is none. Two such functions agreeing on a
half-plane agree everywhere, so the continued function is well defined, and every statement about
`ζ_K` off the half-plane of convergence, such as a factorization through other L-functions, is a
statement about `dedekindZetaC K`.

## Main definitions

* `TauCeti.LFunctions.dedekindZetaC`: the continued Dedekind zeta function.

## Main results

* `TauCeti.LFunctions.meromorphicNFOn_dedekindZetaC`: it is in meromorphic normal form on `ℂ`.
* `TauCeti.LFunctions.analyticOnNhd_dedekindZetaC`: it is holomorphic on `Re s > 1`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
-/

public section
noncomputable section

open Set

namespace TauCeti.LFunctions

variable (K : Type*) [Field K] [NumberField K]

/-- **The continued Dedekind zeta function** of a number field `K`: the canonical meromorphic
continuation from `Re s > 1` of Mathlib's `NumberField.dedekindZeta K`. It agrees with `ζ_K` on
`Re s > 1` once a continuation to the plane exists (`meromorphicContinuation_eqOn`), and is `0`
otherwise. -/
def dedekindZetaC : ℂ → ℂ :=
  meromorphicContinuation 1 (NumberField.dedekindZeta K)

/-- The defining equation of the continued Dedekind zeta function, through which the general
results on `meromorphicContinuation` apply to it. -/
theorem dedekindZetaC_def :
    dedekindZetaC K = meromorphicContinuation 1 (NumberField.dedekindZeta K) := (rfl)

/-- The continued Dedekind zeta function is in meromorphic normal form on the plane. -/
theorem meromorphicNFOn_dedekindZetaC : MeromorphicNFOn (dedekindZetaC K) univ :=
  meromorphicNFOn_meromorphicContinuation _ _

/-- The continued Dedekind zeta function is holomorphic on `Re s > 1`. -/
theorem analyticOnNhd_dedekindZetaC : AnalyticOnNhd ℂ (dedekindZetaC K) {s | 1 < s.re} :=
  analyticOnNhd_meromorphicContinuation (analyticOnNhd_dedekindZeta K)

end TauCeti.LFunctions
