/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Counting.Basic
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Basic

/-!
# The Dedekind zeta function of `ℚ` is the Riemann zeta function

Every positive integer is the absolute norm of a unique integral ideal of `𝓞 ℚ`
(`TauCeti.dedekindZetaCoeff_rat`), so `NumberField.dedekindZeta ℚ` has the same `LSeries` as
`ArithmeticFunction.zeta`, and agrees with `riemannZeta` on the half-plane `Re s > 1`. Since
`riemannZeta` is meromorphic on `ℂ` (`TauCeti.meromorphic_riemannZeta`) and analytic away from
`s = 1`, the canonical continuation `TauCeti.LFunctions.dedekindZetaC ℚ` is the meromorphic normal
form of `riemannZeta`.

At `s = 1` both functions have a simple pole (`dedekindZetaC ℚ 1 = 0` by normal-form normalization,
whereas `riemannZeta 1` is an unnormalized Hurwitz value), so the comparison is stated as an
equality of punctured germs at every `s : ℂ` and as a value identity for `s ≠ 1`. Punctured-germ
agreement transports `meromorphicOrderAt`, `MeromorphicOn.divisor`, `divisorCount`, and `zeroCount`
on arbitrary sets without excluding `1`.

## Main results

* `TauCeti.LFunctions.meromorphicOrderAt_dedekindZetaC_rat`,
  `TauCeti.LFunctions.divisor_dedekindZetaC_rat`,
  `TauCeti.LFunctions.divisorCount_dedekindZetaC_rat`, and
  `TauCeti.LFunctions.zeroCount_dedekindZetaC_rat`: order, divisor, and zero-count transport.
* `TauCeti.LFunctions.zeroCount_zetaEntireCompletion_eq_dedekindZetaC_rat_inter`: zero-count
  comparison between `zetaEntireCompletion` and `dedekindZetaC ℚ`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
-/

public section

open Filter NumberField Set
open scoped Topology

namespace TauCeti

namespace LFunctions

@[simp]
theorem meromorphicOrderAt_dedekindZetaC_rat (s : ℂ) :
    meromorphicOrderAt (dedekindZetaC ℚ) s = meromorphicOrderAt riemannZeta s :=
  meromorphicOrderAt_congr (dedekindZetaC_rat_eventuallyEq_riemannZeta s)

@[simp]
theorem divisor_dedekindZetaC_rat (U : Set ℂ) :
    MeromorphicOn.divisor (dedekindZetaC ℚ) U = MeromorphicOn.divisor riemannZeta U :=
  MeromorphicOn.divisor_congr_nhdsNE fun s _ ↦ dedekindZetaC_rat_eventuallyEq_riemannZeta s

@[simp]
theorem divisorCount_dedekindZetaC_rat (U R : Set ℂ) :
    divisorCount (dedekindZetaC ℚ) U R = divisorCount riemannZeta U R :=
  divisorCount_congr_nhdsNE fun s _ ↦ dedekindZetaC_rat_eventuallyEq_riemannZeta s

@[simp]
theorem zeroCount_dedekindZetaC_rat (U R : Set ℂ) :
    zeroCount (dedekindZetaC ℚ) U R = zeroCount riemannZeta U R :=
  zeroCount_congr_nhdsNE fun s _ ↦ dedekindZetaC_rat_eventuallyEq_riemannZeta s

/-- On any region `R`, the zero count of `zetaEntireCompletion` is the zero count of
`dedekindZetaC ℚ` on the intersection of `R` with the open critical strip. -/
theorem zeroCount_zetaEntireCompletion_eq_dedekindZetaC_rat_inter (R : Set ℂ) :
    zeroCount zetaEntireCompletion univ R =
      zeroCount (dedekindZetaC ℚ) univ (R ∩ {s | s.re ∈ Ioo 0 1}) := by
  rw [zeroCount_dedekindZetaC_rat, zeroCount_zetaEntireCompletion_eq_riemannZeta_inter]

end LFunctions

end TauCeti
