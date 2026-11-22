/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import TauCeti.Analysis.Meromorphic.Counting.Basic
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Basic
import TauCeti.NumberTheory.LSeries.CompletedRiemannZeta

/-!
# The Dedekind zeta function of `ℚ` is the Riemann zeta function

Every positive integer is the absolute norm of a unique integral ideal of `𝓞 ℚ`
(`TauCeti.dedekindZetaCoeff_rat`), so `NumberField.dedekindZeta ℚ` has the same `LSeries` as `1`
(`TauCeti.dedekindZeta_rat`), and agrees with `riemannZeta` on the half-plane `Re s > 1`. Since
`riemannZeta` is meromorphic on `ℂ` (`TauCeti.meromorphic_riemannZeta`) and analytic away from
`s = 1`, the canonical continuation `TauCeti.LFunctions.dedekindZetaC ℚ` is the meromorphic normal
form of `riemannZeta`.

At `s = 1` both functions have a simple pole (`dedekindZetaC ℚ 1 = 0` by normal-form normalization,
whereas `riemannZeta 1` is an unnormalized Hurwitz value), so the comparison is stated as an
equality of punctured germs at every `s : ℂ` and as a value identity for `s ≠ 1`. Punctured-germ
agreement transports `meromorphicOrderAt`, `MeromorphicOn.divisor`, `divisorCount`, and `zeroCount`
on arbitrary sets without excluding `1`.

## Main results

* `TauCeti.LFunctions.dedekindZeta_rat_eq_riemannZeta`,
  `TauCeti.LFunctions.dedekindZetaC_rat_eq_toMeromorphicNFOn`,
  `TauCeti.LFunctions.dedekindZetaC_rat_eventuallyEq_riemannZeta`, and
  `TauCeti.LFunctions.dedekindZetaC_rat_eq_riemannZeta`: over `ℚ`, `ζ_ℚ` and `dedekindZetaC ℚ`
  identify with `riemannZeta`.
* `TauCeti.LFunctions.meromorphicOrderAt_dedekindZetaC_rat`,
  `TauCeti.LFunctions.divisor_dedekindZetaC_rat`,
  `TauCeti.LFunctions.divisorCount_dedekindZetaC_rat`, and
  `TauCeti.LFunctions.zeroCount_dedekindZetaC_rat`: order, divisor, and zero-count transport.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
-/

public section

open Filter NumberField Set
open scoped Topology

namespace TauCeti.LFunctions

/-- **On `Re s > 1`, the Dedekind zeta function of `ℚ` equals the Riemann zeta function.** -/
theorem dedekindZeta_rat_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta ℚ s = riemannZeta s := by
  rw [dedekindZeta_rat, LSeries_one_eq_riemannZeta hs]

/-- **The continued Dedekind zeta function of `ℚ` is the meromorphic normal form of
`riemannZeta`.** -/
theorem dedekindZetaC_rat_eq_toMeromorphicNFOn :
    dedekindZetaC ℚ = toMeromorphicNFOn riemannZeta univ := by
  rw [dedekindZetaC_def]
  exact meromorphicContinuation_eq_toMeromorphicNFOn meromorphic_riemannZeta
    (fun s hs ↦ analyticOn_riemannZeta s fun h1 ↦ by simp [mem_singleton_iff.mp h1] at hs)
    fun _ hs ↦ (dedekindZeta_rat_eq_riemannZeta hs).symm

/-- **The continued Dedekind zeta function of `ℚ` has the punctured germ of `riemannZeta`** at
every point of the plane, including the pole `s = 1`. -/
theorem dedekindZetaC_rat_eventuallyEq_riemannZeta (s : ℂ) :
    dedekindZetaC ℚ =ᶠ[𝓝[≠] s] riemannZeta := by
  rw [dedekindZetaC_rat_eq_toMeromorphicNFOn]
  exact meromorphic_riemannZeta.meromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ s)

/-- **The continued Dedekind zeta function of `ℚ` equals `riemannZeta`** at every `s ≠ 1`. At
`s = 1` both sides have a pole, and `dedekindZetaC_rat_eventuallyEq_riemannZeta` compares their
germs there. -/
theorem dedekindZetaC_rat_eq_riemannZeta {s : ℂ} (hs : s ≠ 1) :
    dedekindZetaC ℚ s = riemannZeta s := by
  rw [dedekindZetaC_rat_eq_toMeromorphicNFOn,
    toMeromorphicNFOn_apply_of_analyticAt meromorphic_riemannZeta (analyticOn_riemannZeta s hs)]

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

end TauCeti.LFunctions
