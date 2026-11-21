/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import TauCeti.Analysis.Meromorphic.Continuation
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
import TauCeti.NumberTheory.LSeries.CompletedRiemannZeta

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

For `K = ℚ`, there is a unique integral ideal of each positive norm
(`TauCeti.dedekindZetaCoeff_rat`), so `NumberField.dedekindZeta ℚ` agrees with `riemannZeta` on
`Re s > 1` (`TauCeti.LFunctions.dedekindZeta_rat_eq_riemannZeta`), and `dedekindZetaC ℚ` agrees
with `riemannZeta` as punctured germs everywhere and pointwise away from the pole `s = 1`.

## Main definitions

* `TauCeti.LFunctions.dedekindZetaC`: the continued Dedekind zeta function.

## Main results

* `TauCeti.LFunctions.meromorphicNFOn_dedekindZetaC`: it is in meromorphic normal form on `ℂ`.
* `TauCeti.LFunctions.analyticOnNhd_dedekindZetaC`: it is holomorphic on `Re s > 1`.
* `TauCeti.dedekindZeta_rat_eq_LSeries_zeta`: `dedekindZeta ℚ s` equals the `LSeries` of
  `ArithmeticFunction.zeta`.
* `TauCeti.LFunctions.dedekindZeta_rat_eq_riemannZeta`,
  `TauCeti.LFunctions.dedekindZetaC_rat_eq_toMeromorphicNFOn`,
  `TauCeti.LFunctions.dedekindZetaC_rat_eventuallyEq_riemannZeta`, and
  `TauCeti.LFunctions.dedekindZetaC_rat_eq_riemannZeta`: over `ℚ`, `ζ_ℚ` and `dedekindZetaC ℚ`
  identify with `riemannZeta`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
-/

public section
noncomputable section

open Filter Set
open scoped Topology

namespace TauCeti

/-- Over `ℚ`, the Dedekind zeta series is the `L`-series of `ArithmeticFunction.zeta` at every
complex point (both sides vanish outside the convergence half-plane). -/
theorem dedekindZeta_rat_eq_LSeries_zeta (s : ℂ) :
    NumberField.dedekindZeta ℚ s = LSeries (fun n ↦ (ArithmeticFunction.zeta n : ℂ)) s := by
  rw [dedekindZeta_eq_LSeries_dedekindZetaCoeff]
  refine LSeries_congr (fun {n} hn ↦ ?_) s
  simp [hn]

namespace LFunctions

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

/-- **On `Re s > 1`, the Dedekind zeta function of `ℚ` equals the Riemann zeta function.** -/
theorem dedekindZeta_rat_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta ℚ s = riemannZeta s := by
  rw [dedekindZeta_rat_eq_LSeries_zeta, ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]

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

end LFunctions

end TauCeti
