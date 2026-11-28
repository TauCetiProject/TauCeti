/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import TauCeti.Analysis.Meromorphic.Continuation
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
import TauCeti.NumberTheory.LSeries.RiemannZeta.Meromorphic

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
* `TauCeti.LFunctions.meromorphic_dedekindZetaC`: it is meromorphic on `ℂ`.
* `TauCeti.LFunctions.analyticOnNhd_dedekindZetaC`: it is holomorphic on `Re s > 1`.
* `TauCeti.LFunctions.dedekindZeta_rat_eq_riemannZeta`,
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

/-- The continued Dedekind zeta function is meromorphic on the plane. -/
@[fun_prop]
theorem meromorphic_dedekindZetaC : Meromorphic (dedekindZetaC K) :=
  meromorphicOn_univ.mp (meromorphicNFOn_dedekindZetaC K).meromorphicOn

/-- The continued Dedekind zeta function is holomorphic on `Re s > 1`. -/
theorem analyticOnNhd_dedekindZetaC : AnalyticOnNhd ℂ (dedekindZetaC K) {s | 1 < s.re} :=
  analyticOnNhd_meromorphicContinuation (analyticOnNhd_dedekindZeta K)

/-- **On `Re s > 1`, the Dedekind zeta function of `ℚ` equals the Riemann zeta function.** -/
theorem dedekindZeta_rat_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta ℚ s = riemannZeta s := by
  rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs,
    dedekindZeta_eq_LSeries_dedekindZetaCoeff]
  refine LSeries_congr (fun {n} hn ↦ ?_) s
  rw [ArithmeticFunction.zeta_apply, ite_eq_right hn, dedekindZetaCoeff_rat, Nat.cast_one]

/-- **The continued Dedekind zeta function of `ℚ` has the punctured germ of `riemannZeta`** at
every point of the plane, including the pole `s = 1`. -/
theorem dedekindZetaC_rat_eventuallyEq_riemannZeta (s : ℂ) :
    dedekindZetaC ℚ =ᶠ[𝓝[≠] s] riemannZeta := by
  rw [dedekindZetaC_def]
  exact meromorphicContinuation_eventuallyEq meromorphic_riemannZeta
    (analyticOn_riemannZeta.mono fun z hz h ↦ by simp [Set.mem_singleton_iff.mp h] at hz)
    (fun _ hs ↦ (dedekindZeta_rat_eq_riemannZeta hs).symm) s

/-- **The continued Dedekind zeta function of `ℚ` equals `riemannZeta`** at every `s ≠ 1`. At
`s = 1` both sides have a pole, and `dedekindZetaC_rat_eventuallyEq_riemannZeta` compares their
germs there. -/
theorem dedekindZetaC_rat_eq_riemannZeta {s : ℂ} (hs : s ≠ 1) :
    dedekindZetaC ℚ s = riemannZeta s := by
  rw [dedekindZetaC_def]
  exact meromorphicContinuation_apply meromorphic_riemannZeta
    (analyticOn_riemannZeta.mono fun z hz h ↦ by simp [Set.mem_singleton_iff.mp h] at hz)
    (fun _ hs ↦ (dedekindZeta_rat_eq_riemannZeta hs).symm)
    (analyticOn_riemannZeta s hs)

end TauCeti.LFunctions
