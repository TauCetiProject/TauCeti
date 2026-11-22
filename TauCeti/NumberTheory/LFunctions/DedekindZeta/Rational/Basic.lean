/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Basic
import TauCeti.NumberTheory.LSeries.CompletedRiemannZeta

/-!
# Comparison of the Dedekind zeta function over `ℚ` with `riemannZeta`

For `K = ℚ`, there is a unique integral ideal of each positive norm
(`TauCeti.dedekindZetaCoeff_rat`), so `NumberField.dedekindZeta ℚ` agrees with `riemannZeta` on
`Re s > 1` (`TauCeti.LFunctions.dedekindZeta_rat_eq_riemannZeta`), and `dedekindZetaC ℚ` agrees
with `riemannZeta` as punctured germs everywhere and pointwise away from the pole `s = 1`.

## Main results

* `TauCeti.LFunctions.dedekindZeta_rat_eq_riemannZeta`: over `ℚ`, `ζ_ℚ` equals `riemannZeta` on
  `Re s > 1`.
* `TauCeti.LFunctions.dedekindZetaC_rat_eventuallyEq_riemannZeta`: punctured-germ identification
  of `dedekindZetaC ℚ` with `riemannZeta` at every `s : ℂ`.
* `TauCeti.LFunctions.dedekindZetaC_rat_eq_riemannZeta`: pointwise identification of
  `dedekindZetaC ℚ` with `riemannZeta` for `s ≠ 1`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
-/

public section
noncomputable section

open Filter Set
open scoped Topology

namespace TauCeti.LFunctions

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
