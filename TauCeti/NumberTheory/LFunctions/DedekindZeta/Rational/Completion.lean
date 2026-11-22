/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Completion
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Rational.Basic
import TauCeti.NumberTheory.LSeries.CompletedRiemannZeta

/-!
# Comparison of the completed Dedekind zeta function over `ℚ` with `completedRiemannZeta`

Over `ℚ`, `completedDedekindZeta ℚ` agrees with `completedRiemannZeta` on `Re s > 1`. Extending
this identity by meromorphic continuation identifies `completedDedekindZeta ℚ` with
`completedRiemannZeta` as punctured germs at every point of `ℂ` (including the poles `0` and `1`)
and pointwise away from `{0, 1}`.

Use `TauCeti.LFunctions.completedDedekindZeta_rat_eventuallyEq_completedRiemannZeta` at or near
the simple poles `0` and `1` (where only the punctured-germ comparison applies) and
`TauCeti.LFunctions.completedDedekindZeta_rat_eq_completedRiemannZeta` for pointwise equality off
`{0, 1}`.

## Main results

* `TauCeti.LFunctions.completedDedekindZeta_rat_eventuallyEq_completedRiemannZeta`: punctured-germ
  identification with `completedRiemannZeta` at every `s : ℂ`.
* `TauCeti.LFunctions.completedDedekindZeta_rat_eq_completedRiemannZeta`: pointwise identification
  with `completedRiemannZeta` for `s ≠ 0` and `s ≠ 1`.
-/

public section

noncomputable section

open Complex Filter NumberField Set
open scoped Topology

namespace TauCeti.LFunctions

/-! ### Comparison with the completed Riemann zeta function over `ℚ` -/

/- Adapted from `dedekindZetaC_rat_eventuallyEq_riemannZeta` and
`dedekindZetaC_rat_eq_riemannZeta`
(`TauCeti.NumberTheory.LFunctions.DedekindZeta.Rational.Basic`). -/

private theorem completedDedekindZeta_rat_eqOn :
    EqOn (completedDedekindZeta ℚ) completedRiemannZeta {s | 1 < s.re} := by
  intro s hs
  have hs_re : 1 < s.re := Set.mem_ofPred_eq.mp hs
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs_re
  rw [completedDedekindZeta_eq hs_re, NumberField.discr_rat,
    InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one (Module.finrank_self ℚ),
    InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one (Module.finrank_self ℚ),
    dedekindZeta_rat_eq_riemannZeta hs_re, riemannZeta_def_of_ne_zero hs0]
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hs_re)
  simp [field]

/-- **The completed Dedekind zeta function of `ℚ` has the punctured germ of
`completedRiemannZeta`** at every point of the plane, including the poles `0` and `1`. -/
theorem completedDedekindZeta_rat_eventuallyEq_completedRiemannZeta (s : ℂ) :
    completedDedekindZeta ℚ =ᶠ[𝓝[≠] s] completedRiemannZeta :=
  eventuallyEq_of_meromorphic_of_eqOn_halfPlane (σ := 1)
    (meromorphic_completedDedekindZeta ℚ) meromorphic_completedRiemannZeta
    completedDedekindZeta_rat_eqOn s

/-- **The completed Dedekind zeta function of `ℚ` equals `completedRiemannZeta`** away from `0` and
`1`. At `0` and `1` both sides have simple poles, and
`completedDedekindZeta_rat_eventuallyEq_completedRiemannZeta` compares their germs there. -/
theorem completedDedekindZeta_rat_eq_completedRiemannZeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedDedekindZeta ℚ s = completedRiemannZeta s :=
  eq_of_meromorphic_of_eqOn_halfPlane (σ := 1)
    (meromorphic_completedDedekindZeta ℚ) meromorphic_completedRiemannZeta
    completedDedekindZeta_rat_eqOn (analyticAt_completedDedekindZeta h0 h1)
    (analyticAt_completedRiemannZeta h0 h1)

end TauCeti.LFunctions
