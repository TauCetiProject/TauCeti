/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Basic

import TauCeti.NumberTheory.LSeries.RiemannZeta.FunctionalEquation

/-!
# Logarithmic derivatives of the completed Riemann zeta function

Away from `0`, `1`, and the zeros of `riemannZeta`, the pole-clearing factorization
`zetaEntireCompletion s = s * (s - 1) * completedRiemannZeta s` yields the decomposition

```text
logDeriv zetaEntireCompletion s =
  1 / s + 1 / (s - 1) + logDeriv Gammaℝ s + logDeriv riemannZeta s.
```

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §12.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2006), §10.2.
-/

public section

open Complex Filter Topology

namespace TauCeti.LFunctions

/-- Away from `0`, `1`, and the zeros of `ζ`, the logarithmic derivative of the entire completion
splits into the pole-clearing terms `1 / s + 1 / (s - 1)`, the archimedean term, and `ζ'/ζ`. -/
theorem logDeriv_zetaEntireCompletion_eq_add {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) :
    logDeriv zetaEntireCompletion s =
      1 / s + 1 / (s - 1) + logDeriv Gammaℝ s + logDeriv riemannZeta s := by
  have hΛ : completedRiemannZeta s ≠ 0 := by
    intro h
    apply hζ
    rw [riemannZeta_def_of_ne_zero hs0, h, zero_div]
  have heq : zetaEntireCompletion =ᶠ[𝓝 s] fun z : ℂ ↦ z * (z - 1) * completedRiemannZeta z := by
    filter_upwards [(isOpen_ne.inter isOpen_ne).mem_nhds ⟨hs0, hs1⟩] with z hz
    exact zetaEntireCompletion_eq_mul hz.1 hz.2
  have hprod0 : s * (s - 1) ≠ 0 := mul_ne_zero hs0 (sub_ne_zero.mpr hs1)
  have hld_prod : logDeriv (fun z : ℂ ↦ z * (z - 1)) s = 1 / s + 1 / (s - 1) := by
    rw [logDeriv_fun_mul (f := fun z : ℂ ↦ z) (g := fun z : ℂ ↦ z - 1) s
      hs0 (sub_ne_zero.mpr hs1) (by fun_prop) (by fun_prop)]
    simp [logDeriv_apply]
  rw [(logDeriv_congr_nhds heq).eq_of_nhds,
    logDeriv_fun_mul (f := fun z : ℂ ↦ z * (z - 1)) (g := completedRiemannZeta)
      s hprod0 hΛ (by fun_prop) (differentiableAt_completedZeta hs0 hs1),
    hld_prod, logDeriv_riemannZeta_eq_completedRiemannZeta_sub_Gammaℝ hs0 hs1 hζ]
  ring

end TauCeti.LFunctions
