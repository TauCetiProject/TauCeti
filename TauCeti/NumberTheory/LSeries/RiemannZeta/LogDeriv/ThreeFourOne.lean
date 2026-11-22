/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.NumberTheory.LSeries.RiemannZeta

import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.ThreeFourOne

/-!
# The 3-4-1 logarithmic-derivative inequality for `riemannZeta`

Specializing `DirichletCharacter.threeFourOne_neg_re_logDeriv_LFunction_nonneg` to the unique
Dirichlet character modulo `1` yields the classical `3-4-1` inequality for `riemannZeta`:

```text
0 ≤ 3 * (-Re ζ'/ζ(σ)) + 4 * (-Re ζ'/ζ(σ + it)) + (-Re ζ'/ζ(σ + 2it))
```

for every real `σ > 1` and real `t`.

## Main results

* `TauCeti.threeFourOne_neg_re_logDeriv_riemannZeta_nonneg`: the `3-4-1` logarithmic-derivative
  inequality for `riemannZeta`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §13.
-/

public section

open Complex DirichletCharacter

namespace TauCeti

/-- **The `3-4-1` logarithmic-derivative inequality for `riemannZeta`.** For real `σ > 1` and
real `t`, `0 ≤ 3 * (-Re ζ'/ζ(σ)) + 4 * (-Re ζ'/ζ(σ + it)) + (-Re ζ'/ζ(σ + 2it))`. -/
theorem threeFourOne_neg_re_logDeriv_riemannZeta_nonneg {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (-logDeriv riemannZeta σ).re +
      4 * (-logDeriv riemannZeta (σ + t * I)).re +
      (-logDeriv riemannZeta (σ + 2 * t * I)).re := by
  simpa only [DirichletCharacter.LFunction_modOne_eq, one_pow] using
    (1 : DirichletCharacter ℂ 1).threeFourOne_neg_re_logDeriv_LFunction_nonneg hσ t

end TauCeti
