/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.HurwitzZeta.Series
public import TauCeti.NumberTheory.LSeries.ZMod.LFunction

/-!
# Complex Hurwitz series decomposition of periodic L-functions

Bridges `ZMod.LFunction` (applying in particular to any Dirichlet character
`χ : DirichletCharacter ℂ N`, whose `χ.LFunction` is definitionally `ZMod.LFunction χ`) and the
convergent complex-parameter Hurwitz series `TauCeti.complexHurwitzSeries` on `1 < s.re` without
importing the full analytic continuation machinery.

See `TauCeti.NumberTheory.LSeries.ZMod.LFunction` for the underlying circle-Hurwitz and transport
lemmas.

## Main results

* `ZMod.LFunction_eq_cpow_mul_sum_Icc_complexHurwitzSeries`: finite `Icc 1 N` decomposition of
  `ZMod.LFunction Φ s` for `1 < s.re` in terms of `TauCeti.complexHurwitzSeries`.
-/

public section

open Complex Set

namespace ZMod

variable {N : ℕ} [NeZero N]

/-- On `1 < s.re`, `ZMod.LFunction Φ s` equals `(N : ℂ) ^ (-s)` times the finite sum of
`Φ a * TauCeti.complexHurwitzSeries s (a / N)` over `a ∈ {1, ..., N}`. -/
theorem LFunction_eq_cpow_mul_sum_Icc_complexHurwitzSeries (Φ : ZMod N → ℂ) {s : ℂ}
    (hs : 1 < s.re) :
    ZMod.LFunction Φ s =
      (N : ℂ) ^ (-s) *
        ∑ a ∈ Finset.Icc 1 N, Φ a * TauCeti.complexHurwitzSeries s ((a : ℂ) / N) :=
  LFunction_eq_cpow_mul_sum_Icc_of_eq_hurwitzZeta Φ s
    fun _ hx => TauCeti.complexHurwitzSeries_ofReal_eq_hurwitzZeta hs hx

end ZMod

end
