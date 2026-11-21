/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.HurwitzZeta.Continuation
public import TauCeti.NumberTheory.LSeries.HurwitzZeta.ZMod

/-!
# Finite complex-Hurwitz decomposition of continued periodic L-functions

Reindexing `ZMod N` over positive residue representatives `a ∈ Finset.Icc 1 N` expresses
`ZMod.LFunction Φ s` (for `Φ : ZMod N → ℂ`, applying in particular to any Dirichlet character
`χ : DirichletCharacter ℂ N`, whose `χ.LFunction` is definitionally `ZMod.LFunction χ`) in terms
of the continued complex Hurwitz zeta function `TauCeti.complexHurwitzZeta s ((a : ℂ) / N)` away
from `s = 1`.

See `TauCeti.NumberTheory.LSeries.HurwitzZeta.ZMod` for the lightweight circle-Hurwitz, transport,
and convergent `TauCeti.complexHurwitzSeries` decompositions.

## Main results

* `ZMod.LFunction_eq_cpow_mul_sum_Icc_complexHurwitzZeta`: finite `Icc 1 N` decomposition of
  `ZMod.LFunction Φ s` for `s ≠ 1` in terms of `TauCeti.complexHurwitzZeta`.
-/

public section

open Complex Set

namespace ZMod

variable {N : ℕ} [NeZero N]

/-- Away from `s = 1`, `ZMod.LFunction Φ s` is `(N : ℂ) ^ (-s)` times the finite sum of
`Φ a * TauCeti.complexHurwitzZeta s (a / N)` over `a ∈ {1, ..., N}`. -/
theorem LFunction_eq_cpow_mul_sum_Icc_complexHurwitzZeta (Φ : ZMod N → ℂ) {s : ℂ} (hs : s ≠ 1) :
    ZMod.LFunction Φ s =
      (N : ℂ) ^ (-s) *
        ∑ a ∈ Finset.Icc 1 N, Φ a * TauCeti.complexHurwitzZeta s ((a : ℂ) / N) :=
  LFunction_eq_cpow_mul_sum_Icc_of_eq_hurwitzZeta Φ s
    fun _ hx => TauCeti.complexHurwitzZeta_ofReal_eq_hurwitzZeta hs hx

end ZMod

end
