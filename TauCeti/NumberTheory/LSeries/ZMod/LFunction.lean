/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.ZMod
import TauCeti.Data.ZMod.Count

/-!
# Circle-Hurwitz decompositions of periodic L-functions

Reindexing `ZMod N` over positive residue representatives `a ∈ Finset.Icc 1 N` expresses
`ZMod.LFunction Φ s` (applying in particular to any Dirichlet character
`χ : DirichletCharacter ℂ N`, whose `χ.LFunction` is definitionally `ZMod.LFunction χ`) in terms
of Mathlib's `HurwitzZeta.hurwitzZeta` for all `s : ℂ`, and transports any function agreeing with
`HurwitzZeta.hurwitzZeta ((a / N : ℝ) : UnitAddCircle) s` at the sampled shifts
`a ∈ Finset.Icc 1 N`.

## Main results

* `ZMod.LFunction_eq_cpow_mul_sum_Icc_hurwitzZeta`: finite `Icc 1 N` decomposition of
  `ZMod.LFunction Φ s` for all `s : ℂ` in terms of `HurwitzZeta.hurwitzZeta`.
* `ZMod.LFunction_eq_cpow_mul_sum_Icc_of_eq_hurwitzZeta`: transport lemma rewriting
  `ZMod.LFunction Φ s` in terms of any function `G : ℂ → ℂ` matching
  `HurwitzZeta.hurwitzZeta ((a / N : ℝ) : UnitAddCircle) s` for `a ∈ Finset.Icc 1 N`.
-/

public section

open Complex Set

namespace ZMod

variable {N : ℕ} [NeZero N]

/-- Reindexing `ZMod N` over `a ∈ {1, ..., N}` expresses `ZMod.LFunction Φ s` for all `s ∈ ℂ`
(including `s = 1`) as `(N : ℂ) ^ (-s)` times the finite circle-Hurwitz sum over the positive
residue representatives `a / N ∈ (0, 1]`. -/
theorem LFunction_eq_cpow_mul_sum_Icc_hurwitzZeta (Φ : ZMod N → ℂ) (s : ℂ) :
    ZMod.LFunction Φ s =
      (N : ℂ) ^ (-s) *
        ∑ a ∈ Finset.Icc 1 N,
          Φ a * HurwitzZeta.hurwitzZeta ((a / N : ℝ) : UnitAddCircle) s := by
  rw [ZMod.LFunction, ZMod.sum_eq_sum_Icc]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ZMod.toAddCircle_natCast]

/-- Transport lemma rewriting `ZMod.LFunction Φ s` in terms of any function `G : ℂ → ℂ` agreeing
with `HurwitzZeta.hurwitzZeta ((a / N : ℝ) : UnitAddCircle) s` at the sampled shifts
`a ∈ Finset.Icc 1 N`. -/
theorem LFunction_eq_cpow_mul_sum_Icc_of_eq_hurwitzZeta (Φ : ZMod N → ℂ) (s : ℂ) {G : ℂ → ℂ}
    (hG : ∀ ⦃a : ℕ⦄, a ∈ Finset.Icc 1 N →
      G ((a : ℂ) / N) = HurwitzZeta.hurwitzZeta ((a / N : ℝ) : UnitAddCircle) s) :
    ZMod.LFunction Φ s =
      (N : ℂ) ^ (-s) * ∑ a ∈ Finset.Icc 1 N, Φ a * G ((a : ℂ) / N) := by
  rw [ZMod.LFunction_eq_cpow_mul_sum_Icc_hurwitzZeta]
  congr 1
  exact Finset.sum_congr rfl fun a ha => by rw [hG ha]

end ZMod

end
