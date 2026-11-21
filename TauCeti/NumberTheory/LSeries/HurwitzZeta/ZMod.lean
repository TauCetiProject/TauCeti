/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.ZMod
public import TauCeti.NumberTheory.LSeries.HurwitzZeta.Series
import TauCeti.Data.ZMod.Count

/-!
# Lightweight Hurwitz decompositions of periodic L-functions

This module bridges `ZMod.LFunction`, Mathlib's circle-parametrized `HurwitzZeta.hurwitzZeta`, and
the convergent complex-parameter Hurwitz series `TauCeti.complexHurwitzSeries` without importing
the full analytic continuation machinery.

Reindexing `ZMod N` over positive residue representatives `a ∈ Finset.Icc 1 N` expresses
`ZMod.LFunction Φ s` (applying in particular to any Dirichlet character
`χ : DirichletCharacter ℂ N`, whose `χ.LFunction` is definitionally `ZMod.LFunction χ`) in terms
of `HurwitzZeta.hurwitzZeta` for all `s : ℂ`, and in terms of `TauCeti.complexHurwitzSeries` on
`1 < s.re`.

## Main results

* `ZMod.LFunction_eq_cpow_mul_sum_Icc_hurwitzZeta`: finite `Icc 1 N` decomposition of
  `ZMod.LFunction Φ s` for all `s : ℂ` in terms of `HurwitzZeta.hurwitzZeta`.
* `ZMod.LFunction_eq_cpow_mul_sum_Icc_of_eq_hurwitzZeta`: transport lemma rewriting
  `ZMod.LFunction Φ s` in terms of any function `G : ℂ → ℂ` matching
  `HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s` on `Ioc 0 1`.
* `ZMod.LFunction_eq_cpow_mul_sum_Icc_complexHurwitzSeries`: finite `Icc 1 N` decomposition of
  `ZMod.LFunction Φ s` for `1 < s.re` in terms of `TauCeti.complexHurwitzSeries`.
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
with `HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s` on real shifts `x ∈ (0, 1]`. -/
theorem LFunction_eq_cpow_mul_sum_Icc_of_eq_hurwitzZeta (Φ : ZMod N → ℂ) (s : ℂ) {G : ℂ → ℂ}
    (hG : ∀ ⦃x : ℝ⦄, x ∈ Ioc 0 1 → G x = HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s) :
    ZMod.LFunction Φ s =
      (N : ℂ) ^ (-s) * ∑ a ∈ Finset.Icc 1 N, Φ a * G ((a : ℂ) / N) := by
  rw [ZMod.LFunction_eq_cpow_mul_sum_Icc_hurwitzZeta]
  congr 1
  refine Finset.sum_congr rfl fun a ha => ?_
  obtain ⟨ha1, haN⟩ := Finset.mem_Icc.mp ha
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hx : (a : ℝ) / N ∈ Ioc 0 1 :=
    ⟨div_pos (by exact_mod_cast ha1) hN, (div_le_one hN).mpr (by exact_mod_cast haN)⟩
  rw [← hG hx]
  simp_rw [Complex.ofReal_div, Complex.ofReal_natCast]

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
