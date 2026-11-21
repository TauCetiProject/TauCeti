/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.HurwitzZeta.Continuation
public import TauCeti.NumberTheory.LSeries.ZMod

/-!
# Finite Hurwitz decompositions of periodic L-functions

Reindexing `ZMod N` over positive residue representatives `a ∈ Finset.Icc 1 N` expresses
`ZMod.LFunction Φ s` (for `Φ : ZMod N → ℂ`, including Dirichlet characters
`χ : DirichletCharacter ℂ N`) in terms of the continued complex Hurwitz zeta function
`TauCeti.complexHurwitzZeta s ((a : ℂ) / N)` away from `s = 1`, and in terms of
`TauCeti.complexHurwitzSeries s ((a : ℂ) / N)` on `1 < s.re`.

## Main results

* `ZMod.LFunction_eq_cpow_mul_sum_Icc_complexHurwitzZeta`: finite `Icc 1 N` decomposition of
  `ZMod.LFunction Φ s` for `s ≠ 1` in terms of `TauCeti.complexHurwitzZeta`.
* `ZMod.LFunction_eq_cpow_mul_sum_Icc_complexHurwitzSeries`: finite `Icc 1 N` decomposition of
  `ZMod.LFunction Φ s` for `1 < s.re` in terms of `TauCeti.complexHurwitzSeries`.
-/

public section

open Complex Set

namespace ZMod

variable {N : ℕ} [NeZero N]

/-- Away from `s = 1`, `ZMod.LFunction Φ s` is `(N : ℂ) ^ (-s)` times the finite sum of
`Φ a * TauCeti.complexHurwitzZeta s (a / N)` over `a ∈ {1, ..., N}`. Applies in particular to any
Dirichlet character `χ : DirichletCharacter ℂ N`. -/
theorem LFunction_eq_cpow_mul_sum_Icc_complexHurwitzZeta (Φ : ZMod N → ℂ) {s : ℂ} (hs : s ≠ 1) :
    ZMod.LFunction Φ s =
      (N : ℂ) ^ (-s) *
        ∑ a ∈ Finset.Icc 1 N, Φ a * TauCeti.complexHurwitzZeta s ((a : ℂ) / N) := by
  rw [ZMod.LFunction_eq_cpow_mul_sum_Icc_hurwitzZeta]
  congr 1
  refine Finset.sum_congr rfl fun a ha => ?_
  obtain ⟨ha1, haN⟩ := Finset.mem_Icc.mp ha
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hx : (a : ℝ) / N ∈ Ioc 0 1 :=
    ⟨div_pos (by exact_mod_cast ha1) hN, (div_le_one hN).mpr (by exact_mod_cast haN)⟩
  rw [← TauCeti.complexHurwitzZeta_ofReal_eq_hurwitzZeta hs hx]
  push_cast; rfl

/-- On `1 < s.re`, `ZMod.LFunction Φ s` equals `(N : ℂ) ^ (-s)` times the finite sum of
`Φ a * TauCeti.complexHurwitzSeries s (a / N)` over `a ∈ {1, ..., N}`. Applies in particular to any
Dirichlet character `χ : DirichletCharacter ℂ N`. -/
theorem LFunction_eq_cpow_mul_sum_Icc_complexHurwitzSeries (Φ : ZMod N → ℂ) {s : ℂ}
    (hs : 1 < s.re) :
    ZMod.LFunction Φ s =
      (N : ℂ) ^ (-s) *
        ∑ a ∈ Finset.Icc 1 N, Φ a * TauCeti.complexHurwitzSeries s ((a : ℂ) / N) := by
  have hs1 : s ≠ 1 := fun h => lt_irrefl (1 : ℝ) (by rwa [h, one_re] at hs)
  rw [LFunction_eq_cpow_mul_sum_Icc_complexHurwitzZeta Φ hs1]
  congr 1
  refine Finset.sum_congr rfl fun a ha => ?_
  have hre : 0 < ((a : ℂ) / N).re := by
    have heq : ((a : ℂ) / N) = (((a : ℝ) / N : ℝ) : ℂ) := by push_cast; rfl
    rw [heq, ofReal_re]
    exact div_pos (by exact_mod_cast (Finset.mem_Icc.mp ha).1) (Nat.cast_pos.mpr (NeZero.pos N))
  rw [TauCeti.complexHurwitzZeta_eq_complexHurwitzSeries hs hre]

end ZMod

end
