/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.RingTheory.QuotSMulTop

/-!
# Torsion and reduction of `ℤ`

For `n ≠ 0`, the `n`-torsion of `ℤ` is zero and the reduction `ℤ ⧸ nℤ = QuotSMulTop n ℤ` is
finite. These are recorded as instances, so that `ℤ` meets the finiteness hypotheses of
constructions that take both the `n`-torsion and the reduction mod `n` of a `ℤ`-module.

## Main results

* `TauCeti.subsingleton_torsionBy_int`: the `n`-torsion of `ℤ` is zero for `n ≠ 0`.
* `TauCeti.finite_quotSMulTop_int`: `ℤ ⧸ nℤ` is finite for `n ≠ 0`.
-/

public section

namespace TauCeti

/-- `ℤ` has no nonzero `n`-torsion for `n ≠ 0`. -/
instance subsingleton_torsionBy_int (n : ℕ) [NeZero n] :
    Subsingleton (Submodule.torsionBy ℤ ℤ (n : ℤ)) := by
  refine ⟨fun x y ↦ Subtype.ext ?_⟩
  have hx := (Submodule.mem_torsionBy_iff _ _).mp x.property
  have hy := (Submodule.mem_torsionBy_iff _ _).mp y.property
  simp only [smul_eq_mul, mul_eq_zero, Int.natCast_eq_zero, NeZero.ne n, false_or] at hx hy
  rw [hx, hy]

/-- `ℤ ⧸ nℤ` is finite for `n ≠ 0`. -/
instance finite_quotSMulTop_int (n : ℕ) [NeZero n] : Finite (QuotSMulTop (n : ℤ) ℤ) :=
  Module.finite_of_fg_torsion _ fun x ↦
    ⟨⟨n, mem_nonZeroDivisors_of_ne_zero (Int.natCast_ne_zero.mpr (NeZero.ne n))⟩,
      Module.mem_annihilator.mp (QuotSMulTop.mem_annihilator ℤ (n : ℤ)) x⟩

end TauCeti
