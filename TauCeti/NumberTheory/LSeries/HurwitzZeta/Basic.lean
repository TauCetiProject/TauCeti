/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.HurwitzZetaEven

/-!
# Endpoint corrections for the even Hurwitz theta kernel

Mathlib subtracts different terms from the even Hurwitz theta kernel on `(0, 1)` and `(1, ∞)`
to obtain a kernel whose Mellin integral converges at every parameter. These formulas make the
corrections explicit so they can be evaluated in weighted sums of residue-class kernels.
-/

public section

open Set

namespace HurwitzZeta

/-- Below `1`, the modified even Hurwitz kernel subtracts `x ^ (-1 / 2)` independently of the
residue class. -/
theorem hurwitzEvenFEPair_f_modif_of_mem_Ioo (a : UnitAddCircle) {x : ℝ} (hx : x ∈ Ioo 0 1) :
    (hurwitzEvenFEPair a).f_modif x = (evenKernel a x : ℂ) - (x ^ (-(1 / 2) : ℝ) : ℝ) := by
  simp only [WeakFEPair.f_modif, Pi.add_apply, indicator_of_notMem (notMem_Ioi.mpr hx.2.le),
    indicator_of_mem hx, zero_add, hurwitzEvenFEPair, Function.comp_apply, one_mul, smul_eq_mul,
    mul_one]

/-- Above `1`, the modified even Hurwitz kernel subtracts the constant term, which is `1` for the
zero residue class and `0` otherwise. -/
theorem hurwitzEvenFEPair_f_modif_of_one_lt (a : UnitAddCircle) {x : ℝ} (hx : 1 < x) :
    (hurwitzEvenFEPair a).f_modif x = (evenKernel a x : ℂ) - (if a = 0 then 1 else 0) := by
  simp only [WeakFEPair.f_modif, Pi.add_apply, indicator_of_mem (mem_Ioi.mpr hx),
    indicator_of_notMem (notMem_Ioo_of_ge hx.le), add_zero, hurwitzEvenFEPair, Function.comp_apply]

end HurwitzZeta
