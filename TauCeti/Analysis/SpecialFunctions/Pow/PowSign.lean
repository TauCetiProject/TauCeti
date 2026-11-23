/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Complex powers of the modulus with the sign kept

For a vector `c` in a complex normed space and `w ∈ ℂ`, `TauCeti.powSign w c = ‖c‖ ^ (w - 1) • c`
is `sgn(c) |c| ^ w`: it keeps the direction of `c` and replaces its length by the complex power
`‖c‖ ^ w`, with `powSign w 0 = 0`. It is entire in `w`, equals `c` at `w = 1`
(`TauCeti.powSign_one`), and has norm `‖c‖ ^ re w` for `c ≠ 0` (`TauCeti.norm_powSign`) and at most
`‖c‖ ^ re w` in general (`TauCeti.norm_powSign_le`). Applied pointwise to a function `f`, it gives
Thorin's analytic family `sgn(f) |f| ^ w` through `f`, used to prove the Riesz–Thorin theorem.
-/

public section

open Complex

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- `powSign w c = ‖c‖ ^ (w - 1) • c`, the value at `c` of the analytic family `sgn(f) |f| ^ w`.
The convention `Real.log 0 = 0` gives `powSign w 0 = 0`. -/
noncomputable def powSign (w : ℂ) (c : E) : E :=
  exp ((w - 1) * Real.log ‖c‖) • c

theorem powSign_def (w : ℂ) (c : E) : powSign w c = exp ((w - 1) * Real.log ‖c‖) • c :=
  (rfl)

@[simp]
theorem powSign_one (c : E) : powSign 1 c = c := by
  simp [powSign]

@[simp]
theorem powSign_zero_right (w : ℂ) : powSign w (0 : E) = 0 := by
  simp [powSign]

theorem powSign_ne_zero (w : ℂ) {c : E} (hc : c ≠ 0) : powSign w c ≠ 0 :=
  smul_ne_zero (exp_ne_zero _) hc

theorem norm_powSign (w : ℂ) {c : E} (hc : c ≠ 0) : ‖powSign w c‖ = ‖c‖ ^ w.re := by
  have hpos : 0 < ‖c‖ := norm_pos_iff.2 hc
  have hre : ((w - 1) * (Real.log ‖c‖ : ℂ)).re = Real.log ‖c‖ * (w.re - 1) := by
    simp [mul_comm]
  rw [powSign, norm_smul, norm_exp, hre, ← Real.rpow_def_of_pos hpos,
    Real.rpow_sub_one hpos.ne', div_mul_cancel₀ _ hpos.ne']

theorem norm_powSign_le (w : ℂ) (c : E) : ‖powSign w c‖ ≤ ‖c‖ ^ w.re := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [Real.rpow_nonneg]
  · exact (norm_powSign w hc).le

theorem norm_powSign_le_exp (w : ℂ) (c : E) :
    ‖powSign w c‖ ≤ Real.exp (|w.re| * |Real.log ‖c‖|) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have hpos : 0 < ‖c‖ := norm_pos_iff.2 hc
    rw [norm_powSign w hc, Real.rpow_def_of_pos hpos, mul_comm]
    exact Real.exp_le_exp.2 ((le_abs_self _).trans (abs_mul _ _).le)

end TauCeti
