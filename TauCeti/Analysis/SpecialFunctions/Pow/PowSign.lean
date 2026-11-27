/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Sign
import TauCeti.Basic.Real.Sign

/-!
# Complex powers of the modulus with the sign kept

For a vector `c` in a complex normed space and `w ∈ ℂ`, `TauCeti.powSign w c = ‖c‖ ^ (w - 1) • c`
is `sgn(c) |c| ^ w`: it keeps the direction of `c` and replaces its length by the complex power
`‖c‖ ^ w`, with `powSign w 0 = 0`. It is entire in `w`, equals `c` at `w = 1`
(`TauCeti.powSign_one`), and has norm `‖c‖ ^ re w` for `c ≠ 0` (`TauCeti.norm_powSign`) and at most
`‖c‖ ^ re w` in general (`TauCeti.norm_powSign_le`). Applied pointwise to a function `f`, it gives
Thorin's analytic family `sgn(f) |f| ^ w` through `f`, used to prove the Riesz–Thorin theorem.

On the real line the signed powers `|x|^r sgn(x)^j` are at most `|x|^r` in absolute value
(`TauCeti.abs_abs_rpow_mul_sign_pow_le`). For all real `r` and `x`,
`|x| ^ (r - 2) x = |x| ^ (r - 1) sgn(x)` (`Real.abs_rpow_sub_two_mul_eq_mul_sign`). For `p > 1`,
where `|x| ^ p` is differentiable everywhere, this turns Mathlib's derivative `p |x| ^ (p - 2) x`
of `|x| ^ p` (`hasDerivAt_abs_rpow`) into the signed power `p |x| ^ (p - 1) sgn(x)`.
-/

public section

open Complex

namespace Real

/-- The identity `|x|^(r - 2) x = |x|^(r - 1) sgn(x)`, for all real `r` and `x`. For `r > 1` it
rewrites Mathlib's derivative `|x|^(r - 2) x` of `|x|^r / r` (`hasDerivAt_abs_rpow`) as a signed
power. -/
theorem abs_rpow_sub_two_mul_eq_mul_sign (r x : ℝ) :
    |x| ^ (r - 2) * x = |x| ^ (r - 1) * sign x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [sign_zero]
  · -- `Real.rpow_add_one` peels a factor `|x|` off an exponent of the form `a + 1`, so the
    -- exponent `r - 1` is first written in that form, as `(r - 2) + 1`.
    rw [show r - 1 = r - 2 + 1 by ring, rpow_add_one (abs_pos.2 hx).ne', mul_assoc, abs_mul_sign]

end Real

namespace TauCeti

/-- The signed power `|x|^r sgn(x)^j` is at most `|x|^r` in absolute value. -/
theorem abs_abs_rpow_mul_sign_pow_le {r : ℝ} (j : ℕ) (x : ℝ) :
    |(|x| ^ r * Real.sign x ^ j)| ≤ |x| ^ r := by
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) r)]
  exact mul_le_of_le_one_right (Real.rpow_nonneg (abs_nonneg x) r) (Real.abs_sign_pow_le_one x j)

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
