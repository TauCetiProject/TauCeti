/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.LocalDepthOrder.Cyclotomic

/-!
# Examples of the local-depth order

The Gaussian field `ℚ(i) = ℚ(ζ₄)` has `|μ(ℚ(i))| = 4` roots of unity, and the prime `2` is totally
ramified, `(2) = 𝔓 ^ 2` with `𝔓 = (ζ₄ - 1) = (1 + i)` up to a unit. Along the levels `𝔓 ^ h` the
local-depth order is

* `r(𝔓 ^ h) = 1` for `h ≤ 3`,
* `r(𝔓 ^ h) = 2` for `h = 4, 5`,
* `r(𝔓 ^ h) = 4` for `h ≥ 6`.

The ramification index `e(𝔓 | 2) = 2` is the denominator in `⌊h / 2 - 1⌋`: with `e = 1` the level
`𝔓 ^ 2` would already have order `2`. The level `𝔓 ^ 6` is the first one satisfying the full-depth
inequality `h ≥ e (ord₂ 4 + 1 / (2 - 1)) = 6`. Every number field has `r(𝓞 F) = 1`.
-/

public section

open Ideal NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {2 ^ (1 + 1)} ℚ K] {ζ : K}
  (hζ : IsPrimitiveRoot ζ (2 ^ (1 + 1)))

-- The levels `𝔓 ^ h` with `h ≤ 3` have order `1`.
example {h : ℕ} (hh : h ≤ 3) : localDepthOrder K (span {hζ.toInteger - 1} ^ h) = 1 := by
  rw [localDepthOrder_span_zeta_sub_one_pow hζ]
  interval_cases h <;> norm_num

-- The levels `𝔓 ^ 4` and `𝔓 ^ 5` have order `2`.
example : localDepthOrder K (span {hζ.toInteger - 1} ^ 4) = 2 ∧
    localDepthOrder K (span {hζ.toInteger - 1} ^ 5) = 2 := by
  rw [localDepthOrder_span_zeta_sub_one_pow hζ, localDepthOrder_span_zeta_sub_one_pow hζ]
  norm_num

-- The levels `𝔓 ^ h` with `h ≥ 6` have order `4 = |μ(ℚ(i))|`.
example {h : ℕ} (hh : 6 ≤ h) : localDepthOrder K (span {hζ.toInteger - 1} ^ h) = 4 := by
  rw [localDepthOrder_span_zeta_sub_one_pow hζ]
  have : (2 : ℤ) ≤ ⌊(h : ℚ) / (2 ^ 1 * (2 - 1) : ℕ) - 1 / (((2 : ℕ) : ℚ) - 1)⌋ := by
    rw [Int.le_floor]
    have : (6 : ℚ) ≤ h := mod_cast hh
    push_cast
    linarith
  rw [min_eq_left (by omega)]
  norm_num

-- The unit ideal has order `1` in every number field.
example (F : Type*) [Field F] [NumberField F] : localDepthOrder F ⊤ = 1 :=
  localDepthOrder_top

end TauCeti.NumberField
