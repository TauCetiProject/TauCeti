/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Normed.Module.Seminorm.Norm

/-!
# Separating radii by norms of a nontrivially normed field

In a nontrivially normed field `𝕜` the norms need not be dense, so two radii `0 < r < s` need not
be separated by the norm of an element of `𝕜`. They are separated after raising to a power:
`NormedField.exists_pow_lt_norm_lt_pow` gives `m : ℕ` and `c : 𝕜` with `rᵐ < ‖c‖ < sᵐ`. Compare
`NormedField.exists_lt_norm_lt`, which separates the radii themselves in a densely normed field.
-/

public section

namespace NormedField

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]

/-- **Two radii `0 < r < s` are separated by a norm after raising to a power**: there are `m : ℕ`
and `c : 𝕜` with `rᵐ < ‖c‖ < sᵐ`. -/
theorem exists_pow_lt_norm_lt_pow {r s : ℝ} (hr₀ : 0 < r) (hlt : r < s) :
    ∃ (m : ℕ) (c : 𝕜), r ^ m < ‖c‖ ∧ ‖c‖ < s ^ m := by
  -- choose `m` with `‖k‖ < (s / r)ᵐ` and `c` in the shell `sᵐ / ‖k‖ ≤ ‖c‖ < sᵐ`
  obtain ⟨k, hk⟩ := exists_one_lt_norm 𝕜
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ‖k‖ ((one_lt_div hr₀).mpr hlt)
  obtain ⟨c, -, hcs, hcr, -⟩ :=
    rescale_to_shell hk (pow_pos (hr₀.trans hlt) m) (one_ne_zero' 𝕜)
  rw [smul_eq_mul, mul_one] at hcs hcr
  refine ⟨m, c, lt_of_lt_of_le ?_ hcr, hcs⟩
  rw [lt_div_iff₀ (one_pos.trans hk), ← lt_div_iff₀' (pow_pos hr₀ m), ← div_pow]
  exact hm

end NormedField
