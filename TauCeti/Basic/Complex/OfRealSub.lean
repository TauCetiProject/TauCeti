/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Complex.Basic

/-!
# Real points avoid non-real complex numbers

A complex number with nonzero imaginary part differs from every real number. In the form
`(t : ℂ) - z ≠ 0` this is the nonvanishing of the denominator of kernels such as `(t - z)⁻¹`,
which appear in the Cauchy and resolvent (Stieltjes) transforms on the real line.
-/

public section

namespace Complex

/-- For non-real `z`, the point `t - z` is nonzero for every real `t`. -/
theorem ofReal_sub_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) (t : ℝ) : (t : ℂ) - z ≠ 0 :=
  fun h ↦ hz (by simpa using congrArg im h)

end Complex
