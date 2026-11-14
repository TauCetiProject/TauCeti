/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.WithAbs

/-!
# Completion maps along extensions of absolute values

If `w` is an absolute value on `L` lying over an absolute value `v` on `K`, the completion map
`AbsoluteValue.Completion.map v w : v.Completion →+* w.Completion` is an isometry, so it preserves
the norm (`AbsoluteValue.Completion.norm_map`).
-/

public section

namespace AbsoluteValue.Completion

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {v : AbsoluteValue K ℝ} {w : AbsoluteValue L ℝ} [w.LiesOver v]

/-- The completion map along an extension of absolute values preserves the norm. -/
@[simp]
theorem norm_map (x : v.Completion) : ‖map v w x‖ = ‖x‖ :=
  (isometry_map v w).norm_map_of_map_zero (map_zero _) x

end AbsoluteValue.Completion
