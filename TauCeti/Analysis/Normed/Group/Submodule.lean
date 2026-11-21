/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Submodule

/-!
# Negation and subtraction in closed submodules of seminormed groups

Mathlib's group structure on a closed submodule of a seminormed group comes from
`ClosedSubmodule.seminormedAddCommGroup`, since `ClosedSubmodule` is only an
`AddSubmonoidClass`; `ClosedSubmodule.coe_neg` and `ClosedSubmodule.coe_sub` compute the ambient
value of a negation and a difference.
-/

public section

namespace ClosedSubmodule

variable {R M : Type*} [Ring R] [SeminormedAddCommGroup M] [Module R M] {S : ClosedSubmodule R M}

/-- The ambient value of a negation in a closed submodule of a seminormed group. -/
@[simp, norm_cast]
theorem coe_neg (x : S) : ((-x : S) : M) = -(x : M) :=
  (rfl)

/-- The ambient value of a difference in a closed submodule of a seminormed group. -/
@[simp, norm_cast]
theorem coe_sub (x y : S) : ((x - y : S) : M) = (x : M) - y :=
  (rfl)

end ClosedSubmodule
