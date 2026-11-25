/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinC.Basic

/-!
# The group `Spinᶜ(n)` of the standard form on `ℝⁿ`

This file specializes the group `Spinᶜ(Q)` (`CliffordAlgebra.spinCGroup`) to the standard
positive-definite form on `ℝⁿ`, as `Spin(n)` (`CliffordAlgebra.realCliffordSpinGroupZero`)
specializes `Spin(Q)`.

## Main definitions

* `CliffordAlgebra.realCliffordSpinCGroupZero n`: the group `Spinᶜ(n)` of the standard
  positive-definite form on `ℝⁿ`.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
-/

public section

namespace CliffordAlgebra

/-- **The group `Spinᶜ(n)`** of the standard positive-definite form on `ℝⁿ`, for `n ≥ 1`. -/
abbrev realCliffordSpinCGroupZero (n : ℕ) [NeZero n] : Type :=
  spinCGroup (TauCeti.realCliffordForm n 0) (TauCeti.nondegenerate_realCliffordForm n 0).ne_zero

end CliffordAlgebra
