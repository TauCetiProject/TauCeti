/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Powers

/-!
# The squares in the ideles of `ℚ` are closed

The squaring map `x ↦ x²` of `𝔾ₘ` induces on adelic points the squaring map of the ideles `𝔸_ℚ^×`.
Its image `(𝔸_ℚ^×)²` is closed: an idele is a square exactly when each of its coordinates is, and
the squares of each local unit group form an open, hence closed, subgroup
(`NumberField.IdeleGroup.isClosed_range_powMonoidHom`).

## Main results

* `TauCeti.Examples.AdelicSquares.isClosed_range_sq`: `(𝔸_ℚ^×)²` is closed.
-/

public section

open NumberField

namespace TauCeti.Examples.AdelicSquares

/-- **The squares are closed in the ideles of `ℚ`.** -/
theorem isClosed_range_sq :
    IsClosed ((powMonoidHom 2 : IdeleGroup (𝓞 ℚ) ℚ →* IdeleGroup (𝓞 ℚ) ℚ).range :
      Set (IdeleGroup (𝓞 ℚ) ℚ)) :=
  IdeleGroup.isClosed_range_powMonoidHom 2

end TauCeti.Examples.AdelicSquares
