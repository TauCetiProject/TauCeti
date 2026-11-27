/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.OrientedRel
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The oriented relation at `t = 0`

For `t = 0` the oriented relation `Ideal.OrientedRel` is neither symmetric nor reflexive. Over `ℤ`,
at the index `0` and every level `I`, the elementary matrix `e₀₁(2) = !![1, 2; 0, 1]` is related to
the identity: take `U = !![0, 2; 0, 0]`, so that `1 + U D = e₀₁(2)` and `1 + D U = 1`. It is not
related the other way round, nor to itself: for `t = 0` the `0`-th row of the second matrix must
vanish off the diagonal, while that of `e₀₁(2)` is `(1, 2)`.
-/

public section

namespace TauCeti.Examples.OrientedRel

/-- For `t = 0`, the elementary matrix `e₀₁(2)` is in oriented relation with the identity. -/
theorem orientedRel_zero_elementary_one (I : Ideal ℤ) :
    I.OrientedRel (0 : Fin 2) 0 !![1, 2; 0, 1] 1 := by
  refine Ideal.orientedRel_iff.2 ⟨⟨0, I.zero_mem, by simp, by simp⟩, ?_, ?_, ?_⟩ <;>
    simp [Fin.forall_fin_two]

/-- For `t = 0`, the identity is not in oriented relation with the elementary matrix `e₀₁(2)`. -/
theorem not_orientedRel_zero_one_elementary (I : Ideal ℤ) :
    ¬ I.OrientedRel (0 : Fin 2) 0 1 !![1, 2; 0, 1] := by
  rw [Ideal.orientedRel_iff]
  rintro ⟨-, -, hrow, -⟩
  simpa using hrow 1 Fin.zero_lt_one.ne'


/-- For `t = 0`, the elementary matrix `e₀₁(2)` is not in oriented relation with itself. -/
theorem not_orientedRel_zero_elementary_self (I : Ideal ℤ) :
    ¬ I.OrientedRel (0 : Fin 2) 0 !![1, 2; 0, 1] !![1, 2; 0, 1] := by
  rw [Ideal.orientedRel_iff]
  rintro ⟨-, -, hrow, -⟩
  simpa using hrow 1 Fin.zero_lt_one.ne'


end TauCeti.Examples.OrientedRel
